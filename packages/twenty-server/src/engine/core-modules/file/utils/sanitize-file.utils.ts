import DOMPurify from 'dompurify';
import { JSDOM } from 'jsdom';

const JPEG_SOI_0 = 0xff;
const JPEG_SOI_1 = 0xd8;

const PNG_SIGNATURE = Buffer.from([
  0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a,
]);

const isJpegBuffer = (buffer: Buffer): boolean =>
  buffer.length >= 2 &&
  buffer[0] === JPEG_SOI_0 &&
  buffer[1] === JPEG_SOI_1;

const isAppMarker = (marker: number): boolean =>
  marker >= 0xe0 && marker <= 0xef;

const isCommentMarker = (marker: number): boolean => marker === 0xfe;

/**
 * Strips APPn (EXIF/XMP/IPTC/JFIF) and COM segments from a JPEG buffer.
 * Image data (SOF/DQT/DHT/SOS/scan data) is preserved byte-for-byte.
 */
const stripJpegMetadata = (buffer: Buffer): Buffer => {
  const chunks: Buffer[] = [buffer.subarray(0, 2)];
  let offset = 2;

  while (offset < buffer.length) {
    if (buffer[offset] !== 0xff) {
      // Start of scan data or entropy-coded data: copy the rest verbatim.
      chunks.push(buffer.subarray(offset));
      break;
    }

    // Skip padding bytes.
    while (offset < buffer.length && buffer[offset] === 0xff) {
      offset += 1;
    }

    if (offset >= buffer.length) {
      break;
    }

    const marker = buffer[offset];
    offset += 1;

    if (marker === 0x01 || (marker >= 0xd0 && marker <= 0xd9)) {
      // Standalone markers (TEM, RSTn, SOI, EOI): single byte, no length.
      chunks.push(Buffer.from([0xff, marker]));
      if (marker === 0xd9) {
        break;
      }
      continue;
    }

    if (marker === 0xda) {
      // Start of scan: header has a length, then entropy-coded data follows
      // until EOI. Find EOI by scanning for 0xFF 0xD9 outside byte-stuffing.
      if (offset + 2 > buffer.length) {
        break;
      }
      const segmentLength = buffer.readUInt16BE(offset);
      const headerEnd = offset + segmentLength;

      if (headerEnd > buffer.length) {
        break;
      }

      chunks.push(Buffer.from([0xff, marker]));
      chunks.push(buffer.subarray(offset, headerEnd));

      let scanEnd = -1;

      for (let i = headerEnd; i + 1 < buffer.length; i += 1) {
        if (buffer[i] !== 0xff) {
          continue;
        }

        if (buffer[i + 1] === 0x00) {
          i += 1;
          continue;
        }

        if (buffer[i + 1] === 0xd9) {
          scanEnd = i;
          break;
        }
        // Other markers inside scan data (e.g. RSTn) are part of the stream;
        // keep scanning.
      }

      if (scanEnd === -1) {
        chunks.push(buffer.subarray(headerEnd));
        break;
      }

      chunks.push(buffer.subarray(headerEnd, scanEnd));
      chunks.push(Buffer.from([0xff, 0xd9]));
      // Anything trailing EOI (rare) is preserved.
      if (scanEnd + 2 < buffer.length) {
        chunks.push(buffer.subarray(scanEnd + 2));
      }
      break;
    }

    if (offset + 2 > buffer.length) {
      break;
    }

    const segmentLength = buffer.readUInt16BE(offset);

    if (segmentLength < 2 || offset + segmentLength > buffer.length) {
      // Malformed segment: preserve the rest to avoid corrupting the image.
      chunks.push(buffer.subarray(offset - 2));
      break;
    }

    if (isAppMarker(marker) || isCommentMarker(marker)) {
      // Drop metadata segment (EXIF APP1, IPTC APP13, XMP, comments, ...).
      offset += segmentLength;
      continue;
    }

    chunks.push(Buffer.from([0xff, marker]));
    chunks.push(buffer.subarray(offset, offset + segmentLength));
    offset += segmentLength;
  }

  return Buffer.concat(chunks);
};

const PNG_TEXTUAL_CHUNK_TYPES = new Set(['tEXt', 'zTXt', 'iTXt', 'eXIf']);

/**
 * Strips textual (tEXt/zTXt/iTXt) and eXIf chunks from a PNG buffer.
 */
const stripPngMetadata = (buffer: Buffer): Buffer => {
  if (
    buffer.length < PNG_SIGNATURE.length ||
    !buffer.subarray(0, PNG_SIGNATURE.length).equals(PNG_SIGNATURE)
  ) {
    return buffer;
  }

  const chunks: Buffer[] = [buffer.subarray(0, PNG_SIGNATURE.length)];
  let offset = PNG_SIGNATURE.length;

  while (offset + 8 <= buffer.length) {
    const length = buffer.readUInt32BE(offset);
    const type = buffer.subarray(offset + 4, offset + 8).toString('ascii');
    const chunkEnd = offset + 8 + length + 4;

    if (length > buffer.length || chunkEnd > buffer.length) {
      // Malformed chunk: preserve the rest to avoid corrupting the image.
      chunks.push(buffer.subarray(offset));
      break;
    }

    if (!PNG_TEXTUAL_CHUNK_TYPES.has(type)) {
      chunks.push(buffer.subarray(offset, chunkEnd));
    }

    offset = chunkEnd;

    if (type === 'IEND') {
      // Preserve any trailing bytes after IEND.
      if (offset < buffer.length) {
        chunks.push(buffer.subarray(offset));
      }
      break;
    }
  }

  if (offset < buffer.length) {
    // Trailing bytes (e.g. no IEND found): preserve to avoid corruption.
    chunks.push(buffer.subarray(offset));
  }

  return Buffer.concat(chunks);
};

const readAscii = (buffer: Buffer, offset: number, length: number): string =>
  buffer.subarray(offset, offset + length).toString('ascii');

/**
 * Strips EXIF and XMP chunks from a WebP (RIFF) buffer and fixes the
 * RIFF size header accordingly.
 */
const stripWebpMetadata = (buffer: Buffer): Buffer => {
  if (
    buffer.length < 12 ||
    readAscii(buffer, 0, 4) !== 'RIFF' ||
    readAscii(buffer, 8, 4) !== 'WEBP'
  ) {
    return buffer;
  }

  const chunks: Buffer[] = [buffer.subarray(0, 12)];
  let offset = 12;
  let removedBytes = 0;

  while (offset + 8 <= buffer.length) {
    const type = readAscii(buffer, offset, 4);
    const size = buffer.readUInt32LE(offset + 4);
    const paddedSize = size + (size % 2);
    const chunkEnd = offset + 8 + paddedSize;

    if (chunkEnd > buffer.length) {
      // Malformed chunk: preserve the rest to avoid corrupting the image.
      chunks.push(buffer.subarray(offset));
      break;
    }

    if (type === 'EXIF' || type === 'XMP ') {
      removedBytes += 8 + paddedSize;
    } else {
      chunks.push(buffer.subarray(offset, chunkEnd));
    }

    offset = chunkEnd;
  }

  if (offset < buffer.length) {
    chunks.push(buffer.subarray(offset));
  }

  const result = Buffer.concat(chunks);

  result.writeUInt32LE(result.readUInt32LE(4) - removedBytes, 4);

  return result;
};

const RASTER_MIME_TYPES = new Set([
  'image/jpeg',
  'image/png',
  'image/webp',
]);

const RASTER_EXTENSIONS = new Set(['jpg', 'jpeg', 'png', 'webp']);

const stripRasterMetadata = (buffer: Buffer): Buffer => {
  if (isJpegBuffer(buffer)) {
    return stripJpegMetadata(buffer);
  }

  if (
    buffer.length >= PNG_SIGNATURE.length &&
    buffer.subarray(0, PNG_SIGNATURE.length).equals(PNG_SIGNATURE)
  ) {
    return stripPngMetadata(buffer);
  }

  if (
    buffer.length >= 12 &&
    readAscii(buffer, 0, 4) === 'RIFF' &&
    readAscii(buffer, 8, 4) === 'WEBP'
  ) {
    return stripWebpMetadata(buffer);
  }

  return buffer;
};

export const sanitizeFile = ({
  file,
  ext,
  mimeType,
}: {
  file: Buffer | Uint8Array | string;
  ext: string;
  mimeType: string | undefined;
}): Buffer | Uint8Array | string => {
  if (ext === 'svg' || mimeType === 'image/svg+xml') {
    const window = new JSDOM('').window;
    const purify = DOMPurify(window);

    let fileString: string;

    if (typeof file === 'string') {
      fileString = file;
    } else if (Buffer.isBuffer(file)) {
      fileString = file.toString('utf-8');
    } else {
      fileString = Buffer.from(file).toString('utf-8');
    }

    return purify.sanitize(fileString);
  }

  // Strip EXIF/XMP/IPTC metadata (e.g. GPS coordinates) from raster images
  // such as organization logos. Image pixels are preserved byte-for-byte.
  if (
    typeof file !== 'string' &&
    ((typeof mimeType === 'string' && RASTER_MIME_TYPES.has(mimeType)) ||
      RASTER_EXTENSIONS.has(ext.toLowerCase()))
  ) {
    const buffer = Buffer.isBuffer(file) ? file : Buffer.from(file);
    const stripped = stripRasterMetadata(buffer);

    return Buffer.isBuffer(file) ? stripped : new Uint8Array(stripped);
  }

  return file;
};
