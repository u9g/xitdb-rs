// The TypeScript hop in the game of telephone. See examples/telephone.rs.
//
//   node hop.mjs apply <db> <ops>    appends a moment with the edits in ops
//   node hop.mjs dump <db>           prints every moment

import { readFileSync, writeSync } from 'node:fs';
import {
  Bytes, CoreBufferedFile, Database, Float, Hasher, Int, Uint, WriteArrayList, WriteCountedHashMap,
  WriteHashMap, WriteHashSet, WriteLinkedArrayList, WriteSortedMap,
} from 'xitdb';

// Tag is a const enum, so it doesn't exist at runtime
const Tag = {
  NONE: 0, ARRAY_LIST: 2, LINKED_ARRAY_LIST: 3, HASH_MAP: 4, KV_PAIR: 5, BYTES: 6, SHORT_BYTES: 7, UINT: 8,
  INT: 9, FLOAT: 10, HASH_SET: 11, COUNTED_HASH_MAP: 12, COUNTED_HASH_SET: 13, SORTED_MAP: 14, SORTED_SET: 15,
  SORTED_KV_PAIR: 16,
};

const unhex = (s) => (s === '-' ? new Uint8Array() : Uint8Array.from(Buffer.from(s, 'hex')));
const hex = (b) => (b.length === 0 ? '-' : Buffer.from(b).toString('hex'));

function floatFromBits(bits) {
  const view = new DataView(new ArrayBuffer(8));
  view.setBigUint64(0, BigInt('0x' + bits));
  return view.getFloat64(0);
}

function floatBits(value) {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, value);
  return view.getBigUint64(0).toString(16).padStart(16, '0');
}

function value(f) {
  switch (f[0]) {
    case 'uint': return new Uint(BigInt(f[1]));
    case 'int': return new Int(BigInt(f[1]));
    case 'float': return new Float(floatFromBits(f[1]));
    case 'bytes': return new Bytes(unhex(f[1]), f[2] === '-' ? null : unhex(f[2]));
  }
  throw new Error(`bad value ${f}`);
}

function open(path) {
  const core = new CoreBufferedFile(path);
  return [core, new Database(core, new Hasher('SHA-1'))];
}

function apply(path, opsPath) {
  const ops = readFileSync(opsPath, 'utf8').split('\n').filter((line) => line.trim());
  const [core, db] = open(path);
  try {
    const history = new WriteArrayList(db.rootCursor());
    history.appendContext(history.getSlot(-1), (cursor) => {
      const moment = new WriteHashMap(cursor);
      const kv = () => new WriteHashMap(moment.putCursor('kv'));
      const counted = () => new WriteCountedHashMap(moment.putCursor('counted'));
      const set = () => new WriteHashSet(moment.putCursor('set'));
      const sorted = () => new WriteSortedMap(moment.putCursor('sorted'));
      const list = () => new WriteArrayList(moment.putCursor('list'));
      const linked = () => new WriteLinkedArrayList(moment.putCursor('linked'));
      kv(); counted(); set(); sorted(); list(); linked();
      for (const line of ops) {
        const f = line.trim().split(/\s+/);
        // a Uint8Array key would be taken as a hash, so wrap it
        const key = () => new Bytes(unhex(f[1]));
        switch (f[0]) {
          case 'kv_put': kv().put(key(), value(f.slice(2))); break;
          case 'kv_remove': kv().remove(key()); break;
          case 'counted_put': counted().put(key(), value(f.slice(2))); break;
          case 'counted_remove': counted().remove(key()); break;
          case 'set_put': set().put(key()); break;
          case 'set_remove': set().remove(key()); break;
          case 'sorted_put': sorted().put(unhex(f[1]), value(f.slice(2))); break;
          case 'sorted_remove': sorted().remove(unhex(f[1])); break;
          case 'list_append': list().append(value(f.slice(1))); break;
          case 'list_put': list().put(Number(f[1]), value(f.slice(2))); break;
          case 'list_slice': list().slice(Number(f[1])); break;
          case 'linked_append': linked().append(value(f.slice(1))); break;
          case 'linked_insert': linked().insert(Number(f[1]), value(f.slice(2))); break;
          case 'linked_remove': linked().remove(Number(f[1])); break;
          case 'linked_put': linked().put(Number(f[1]), value(f.slice(2))); break;
          case 'linked_slice': linked().slice(Number(f[1]), Number(f[2])); break;
          default: throw new Error(`bad op ${line}`);
        }
      }
    });
    core.flush();
  } finally {
    core[Symbol.dispose]();
  }
}

// prints any value, following its tags, in the format the driver reads
function dump(cursor, depth, out) {
  const indent = '  '.repeat(depth);
  const slot = cursor.slot();
  const container = (kind, count, pairs) => {
    out.push(`${indent}${kind} ${count}`);
    for (const item of cursor) {
      const tag = item.slot().tag;
      if (pairs) {
        const kv = item.readKeyValuePair();
        dump(kv.keyCursor, depth + 1, out);
        dump(kv.valueCursor, depth + 1, out);
      } else if (tag === Tag.KV_PAIR || tag === Tag.SORTED_KV_PAIR) {
        dump(item.readKeyValuePair().keyCursor, depth + 1, out);
      } else {
        dump(item, depth + 1, out);
      }
    }
    out.push(`${indent}end`);
  };
  switch (slot.tag) {
    case Tag.NONE: out.push(`${indent}none`); break;
    // readUint and readInt return a number, which can't hold every 64-bit
    // value, so check the tag with them but print the slot's bigint
    case Tag.UINT: cursor.readUint(); out.push(`${indent}uint ${slot.value}`); break;
    case Tag.INT: cursor.readInt(); out.push(`${indent}int ${slot.value}`); break;
    case Tag.FLOAT: out.push(`${indent}float ${floatBits(cursor.readFloat())}`); break;
    case Tag.BYTES:
    case Tag.SHORT_BYTES: {
      const bytes = cursor.readBytesObject(null);
      out.push(`${indent}bytes ${hex(bytes.value)} ${bytes.formatTag ? hex(bytes.formatTag) : '-'}`);
      break;
    }
    case Tag.ARRAY_LIST: container('array_list', cursor.count(), false); break;
    case Tag.LINKED_ARRAY_LIST: container('linked_array_list', cursor.count(), false); break;
    case Tag.HASH_MAP: container('hash_map', '-', true); break;
    case Tag.COUNTED_HASH_MAP: container('counted_hash_map', cursor.count(), true); break;
    case Tag.SORTED_MAP: container('sorted_map', cursor.count(), true); break;
    case Tag.HASH_SET: container('hash_set', '-', false); break;
    case Tag.COUNTED_HASH_SET: container('counted_hash_set', cursor.count(), false); break;
    case Tag.SORTED_SET: container('sorted_set', cursor.count(), false); break;
    default: throw new Error(`unexpected tag ${slot.tag}`);
  }
}

const [command, ...args] = process.argv.slice(2);
if (command === 'apply' && args.length === 2) {
  apply(args[0], args[1]);
} else if (command === 'dump' && args.length === 1) {
  const [core, db] = open(args[0]);
  try {
    const out = [];
    dump(db.rootCursor(), 0, out);
    writeSync(1, out.join('\n') + '\n');
  } finally {
    core[Symbol.dispose]();
  }
} else {
  console.error('usage: node hop.mjs apply <db> <ops> | dump <db>');
  process.exit(2);
}
