// The xitdb-ts side of the replication test driven by
// `examples/ts_replication.rs` (see run.sh). It holds an in-memory replica,
// like a browser client would, and reads it with the plain accessor API.
//
// The Rust example writes one JSON request per line to stdin, and this script
// answers each with one JSON line on stdout:
//
// * {"type":"state"}
//     -> {"state":STATE,"trailer":TRAILER}
// * {"type":"sync","start":S,"end":E,"bytes":HEX}
//     applies the committed bytes [S, E) of the source, like a client applies
//     a full copy (S = 0) or a broadcast delta.
//     -> {"applied":true,"state":STATE,"trailer":TRAILER}, or
//        {"applied":false,"error":NAME,"state":STATE,...} if it was rejected,
//        in which case the replica is unchanged and must re-sync.
// * {"type":"check","moments":[N, ...]}
//     checks that the replica's history holds exactly the moments numbered N
//     (see momentOf in the Rust example). -> {"ok":true}
// * {"type":"checksum","fileId":DEC,"position":P,"root":HEX,"commitId":DEC}
//     -> {"checksum":DEC}, computed by xitdb-ts.
// * {"type":"source-write","n":N} writes moment N into a database owned by
//     this script, and {"type":"source-sync","state":STATE} answers a Rust
//     replica in STATE like a server would: -> {"start":S,"end":E,"bytes":HEX,
//     "state":STATE}.
//
// STATE is the ReplicaState wire form: {"committedSize":123,"checksum":"456"},
// with the u64 checksum as a decimal string. TRAILER describes the trailer
// that ends the committed bytes, read from the replica's own bytes, and the
// checksum xitdb-ts computes for it, so the Rust side can compare it with its
// own computation.
//
// Any failure is answered with {"fatal":MESSAGE} and exits with status 1.

import { createInterface } from 'node:readline';
import {
  Bytes,
  CoreMemory,
  Database,
  Hasher,
  ReadArrayList,
  ReadCountedHashMap,
  ReadCountedHashSet,
  ReadCursor,
  ReadHashMap,
  ReadHashSet,
  ReadLinkedArrayList,
  ReadSortedMap,
  ReadSortedSet,
  RootTrailer,
  Slot,
  Tag,
  Uint,
  WriteArrayList,
  WriteHashMap,
  type ReplicaState,
} from 'xitdb';

type Json = Record<string, unknown>;

const sha1 = () => new Hasher('SHA-1', Hasher.stringToId('sha1'));

// the in-memory replica. it starts out as a new database, so its first sync
// is a full copy.
const replica = new Database(new CoreMemory(), sha1());
// a database written by this script, replicated to Rust
const source = new Database(new CoreMemory(), sha1());

// --- the ReplicaState wire form ---

function stateToJson(state: ReplicaState): Json {
  return { committedSize: state.committedSize, checksum: state.checksum.toString() };
}

function stateFromJson(json: Json): ReplicaState {
  if (typeof json.committedSize !== 'number' || typeof json.checksum !== 'string') {
    throw new Error(`bad replica state: ${JSON.stringify(json)}`);
  }
  return { committedSize: json.committedSize, checksum: BigInt(json.checksum) };
}

// --- reading and writing raw bytes ---

function readCommitted(db: Database, start: number, end: number): Buffer {
  const chunks: Uint8Array[] = [];
  db.readCommitted(start, end, { write: (chunk) => chunks.push(chunk.slice()) });
  return Buffer.concat(chunks);
}

function readRaw(db: Database, position: number, length: number): Uint8Array {
  const bytes = new Uint8Array(length);
  db.core.seek(position);
  db.core.reader().readFully(bytes);
  return bytes;
}

// the trailer that ends the committed bytes, read from the replica's bytes,
// and the checksum xitdb-ts computes for it
function trailerOf(db: Database): Json {
  const end = db.committedSize();
  const position = end - RootTrailer.LENGTH;
  const bytes = readRaw(db, position, RootTrailer.LENGTH);
  const root = bytes.subarray(0, Slot.LENGTH);
  const view = new DataView(bytes.buffer);
  const commitId = view.getBigUint64(Slot.LENGTH, false);
  const stored = view.getBigUint64(Slot.LENGTH + 8, false);
  const computed = RootTrailer.computeChecksum(db.header.fileId, position, root, commitId);
  return {
    fileId: db.header.fileId.toString(),
    position,
    root: Buffer.from(root).toString('hex'),
    commitId: commitId.toString(),
    stored: stored.toString(),
    computed: computed.toString(),
  };
}

// --- checks ---

function check(condition: boolean, what: string): void {
  if (!condition) throw new Error(`check failed: ${what}`);
}

function equalBytes(a: Uint8Array, b: Uint8Array): boolean {
  return a.length === b.length && a.every((byte, i) => byte === b[i]);
}

const utf8 = new TextEncoder();
const text = (cursor: ReadCursor | null, what: string): string => {
  check(cursor !== null, `${what} exists`);
  return new TextDecoder().decode(cursor!.readBytes());
};
const get = (map: ReadHashMap, key: string): ReadCursor => {
  const cursor = map.getCursor(key);
  check(cursor !== null, `key ${key} exists`);
  return cursor!;
};
// the full 64-bit value of a uint or int slot. readUint and readInt return
// a number, which can't hold every 64-bit integer (see the README).
const uint64 = (cursor: ReadCursor): bigint => {
  check(cursor.slot().tag === Tag.UINT, 'uint tag');
  return BigInt.asUintN(64, cursor.slot().value);
};
const int64 = (cursor: ReadCursor): bigint => {
  check(cursor.slot().tag === Tag.INT, 'int tag');
  return cursor.slot().value;
};

// these mirror the data written by momentOf in examples/ts_replication.rs
function longBytes(length: number, seed: number): Uint8Array {
  const bytes = new Uint8Array(length);
  for (let i = 0; i < length; i++) bytes[i] = (i * 31 + seed) % 251;
  return bytes;
}
const pad3 = (i: number) => i.toString().padStart(3, '0');

function checkMoment(moment: ReadHashMap, n: number): void {
  const at = (what: string) => `moment ${n}: ${what}`;

  // scalars
  check(text(moment.getCursor('name'), 'name') === 'xitdb-rs', at('name'));
  check(get(moment, 'n').readUint() === n, at('n'));
  check(get(moment, 'uint').readUint() === 42, at('uint'));
  check(uint64(get(moment, 'uint-max')) === 18446744073709551615n, at('uint-max'));
  check(uint64(get(moment, 'uint-2^53+1')) === 9007199254740993n, at('uint-2^53+1'));
  check(get(moment, 'int').readInt() === -7, at('int'));
  check(int64(get(moment, 'int-min')) === -9223372036854775808n, at('int-min'));
  check(int64(get(moment, 'int-max')) === 9223372036854775807n, at('int-max'));
  check(get(moment, 'float').readFloat() === 3.5, at('float'));
  check(get(moment, 'float-n').readFloat() === n * 0.25, at('float-n'));
  check(Object.is(get(moment, 'float-neg-zero').readFloat(), -0), at('float-neg-zero'));
  check(get(moment, 'float-inf').readFloat() === -Infinity, at('float-inf'));
  check(Number.isNaN(get(moment, 'float-nan').readFloat()), at('float-nan'));
  check(get(moment, 'float-tiny').readFloat() === 5e-324, at('float-tiny'));
  check(get(moment, 'null').slot().tag === Tag.NONE, at('null'));

  // short and long bytes, with and without a format tag
  check(text(moment.getCursor('short-string'), 'short-string') === 'hi', at('short-string'));
  check(text(moment.getCursor('unicode'), 'unicode') === 'héllo, wörld ✓', at('unicode'));
  check(get(moment, 'empty').readBytes().length === 0, at('empty bytes'));
  check(get(moment, 'short-bytes').slot().tag === Tag.SHORT_BYTES, at('short-bytes tag'));
  check(equalBytes(get(moment, 'short-bytes').readBytes(), new Uint8Array([1, 2, 255])), at('short-bytes'));
  // bytes with a zero can't be short, because a zero ends short bytes
  check(get(moment, 'zero-bytes').slot().tag === Tag.BYTES, at('zero-bytes tag'));
  check(equalBytes(get(moment, 'zero-bytes').readBytes(), new Uint8Array([0, 1, 0])), at('zero-bytes'));
  check(get(moment, 'eight-bytes').slot().tag === Tag.SHORT_BYTES, at('eight-bytes tag'));
  check(equalBytes(get(moment, 'eight-bytes').readBytes(), utf8.encode('12345678')), at('eight-bytes'));
  check(get(moment, 'nine-bytes').slot().tag === Tag.BYTES, at('nine-bytes tag'));
  check(equalBytes(get(moment, 'nine-bytes').readBytes(), utf8.encode('123456789')), at('nine-bytes'));
  check(get(moment, 'long').slot().tag === Tag.BYTES, at('long tag'));
  check(equalBytes(get(moment, 'long').readBytes(), longBytes(5000, 0)), at('long'));
  const tagged = get(moment, 'tagged').readBytesObject();
  check(equalBytes(tagged.value, new Uint8Array(32).fill(0xab)), at('tagged value'));
  check(tagged.formatTag !== null && equalBytes(tagged.formatTag, utf8.encode('bi')), at('tagged format tag'));
  const shortTagged = get(moment, 'short-tagged').readBytesObject();
  check(get(moment, 'short-tagged').slot().tag === Tag.SHORT_BYTES, at('short-tagged tag'));
  check(equalBytes(shortTagged.value, utf8.encode('hi')), at('short-tagged value'));
  check(shortTagged.formatTag !== null && equalBytes(shortTagged.formatTag, utf8.encode('st')), at('short-tagged format tag'));
  if (n >= 3) {
    check(equalBytes(get(moment, 'big').readBytes(), longBytes(100_000, 3)), at('big'));
  } else {
    check(moment.getCursor('big') === null, at('no big yet'));
  }
  // a key whose value is a byte string with a format tag
  const taggedKey = moment.getCursor(new Bytes('key', 'tk'));
  check(taggedKey !== null && taggedKey.readUint() === 7, at('tagged key'));
  if (n < 4) {
    check(text(moment.getCursor('removed-at-4'), 'removed-at-4') === 'still here', at('removed-at-4'));
  } else {
    check(moment.getCursor('removed-at-4') === null, at('removed-at-4 removed'));
  }

  // array list
  const list = new ReadArrayList(get(moment, 'list'));
  check(list.count() === 300 + n, at('list count'));
  let i = 0;
  for (const item of list) {
    check(item.readUint() === i * 3, at(`list item ${i}`));
    i++;
  }
  check(i === 300 + n, at('list iteration'));
  check(list.getCursor(-1)!.readUint() === (299 + n) * 3, at('list last'));

  // linked array list
  const linked = new ReadLinkedArrayList(get(moment, 'linked'));
  const expectedLinked: string[] = [];
  for (let j = 1; j < 100; j++) expectedLinked.push(`item-${j}`);
  expectedLinked.splice(49, 0, 'inserted');
  for (let j = 1; j <= n; j++) expectedLinked.push(`tx-${j}`);
  check(linked.count() === expectedLinked.length, at('linked count'));
  const linkedValues = [...linked].map((cursor) => text(cursor, 'linked item'));
  check(linkedValues.join(',') === expectedLinked.join(','), at('linked items'));

  // sorted map: k000..k099 without k050, then t001..tNNN
  const sorted = new ReadSortedMap(get(moment, 'sorted'));
  const expectedSorted: [string, number][] = [];
  for (let j = 0; j < 100; j++) if (j !== 50) expectedSorted.push([`k${pad3(j)}`, j]);
  for (let j = 1; j <= n; j++) expectedSorted.push([`t${pad3(j)}`, j * 1000]);
  check(sorted.count() === expectedSorted.length, at('sorted count'));
  const sortedPairs = [...sorted].map((cursor) => {
    const kv = cursor.readKeyValuePair();
    return [text(kv.keyCursor, 'sorted key'), kv.valueCursor.readUint()] as [string, number];
  });
  check(JSON.stringify(sortedPairs) === JSON.stringify(expectedSorted), at('sorted pairs in order'));
  check(sorted.getCursor('k050') === null, at('k050 removed'));
  check(sorted.getCursor('k051')!.readUint() === 51, at('sorted lookup'));

  // hash set: a, c, s1..sN, and b until moment 2
  const set = new ReadHashSet(get(moment, 'set'));
  const members = ['a', 'c'];
  for (let j = 1; j <= n; j++) members.push(`s${j}`);
  for (const member of members) check(set.getCursor(member) !== null, at(`set has ${member}`));
  check((set.getCursor('b') !== null) === n < 2, at('set b'));
  check(set.getCursor('d') === null, at('set has no d'));
  check([...set].length === members.length + (n < 2 ? 1 : 0), at('set size'));

  // counted hash map and set
  const counted = new ReadCountedHashMap(get(moment, 'counted'));
  check(counted.count() === 2 + n, at('counted count'));
  check(counted.getCursor('x')!.readUint() === 1 && counted.getCursor('y')!.readUint() === 2, at('counted x y'));
  for (let j = 1; j <= n; j++) check(counted.getCursor(`z${j}`)!.readUint() === j, at(`counted z${j}`));
  const countedSet = new ReadCountedHashSet(get(moment, 'counted-set'));
  check(countedSet.count() === 2, at('counted set count'));
  check(countedSet.getCursor('p') !== null && countedSet.getCursor('q') !== null, at('counted set members'));

  // sorted set
  const sortedSet = new ReadSortedSet(get(moment, 'sorted-set'));
  const keys = [...sortedSet].map((cursor) => text(cursor.readKeyValuePair().keyCursor, 'sorted set key'));
  check(keys.join(',') === 'alpha,mid,zeta', at('sorted set order'));

  // nested maps and lists: nested.inner.deep[0].x, nested.inner.version
  const inner = new ReadHashMap(get(new ReadHashMap(get(moment, 'nested')), 'inner'));
  check(get(inner, 'version').readUint() === n, at('nested version'));
  const deep = new ReadArrayList(get(inner, 'deep'));
  check(deep.count() === 1 + n, at('deep count'));
  for (let j = 0; j <= n; j++) {
    const entry = new ReadHashMap(deep.getCursor(j)!);
    check(get(entry, 'x').readUint() === j, at(`deep ${j} x`));
    check(text(entry.getCursor('label'), 'label') === `deep-${j}`, at(`deep ${j} label`));
  }
}

function checkMoments(db: Database, moments: number[]): void {
  const history = new ReadArrayList(db.rootCursor());
  check(history.count() === moments.length, `history has ${moments.length} moments, not ${history.count()}`);
  moments.forEach((n, i) => checkMoment(new ReadHashMap(history.getCursor(i)!), n));
}

// --- requests ---

function handle(request: Json): Json {
  switch (request.type) {
    case 'state':
      return { state: stateToJson(replica.replicaState()), trailer: trailerOf(replica) };

    case 'sync': {
      const start = request.start as number;
      const end = request.end as number;
      const bytes = Buffer.from(request.bytes as string, 'hex');
      check(bytes.length === end - start, 'sync length');
      const before = replica.replicaState();
      try {
        // openReplicated rejects a start that is neither 0 nor the
        // replica's committed size, and close() rejects bytes that don't end
        // with a trailer of this file at start + length
        const writer = replica.openReplicated(start, bytes.length);
        // give it the bytes in pieces, like chunks from a network stream
        for (let i = 0; i < bytes.length; i += 1000) writer.write(bytes.subarray(i, i + 1000));
        writer.close();
      } catch (e) {
        const after = replica.replicaState();
        return {
          applied: false,
          error: (e as Error).constructor.name,
          unchanged: after.committedSize === before.committedSize && after.checksum === before.checksum,
          state: stateToJson(after),
          trailer: trailerOf(replica),
        };
      }
      return { applied: true, state: stateToJson(replica.replicaState()), trailer: trailerOf(replica) };
    }

    case 'check':
      checkMoments(replica, request.moments as number[]);
      return { ok: true };

    case 'checksum': {
      const checksum = RootTrailer.computeChecksum(
        BigInt(request.fileId as string),
        request.position as number,
        Buffer.from(request.root as string, 'hex'),
        BigInt(request.commitId as string),
      );
      return { checksum: checksum.toString() };
    }

    case 'source-write': {
      // moment N, written by xitdb-ts as a copy of moment N - 1, with N
      // appended to its list of values
      const n = request.n as number;
      const history = new WriteArrayList(source.rootCursor());
      history.appendContext(history.getSlot(-1), (cursor) => {
        const moment = new WriteHashMap(cursor);
        moment.put('from', new Bytes('xitdb-ts'));
        moment.put('n', new Uint(n));
        const values = new WriteArrayList(moment.putCursor('values'));
        values.append(new Uint(n));
        moment.put('long', new Bytes(longBytes(1000, n)));
      });
      return { state: stateToJson(source.replicaState()) };
    }

    case 'source-sync': {
      const start = source.replicationStart(stateFromJson(request.state as Json));
      const end = source.committedSize();
      const bytes = readCommitted(source, start, end);
      return { start, end, bytes: bytes.toString('hex'), state: stateToJson(source.replicaState()) };
    }

    default:
      throw new Error(`unknown request ${JSON.stringify(request)}`);
  }
}

for await (const line of createInterface({ input: process.stdin })) {
  if (line.trim() === '') continue;
  try {
    console.log(JSON.stringify(handle(JSON.parse(line) as Json)));
  } catch (e) {
    console.log(JSON.stringify({ fatal: (e as Error).stack ?? String(e) }));
    process.exit(1);
  }
}
