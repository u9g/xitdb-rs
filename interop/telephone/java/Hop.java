// The Java hop in the game of telephone. See examples/telephone.rs.
//
//   java -cp xitdb.jar:. Hop apply <db> <ops>    appends a moment with the edits in ops
//   java -cp xitdb.jar:. Hop dump <db>           prints every moment

import io.github.radarroark.xitdb.*;

import java.io.File;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.HexFormat;
import java.util.List;

public class Hop {
    static byte[] unhex(String s) {
        return s.equals("-") ? new byte[0] : HexFormat.of().parseHex(s);
    }

    static String hex(byte[] b) {
        return b.length == 0 ? "-" : HexFormat.of().formatHex(b);
    }

    static CoreBufferedFile open(String path) throws Exception {
        return new CoreBufferedFile(new RandomAccessBufferedFile(new File(path), "rw"));
    }

    static Database.WriteableData value(String[] f, int i) throws Exception {
        return switch (f[i]) {
            case "uint" -> new Database.Uint(Long.parseLong(f[i + 1]));
            case "int" -> new Database.Int(Long.parseLong(f[i + 1]));
            case "float" -> new Database.Float(Double.longBitsToDouble(Long.parseUnsignedLong(f[i + 1], 16)));
            case "bytes" -> f[i + 2].equals("-")
                ? new Database.Bytes(unhex(f[i + 1]))
                : new Database.Bytes(unhex(f[i + 1]), unhex(f[i + 2]));
            default -> throw new IllegalArgumentException("bad value " + f[i]);
        };
    }

    static void apply(String path, String opsPath) throws Exception {
        List<String> ops = Files.readAllLines(Path.of(opsPath));
        try (var core = open(path)) {
            var db = new Database(core, new Hasher(MessageDigest.getInstance("SHA-1")));
            var history = new WriteArrayList(db.rootCursor());
            history.appendContext(history.getSlot(-1), cursor -> {
                var moment = new WriteHashMap(cursor);
                new WriteHashMap(moment.putCursor("kv"));
                new WriteCountedHashMap(moment.putCursor("counted"));
                new WriteHashSet(moment.putCursor("set"));
                new WriteSortedMap(moment.putCursor("sorted"));
                new WriteArrayList(moment.putCursor("list"));
                new WriteLinkedArrayList(moment.putCursor("linked"));
                for (String line : ops) {
                    String[] f = line.trim().split("\\s+");
                    if (f[0].isEmpty()) continue;
                    switch (f[0]) {
                        case "kv_put" -> new WriteHashMap(moment.putCursor("kv")).put(key(f), value(f, 2));
                        case "kv_remove" -> new WriteHashMap(moment.putCursor("kv")).remove(key(f));
                        case "counted_put" -> new WriteCountedHashMap(moment.putCursor("counted")).put(key(f), value(f, 2));
                        case "counted_remove" -> new WriteCountedHashMap(moment.putCursor("counted")).remove(key(f));
                        case "set_put" -> new WriteHashSet(moment.putCursor("set")).put(key(f));
                        case "set_remove" -> new WriteHashSet(moment.putCursor("set")).remove(key(f));
                        case "sorted_put" -> new WriteSortedMap(moment.putCursor("sorted")).put(unhex(f[1]), value(f, 2));
                        case "sorted_remove" -> new WriteSortedMap(moment.putCursor("sorted")).remove(unhex(f[1]));
                        case "list_append" -> new WriteArrayList(moment.putCursor("list")).append(value(f, 1));
                        case "list_put" -> new WriteArrayList(moment.putCursor("list")).put(Long.parseLong(f[1]), value(f, 2));
                        case "list_slice" -> new WriteArrayList(moment.putCursor("list")).slice(Long.parseLong(f[1]));
                        case "linked_append" -> new WriteLinkedArrayList(moment.putCursor("linked")).append(value(f, 1));
                        case "linked_insert" ->
                            new WriteLinkedArrayList(moment.putCursor("linked")).insert(Long.parseLong(f[1]), value(f, 2));
                        case "linked_remove" -> new WriteLinkedArrayList(moment.putCursor("linked")).remove(Long.parseLong(f[1]));
                        case "linked_put" ->
                            new WriteLinkedArrayList(moment.putCursor("linked")).put(Long.parseLong(f[1]), value(f, 2));
                        case "linked_slice" ->
                            new WriteLinkedArrayList(moment.putCursor("linked")).slice(Long.parseLong(f[1]), Long.parseLong(f[2]));
                        default -> throw new IllegalArgumentException("bad op " + line);
                    }
                }
            });
            core.flush();
        }
    }

    // a byte[] key would be taken as a hash, so wrap it
    static Database.Bytes key(String[] f) {
        return new Database.Bytes(unhex(f[1]));
    }

    // prints any value, following its tags, in the format the driver reads
    static void dump(ReadCursor cursor, int depth, PrintStream out) throws Exception {
        String indent = "  ".repeat(depth);
        switch (cursor.slot().tag()) {
            case NONE -> out.println(indent + "none");
            case UINT -> out.println(indent + "uint " + cursor.readUint());
            case INT -> out.println(indent + "int " + cursor.readInt());
            case FLOAT -> out.println(indent + "float " + String.format("%016x", Double.doubleToRawLongBits(cursor.readFloat())));
            case BYTES, SHORT_BYTES -> {
                var bytes = cursor.readBytesObject(null);
                String tag = bytes.formatTag() == null ? "-" : hex(bytes.formatTag());
                out.println(indent + "bytes " + hex(bytes.value()) + " " + tag);
            }
            case ARRAY_LIST -> container(cursor, depth, out, "array_list", String.valueOf(cursor.count()), false);
            case LINKED_ARRAY_LIST -> container(cursor, depth, out, "linked_array_list", String.valueOf(cursor.count()), false);
            case HASH_MAP -> container(cursor, depth, out, "hash_map", "-", true);
            case COUNTED_HASH_MAP -> container(cursor, depth, out, "counted_hash_map", String.valueOf(cursor.count()), true);
            case SORTED_MAP -> container(cursor, depth, out, "sorted_map", String.valueOf(cursor.count()), true);
            case HASH_SET -> container(cursor, depth, out, "hash_set", "-", false);
            case COUNTED_HASH_SET -> container(cursor, depth, out, "counted_hash_set", String.valueOf(cursor.count()), false);
            case SORTED_SET -> container(cursor, depth, out, "sorted_set", String.valueOf(cursor.count()), false);
            default -> throw new IllegalStateException("unexpected tag " + cursor.slot().tag());
        }
    }

    static void container(ReadCursor cursor, int depth, PrintStream out, String kind, String count, boolean pairs) throws Exception {
        String indent = "  ".repeat(depth);
        out.println(indent + kind + " " + count);
        var it = cursor.iterator();
        while (it.hasNext()) {
            ReadCursor item = it.next();
            Tag tag = item.slot().tag();
            if (pairs) {
                var kv = item.readKeyValuePair();
                dump(kv.keyCursor, depth + 1, out);
                dump(kv.valueCursor, depth + 1, out);
            } else if (tag == Tag.KV_PAIR || tag == Tag.SORTED_KV_PAIR) {
                dump(item.readKeyValuePair().keyCursor, depth + 1, out);
            } else {
                dump(item, depth + 1, out);
            }
        }
        out.println(indent + "end");
    }

    public static void main(String[] args) throws Exception {
        if (args.length == 3 && args[0].equals("apply")) {
            apply(args[1], args[2]);
        } else if (args.length == 2 && args[0].equals("dump")) {
            try (var core = open(args[1])) {
                var db = new Database(core, new Hasher(MessageDigest.getInstance("SHA-1")));
                var out = new PrintStream(new java.io.BufferedOutputStream(System.out), false);
                dump(db.rootCursor(), 0, out);
                out.flush();
            }
        } else {
            System.err.println("usage: Hop apply <db> <ops> | dump <db>");
            System.exit(2);
        }
    }
}
