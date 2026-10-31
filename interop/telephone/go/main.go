// The Go hop in the game of telephone. See examples/telephone.rs.
//
//	go run ./telephone/go apply <db> <ops>    appends a moment with the edits in ops
//	go run ./telephone/go dump <db>           prints every moment
package main

import (
	"bufio"
	"crypto/sha1"
	"encoding/hex"
	"fmt"
	"log"
	"math"
	"os"
	"strconv"
	"strings"

	xitdb "github.com/xit-vcs/xitdb-go"
)

func must[T any](v T, err error) T {
	if err != nil {
		log.Fatal(err)
	}
	return v
}

func check(err error) {
	if err != nil {
		log.Fatal(err)
	}
}

func unhex(s string) []byte {
	if s == "-" {
		return []byte{}
	}
	return must(hex.DecodeString(s))
}

func hexOrDash(b []byte) string {
	if len(b) == 0 {
		return "-"
	}
	return hex.EncodeToString(b)
}

func open(path string) (*xitdb.CoreBufferedFile, *xitdb.Database) {
	f := must(os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0644))
	core := xitdb.NewCoreBufferedFile(f)
	return core, must(xitdb.NewDatabase(core, xitdb.Hasher{Hash: sha1.New}))
}

func value(f []string) xitdb.WriteableData {
	switch f[0] {
	case "uint":
		return xitdb.NewUint(must(strconv.ParseUint(f[1], 10, 64)))
	case "int":
		return xitdb.NewInt(must(strconv.ParseInt(f[1], 10, 64)))
	case "float":
		return xitdb.NewFloat(math.Float64frombits(must(strconv.ParseUint(f[1], 16, 64))))
	case "bytes":
		if f[2] == "-" {
			return xitdb.NewBytes(unhex(f[1]))
		}
		return xitdb.NewTaggedBytes(unhex(f[1]), unhex(f[2]))
	}
	log.Fatalf("bad value %q", f)
	return nil
}

func index(s string) int64 {
	return must(strconv.ParseInt(s, 10, 64))
}

func apply(path, opsPath string) {
	ops := strings.Split(strings.TrimSpace(string(must(os.ReadFile(opsPath)))), "\n")
	core, db := open(path)
	defer core.Close()
	history := must(xitdb.NewWriteArrayList(db.RootCursor()))
	err := history.AppendContext(must(history.GetSlot(-1)), func(cursor *xitdb.WriteCursor) error {
		moment := must(xitdb.NewWriteHashMap(cursor))
		kv := func() *xitdb.WriteHashMap { return must(xitdb.NewWriteHashMap(must(moment.PutCursor("kv")))) }
		counted := func() *xitdb.WriteCountedHashMap {
			return must(xitdb.NewWriteCountedHashMap(must(moment.PutCursor("counted"))))
		}
		set := func() *xitdb.WriteHashSet { return must(xitdb.NewWriteHashSet(must(moment.PutCursor("set")))) }
		sorted := func() *xitdb.WriteSortedMap { return must(xitdb.NewWriteSortedMap(must(moment.PutCursor("sorted")))) }
		list := func() *xitdb.WriteArrayList { return must(xitdb.NewWriteArrayList(must(moment.PutCursor("list")))) }
		linked := func() *xitdb.WriteLinkedArrayList {
			return must(xitdb.NewWriteLinkedArrayList(must(moment.PutCursor("linked"))))
		}
		kv()
		counted()
		set()
		sorted()
		list()
		linked()
		for _, line := range ops {
			f := strings.Fields(line)
			if len(f) == 0 {
				continue
			}
			key := func() xitdb.Bytes { return xitdb.NewBytes(unhex(f[1])) }
			switch f[0] {
			case "kv_put":
				check(kv().PutBytes(key(), value(f[2:])))
			case "kv_remove":
				must(kv().RemoveByBytes(key()))
			case "counted_put":
				check(counted().PutBytes(key(), value(f[2:])))
			case "counted_remove":
				must(counted().RemoveByBytes(key()))
			case "set_put":
				check(set().PutBytes(key()))
			case "set_remove":
				must(set().RemoveByBytes(key()))
			case "sorted_put":
				check(sorted().PutByBytes(unhex(f[1]), value(f[2:])))
			case "sorted_remove":
				must(sorted().RemoveByBytes(unhex(f[1])))
			case "list_append":
				check(list().Append(value(f[1:])))
			case "list_put":
				check(list().Put(index(f[1]), value(f[2:])))
			case "list_slice":
				check(list().Slice(index(f[1])))
			case "linked_append":
				check(linked().Append(value(f[1:])))
			case "linked_insert":
				check(linked().Insert(index(f[1]), value(f[2:])))
			case "linked_remove":
				check(linked().Remove(index(f[1])))
			case "linked_put":
				check(linked().Put(index(f[1]), value(f[2:])))
			case "linked_slice":
				check(linked().Slice(index(f[1]), index(f[2])))
			default:
				log.Fatalf("bad op %q", line)
			}
		}
		return nil
	})
	check(err)
	check(core.Flush())
}

// dump prints any value, following its tags, in the format the driver reads
func dump(c *xitdb.ReadCursor, depth int, w *bufio.Writer) {
	indent := strings.Repeat("  ", depth)
	slot := must(c.Slot())
	container := func(kind string, count string, pairs bool) {
		fmt.Fprintf(w, "%s%s %s\n", indent, kind, count)
		for item, err := range c.All() {
			check(err)
			itemSlot := must(item.Slot())
			if pairs {
				kv := must(item.ReadKeyValuePair())
				dump(kv.KeyCursor, depth+1, w)
				dump(kv.ValueCursor, depth+1, w)
			} else if itemSlot.Tag == xitdb.TagKVPair || itemSlot.Tag == xitdb.TagSortedKVPair {
				dump(must(item.ReadKeyValuePair()).KeyCursor, depth+1, w)
			} else {
				dump(item, depth+1, w)
			}
		}
		fmt.Fprintf(w, "%send\n", indent)
	}
	count := func() string { return strconv.FormatInt(must(c.Count()), 10) }
	switch slot.Tag {
	case xitdb.TagNone:
		fmt.Fprintf(w, "%snone\n", indent)
	case xitdb.TagUint:
		fmt.Fprintf(w, "%suint %d\n", indent, must(c.ReadUint()))
	case xitdb.TagInt:
		fmt.Fprintf(w, "%sint %d\n", indent, must(c.ReadInt()))
	case xitdb.TagFloat:
		fmt.Fprintf(w, "%sfloat %016x\n", indent, math.Float64bits(must(c.ReadFloat())))
	case xitdb.TagBytes, xitdb.TagShortBytes:
		b := must(c.ReadBytesObject(0))
		tag := "-"
		if b.FormatTag != nil {
			tag = hex.EncodeToString(b.FormatTag)
		}
		fmt.Fprintf(w, "%sbytes %s %s\n", indent, hexOrDash(b.Value), tag)
	case xitdb.TagArrayList:
		container("array_list", count(), false)
	case xitdb.TagLinkedArrayList:
		container("linked_array_list", count(), false)
	case xitdb.TagHashMap:
		container("hash_map", "-", true)
	case xitdb.TagCountedHashMap:
		container("counted_hash_map", count(), true)
	case xitdb.TagSortedMap:
		container("sorted_map", count(), true)
	case xitdb.TagHashSet:
		container("hash_set", "-", false)
	case xitdb.TagCountedHashSet:
		container("counted_hash_set", count(), false)
	case xitdb.TagSortedSet:
		container("sorted_set", count(), false)
	default:
		log.Fatalf("unexpected tag %d", slot.Tag)
	}
}

func main() {
	switch {
	case len(os.Args) == 4 && os.Args[1] == "apply":
		apply(os.Args[2], os.Args[3])
	case len(os.Args) == 3 && os.Args[1] == "dump":
		core, db := open(os.Args[2])
		defer core.Close()
		w := bufio.NewWriter(os.Stdout)
		dump(db.RootCursor().ReadCursor, 0, w)
		check(w.Flush())
	default:
		log.Fatal("usage: go run ./telephone/go apply <db> <ops> | dump <db>")
	}
}
