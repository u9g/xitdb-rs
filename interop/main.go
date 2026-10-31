// Exchanges databases with the Rust port, to check that they share a file
// format. See run.sh.
//
//	go run . append <path>    verifies the moment Rust wrote, then appends one
//	go run . verify <path>    verifies a compacted copy made by Rust
package main

import (
	"bytes"
	"crypto/sha1"
	"fmt"
	"log"
	"os"

	xitdb "github.com/xit-vcs/xitdb-go"
)

func check(ok bool, what string) {
	if !ok {
		log.Fatalf("check failed: %s", what)
	}
}

func must[T any](v T, err error) T {
	if err != nil {
		log.Fatal(err)
	}
	return v
}

func open(path string) (*xitdb.CoreBufferedFile, *xitdb.Database) {
	f := must(os.OpenFile(path, os.O_RDWR, 0644))
	core := xitdb.NewCoreBufferedFile(f)
	db := must(xitdb.NewDatabase(core, xitdb.Hasher{Hash: sha1.New}))
	return core, db
}

func str(c *xitdb.ReadCursor) string {
	check(c != nil, "missing value")
	return string(must(c.ReadBytes(0)))
}

func longBytes() []byte {
	b := make([]byte, 5000)
	for i := range b {
		b[i] = byte(i % 251)
	}
	return b
}

// checks the moment the Rust port wrote
func checkRustMoment(moment *xitdb.ReadHashMap) {
	check(str(must(moment.GetCursor("name"))) == "xitdb-rs", "name")
	check(must(must(moment.GetCursor("uint")).ReadUint()) == 42, "uint")
	check(must(must(moment.GetCursor("int")).ReadInt()) == -7, "int")
	check(must(must(moment.GetCursor("float")).ReadFloat()) == 3.5, "float")
	tagged := must(must(moment.GetCursor("tagged")).ReadBytesObject(0))
	check(bytes.Equal(tagged.Value, bytes.Repeat([]byte{0xAB}, 32)) && string(tagged.FormatTag) == "bi", "tagged")
	shortTagged := must(must(moment.GetCursor("short-tagged")).ReadBytesObject(0))
	check(string(shortTagged.Value) == "hi" && string(shortTagged.FormatTag) == "st", "short-tagged")
	check(bytes.Equal(must(must(moment.GetCursor("long")).ReadBytes(0)), longBytes()), "long")

	set := must(xitdb.NewReadHashSet(must(moment.GetCursor("set"))))
	check(must(set.GetCursor("a")) != nil && must(set.GetCursor("d")) == nil, "set")

	sortedSet := must(xitdb.NewReadSortedSet(must(moment.GetCursor("sorted-set"))))
	var keys []string
	for kvCursor, err := range sortedSet.All() {
		check(err == nil, "sorted set iteration")
		keys = append(keys, str(must(kvCursor.ReadKeyValuePair()).KeyCursor))
	}
	check(fmt.Sprint(keys) == "[alpha mid zeta]", "sorted set order")
}

func appendMoment(path string) {
	core, db := open(path)
	defer core.Close()
	history := must(xitdb.NewWriteArrayList(db.RootCursor()))
	check(must(history.Count()) == 1, "one moment")

	moment := must(xitdb.NewReadHashMap(must(history.GetCursor(-1))))
	checkRustMoment(moment)

	list := must(xitdb.NewReadArrayList(must(moment.GetCursor("list"))))
	check(must(list.Count()) == 300, "list count")
	i := uint64(0)
	for c, err := range list.All() {
		check(err == nil && must(c.ReadUint()) == i, "list item")
		i++
	}

	sorted := must(xitdb.NewReadSortedMap(must(moment.GetCursor("sorted"))))
	check(must(sorted.Count()) == 99, "sorted count")
	check(must(sorted.GetCursor("k050")) == nil, "k050 removed")
	check(must(sorted.Rank("k051")) == 50, "rank")

	linked := must(xitdb.NewReadLinkedArrayList(must(moment.GetCursor("linked"))))
	check(must(linked.Count()) == 100, "linked count")
	check(str(must(linked.GetCursor(49))) == "inserted", "linked inserted")

	counted := must(xitdb.NewReadCountedHashMap(must(moment.GetCursor("counted"))))
	check(must(counted.Count()) == 2, "counted count")

	lastSlot := must(history.GetSlot(-1))
	err := history.AppendContext(lastSlot, func(cursor *xitdb.WriteCursor) error {
		moment := must(xitdb.NewWriteHashMap(cursor))
		if err := moment.Put("from-go", xitdb.NewString("hello from go")); err != nil {
			return err
		}
		list := must(xitdb.NewWriteArrayList(must(moment.PutCursor("list"))))
		if err := list.Append(xitdb.NewUint(300)); err != nil {
			return err
		}
		sorted := must(xitdb.NewWriteSortedMap(must(moment.PutCursor("sorted"))))
		if err := sorted.Put("k050", xitdb.NewUint(50)); err != nil {
			return err
		}
		linked := must(xitdb.NewWriteLinkedArrayList(must(moment.PutCursor("linked"))))
		if err := linked.Append(xitdb.NewString("go-item")); err != nil {
			return err
		}
		counted := must(xitdb.NewWriteCountedHashMap(must(moment.PutCursor("counted"))))
		return counted.Put("z", xitdb.NewUint(3))
	})
	check(err == nil, fmt.Sprint("append: ", err))
	fmt.Printf("go: verified the moment rust wrote to %s and appended one\n", path)
}

func verifyCompacted(path string) {
	core, db := open(path)
	defer core.Close()
	history := must(xitdb.NewReadArrayList(db.RootCursor().ReadCursor))
	check(must(history.Count()) == 1, "compacted history has one moment")
	moment := must(xitdb.NewReadHashMap(must(history.GetCursor(-1))))
	checkRustMoment(moment)
	check(str(must(moment.GetCursor("from-go"))) == "hello from go", "from-go")
	list := must(xitdb.NewReadArrayList(must(moment.GetCursor("list"))))
	check(must(list.Count()) == 301, "list count")
	sorted := must(xitdb.NewReadSortedMap(must(moment.GetCursor("sorted"))))
	check(must(sorted.Count()) == 100, "sorted count")
	linked := must(xitdb.NewReadLinkedArrayList(must(moment.GetCursor("linked"))))
	check(str(must(linked.GetCursor(-1))) == "go-item", "linked last")
	fmt.Printf("go: verified the compacted copy rust wrote to %s\n", path)
}

func main() {
	if len(os.Args) != 3 {
		log.Fatal("usage: go run . append|verify <path>")
	}
	switch os.Args[1] {
	case "append":
		appendMoment(os.Args[2])
	case "verify":
		verifyCompacted(os.Args[2])
	default:
		log.Fatalf("unknown command %q", os.Args[1])
	}
}
