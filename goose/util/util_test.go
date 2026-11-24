package util

import (
	"os"
	"path"
	"path/filepath"
	"reflect"
	"sort"
	"testing"

	"golang.org/x/tools/go/packages"
)

func TestParseTags(t *testing.T) {
	for _, c := range []struct {
		arg  string
		tags []string
	}{
		{"", nil},
		{"a", []string{"a"}},
		{"a,b", []string{"a", "b"}},
		{"a,,b,", []string{"a", "b"}},
	} {
		if got := ParseTags(c.arg); !reflect.DeepEqual(got, c.tags) {
			t.Errorf("ParseTags(%q) = %q, want %q", c.arg, got, c.tags)
		}
	}
}

// TestNewPackageConfigTags checks which files of testdata/tags are loaded:
// those of the goose tag always, and those of the additional tags.
func TestNewPackageConfigTags(t *testing.T) {
	for _, c := range []struct {
		tags  []string
		files []string
	}{
		{nil, []string{"common.go", "goose.go", "without.go"}},
		{[]string{"other"}, []string{"common.go", "goose.go", "without.go"}},
		{[]string{"goose_test_tag"}, []string{"common.go", "goose.go", "with.go"}},
		{[]string{"other", "goose_test_tag"}, []string{"common.go", "goose.go", "with.go"}},
	} {
		pkgs, err := packages.Load(NewPackageConfig(".", false, LoadOptions{Tags: c.tags}), "./testdata/tags")
		if err != nil {
			t.Fatal(err)
		}
		if len(pkgs) != 1 || len(pkgs[0].Errors) > 0 {
			t.Fatalf("tags %q: could not load testdata/tags: %v", c.tags, pkgs)
		}
		var files []string
		for _, f := range pkgs[0].CompiledGoFiles {
			files = append(files, filepath.Base(f))
		}
		sort.Strings(files)
		if !reflect.DeepEqual(files, c.files) {
			t.Errorf("tags %q: loaded %q, want %q", c.tags, files, c.files)
		}
	}
}

func TestFileHasContents(t *testing.T) {
	// Create a temporary directory
	tempDir := t.TempDir()
	tempFile := path.Join(tempDir, "testfile.txt")

	contents := []byte("hello world!")

	// Create a file with some contents
	err := os.WriteFile(tempFile, contents, 0644)
	if err != nil {
		t.Fatalf("Failed to create test file: %v", err)
	}

	if !fileHasContents(tempFile, contents) {
		t.Fatalf("fileHasContents failed")
	}
}

func TestWriteFileIfChanged(t *testing.T) {
	// Create a temporary directory
	tempDir := t.TempDir()
	tempFile := path.Join(tempDir, "testfile.txt")

	// Initial data
	initialData := []byte("Hello, World!")
	err := WriteFileIfChanged(tempFile, initialData, 0644)
	if err != nil {
		t.Fatalf("Failed to write initial data: %v", err)
	}

	// Verify the file's contents
	content, err := os.ReadFile(tempFile)
	if err != nil {
		t.Fatalf("Failed to read file: %v", err)
	}
	if string(content) != string(initialData) {
		t.Fatalf("File contents do not match initial data")
	}

	// Attempt to write the same data again
	err = WriteFileIfChanged(tempFile, initialData, 0644)
	if err != nil {
		t.Fatalf("Failed to write same data: %v", err)
	}

	// Write different data
	newData := []byte("Goodbye, World!")
	err = WriteFileIfChanged(tempFile, newData, 0644)
	if err != nil {
		t.Fatalf("Failed to write new data: %v", err)
	}

	// Verify the file's contents again
	content, err = os.ReadFile(tempFile)
	if err != nil {
		t.Fatalf("Failed to read file after update: %v", err)
	}
	if string(content) != string(newData) {
		t.Fatalf("File contents do not match new data")
	}

	// Write different data, but of same length
	newData = []byte("Gooxbye, Wxrld!")
	err = WriteFileIfChanged(tempFile, newData, 0644)
	if err != nil {
		t.Fatalf("Failed to write new data: %v", err)
	}

	// Verify the file's contents again
	content, err = os.ReadFile(tempFile)
	if err != nil {
		t.Fatalf("Failed to read file after update: %v", err)
	}
	if string(content) != string(newData) {
		t.Fatalf("File contents do not match new data")
	}
}

// TestReadOverlay checks the overlay file format: paths made absolute
// (relative ones against the current directory), the replacements' contents
// read, and what is refused.
func TestReadOverlay(t *testing.T) {
	dir := t.TempDir()
	repl := filepath.Join(dir, "repl.go")
	if err := os.WriteFile(repl, []byte("package p\n"), 0644); err != nil {
		t.Fatal(err)
	}
	write := func(contents string) string {
		f := filepath.Join(dir, "overlay.json")
		if err := os.WriteFile(f, []byte(contents), 0644); err != nil {
			t.Fatal(err)
		}
		return f
	}
	cwd, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}

	overlay, err := ReadOverlay(write(`{"Replace": {"/abs/a.go": "` + repl + `", "rel/b.go": "` + repl + `"}}`))
	if err != nil {
		t.Fatal(err)
	}
	want := map[string][]byte{
		"/abs/a.go":                       []byte("package p\n"),
		filepath.Join(cwd, "rel", "b.go"): []byte("package p\n"),
	}
	if !reflect.DeepEqual(overlay, want) {
		t.Errorf("ReadOverlay = %q, want %q", overlay, want)
	}

	for _, bad := range []string{
		`{"Replace": {"": "` + repl + `"}}`, // empty path
		`{"Replace": {"/abs/a.go": ""}}`,    // deletion
		`{"Replace": {"/abs/a.go": "` + filepath.Join(dir, "missing.go") + `"}}`,
		`{"Replace": {"/abs/a.go": "` + dir + `"}}`,                                 // a directory    // no replacement
		`{"Replace": {"a.go": "` + repl + `", "` + cwd + `/a.go": "` + repl + `"}}`, // twice
		`{"Replace": {}, "Other": 1}`,                                               // unknown field
		`{"Replace": `,                                                              // not JSON
	} {
		if _, err := ReadOverlay(write(bad)); err == nil {
			t.Errorf("ReadOverlay accepted %s", bad)
		}
	}
	if _, err := ReadOverlay(filepath.Join(dir, "none.json")); err == nil {
		t.Errorf("ReadOverlay accepted a missing overlay file")
	}
}
