package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

var gooseBin string

func TestMain(m *testing.M) {
	// Build the goose binary once for all tests.
	tmp, err := os.MkdirTemp("", "goose-integration")
	if err != nil {
		panic(err)
	}
	defer os.RemoveAll(tmp)

	gooseBin = filepath.Join(tmp, "goose")
	cmd := exec.Command("go", "build", "-o", gooseBin, ".")
	cmd.Stderr = os.Stderr
	if err := cmd.Run(); err != nil {
		panic("failed to build goose: " + err.Error())
	}

	os.Exit(m.Run())
}

// testDir returns the absolute path to testdata/goose-tests.
func testDir(t *testing.T) string {
	t.Helper()
	// This file is at goose/cmd/goose/integration_test.go,
	// testdata is at goose/testdata/goose-tests.
	dir, err := filepath.Abs(filepath.Join("..", "..", "testdata", "goose-tests"))
	if err != nil {
		t.Fatal(err)
	}
	return dir
}

// outDir returns the "Goose/example_com/goose_demo" prefix within dir.
func outDir(dir string) string {
	return filepath.Join(dir, "Goose", "example_com", "goose_demo")
}

// runGoose runs the goose binary with the given args, using dir as the working
// directory. It returns stdout+stderr combined and any error.
func runGoose(t *testing.T, dir string, args ...string) (string, error) {
	t.Helper()
	cmd := exec.Command(gooseBin, args...)
	cmd.Dir = dir
	out, err := cmd.CombinedOutput()
	return string(out), err
}

// mustRunGoose is like runGoose but fails the test on error.
func mustRunGoose(t *testing.T, dir string, args ...string) string {
	t.Helper()
	out, err := runGoose(t, dir, args...)
	if err != nil {
		t.Fatalf("goose %v failed: %v\noutput: %s", args, err, out)
	}
	return out
}

// withCleanOutput creates a temp "Goose" output dir inside dir and removes it
// after the test.
func withCleanOutput(t *testing.T, dir string) string {
	t.Helper()
	outRoot := filepath.Join(dir, "Goose")
	t.Cleanup(func() { os.RemoveAll(outRoot) })
	return outRoot
}

func assertFileExists(t *testing.T, path string) {
	t.Helper()
	if _, err := os.Stat(path); os.IsNotExist(err) {
		t.Errorf("expected file to exist: %s", path)
	}
}

func assertFileNotExist(t *testing.T, path string) {
	t.Helper()
	if _, err := os.Stat(path); err == nil {
		t.Errorf("expected file to not exist: %s", path)
	}
}

func TestCurrentDirectory(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	mustRunGoose(t, dir, "-out", "Goose")

	content, err := os.ReadFile(filepath.Join(outDir(dir), "m.v"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(content), "Require Export New.code.github_com.tchajed.marshal.") {
		t.Error("m.v should contain marshal Require Export")
	}
}

func TestDot(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	mustRunGoose(t, dir, "-out", "Goose", ".")
	assertFileExists(t, filepath.Join(outDir(dir), "m.v"))
}

func TestMultiplePatterns(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	mustRunGoose(t, dir, "-out", "Goose", ".", "./use_disk", "./use_grove")

	out := outDir(dir)
	assertFileExists(t, filepath.Join(out, "m.v"))
	assertFileExists(t, filepath.Join(out, "m", "use_disk.v"))
	assertFileExists(t, filepath.Join(out, "m", "use_grove.v"))
}

func TestGroveFFI(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	mustRunGoose(t, dir, "-out", "Goose", "./use_grove")

	content, err := os.ReadFile(filepath.Join(outDir(dir), "m", "use_grove.v"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(content), "grove_prelude") {
		t.Error("use_grove.v should contain grove_prelude")
	}
}

func TestBadPath(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	out, err := runGoose(t, dir, "-out", "Goose", "./not_a_thing")
	if err == nil {
		t.Fatal("expected goose to fail on bad path")
	}
	if !strings.Contains(out, "could not load package") {
		t.Errorf("expected 'could not load package' in output, got: %s", out)
	}
}

func TestBuildTag(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	mustRunGoose(t, dir, "-out", "Goose", "./errors/build_tag")

	content, err := os.ReadFile(filepath.Join(outDir(dir), "m", "errors", "build_tag.v"))
	if err != nil {
		t.Fatal(err)
	}
	s := string(content)
	if !strings.Contains(s, "Definition Foo") {
		t.Error("build_tag.v should contain Definition Foo")
	}
	if strings.Contains(s, "WontTranslate") {
		t.Error("build_tag.v should not contain WontTranslate")
	}
}

func TestWildcard(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	mustRunGoose(t, dir, "-out", "Goose", "./...")

	out := outDir(dir)
	assertFileExists(t, filepath.Join(out, "m.v"))
	assertFileExists(t, filepath.Join(out, "m", "use_disk.v"))
	assertFileExists(t, filepath.Join(out, "m", "errors", "build_tag.v"))
}

func TestExternalPackage(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	mustRunGoose(t, dir, "-out", "Goose", "github.com/tchajed/marshal")

	content, err := os.ReadFile(filepath.Join(dir, "Goose", "github_com", "tchajed", "marshal.v"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(content), "NewEnc") {
		t.Error("marshal.v should contain NewEnc")
	}
}

func TestDirFlag(t *testing.T) {
	dir := testDir(t)
	// Run from a different directory (the repo root) to test -dir flag.
	repoRoot, err := filepath.Abs(filepath.Join("..", ".."))
	if err != nil {
		t.Fatal(err)
	}
	outRoot := filepath.Join(dir, "Goose")
	t.Cleanup(func() { os.RemoveAll(outRoot) })

	mustRunGoose(t, repoRoot, "-out", outRoot, "-dir", dir)
	assertFileExists(t, filepath.Join(outDir(dir), "m.v"))
}

func TestLocalPath(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	mustRunGoose(t, dir, "-out", "Goose", "example.com/goose-demo/m")
	assertFileExists(t, filepath.Join(outDir(dir), "m.v"))
}

func TestLocalPathWithSubdir(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)
	mustRunGoose(t, dir, "-out", "Goose", "-dir", "use_disk", "example.com/goose-demo/m")

	out := outDir(dir)
	assertFileExists(t, filepath.Join(out, "m.v"))
	assertFileNotExist(t, filepath.Join(out, "m", "use_disk.v"))
}

func TestAfterChange(t *testing.T) {
	dir := testDir(t)
	withCleanOutput(t, dir)

	mFile := filepath.Join(dir, "m.go")
	original, err := os.ReadFile(mFile)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { os.WriteFile(mFile, original, 0644) })

	// First translation
	mustRunGoose(t, dir, "-out", "Goose")

	// Modify source
	modified := strings.ReplaceAll(string(original), "UseMarshal", "ExampleFunc")
	if err := os.WriteFile(mFile, []byte(modified), 0644); err != nil {
		t.Fatal(err)
	}

	// Re-translate
	os.RemoveAll(filepath.Join(dir, "Goose"))
	mustRunGoose(t, dir, "-out", "Goose")

	content, err := os.ReadFile(filepath.Join(outDir(dir), "m.v"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(content), "ExampleFunc") {
		t.Error("m.v should contain ExampleFunc after source change")
	}
}
