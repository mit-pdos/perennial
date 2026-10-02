package util

import (
	"os"
	"path"
	"testing"
)

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
