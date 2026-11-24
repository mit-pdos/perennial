package fmt_test

// model_test.go is the overlay's model printer (goose/model/overlay/fmt/printmodel.go, package
// fmt) rewritten into this package, so that the differential tests run the very Go that goose
// translates: the package clause, the import of internal/gomodel dropped, and each
// gomodel.ChooseUint64() replaced by arbitrary() and each gomodel.Choose() by arbitraryBool()
// (model_harness_test.go). TestModelCopy fails when
// the two differ; go test -run TestModelCopy -update rewrites model_test.go.

import (
	"flag"
	"os"
	"strings"
	"testing"
)

var update = flag.Bool("update", false, "rewrite model_test.go from the overlay's printmodel.go")

func modelCopy(src string) string {
	s := strings.Replace(src, "\npackage fmt\n", "\npackage fmt_test\n", 1)
	s = strings.Replace(s, "\t\"internal/gomodel\"\n", "", 1)
	s = strings.ReplaceAll(s, "gomodel.ChooseUint64()", "arbitrary()")
	s = strings.ReplaceAll(s, "gomodel.Choose()", "arbitraryBool()")
	return "// Code generated from goose/model/overlay/fmt/printmodel.go by model_copy_test.go; DO NOT EDIT.\n\n" + s
}

func TestModelCopy(t *testing.T) {
	src, err := os.ReadFile("../overlay/fmt/printmodel.go")
	if err != nil {
		t.Fatal(err)
	}
	want := modelCopy(string(src))
	if strings.Contains(want, "gomodel.") {
		t.Fatal("printmodel.go calls a gomodel function other than Choose and ChooseUint64: extend modelCopy")
	}
	if *update {
		if err := os.WriteFile("model_test.go", []byte(want), 0o644); err != nil {
			t.Fatal(err)
		}
		return
	}
	got, err := os.ReadFile("model_test.go")
	if err != nil {
		t.Fatal(err)
	}
	if string(got) != want {
		t.Fatal("model_test.go differs from the overlay's printmodel.go: go test -run TestModelCopy -update")
	}
}
