// The Go model overlays: each directory, goose/model/overlay/<import path>, is
// the model of that package, named by the [model] table of its goose config
// (Perennial/Code/<import path>.toml). Its files are compiled only as part of
// the real package, under the overlay goose builds (`goose model-overlay`),
// so this module, which nothing builds, keeps ./... from compiling them on
// their own.
module github.com/mit-pdos/perennial/goose/model/overlay

go 1.26
