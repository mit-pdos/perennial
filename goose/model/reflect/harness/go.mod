// The differential harness of the reflect model (goose/model/overlay/reflect): its own module,
// so that ./... of the main module does not build it (gen.sh writes part of it from the overlay).
module github.com/mit-pdos/perennial/goose/model/reflect/harness

go 1.26
