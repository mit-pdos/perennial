package skip_init

var X = uint64(1)

var Y = X + 1 // ERROR skipped variable X (skip: "a constant: cannot panic, no effect beyond the variable") is referenced by translated the initializer of Y
