ci:
	test -z "$$(gofmt -d -s .)"
	go vet -composites=false ./...
	go test $$(go list -f '{{.Dir}}/...' -m | xargs)
	./test/bats/bin/bats ./test/goose.bats

fix:
	gofmt -w -s .
	go generate ./...

.PHONY: ci fix
