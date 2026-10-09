ci:
	test -z "$$(gofmt -d -s .)"
	go vet -composites=false ./...
	go test $$(go list -f '{{.Dir}}/...' -m | xargs)

fix:
	gofmt -w -s .
	go generate ./...

.PHONY: ci fix
