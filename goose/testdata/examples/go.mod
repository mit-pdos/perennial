module github.com/mit-pdos/perennial/goose/testdata/examples

go 1.26

require (
	github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
	github.com/goose-lang/std v0.7.0
	github.com/stretchr/testify v1.12.1
	github.com/tchajed/marshal v0.6.2
)

require (
	github.com/pkg/errors v0.9.1 // indirect
	go.yaml.in/yaml/v3 v3.0.5 // indirect
	golang.org/x/sys v0.47.0 // indirect
)

replace github.com/tchajed/marshal => github.com/upamanyus/marshal v0.0.0-20260212025754-cf86d74f6773
