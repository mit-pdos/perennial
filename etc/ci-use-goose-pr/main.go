package main

import (
	"flag"
	"fmt"
	"os"

	"github.com/google/go-github/v73/github"
	"github.com/mit-pdos/perennial/etc/ci-use-goose-pr/check_pr"
)

var verbose bool

func verbosePrintf(format string, args ...any) {
	if verbose {
		fmt.Fprintf(os.Stderr, format, args...)
	}
}

func main() {
	prNum := flag.Int("pr", 0, "perennial PR to check")
	flag.BoolVar(&verbose, "verbose", false, "print extra info to stderr")
	flag.Parse()

	token := os.Getenv("GITHUB_TOKEN")

	if *prNum == 0 {
		fmt.Fprintf(os.Stderr, "No PR specified\n")
		os.Exit(1)
	}

	client := github.NewClient(nil)
	if token != "" {
		client = client.WithAuthToken(token)
	}
	info, err := check_pr.CheckPrDependency(client, "mit-pdos/perennial", *prNum, "goose-lang/goose")
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error checking PR dependency: %v\n", err)
		os.Exit(1)
	}

	if !info.HasDependency {
		verbosePrintf("no dependent goose PR found\n")
		return
	}

	verbosePrintf("INFO depends on: %s#%d\n", info.DependentSlug, info.DependentNum)
	verbosePrintf("INFO status: %s\n", info.DependentPr.GetState())
	verbosePrintf("INFO source: %s at %s\n", info.SourceSlug, info.SourceRef)
	if !(info.DependentPr.GetState() == "open") {
		return
	}
	fmt.Println(info.SourceUrl())
}
