package proofsetup

import (
	"os"
	"path"
	"testing"

	"github.com/mit-pdos/perennial/goose/util"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"golang.org/x/tools/go/packages"
)

func TestNewSetup(t *testing.T) {
	assert := assert.New(t)
	require := require.New(t)
	os.Chdir("..")
	pkgs, err := packages.Load(util.NewPackageConfig("./testdata/examples", false), "./semantics")
	require.NoError(err, "internal error: could not load test")
	require.Len(pkgs, 1, "internal error")
	pkg := pkgs[0]
	pf := New(pkg, false)
	assert.Equal(path.Join("new/proof",
		"github_com/mit_pdos/perennial/goose/testdata/examples",
		"semantics.v",
	), pf.ProofPath)
	_ = pf.SkeletonFile()
}
