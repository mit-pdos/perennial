package check_pr

import (
	"context"
	"fmt"
	"regexp"
	"strconv"
	"strings"

	"github.com/google/go-github/v73/github"
)

type PrDependencyInfo struct {
	MainPr        *github.PullRequest
	HasDependency bool
	DependentPr   *github.PullRequest
	DependentNum  int
	DependentSlug string
	SourceSlug    string
	SourceRef     string
}

func (info *PrDependencyInfo) SourceUrl() string {
	return fmt.Sprintf("https://github.com/%s/tree/%s", info.SourceSlug, info.SourceRef)
}

func parseSlug(slug string) (owner string, repo string) {
	if strings.Contains(slug, "https://") {
		panic("slug should be owner/repo, not a URL")
	}
	parts := strings.Split(slug, "/")
	if len(parts) != 2 {
		panic("invalid slug format")
	}
	return parts[0], parts[1]
}

func getPr(client *github.Client, slug string, prNumber int) (*github.PullRequest, error) {
	owner, repo := parseSlug(slug)
	pr, _, err := client.PullRequests.Get(context.Background(), owner, repo, prNumber)
	return pr, err
}

func dependentPr(description string, repoSlug string) (pr int, ok bool) {
	matchOwner, matchRepo := parseSlug(repoSlug)
	re := regexp.MustCompile(`https://github.com/([^/]+)/([^/]+)/pull/(\d+)`)
	matches := re.FindAllStringSubmatch(description, -1)
	for _, match := range matches {
		if len(match) < 3 {
			continue
		}
		owner := match[1]
		repo := match[2]
		prNumber := match[3]

		// Check if this matches the expected repository (format: "owner/repo")
		if owner == matchOwner && repo == matchRepo {
			pr, _ = strconv.Atoi(prNumber)
			ok = true
		}
		return
	}
	return
}

// Get the source (slug and ref) of a PR
func prSource(pr *github.PullRequest) (slug string, ref string) {
	base := pr.GetHead()
	slug = fmt.Sprintf("%s/%s", base.GetRepo().GetOwner().GetLogin(), base.GetRepo().GetName())
	ref = base.GetRef()
	return
}

// CheckPrDependency checks for dependencies in a PR and returns structured information
func CheckPrDependency(client *github.Client, mainRepoSlug string, prNum int, dependentRepoSlug string) (*PrDependencyInfo, error) {
	// Get the main PR
	mainPr, err := getPr(client, mainRepoSlug, prNum)
	if err != nil {
		return nil, fmt.Errorf("failed to get main PR %s#%d: %w", mainRepoSlug, prNum, err)
	}

	info := &PrDependencyInfo{
		MainPr:        mainPr,
		HasDependency: false,
	}

	// Check for dependent PR
	dependentPrNum, ok := dependentPr(mainPr.GetBody(), dependentRepoSlug)
	if !ok {
		return info, nil
	}

	info.HasDependency = true
	info.DependentSlug = dependentRepoSlug
	info.DependentNum = dependentPrNum

	// Get the dependent PR
	dependentPr, err := getPr(client, dependentRepoSlug, dependentPrNum)
	if err != nil {
		return nil, fmt.Errorf("failed to get dependent PR %s#%d: %w", dependentRepoSlug, dependentPrNum, err)
	}

	info.DependentPr = dependentPr
	info.SourceSlug, info.SourceRef = prSource(dependentPr)

	return info, nil
}
