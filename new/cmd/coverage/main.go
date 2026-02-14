package main

import (
	"bufio"
	"flag"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
)

type Instance struct {
	Name        string
	File        string
	Line        int
	PatternType string // "Instance" or "ClassField"
}

func (i Instance) String() string {
	return i.Name
}

// ExtractInstances extracts all global instances from .v files in the given directory
func ExtractInstances(golangDir string) ([]Instance, error) {
	var instances []Instance

	// Patterns to match
	// Pattern 1: #[global] Instance <name> ...
	instanceRe := regexp.MustCompile(`#\[global\]\s+Instance\s+(\w+)`)
	// Pattern 2: #[global] <name> <params> :: <type>
	classFieldRe := regexp.MustCompile(`#\[global\]\s+(\w+)(?:\s+[^:]+)?\s*::`)

	err := filepath.Walk(golangDir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if info.IsDir() || !strings.HasSuffix(path, ".v") {
			return nil
		}

		file, err := os.Open(path)
		if err != nil {
			return err
		}
		defer file.Close()

		relPath, _ := filepath.Rel(filepath.Dir(filepath.Dir(golangDir)), path)
		scanner := bufio.NewScanner(file)
		lineNum := 0

		for scanner.Scan() {
			lineNum++
			line := scanner.Text()

			// Check for Instance pattern
			if match := instanceRe.FindStringSubmatch(line); match != nil {
				instances = append(instances, Instance{
					Name:        match[1],
					File:        relPath,
					Line:        lineNum,
					PatternType: "Instance",
				})
				continue
			}

			// Check for ClassField pattern
			if match := classFieldRe.FindStringSubmatch(line); match != nil {
				name := match[1]
				// Skip if it's actually "Instance"
				if name != "Instance" {
					instances = append(instances, Instance{
						Name:        name,
						File:        relPath,
						Line:        lineNum,
						PatternType: "ClassField",
					})
				}
			}
		}

		return scanner.Err()
	})

	if err != nil {
		return nil, err
	}

	// Sort by file and line
	sort.Slice(instances, func(i, j int) bool {
		if instances[i].File != instances[j].File {
			return instances[i].File < instances[j].File
		}
		return instances[i].Line < instances[j].Line
	})

	return instances, nil
}

// WriteInstanceList writes the instance list to a file
func WriteInstanceList(instances []Instance, outputPath string) error {
	file, err := os.Create(outputPath)
	if err != nil {
		return err
	}
	defer file.Close()

	fmt.Fprintf(file, "# Found %d instances\n", len(instances))
	fmt.Fprintln(file, "# Format: name|file|line|type")
	for _, inst := range instances {
		fmt.Fprintf(file, "%s|%s|%d|%s\n", inst.Name, inst.File, inst.Line, inst.PatternType)
	}

	return nil
}

// LoadInstanceList loads an instance list from a file
func LoadInstanceList(path string) ([]Instance, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	var instances []Instance
	scanner := bufio.NewScanner(file)

	for scanner.Scan() {
		line := scanner.Text()
		if strings.HasPrefix(line, "#") || line == "" {
			continue
		}

		parts := strings.Split(line, "|")
		if len(parts) != 4 {
			continue
		}

		lineNum, _ := strconv.Atoi(parts[2])
		instances = append(instances, Instance{
			Name:        parts[0],
			File:        parts[1],
			Line:        lineNum,
			PatternType: parts[3],
		})
	}

	return instances, scanner.Err()
}

// ParseTypeclassDebugOutput parses Coq typeclass debug output from a reader and returns instance usage counts
func ParseTypeclassDebugOutput(r io.Reader) (map[string]int, error) {
	counts := make(map[string]int)
	scanner := bufio.NewScanner(r)
	// Increase buffer size for potentially long lines
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	// Match patterns like:
	// "Debug: 1.1: exact Nat.eq_dec on (EqDecision nat), 0 subgoal(s)"
	// "Debug: 1.1: simple apply @decide_rel on (Decision (x = y)), 1 subgoal(s)"
	// "Debug: 1.1: simple apply bool_GenType on (GenType bool Σ), 0 subgoal(s)"
	exactRe := regexp.MustCompile(`Debug:.*: exact (@?\S+) on`)
	applyRe := regexp.MustCompile(`Debug:.*: simple apply (@?\S+) on`)

	for scanner.Scan() {
		line := scanner.Text()

		// Check for exact pattern
		if match := exactRe.FindStringSubmatch(line); match != nil {
			instanceName := strings.TrimPrefix(match[1], "@")
			counts[instanceName]++
			continue
		}

		// Check for simple apply pattern
		if match := applyRe.FindStringSubmatch(line); match != nil {
			instanceName := strings.TrimPrefix(match[1], "@")
			counts[instanceName]++
		}
	}

	return counts, scanner.Err()
}

// ParseBuildLogPerFile parses a full build log with "ROCQ COMPILE" markers
// and returns a map of file -> instance counts
func ParseBuildLogPerFile(r io.Reader) (map[string]map[string]int, error) {
	fileCounts := make(map[string]map[string]int)
	scanner := bufio.NewScanner(r)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	// Match "ROCQ COMPILE <file>"
	compileRe := regexp.MustCompile(`ROCQ COMPILE (.+\.v)`)
	exactRe := regexp.MustCompile(`Debug:.*: exact (@?\S+) on`)
	applyRe := regexp.MustCompile(`Debug:.*: simple apply (@?\S+) on`)

	currentFile := ""

	for scanner.Scan() {
		line := scanner.Text()

		// Check for new file being compiled
		if match := compileRe.FindStringSubmatch(line); match != nil {
			currentFile = match[1]
			if _, exists := fileCounts[currentFile]; !exists {
				fileCounts[currentFile] = make(map[string]int)
			}
			continue
		}

		// Skip if no current file
		if currentFile == "" {
			continue
		}

		// Check for exact pattern
		if match := exactRe.FindStringSubmatch(line); match != nil {
			instanceName := strings.TrimPrefix(match[1], "@")
			fileCounts[currentFile][instanceName]++
			continue
		}

		// Check for simple apply pattern
		if match := applyRe.FindStringSubmatch(line); match != nil {
			instanceName := strings.TrimPrefix(match[1], "@")
			fileCounts[currentFile][instanceName]++
		}
	}

	return fileCounts, scanner.Err()
}

// ParseTypeclassDebugLog parses Coq typeclass debug output from a file
func ParseTypeclassDebugLog(logPath string) (map[string]int, error) {
	file, err := os.Open(logPath)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	return ParseTypeclassDebugOutput(file)
}

// WriteCovFile writes a .cov file with instance usage counts
func WriteCovFile(counts map[string]int, outputPath string) error {
	file, err := os.Create(outputPath)
	if err != nil {
		return err
	}
	defer file.Close()

	// Sort by name for consistent output
	var names []string
	for name := range counts {
		names = append(names, name)
	}
	sort.Strings(names)

	for _, name := range names {
		fmt.Fprintf(file, "%s|%d\n", name, counts[name])
	}

	return nil
}

// LoadCovFile loads a .cov file
func LoadCovFile(path string) (map[string]int, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	counts := make(map[string]int)
	scanner := bufio.NewScanner(file)

	for scanner.Scan() {
		line := scanner.Text()
		parts := strings.Split(line, "|")
		if len(parts) != 2 {
			continue
		}
		count, _ := strconv.Atoi(parts[1])
		counts[parts[0]] = count
	}

	return counts, scanner.Err()
}

// AggregateCovFiles aggregates multiple .cov files into a single map
func AggregateCovFiles(covDir string) (map[string]int, error) {
	totals := make(map[string]int)

	err := filepath.Walk(covDir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if info.IsDir() || !strings.HasSuffix(path, ".cov") {
			return nil
		}

		counts, err := LoadCovFile(path)
		if err != nil {
			return err
		}

		for name, count := range counts {
			totals[name] += count
		}

		return nil
	})

	return totals, err
}

// FindUncoveredInstances returns instances that have zero coverage
func FindUncoveredInstances(instances []Instance, coverage map[string]int) []Instance {
	var uncovered []Instance

	for _, inst := range instances {
		if coverage[inst.Name] == 0 {
			uncovered = append(uncovered, inst)
		}
	}

	return uncovered
}

// ParseRocqProject reads _RocqProject and extracts the arguments for rocq compile
func ParseRocqProject(projectFile string) ([]string, error) {
	file, err := os.Open(projectFile)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	var args []string
	scanner := bufio.NewScanner(file)

	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		// Skip comments and empty lines
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}

		// Parse -Q and -arg directives
		if strings.HasPrefix(line, "-Q ") {
			parts := strings.Fields(line)
			if len(parts) >= 3 {
				args = append(args, "-Q", parts[1], parts[2])
			}
		} else if strings.HasPrefix(line, "-arg ") {
			// -arg <value> adds <value> as an argument
			rest := strings.TrimPrefix(line, "-arg ")
			rest = strings.TrimSpace(rest)
			// Handle quoted arguments
			if strings.HasPrefix(rest, "-w") {
				args = append(args, rest)
			} else {
				args = append(args, rest)
			}
		}
	}

	return args, scanner.Err()
}

func cmdExtract(args []string) {
	fs := flag.NewFlagSet("extract", flag.ExitOnError)
	output := fs.String("o", "", "Output file (default: stdout)")
	fs.Parse(args)

	golangDir := fs.Arg(0)
	if golangDir == "" {
		golangDir = "new/golang/defn"
	}

	instances, err := ExtractInstances(golangDir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error extracting instances: %v\n", err)
		os.Exit(1)
	}

	if *output != "" {
		if err := WriteInstanceList(instances, *output); err != nil {
			fmt.Fprintf(os.Stderr, "Error writing output: %v\n", err)
			os.Exit(1)
		}
		fmt.Printf("Wrote %d instances to %s\n", len(instances), *output)
	} else {
		fmt.Printf("# Found %d instances\n", len(instances))
		fmt.Println("# Format: name|file|line|type")
		for _, inst := range instances {
			fmt.Printf("%s|%s|%d|%s\n", inst.Name, inst.File, inst.Line, inst.PatternType)
		}
	}
}

func cmdParselog(args []string) {
	fs := flag.NewFlagSet("parselog", flag.ExitOnError)
	output := fs.String("o", "", "Output .cov file (for single file mode)")
	perFile := fs.Bool("per-file", false, "Parse build log with ROCQ COMPILE markers and generate per-file .cov files")
	proofPrefix := fs.String("proof-prefix", "new/proof/", "Only generate .cov files for files with this prefix")
	fs.Parse(args)

	logPath := fs.Arg(0)
	if logPath == "" {
		fmt.Fprintln(os.Stderr, "Usage: coverage parselog [-o output.cov | -per-file] logfile")
		os.Exit(1)
	}

	file, err := os.Open(logPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error opening log file: %v\n", err)
		os.Exit(1)
	}
	defer file.Close()

	if *perFile {
		fileCounts, err := ParseBuildLogPerFile(file)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error parsing log: %v\n", err)
			os.Exit(1)
		}

		totalFiles := 0
		totalInstances := 0
		for filePath, counts := range fileCounts {
			// Only process files with the specified prefix
			if !strings.HasPrefix(filePath, *proofPrefix) {
				continue
			}
			if len(counts) == 0 {
				continue
			}
			outPath := strings.TrimSuffix(filePath, ".v") + ".cov"
			if err := WriteCovFile(counts, outPath); err != nil {
				fmt.Fprintf(os.Stderr, "Error writing %s: %v\n", outPath, err)
				continue
			}
			totalFiles++
			totalInstances += len(counts)
			fmt.Printf("Wrote %d instances to %s\n", len(counts), outPath)
		}
		fmt.Printf("\nTotal: %d files, %d unique instances\n", totalFiles, totalInstances)
	} else {
		if *output == "" {
			fmt.Fprintln(os.Stderr, "Usage: coverage parselog -o output.cov logfile")
			os.Exit(1)
		}

		counts, err := ParseTypeclassDebugOutput(file)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error parsing log: %v\n", err)
			os.Exit(1)
		}

		if err := WriteCovFile(counts, *output); err != nil {
			fmt.Fprintf(os.Stderr, "Error writing coverage file: %v\n", err)
			os.Exit(1)
		}

		fmt.Printf("Wrote coverage data (%d unique instances) to %s\n", len(counts), *output)
	}
}

func cmdAggregate(args []string) {
	fs := flag.NewFlagSet("aggregate", flag.ExitOnError)
	instancesFile := fs.String("instances", "", "Instance list file (from extract command) - required")
	fs.Parse(args)

	if *instancesFile == "" {
		fmt.Fprintln(os.Stderr, "Usage: coverage aggregate -instances instances.txt [cov-dir]")
		fmt.Fprintln(os.Stderr, "Error: -instances flag is required")
		os.Exit(1)
	}

	covDir := fs.Arg(0)
	if covDir == "" {
		covDir = "."
	}

	// Load the instance list
	instances, err := LoadInstanceList(*instancesFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error loading instances: %v\n", err)
		os.Exit(1)
	}

	// Aggregate coverage from .cov files
	totals, err := AggregateCovFiles(covDir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error aggregating coverage: %v\n", err)
		os.Exit(1)
	}

	// Build sorted list with counts for each instance (including 0s)
	type kv struct {
		Name  string
		File  string
		Line  int
		Count int
	}
	var sorted []kv
	for _, inst := range instances {
		sorted = append(sorted, kv{
			Name:  inst.Name,
			File:  inst.File,
			Line:  inst.Line,
			Count: totals[inst.Name], // will be 0 if not found
		})
	}

	// Sort by count (descending) then name
	sort.Slice(sorted, func(i, j int) bool {
		if sorted[i].Count != sorted[j].Count {
			return sorted[i].Count > sorted[j].Count
		}
		return sorted[i].Name < sorted[j].Name
	})

	// Calculate coverage stats
	covered := 0
	for _, kv := range sorted {
		if kv.Count > 0 {
			covered++
		}
	}

	fmt.Printf("# Aggregated coverage from %s\n", covDir)
	fmt.Printf("# Coverage: %d/%d (%.1f%%)\n", covered, len(instances),
		float64(covered)/float64(len(instances))*100)

	fmt.Println("\n# Instance usage counts:")
	for _, kv := range sorted {
		fmt.Printf("%s|%d\n", kv.Name, kv.Count)
	}
}

// RunProofWithDebug compiles a proof file with Typeclasses Debug enabled and returns instance counts
func RunProofWithDebug(proofFile string, projectRoot string) (map[string]int, error) {
	// Read arguments from _RocqProject
	rocqProjectPath := filepath.Join(projectRoot, "_RocqProject")
	projectArgs, err := ParseRocqProject(rocqProjectPath)
	if err != nil {
		return nil, fmt.Errorf("failed to parse _RocqProject: %w", err)
	}

	// Build the rocq compile command with Typeclasses Debug enabled
	args := []string{"compile"}
	args = append(args, projectArgs...)
	args = append(args, "-set", "Typeclasses Debug", proofFile)

	cmd := exec.Command("rocq", args...)
	cmd.Dir = projectRoot

	// Capture stderr which contains the debug output
	stderr, err := cmd.StderrPipe()
	if err != nil {
		return nil, fmt.Errorf("failed to create stderr pipe: %w", err)
	}

	if err := cmd.Start(); err != nil {
		return nil, fmt.Errorf("failed to start rocq: %w", err)
	}

	// Parse the debug output
	counts, parseErr := ParseTypeclassDebugOutput(stderr)

	if err := cmd.Wait(); err != nil {
		// Compilation might fail but we still want the coverage data
		fmt.Fprintf(os.Stderr, "Warning: rocq compile returned error: %v\n", err)
	}

	if parseErr != nil {
		return nil, fmt.Errorf("failed to parse debug output: %w", parseErr)
	}

	return counts, nil
}

// FindProofFiles returns all .v files in the proof directory
func FindProofFiles(proofDir string) ([]string, error) {
	var files []string

	err := filepath.Walk(proofDir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if info.IsDir() || !strings.HasSuffix(path, ".v") {
			return nil
		}
		// Skip __nobuild files
		if strings.Contains(path, "__nobuild") {
			return nil
		}
		files = append(files, path)
		return nil
	})

	return files, err
}

func cmdRun(args []string) {
	fs := flag.NewFlagSet("run", flag.ExitOnError)
	output := fs.String("o", "", "Output .cov file (default: <prooffile>.cov)")
	projectRoot := fs.String("root", ".", "Project root directory")
	fs.Parse(args)

	proofFile := fs.Arg(0)
	if proofFile == "" {
		fmt.Fprintln(os.Stderr, "Usage: coverage run [-o output.cov] [-root dir] prooffile.v")
		os.Exit(1)
	}

	fmt.Printf("Running %s with Typeclasses Debug...\n", proofFile)

	counts, err := RunProofWithDebug(proofFile, *projectRoot)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	outPath := *output
	if outPath == "" {
		outPath = strings.TrimSuffix(proofFile, ".v") + ".cov"
	}

	if err := WriteCovFile(counts, outPath); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing coverage file: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("Wrote coverage data (%d unique instances) to %s\n", len(counts), outPath)
}

func cmdRunall(args []string) {
	fs := flag.NewFlagSet("runall", flag.ExitOnError)
	proofDir := fs.String("proof", "new/proof", "Proof directory")
	projectRoot := fs.String("root", ".", "Project root directory")
	parallel := fs.Int("j", 1, "Number of parallel jobs")
	fs.Parse(args)

	files, err := FindProofFiles(*proofDir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error finding proof files: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("Found %d proof files in %s\n", len(files), *proofDir)

	// Simple sequential execution for now
	// TODO: add parallel execution with -j flag
	_ = parallel

	for i, file := range files {
		fmt.Printf("[%d/%d] Processing %s...\n", i+1, len(files), file)

		counts, err := RunProofWithDebug(file, *projectRoot)
		if err != nil {
			fmt.Fprintf(os.Stderr, "  Error: %v\n", err)
			continue
		}

		outPath := strings.TrimSuffix(file, ".v") + ".cov"
		if err := WriteCovFile(counts, outPath); err != nil {
			fmt.Fprintf(os.Stderr, "  Error writing coverage: %v\n", err)
			continue
		}

		fmt.Printf("  Wrote %d instances to %s\n", len(counts), outPath)
	}
}

func cmdBuild(args []string) {
	fs := flag.NewFlagSet("build", flag.ExitOnError)
	source := fs.String("source", "", "Source .v file to build (e.g., new/proof/sync.v)")
	projectRoot := fs.String("root", ".", "Project root directory")
	proofPrefix := fs.String("proof-prefix", "new/proof/", "Only generate .cov files for files with this prefix")
	fs.Parse(args)

	// Also accept source file as positional argument
	sourceFile := *source
	if sourceFile == "" && fs.NArg() > 0 {
		sourceFile = fs.Arg(0)
	}

	makeArgs := []string{}
	if sourceFile != "" {
		// Convert .v to .vo for make target
		target := strings.TrimSuffix(sourceFile, ".v") + ".vo"
		makeArgs = append(makeArgs, target)
	}
	makeArgs = append(makeArgs, `ROCQ_ARGS=-set "Typeclasses Debug"`)

	cmd := exec.Command("make", makeArgs...)
	cmd.Dir = *projectRoot

	// Create a pipe to capture both stdout and stderr
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error creating stdout pipe: %v\n", err)
		os.Exit(1)
	}
	stderr, err := cmd.StderrPipe()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error creating stderr pipe: %v\n", err)
		os.Exit(1)
	}

	if err := cmd.Start(); err != nil {
		fmt.Fprintf(os.Stderr, "Error starting make: %v\n", err)
		os.Exit(1)
	}

	// Merge stdout and stderr and parse live
	merged := io.MultiReader(stdout, stderr)
	fileCounts, parseErr := ParseBuildLogPerFile(merged)

	if err := cmd.Wait(); err != nil {
		fmt.Fprintf(os.Stderr, "Build returned error: %v\n", err)
	}

	if parseErr != nil {
		fmt.Fprintf(os.Stderr, "Error parsing build output: %v\n", parseErr)
		os.Exit(1)
	}

	// Write .cov files (only for files with the specified prefix)
	totalFiles := 0
	totalInstances := 0
	for filePath, counts := range fileCounts {
		// Only process files with the specified prefix
		if !strings.HasPrefix(filePath, *proofPrefix) {
			continue
		}
		if len(counts) == 0 {
			continue
		}
		outPath := strings.TrimSuffix(filePath, ".v") + ".cov"
		if err := WriteCovFile(counts, outPath); err != nil {
			fmt.Fprintf(os.Stderr, "Error writing %s: %v\n", outPath, err)
			continue
		}
		totalFiles++
		totalInstances += len(counts)
	}

	fmt.Printf("Wrote .cov files for %d files (%d total unique instances)\n", totalFiles, totalInstances)
}

func printUsage() {
	fmt.Println("Usage: coverage <command> [args]")
	fmt.Println("\nCommands:")
	fmt.Println("  extract [golang-dir]       Extract instances from golang directory")
	fmt.Println("  build [-source f.v]        Run make with Typeclasses Debug and generate .cov files")
	fmt.Println("  run [-o out.cov] file.v    Run a single proof file with debug")
	fmt.Println("  parselog [-per-file] log   Parse typeclass debug log")
	fmt.Println("  aggregate -instances f dir Aggregate .cov files and report coverage")
	fmt.Println("  help                       Show this help message")
	fmt.Println("\nTypical workflow:")
	fmt.Println("  1. coverage extract -o instances.txt  # defaults to new/golang/defn")
	fmt.Println("  2. coverage build new/proof/foo.v")
	fmt.Println("  3. coverage aggregate -instances instances.txt new/proof")
}

func main() {
	if len(os.Args) < 2 {
		printUsage()
		os.Exit(1)
	}

	switch os.Args[1] {
	case "extract":
		cmdExtract(os.Args[2:])
	case "build":
		cmdBuild(os.Args[2:])
	case "run":
		cmdRun(os.Args[2:])
	case "runall":
		cmdRunall(os.Args[2:])
	case "parselog":
		cmdParselog(os.Args[2:])
	case "aggregate":
		cmdAggregate(os.Args[2:])
	case "help", "-h", "--help":
		printUsage()
	default:
		fmt.Fprintf(os.Stderr, "Unknown command: %s\n", os.Args[1])
		printUsage()
		os.Exit(1)
	}
}
