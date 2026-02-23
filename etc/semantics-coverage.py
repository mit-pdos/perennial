#!/usr/bin/env python3
#
# opam pin add coq-dpdgraph https://github.com/rocq-community/coq-dpdgraph.git#coq-master
#
# release 1.0 for rocq 9.1 doesn't work - we need Print DependGraph with a list of references.
#
# ./etc/semantics-coverage.py new/proof/github_com/ --generate

import argparse
import os
import re
import subprocess
from dataclasses import dataclass
from typing import Dict, List, Optional


@dataclass
class DpdNode:
    id: int
    name: str
    opaque: bool
    body: bool
    kind: str
    prop: bool
    path: Optional[str]


@dataclass
class DpdEdge:
    src: int
    dst: int
    weight: int


class DpdGraph:
    def __init__(self, nodes: Dict[int, DpdNode], edges: List[DpdEdge]):
        self.nodes = nodes
        self.edges = edges

    @classmethod
    def parse(cls, text: str) -> "DpdGraph":
        nodes: Dict[int, DpdNode] = {}
        edges: List[DpdEdge] = []
        for line in text.splitlines():
            line = line.strip()
            if line.startswith("N:"):
                node = cls._parse_node(line)
                nodes[node.id] = node
            elif line.startswith("E:"):
                edges.append(cls._parse_edge(line))
        return cls(nodes, edges)

    @staticmethod
    def _parse_attrs(attrs_str: str) -> Dict[str, str]:
        attrs: Dict[str, str] = {}
        for attr in attrs_str.split(","):
            attr = attr.strip().rstrip(";").strip()
            if "=" in attr:
                k, v = attr.split("=", 1)
                attrs[k.strip()] = v.strip().strip('"')
        return attrs

    @staticmethod
    def _parse_node(line: str) -> DpdNode:
        # N: 7120 "AE" [opaque=no, body=yes, kind=cnst, prop=no, path="fupd_level", ];
        m = re.match(r'N:\s+(\d+)\s+"([^"]+)"\s+\[([^\]]*)\]', line)
        if not m:
            raise ValueError(f"Invalid node line: {line!r}")
        node_id = int(m.group(1))
        name = m.group(2)
        attrs = DpdGraph._parse_attrs(m.group(3))
        return DpdNode(
            id=node_id,
            name=name,
            opaque=attrs.get("opaque") == "yes",
            body=attrs.get("body") == "yes",
            kind=attrs.get("kind", ""),
            prop=attrs.get("prop") == "yes",
            path=attrs.get("path") or None,
        )

    @staticmethod
    def _parse_edge(line: str) -> DpdEdge:
        # E: 1 14 [weight=1, ];
        m = re.match(r"E:\s+(\d+)\s+(\d+)\s+\[weight=(\d+)", line)
        if not m:
            raise ValueError(f"Invalid edge line: {line!r}")
        return DpdEdge(
            src=int(m.group(1)),
            dst=int(m.group(2)),
            weight=int(m.group(3)),
        )


class CoverageAnalyzer:
    @staticmethod
    def get_semantics_instances(repo_root: str) -> List[str]:
        """Get all global typeclass instance names defined in new/golang/."""
        golang_dir = os.path.join(repo_root, "new", "golang")
        pattern = re.compile(r"#\[global\]\s+([a-zA-Z_]\w*)")
        instances = []
        for dirpath, _, filenames in os.walk(golang_dir):
            for fname in filenames:
                if not fname.endswith(".v"):
                    continue
                with open(os.path.join(dirpath, fname)) as f:
                    for line in f:
                        m = pattern.search(line)
                        if m and "::" in line:
                            instances.append(m.group(1))
        return instances

    @staticmethod
    def get_coverage_proofs(repo_root: str, directory: str) -> List[str]:
        """Get all the .v files for proofs that should be used for coverage."""
        result = []
        for dirpath, _, filenames in os.walk(directory):
            for fname in filenames:
                if fname.endswith(".v"):
                    full = os.path.join(dirpath, fname)
                    result.append(os.path.relpath(full, repo_root))
        return result

    @staticmethod
    def require_path(proof_file: str) -> str:
        # strip leading new/ prefix and .v extension, convert / to .
        # proof_file is relative to repo root, e.g. new/proof/foo/bar.v
        path = proof_file.replace(os.sep, "/")
        if path.startswith("new/"):
            path = path[len("new/") :]
        if path.endswith(".v"):
            path = path[:-2]
        return path.replace("/", ".")

    @staticmethod
    def require_paths(proof_files: List[str]) -> List[str]:
        return [CoverageAnalyzer.require_path(f) for f in proof_files]

    @staticmethod
    def get_rocqproject_args(repo_root: str) -> List[str]:
        rocqproject = os.path.join(repo_root, "_RocqProject")
        with open(rocqproject) as f:
            lines = f.readlines()
        result = []
        for line in lines:
            line = line.strip()
            if line.startswith("#") or not line:
                continue
            line = re.sub(r"-arg ([^ ]*)", r"\1", line)
            line = line.strip()
            if line:
                result.extend(line.split())
        return result

    @staticmethod
    def run_rocq_top(repo_root: str, args: List[str]):
        rocqproject_args = CoverageAnalyzer.get_rocqproject_args(repo_root)
        cmd = ["rocq", "top"] + rocqproject_args + args
        subprocess.run(
            cmd,
            cwd=repo_root,
            stdout=subprocess.DEVNULL,
            check=True,
        )

    @staticmethod
    def get_wp_lemmas(repo_root: str, requires: List[str]) -> List[str]:
        contents = ""
        for p in requires:
            contents += f"From New Require {p}.\n"
        contents += """
Set Search Output Name Only.
Redirect "wp_lemmas" Search concl:weakestpre.wp.
"""
        filename = os.path.join(repo_root, "src", "get_wp_lemmas.v")
        with open(filename, "w") as f:
            f.write(contents)
        try:
            CoverageAnalyzer.run_rocq_top(
                repo_root, ["-l", filename, "-batch", "-output-directory", "."]
            )
        finally:
            os.remove(filename)
        wp_lemmas_out = os.path.join(repo_root, "wp_lemmas.out")
        with open(wp_lemmas_out) as f:
            lemmas = [line.strip() for line in f if line.strip()]
        os.remove(wp_lemmas_out)
        return lemmas

    @staticmethod
    def _create_dpdgraph_file(requires: List[str], lemmas: List[str]) -> str:
        contents = "From dpdgraph Require dpdgraph.\n"
        for p in requires:
            contents += f"From New Require {p}.\n"
        contents += "Print DependGraph\n"
        for lemma in lemmas:
            contents += f"  {lemma}\n"
        contents += "."
        return contents

    @staticmethod
    def get_dpdgraph(repo_root: str, requires: List[str]) -> DpdGraph:
        lemmas = CoverageAnalyzer.get_wp_lemmas(repo_root, requires)
        dpdgraph_v = os.path.join(repo_root, "src", "dpdgraph.v")
        contents = CoverageAnalyzer._create_dpdgraph_file(requires, lemmas)
        with open(dpdgraph_v, "w") as f:
            f.write(contents)
        try:
            CoverageAnalyzer.run_rocq_top(repo_root, ["-l", dpdgraph_v, "-batch"])
        finally:
            os.remove(dpdgraph_v)
        graph_file = os.path.join(repo_root, "graph.dpd")
        with open(graph_file) as f:
            return DpdGraph.parse(f.read())

    @staticmethod
    def compute_coverage(
        instances: List[str], graph: DpdGraph
    ) -> tuple[List[str], List[str]]:
        """Return (covered, uncovered) lists of instance names."""
        node_names = {node.name for node in graph.nodes.values()}
        covered = [i for i in instances if i in node_names]
        uncovered = [i for i in instances if i not in node_names]
        return covered, uncovered


if __name__ == "__main__":
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    parser = argparse.ArgumentParser(
        description="Generate dpdgraph coverage for a directory of proofs"
    )
    parser.add_argument(
        "directory",
        help="Directory of proof files to analyze (e.g. new/proof/github_com/...)",
    )
    parser.add_argument(
        "--generate",
        action="store_true",
        help="Generate graph.dpd from proofs (slow, ~1min); otherwise load existing file",
    )
    args = parser.parse_args()
    directory = os.path.join(repo_root, args.directory)
    graph_file = os.path.join(repo_root, "graph.dpd")
    if args.generate:
        proofs = CoverageAnalyzer.get_coverage_proofs(repo_root, directory)
        requires = CoverageAnalyzer.require_paths(proofs)
        graph = CoverageAnalyzer.get_dpdgraph(repo_root, requires)
    else:
        if not os.path.exists(graph_file):
            parser.error(f"{graph_file} not found; run with --generate to create it")
        with open(graph_file) as f:
            graph = DpdGraph.parse(f.read())
    instances = CoverageAnalyzer.get_semantics_instances(repo_root)
    covered, uncovered = CoverageAnalyzer.compute_coverage(instances, graph)
    print(
        f"Coverage: {len(covered)}/{len(instances)} instances ({100 * len(covered) // len(instances)}%)"
    )
    print()
    print("Uncovered:")
    for name in uncovered:
        print(f"  {name}")
