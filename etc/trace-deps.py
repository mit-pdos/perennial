#!/usr/bin/env python3
import collections
import sys


def main():
    if len(sys.argv) != 3:
        print(
            "usage: trace-deps.py <A.vos/vo/vok> <B.vos/vo/vok> will show why A transitively depends on B"
        )
        exit(-1)

    deps = collections.defaultdict(set)
    with open(".rocqdeps.d") as f:
        for line in f.readlines():
            parents, children = tuple(m.split(" ") for m in line.strip().split(": "))
            for p in parents:
                for c in children:
                    deps[p].add(c)

    # find path from A to B
    A = sys.argv[1]
    B = sys.argv[2]
    visited = set()
    cur_path = [A]

    def recur():
        cur_node = cur_path[-1]
        visited.add(cur_node)
        if cur_node == B:
            return cur_path
        for next_node in deps[cur_node]:
            if next_node in visited:
                continue
            cur_path.append(next_node)
            r = recur()
            if r:
                return r
            cur_path.pop()
        return None

    print(" -> ".join(recur()))


if __name__ == "__main__":
    main()
