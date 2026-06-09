#!/usr/bin/env python3
"""
Analyze Lean 4 import graph and remove redundant imports.
An import is redundant if the imported module is already transitively
available through another import in the same file.
"""

import os
import re
import sys
from collections import defaultdict

SPQR_ROOT = "/Users/hoangtruong/Documents/lean/Max/SparsePostQuantumRatchet"

def find_lean_files(root_dir):
    """Find all .lean files under Spqr/ directory."""
    lean_files = []
    for dirpath, dirnames, filenames in os.walk(os.path.join(root_dir, "Spqr")):
        for f in filenames:
            if f.endswith(".lean"):
                lean_files.append(os.path.join(dirpath, f))
    # Also include Spqr.lean
    spqr_lean = os.path.join(root_dir, "Spqr.lean")
    if os.path.exists(spqr_lean):
        lean_files.append(spqr_lean)
    return sorted(lean_files)

def file_to_module(filepath, root_dir):
    """Convert a file path to a Lean module name."""
    rel = os.path.relpath(filepath, root_dir)
    if rel.endswith(".lean"):
        rel = rel[:-5]
    return rel.replace(os.sep, ".")

def parse_imports(filepath):
    """Parse import statements from a Lean file.
    Returns list of (line_number, module_name) tuples.
    """
    imports = []
    with open(filepath, "r") as f:
        for i, line in enumerate(f, 1):
            stripped = line.strip()
            # Match import statements - only Spqr imports for our internal analysis
            m = re.match(r'^import\s+(Spqr\.\S+)', stripped)
            if m:
                imports.append((i, m.group(1)))
    return imports

def build_import_graph(root_dir):
    """Build a directed graph of imports between Spqr modules."""
    lean_files = find_lean_files(root_dir)

    # Map module name -> list of directly imported Spqr modules
    direct_imports = {}
    # Map module name -> file path
    module_to_file = {}

    for filepath in lean_files:
        module = file_to_module(filepath, root_dir)
        module_to_file[module] = filepath
        imports = parse_imports(filepath)
        direct_imports[module] = [imp for _, imp in imports]

    return direct_imports, module_to_file

def compute_transitive_closure(direct_imports, module):
    """Compute all modules transitively imported by a given module."""
    visited = set()
    stack = list(direct_imports.get(module, []))

    while stack:
        m = stack.pop()
        if m in visited:
            continue
        visited.add(m)
        for dep in direct_imports.get(m, []):
            if dep not in visited:
                stack.append(dep)

    return visited

def find_redundant_imports(direct_imports, module_to_file):
    """Find redundant imports in each file.
    An import X in file F is redundant if X is transitively imported
    by some other import Y in F (where Y != X).
    """
    redundant = {}  # module -> list of redundant import module names

    for module, imports in direct_imports.items():
        if not imports:
            continue

        # For each import, compute what it transitively provides
        # (excluding itself)
        redundant_imports = []

        for i, imp in enumerate(imports):
            # Check if this import is redundant
            # i.e., it's in the transitive closure of some other import
            is_redundant = False
            for j, other_imp in enumerate(imports):
                if i == j:
                    continue
                # Compute transitive closure of other_imp
                tc = compute_transitive_closure(direct_imports, other_imp)
                if imp in tc:
                    is_redundant = True
                    break

            if is_redundant:
                redundant_imports.append(imp)

        if redundant_imports:
            redundant[module] = redundant_imports

    return redundant

def remove_redundant_imports_from_file(filepath, redundant_modules):
    """Remove redundant import lines from a file."""
    with open(filepath, "r") as f:
        lines = f.readlines()

    new_lines = []
    removed = []
    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        m = re.match(r'^import\s+(Spqr\.\S+)', stripped)
        if m and m.group(1) in redundant_modules:
            removed.append((i, m.group(1)))
            continue
        new_lines.append(line)

    if removed:
        with open(filepath, "w") as f:
            f.writelines(new_lines)

    return removed

def main():
    dry_run = "--dry-run" in sys.argv

    print("Building import graph...")
    direct_imports, module_to_file = build_import_graph(SPQR_ROOT)
    print(f"Found {len(direct_imports)} modules")

    print("Finding redundant imports...")
    redundant = find_redundant_imports(direct_imports, module_to_file)

    # Skip Spqr.lean - it's the root library file that intentionally imports everything
    if "Spqr" in redundant:
        del redundant["Spqr"]

    total_removed = 0
    files_modified = 0

    for module in sorted(redundant.keys()):
        filepath = module_to_file.get(module)
        if not filepath:
            continue

        redundant_mods = set(redundant[module])
        rel_path = os.path.relpath(filepath, SPQR_ROOT)

        if dry_run:
            print(f"\n{rel_path}:")
            for mod in sorted(redundant_mods):
                print(f"  - REMOVE: import {mod}")
            total_removed += len(redundant_mods)
            files_modified += 1
        else:
            removed = remove_redundant_imports_from_file(filepath, redundant_mods)
            if removed:
                print(f"\n{rel_path}:")
                for line_num, mod in removed:
                    print(f"  - Removed line {line_num}: import {mod}")
                total_removed += len(removed)
                files_modified += 1

    print(f"\n{'Would remove' if dry_run else 'Removed'} {total_removed} redundant imports from {files_modified} files")

if __name__ == "__main__":
    main()
