"""Regression checks for the source links and mathematical dependencies in the dashboard."""

from copy import deepcopy
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from lean_source import unique_locations
from math_markdown import protect
from render import validate_locations, validate_packages
from review_sources import local_modules


class DashboardTests(unittest.TestCase):
    def test_link_is_a_definition_in_its_actual_namespace(self):
        source = """
namespace First
section
/-
/- nested comment -/
theorem phantom : True := trivial
-/
theorem statement : True := trivial
end
end First
#print axioms Second.statement
"""
        wanted = {"First.statement", "First.phantom", "Second.statement"}
        self.assertEqual(unique_locations([("A.lean", source)], wanted), {"First.statement": "A.lean#L8"})
        self.assertEqual(unique_locations([("A.lean", source), ("B.lean", source)], wanted), {})

    def test_standalone_build_and_research_copies_are_both_counted(self):
        data = {"packages": [{"headers": ["X.a"]}], "declarations": {"X.a": "Lean/A.lean#L2"}}
        with TemporaryDirectory() as directory:
            root = Path(directory)
            for folder in ("Lean", "bounded"):
                (root / folder).mkdir()
            source = "namespace X\ntheorem a : True := trivial\nend X\n"
            (root / "Lean/A.lean").write_text(source)
            validate_locations(data, root)
            cache = root / "bounded/.lake/packages/example"
            cache.mkdir(parents=True)
            (cache / "Imported.lean").write_text(source)
            validate_locations(data, root)
            (root / "bounded/B.lean").write_text(source)
            with self.assertRaisesRegex(ValueError, "ambiguous"):
                validate_locations(data, root)

    def test_dependencies_are_acyclic_and_have_no_duplicate_edges(self):
        data = {"chapters": ["Height"], "routes": ["Bounded"], "packages": [
            {"id": "a", "chapter": "Height", "routes": ["Bounded"], "state": "kernel", "needs": []},
            {"id": "b", "chapter": "Height", "routes": ["Bounded"], "state": "kernel", "needs": ["a"]},
        ]}
        validate_packages(data)
        cyclic = deepcopy(data)
        cyclic["packages"][0]["needs"] = ["b"]
        with self.assertRaisesRegex(ValueError, "Circular"):
            validate_packages(cyclic)
        data["packages"][1]["needs"].append("a")
        with self.assertRaisesRegex(ValueError, "Invalid package b"):
            validate_packages(data)

    def test_display_row_breaks_survive_github_markdown(self):
        source = "$$\na & = b, " + r"\\" + "\nc & = d.\n$$\n"
        protected, formulas = protect(source)
        self.assertIn(r"\\[0pt]", formulas[0][1])
        self.assertEqual(protect(protected), (protected, formulas))

    def test_imports_resolve_from_library_roots(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").write_text(
                'defaultTargets = ["Proof"]\n[[lean_lib]]\nname = "Proof"\nsrcDir = "src"\n'
                'roots = ["Part.Main"]\n[[lean_lib]]\nname = "Arithmetic"\nsrcDir = "lib"\n')
            sources = {root / "src/Part/Main.lean": "public import Part.Points Arithmetic.Types\n",
                       root / "src/Part/Points.lean": "import Mathlib\n",
                       root / "lib/Arithmetic/Types.lean": ""}
            self.assertEqual(local_modules(root, sources), set(sources))
            sources[root / "src/Arithmetic/Types.lean"] = ""
            with self.assertRaisesRegex(ValueError, "Ambiguous local import"):
                local_modules(root, sources)


if __name__ == "__main__":
    unittest.main()
