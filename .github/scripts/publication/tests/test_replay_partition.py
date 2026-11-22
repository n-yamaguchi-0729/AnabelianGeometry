"""Checks for whole-closure replay scheduling without changing the replay engine."""
from pathlib import Path
import importlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verification"))
scope = importlib.import_module("scope")


class ReplayPartitionTests(unittest.TestCase):
    def test_import_boundaries_and_declarations(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            sources = {
                "Nyll": "/- aggregate -/\nimport A\nimport B\n",
                "A": "import Mathlib.A\ndef first : Nat := 1\n",
                "B": "import Mathlib.B\nimport A\ndef second : Nat := 2\n",
                "C": "import Mathlib.C\ndef third : Nat := 3\n",
            }

            def save(name):
                filename = name + ".lean"
                (root / filename).write_text(sources[name])
                return {"path": filename}

            manifest = {"roots": ["Nyll"], "moduleRows": {n: save(n) for n in ("Nyll", "A", "B")}}
            self.assertEqual(scope.replay_partition(root, manifest, 4),
                             {"replay-01": {"roots": ["B"], "moduleRows": {
                                 n: manifest["moduleRows"][n] for n in ("A", "B")}}})
            with self.assertRaisesRegex(ValueError, "Unknown replay shard"):
                scope.select_scope(root, manifest, {"replayClosureLimit": 4}, "replay-02")
            manifest["moduleRows"]["C"] = save("C")
            with self.assertRaisesRegex(ValueError, "Unpartitionable"):
                scope.replay_partition(root, manifest, 4)
            del manifest["moduleRows"]["C"]
            sources["Nyll"] += "def mustNotSkip : Nat := 2\n"
            save("Nyll")
            with self.assertRaisesRegex(ValueError, "Indivisible replay closure"):
                scope.replay_partition(root, manifest, 4)
            sources["Nyll"] = "import A\nimport B\nimport Mathlib.Other\n"
            save("Nyll")
            with self.assertRaisesRegex(ValueError, "Indivisible replay closure"):
                scope.replay_partition(root, manifest, 5)


if __name__ == "__main__":
    unittest.main()
