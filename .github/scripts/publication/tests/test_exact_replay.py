from copy import deepcopy
from pathlib import Path
from tempfile import TemporaryDirectory
import importlib
import os
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verification"))
exact = importlib.import_module("exact_replay")


class ExactReplayTests(unittest.TestCase):
    def test_gate(self):
        with patch.dict(os.environ, {"GITHUB_SHA": "fixed", "GITHUB_RUN_ID": "run"}):
            m = {"include": [{"phase": "proof", "shard": "all"},
                             {"phase": "replay", "shard": "replay-01"}]}
            a = {"identity": exact.identity(), "audit": {"replay-01": {"A": {".olean": "sha"}}}}
            s = {"identity": exact.identity(), "shard": "replay-01", "artifacts": {"A": {".olean": "sha"}}}
            exact.gate(m, [a, s])
            for evidence in ([a], [s], [a, s, s]):
                with self.assertRaises(ValueError):
                    exact.gate(m, evidence)
            for field, value in (("identity", {"GITHUB_SHA": "other"}), ("shard", "replay-02"),
                                 ("artifacts", {"A": {".olean": "tampered"}})):
                bad = deepcopy(s)
                bad[field] = value
                with self.assertRaises(ValueError):
                    exact.gate(m, [a, bad])
            with self.assertRaises(ValueError):
                exact.gate({"include": m["include"][1:]}, [a, s])

    def test_bind_all_companion_files_and_path_independence(self):
        with TemporaryDirectory() as t:
            root = Path(t)
            one, two = root / "one", root / "two"
            for d in (one, two):
                d.mkdir()
                for role in (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig"):
                    (d / ("M" + role)).write_text(role)

            def read(d):
                return exact.snapshot({"modules": [{"module": "M", "files": [str(p) for p in d.iterdir()]}]})

            self.assertEqual(read(one), read(two))
            (two / "M.olean.private").write_text("tampered")
            self.assertNotEqual(read(one), read(two))
            (two / "M.olean").unlink()
            with self.assertRaises(ValueError):
                read(two)


if __name__ == "__main__":
    unittest.main()
