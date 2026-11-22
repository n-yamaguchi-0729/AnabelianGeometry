"""Fail-closed binding between the exact whole-vs-shard audit and shard replay."""
import hashlib
import json
import os
from pathlib import Path
import sys


def records(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.startswith("{")]


def snapshot(row):
    result = {}
    for entry in row["modules"]:
        name = entry["module"]
        if name in result:
            raise ValueError(f"Duplicate module: {name}")
        files = {}
        for entry_path in entry["files"]:
            path = Path(entry_path)
            role = next((role for role in (".olean.server", ".olean.private", ".olean", ".ir.sig", ".ir")
                         if path.name.endswith(role)), None)
            if role is None or role in files:
                raise ValueError(f"Unexpected artifact role for {name}")
            with path.open("rb") as stream:
                files[role] = hashlib.file_digest(stream, "sha256").hexdigest()
        if ".olean" not in files:
            raise ValueError(f"Missing main artifact for {name}")
        result[name] = files
    if not result:
        raise ValueError("Empty loaded module set")
    return result


def identity():
    return {key: os.environ[key] for key in ("GITHUB_SHA", "GITHUB_RUN_ID")}


def audit_receipt(log, labels):
    data = records(log)
    approvals = [row for row in data if row.get("phase") == "exactCoverage"]
    if (len(approvals) != 1 or approvals[0]["result"] != "PASS"
            or not approvals[0]["required"] or approvals[0]["required"] != approvals[0]["matched"]):
        raise ValueError("The exact whole-environment declaration audit did not pass")
    files = [row for row in data if row.get("phase") == "artifacts"]
    if [row["label"] for row in files] != labels:
        raise ValueError("Exact coverage omitted or duplicated a replay shard")
    return {"identity": identity(), "audit": {row["label"]: snapshot(row) for row in files}}


def replay_receipt(log, expected_shard, loaded_modules):
    files = [row for row in records(log) if row.get("phase") == "artifacts"]
    if (len(files) != 1 or files[0]["label"] != expected_shard
            or [row["module"] for row in files[0]["modules"]] != loaded_modules):
        raise ValueError("Replay's measured files do not match the actual imported module set")
    return {"identity": identity(), "shard": expected_shard, "artifacts": snapshot(files[0])}


def gate(matrix, evidence):
    labels = [row["shard"] for row in matrix["include"] if row["phase"] == "replay"]
    if not labels or len(labels) != len(set(labels)):
        raise ValueError("Invalid replay matrix")
    proof_labels = [row["shard"] for row in matrix["include"] if row["phase"] == "proof"]
    if proof_labels != ["all"] or len(matrix["include"]) != len(labels) + 1:
        raise ValueError("Full proof job missing from replay matrix")
    evidence = list(evidence)
    audits = [row for row in evidence if "audit" in row]
    shards = [row for row in evidence if "shard" in row]
    if len(audits) != 1 or len(shards) != len(labels) or len(evidence) != len(labels) + 1:
        raise ValueError("Coverage evidence is absent, duplicated, or unexpected")
    if any(row.get("identity") != identity() for row in evidence):
        raise ValueError("Coverage evidence belongs to a different commit or workflow run")
    if sorted(row["shard"] for row in shards) != sorted(labels) or sorted(audits[0]["audit"]) != sorted(labels):
        raise ValueError("Coverage evidence does not match required shards")
    for row in shards:
        if row["artifacts"] != audits[0]["audit"][row["shard"]]:
            raise ValueError("Replayed imports differ from exactly audited artifacts: " + row["shard"])


if __name__ == "__main__":
    config = json.loads(Path(sys.argv[1]).read_text())
    if "replayClosureLimit" in config:
        gate(json.loads(sys.argv[2]),
             (json.loads(p.read_text()) for p in Path(sys.argv[3]).rglob("exact-replay.json")))
        print("PASS: every required replay shard used exactly audited compiled inputs")
