#!/usr/bin/env python3
"""Validate trusted GitHub CI reports and publish/promote opaque cache outputs.

This script is checked out from the publishing workflow's trusted revision.
GitHub supplies identities; runner artifacts supply data. No candidate code runs.
"""
from __future__ import annotations

import argparse
import contextlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


prep = module("rh_ci_prepare", "ci-prepare.py")
pub = module("rh_ci_publisher", "publish-ci-cache.py")
REPOSITORY = "leanprover-community/riemann-hypothesis"
WORKFLOW = ".github/workflows/build-pr.yml"
IMPLEMENTATION_BRANCH = "infrastructure/byo-build-ci"
TITLE = re.compile(r"Build PR #([1-9][0-9]*) ([0-9a-f]{40}|manual)\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")


def read_json(path):
    return pub.decode_json(pub.regular_bytes(Path(path), 2 * 1024 * 1024))


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(pub.canonical(value) + b"\n")


def outputs(**values):
    path = os.environ.get("GITHUB_OUTPUT")
    if path:
        with open(path, "a") as stream:
            for key, value in values.items():
                if not re.fullmatch(r"[a-z_]+", key) or "\n" in str(value):
                    raise ValueError("Invalid workflow output")
                stream.write(f"{key}={str(value).lower() if isinstance(value, bool) else value}\n")
    print(json.dumps(values, sort_keys=True))


def envelope(event: dict, run: dict, jobs: dict, workflow: dict, *, allow_implementation=False) -> tuple[int, str]:
    embedded = event.get("workflow_run", {})
    if (event.get("repository", {}).get("full_name") != REPOSITORY
            or run.get("repository", {}).get("full_name") != REPOSITORY):
        raise ValueError("Workflow run belongs to a different repository")
    if (type(embedded.get("id")) is not int or embedded["id"] != run.get("id")
            or type(run.get("run_attempt")) is not int or run["run_attempt"] < 1
            or embedded.get("run_attempt") != run["run_attempt"]):
        raise ValueError("Workflow run identity/attempt changed")
    # REST run.name can be the dynamic run-name, rather than the definition's
    # name. Bind the independent workflow resource by numeric ID and path.
    workflow_id = run.get("workflow_id")
    if (type(workflow_id) is not int or workflow_id <= 0
            or embedded.get("workflow_id") != workflow_id or workflow.get("id") != workflow_id
            or workflow.get("name") != "Build PR" or workflow.get("path") != WORKFLOW
            or run.get("path") != WORKFLOW
            or ("path" in embedded and embedded["path"] != WORKFLOW)
            or run.get("event") not in ("pull_request_target", "workflow_dispatch")):
        raise ValueError("Only the trusted Build PR workflow can publish")
    reported_workflow = event.get("workflow")
    if reported_workflow is not None and (
            not isinstance(reported_workflow, dict)
            or any(reported_workflow.get(key) != workflow[key] for key in ("id", "name", "path"))):
        raise ValueError("Webhook workflow definition differs from the authoritative API identity")
    if run.get("status") != "completed" or run.get("conclusion") not in ("success", "failure"):
        raise ValueError("Cancelled, incomplete or otherwise interrupted runs do not publish")
    if run["event"] == "workflow_dispatch":
        allowed = {"main"}
        if allow_implementation:
            allowed.add(IMPLEMENTATION_BRANCH)
        if run.get("head_branch") not in allowed:
            raise ValueError("Manual build did not use an allowed trusted workflow branch")
    # For pull_request_target the REST head_branch is the PR branch, even though
    # GitHub executes the base's workflow. Check the PR target separately below.
    match = TITLE.fullmatch(run.get("display_title", ""))
    if not match:
        raise ValueError("Build PR run title does not bind a PR number and head")
    rows = jobs.get("jobs")
    if (not isinstance(rows, list) or not rows or jobs.get("total_count") != len(rows)
            or any(row.get("status") != "completed" or row.get("conclusion") in ("cancelled", "timed_out", "action_required") for row in rows)):
        raise ValueError("Run has cancelled, incomplete or unobserved jobs")
    return int(match[1]), match[2]


def live_run(event, *, allow_implementation=False):
    embedded = event.get("workflow_run", {})
    run_id = embedded.get("id")
    if type(run_id) is not int or run_id <= 0:
        raise ValueError("Invalid workflow run ID")
    run = prep.api(f"actions/runs/{run_id}")
    attempt = run.get("run_attempt")
    if type(attempt) is not int or attempt <= 0:
        raise ValueError("Invalid workflow run attempt")
    workflow_id = run.get("workflow_id")
    if type(workflow_id) is not int or workflow_id <= 0:
        raise ValueError("Invalid workflow definition ID")
    workflow = prep.api(f"actions/workflows/{workflow_id}")
    jobs = prep.api(f"actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100")
    number, head = envelope(event, run, jobs, workflow, allow_implementation=allow_implementation)
    return run, number, head


def prepare_event(args):
    event = read_json(args.event_file)
    if (os.environ.get("GITHUB_REPOSITORY") != REPOSITORY
            or event.get("repository", {}).get("full_name") != REPOSITORY):
        raise ValueError("Publishing event belongs to a different repository")
    kind = os.environ.get("GITHUB_EVENT_NAME")
    if kind == "workflow_dispatch":
        if os.environ.get("GITHUB_REF") != "refs/heads/main":
            raise ValueError("Manual publication retries must use the trusted main workflow")
        value = event.get("inputs", {}).get("build_run_id", "")
        if not isinstance(value, str) or not re.fullmatch(r"[1-9][0-9]{0,19}", value):
            raise ValueError("build_run_id must be a positive numeric GitHub run ID")
        run = prep.api(f"actions/runs/{int(value)}")
        if run.get("id") != int(value):
            raise ValueError("GitHub returned a different build run")
        event = {"repository": {"full_name": REPOSITORY}, "workflow_run": run}
    elif kind != "workflow_run":
        raise ValueError("Expected a completed build event or a manual publication retry")
    # Both paths subsequently pass the identical live workflow/run/jobs checks.
    write_json(args.output, event)


def inspect(args):
    event = read_json(args.event_file)
    run, _, _ = live_run(event, allow_implementation=args.allow_implementation_branch)
    artifacts = prep.api(f"actions/runs/{run['id']}/artifacts?per_page=100")
    rows = artifacts.get("artifacts")
    if not isinstance(rows, list) or artifacts.get("total_count") != len(rows):
        raise ValueError("Incomplete run artifact inventory")
    selected = {}
    for row in rows:
        if row.get("name") not in ("ci-input", "ci-request", "ci-cache"):
            continue
        name = row["name"]
        if name in selected or row.get("expired") is not False or type(row.get("size_in_bytes")) is not int:
            raise ValueError("Ambiguous or expired CI artifact")
        limit = 8 * 1024 ** 3 if name == "ci-cache" else 2 * 1024 ** 2
        if not 0 < row["size_in_bytes"] <= limit:
            raise ValueError("CI artifact exceeds its expected bound")
        selected[name] = row
    outputs(ready="ci-input" in selected, has_build={"ci-request", "ci-cache"} <= selected.keys(), run_id=run["id"])


def bind_manual_resolve_log(run, request, identity):
    """Preserve old-head work only when the immutable hosted resolve log binds it."""
    jobs = prep.api(f"actions/runs/{run['id']}/attempts/{run['run_attempt']}/jobs?per_page=100")
    rows = jobs.get("jobs", [])
    selected = [job for job in rows if job.get("name") == "resolve"]
    if jobs.get("total_count") != len(rows) or len(selected) != 1:
        raise ValueError("Cannot identify the original hosted resolve job")
    job = selected[0]
    # GitHub-hosted REST jobs report either null or integer zero for this ID.
    group_id = job.get("runner_group_id", -1)
    if (job.get("status") != "completed" or job.get("conclusion") != "success"
            or not (group_id is None or type(group_id) is int and group_id == 0)
            or job.get("runner_group_name") != "GitHub Actions"
            or "self-hosted" in job.get("labels", []) or type(job.get("id")) is not int or job["id"] <= 0):
        raise ValueError("Original resolve job was not a successful GitHub-hosted job")
    with tempfile.TemporaryDirectory(prefix="rh-ci-resolve-log-") as name:
        path = Path(name) / "resolve.log"
        with path.open("wb") as output:
            subprocess.run(["gh", "run", "view", str(run["id"]), "--repo", REPOSITORY,
                            "--job", str(job["id"]), "--log"], check=True, stdout=output, stderr=subprocess.PIPE, timeout=120)
        log = pub.regular_bytes(path, 2 * 1024 * 1024).decode("utf-8")
    records = []
    for line in log.splitlines():
        start = line.find("{")
        if start < 0:
            continue
        try:
            record = pub.decode_json(line[start:].encode())
        except (ValueError, UnicodeError):
            continue
        if isinstance(record, dict) and set(record) == {"candidate", "pr_head", "fingerprint", "reuse_from"}:
            records.append(record)
    expected = {"candidate": identity["candidate_head"], "pr_head": request["pr_head"],
                "fingerprint": identity["input_fingerprint"], "reuse_from": request.get("reuse_from", "")}
    if records != [expected]:
        raise ValueError("Manual request does not match its original hosted resolve log")


def validated_request(event, request, *, allow_implementation=False):
    run, number, title_head = live_run(event, allow_implementation=allow_implementation)
    allowed = {"repository", "run_id", "pr_number", "pr_head", "expected", "reuse_from"}
    if (not isinstance(request, dict) or set(request) - allowed
            or request.get("repository") != REPOSITORY or type(request.get("run_id")) is not int
            or request["run_id"] != run["id"] or type(request.get("pr_number")) is not int
            or request["pr_number"] != number or not isinstance(request.get("pr_head"), str)
            or not SHA.fullmatch(request["pr_head"])):
        raise ValueError("CI request does not match its trusted workflow run")
    if title_head != "manual" and request["pr_head"] != title_head:
        raise ValueError("CI request head differs from the workflow run title")
    pr = prep.api(f"pulls/{number}")
    if (pr.get("number") != number or pr.get("base", {}).get("repo", {}).get("full_name") != REPOSITORY
            or pr.get("base", {}).get("ref") != "main"):
        raise ValueError("PR does not target this repository's main branch")
    identity = pub.expected_metadata(request.get("expected"), promotion=True)
    actual = prep.identity(identity["candidate_head"], allow_historical=True)
    if pub.canonical(identity) != pub.canonical(pub.expected_metadata(actual, promotion=True)):
        raise ValueError("Candidate source/configuration identity differs from GitHub")
    commit = prep.api("git/commits/" + identity["candidate_head"])
    if request["pr_head"] not in [parent.get("sha") for parent in commit.get("parents", [])]:
        raise ValueError("Candidate is not a merge containing the requested PR head")
    reuse = request.get("reuse_from", "")
    if not isinstance(reuse, str) or reuse and not SHA.fullmatch(reuse):
        raise ValueError("Invalid successful-cache source revision")
    if title_head == "manual" and request["pr_head"] != pr.get("head", {}).get("sha"):
        bind_manual_resolve_log(run, request, identity)
    return request, identity, run


def validate_input(args):
    directory = Path(args.input_dir)
    if directory.is_symlink() or {path.name for path in directory.iterdir()} != {"request.json"}:
        raise ValueError("ci-input must contain only request.json")
    request, identity, run = validated_request(read_json(args.event_file), read_json(directory / "request.json"),
                                              allow_implementation=args.allow_implementation_branch)
    mode = "reuse" if request.get("reuse_from") else "build"
    state = dict(mode=mode, run_id=run["id"], run_attempt=run["run_attempt"], conclusion=run["conclusion"])
    target = Path(args.output)
    write_json(target / "request.json", request)
    write_json(target / "expected.json", identity)
    write_json(target / "state.json", state)
    outputs(mode=mode, candidate_head=identity["candidate_head"])


def validate_build(args):
    validated = Path(args.validated)
    request = read_json(validated / "request.json")
    state = read_json(validated / "state.json")
    if state.get("mode") != "build":
        raise ValueError("A cache-hit run cannot supply new build outputs")
    directory = Path(args.request_dir)
    if directory.is_symlink() or {path.name for path in directory.iterdir()} != {"request.json", "expected.json"}:
        raise ValueError("ci-request must contain only request.json and expected.json")
    if read_json(directory / "request.json") != request:
        raise ValueError("Build request differs from the independently uploaded CI input")
    expected = pub.expected_metadata(read_json(directory / "expected.json"))
    identity = read_json(validated / "expected.json")
    baseline = prep.settings.for_toolchain(expected["toolchain"])
    if (any(expected[key] != identity[key] for key in (*pub.IDENTITY, "input_fingerprint"))
            or expected["pr_head"] != request["pr_head"] or expected["pr_number"] != request["pr_number"]
            or expected["base_revision"] != baseline.REVISION or expected["base_map_sha256"] != baseline.MAP_SHA):
        raise ValueError("Build output metadata differs from trusted GitHub/pinned baseline identity")
    if state["conclusion"] == "success" and expected["build_exit_code"] != 0:
        raise ValueError("A successful workflow cannot report a failed build")
    write_json(validated / "expected.json", expected)
    state["build_validated"] = True
    write_json(validated / "state.json", state)
    outputs(build_validated=True)


@contextlib.contextmanager
def token_file():
    token = os.environ.pop("R2_ACCOUNT_TOKEN", "")
    if not token or any(character.isspace() for character in token):
        raise ValueError("Publishing requires the private R2_ACCOUNT_TOKEN environment secret")
    with tempfile.TemporaryDirectory(prefix="rh-ci-publish-auth-") as name:
        path = Path(name) / "token"
        descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
        with os.fdopen(descriptor, "w") as output:
            output.write(token)
        token = ""
        yield path


def verify_maps(store, revisions):
    for revision in revisions:
        current = store.get(pub.map_key(revision))
        if current is None:
            raise ValueError("Published revision map is missing")
        pub.transport.verify_public(pub.transport.PUBLIC_BASE_URL + "/" + pub.map_key(revision), current.data)


def catch_up_main(store, source):
    """A quick merge may precede workflow_run publication; fill that alias now."""
    current = store.get(f"ci/revisions/{source}.json")
    if current is None or pub.decode_json(current.data).get("build_exit_code") != 0:
        return
    expected = pub.expected_metadata(prep.identity("main"), promotion=True)
    if expected["candidate_head"] == source or matching_record(current.data, expected) is None:
        return
    result = pub.promote(store, expected, source)
    verify_maps(store, {expected["candidate_head"]})
    print(json.dumps({"caught_up_main_alias": result}, sort_keys=True))


def empty_failed_build(cache, expected):
    """An early failed build can have a valid header but no completed modules."""
    if cache.is_symlink() or not cache.is_dir():
        raise ValueError("Downloaded CI cache must be an ordinary directory")
    lines = pub.regular_bytes(cache / "outputs.jsonl").splitlines()
    if len(lines) != 1 or pub.decode_json(lines[0]) != pub.transport.SCHEMA:
        return False
    if type(expected.get("build_exit_code")) is not int or expected["build_exit_code"] == 0:
        raise ValueError("A successful build cannot publish an empty output map")
    return True


def publish(args):
    directory = Path(args.validated)
    request, state = read_json(directory / "request.json"), read_json(directory / "state.json")
    expected = read_json(directory / "expected.json")
    pub.select_toolchain(expected["toolchain"])
    run = prep.api(f"actions/runs/{state['run_id']}")
    if run.get("run_attempt") != state["run_attempt"] or run.get("status") != "completed":
        raise ValueError("Workflow was rerun before publication")
    cache = Path(args.cache_dir).absolute()
    if state["mode"] == "build" and state.get("build_validated") is True and empty_failed_build(cache, expected):
        outputs(published=False, reason="Failed build completed no modules; no cache writes needed")
        return
    with token_file() as credential:
        if state["mode"] == "build" and state.get("build_validated") is True:
            if cache.is_symlink() or not cache.is_dir():
                raise ValueError("Downloaded CI cache must be an ordinary directory")
            # Artifact ZIPs omit empty directories when the logical delta is zero.
            try:
                (cache / "artifacts").lstat()
            except FileNotFoundError:
                (cache / "artifacts").mkdir(mode=0o700)
            subprocess.run([sys.executable, str(Path(__file__).with_name("publish-ci-cache.py")), "publish", str(cache),
                            "--expected", str((directory / "expected.json").absolute()), "--token-file", str(credential)], check=True)
            with tempfile.TemporaryDirectory(prefix="rh-ci-main-catchup-") as name:
                catch_up_main(pub.S3Store(Path(name), credential), expected["candidate_head"])
        elif state["mode"] == "reuse":
            expected = pub.expected_metadata(expected, promotion=True)
            with tempfile.TemporaryDirectory(prefix="rh-ci-cache-reuse-") as name:
                store = pub.S3Store(Path(name), credential)
                result = pub.promote(store, expected, request["reuse_from"])
                if request["pr_head"] != expected["candidate_head"]:
                    index = pub.decode_json(store.get(f"ci/revisions/{expected['candidate_head']}.json").data)
                    value = store.get(index["map_key"])
                    pub.update_map(store, request["pr_head"], value.data, index, alias=True)
                verify_maps(store, {expected["candidate_head"], request["pr_head"]})
                catch_up_main(store, expected["candidate_head"])
                print(json.dumps({"reused_successful_build": result, "pr_head_alias": request["pr_head"]}))
        else:
            raise ValueError("Publishing state was not validated")


def matching_record(data, expected):
    if data is None:
        return None
    record = pub.decode_json(data)
    if (not isinstance(record, dict) or record.get("schema") != 1
            or record.get("repository") != REPOSITORY or record.get("build_exit_code") != 0
            or record.get("input_fingerprint") != expected["input_fingerprint"]
            or any(record.get(key) != expected[key] for key in pub.FINGERPRINT)
            or not isinstance(record.get("candidate_head"), str) or not SHA.fullmatch(record["candidate_head"])):
        return None
    return record


def promote_main(args):
    event = read_json(args.event_file)
    revision = event.get("after", "")
    if (event.get("repository", {}).get("full_name") != REPOSITORY or event.get("ref") != "refs/heads/main"
            or event.get("deleted") is not False or not isinstance(revision, str) or not SHA.fullmatch(revision)):
        raise ValueError("Promotion requires an actual main-branch push")
    expected = pub.expected_metadata(prep.identity(revision), promotion=True)
    associated = prep.api(f"commits/{revision}/pulls?per_page=100")
    if not isinstance(associated, list):
        raise ValueError("Invalid associated-PR response")
    candidates = []
    for pr in associated:
        head = pr.get("head", {}).get("sha", "")
        if (pr.get("merged_at") and pr.get("base", {}).get("repo", {}).get("full_name") == REPOSITORY
                and isinstance(head, str) and SHA.fullmatch(head)):
            candidates.append(f"ci/revisions/{head}.json")
    candidates.append(f"ci/inputs/{expected['input_fingerprint']}.json")
    record = None
    for key in dict.fromkeys(candidates):
        record = matching_record(prep.get(prep.BASE + "/" + key, missing=True, maximum=2 * 1024 * 1024), expected)
        if record:
            break
    if record is None:
        outputs(promoted=False, reason="No successful cache has matching main build inputs; no build was started")
        return
    with token_file() as credential, tempfile.TemporaryDirectory(prefix="rh-ci-cache-promote-") as name:
        store = pub.S3Store(Path(name), credential)
        result = pub.promote(store, expected, record["candidate_head"])
        verify_maps(store, {revision})
        print(json.dumps(result, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("prepare-event")
    command.add_argument("--event-file", required=True)
    command.add_argument("--output", required=True)
    command.set_defaults(function=prepare_event)
    command = commands.add_parser("inspect-run")
    command.add_argument("--event-file", required=True)
    command.add_argument("--allow-implementation-branch", action="store_true")
    command.set_defaults(function=inspect)
    command = commands.add_parser("validate-input")
    for name in ("event-file", "input-dir", "output"):
        command.add_argument("--" + name, required=True)
    command.add_argument("--allow-implementation-branch", action="store_true")
    command.set_defaults(function=validate_input)
    command = commands.add_parser("validate-build")
    command.add_argument("--validated", required=True)
    command.add_argument("--request-dir", required=True)
    command.set_defaults(function=validate_build)
    command = commands.add_parser("publish")
    command.add_argument("--validated", required=True)
    command.add_argument("--cache-dir", required=True)
    command.set_defaults(function=publish)
    command = commands.add_parser("promote-main")
    command.add_argument("--event-file", required=True)
    command.set_defaults(function=promote_main)
    args = parser.parse_args()
    args.function(args)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        raise SystemExit(f"CI cache publication refused: {error}")
