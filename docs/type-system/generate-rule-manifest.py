#!/usr/bin/env python3
"""Generate the type-system rule manifest from normative Markdown rule annotations."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / "rule-manifest.json"
ANNOTATIONS = ROOT / "rule-annotations.json"
RULE = re.compile(r"\b[A-Z]{2,4}(?:-[A-Z0-9]+)+-[0-9]{3}[a-z]?\b")


def is_definition(line: str, rule_id: str, in_fence: bool) -> bool:
    stripped = line.strip()
    if stripped.startswith(f"`{rule_id}`:"):
        return True
    if in_fence and (stripped.endswith(rule_id) or stripped.startswith(f"{rule_id}:")):
        return True
    return False


def main() -> None:
    annotation_document = json.loads(ANNOTATIONS.read_text(encoding="utf-8"))
    annotations = annotation_document.get("rules", {})
    records: dict[str, dict[str, object]] = {}
    for path in sorted(ROOT.glob("*.md")):
        in_fence = False
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if line.strip().startswith("```"):
                in_fence = not in_fence
            for match in RULE.finditer(line):
                rule_id = match.group(0)
                record = records.setdefault(rule_id, {"id": rule_id, "locations": []})
                locations = record["locations"]
                assert isinstance(locations, list)
                locations.append(
                    {
                        "file": path.name,
                        "line": line_number,
                        "definition": is_definition(line, rule_id, in_fence),
                    }
                )

    rules = []
    unknown_annotations = sorted(set(annotations) - set(records))
    if unknown_annotations:
        raise ValueError(f"annotations for unknown rules: {unknown_annotations}")
    for rule_id in sorted(records):
        record = records[rule_id]
        locations = record["locations"]
        assert isinstance(locations, list)
        definitions = [location for location in locations if location["definition"]]
        primary = definitions[0] if definitions else locations[0]
        annotation = annotations.get(rule_id, {})
        rules.append(
            {
                "id": rule_id,
                "title": annotation.get("title", rule_id),
                "primary": {"file": primary["file"], "line": primary["line"]},
                "definitionCount": len(definitions),
                "implementation": annotation.get("implementation", []),
                "tests": annotation.get("tests", []),
                "status": annotation.get("status", "Proposed"),
                "compatibility": annotation.get("compatibility", "Unclassified"),
                "references": [
                    {"file": location["file"], "line": location["line"]}
                    for location in locations
                ],
            }
        )

    manifest = {
        "schemaVersion": 1,
        "sourcePattern": "docs/type-system/*.md",
        "rules": rules,
    }
    # Canonical documentation artifacts use LF even when this generator runs through Windows
    # Python. Otherwise a Windows checkout rewrites every JSON line with CRLF, and
    # `git diff --check` reports each carriage return as trailing whitespace.
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    main()
