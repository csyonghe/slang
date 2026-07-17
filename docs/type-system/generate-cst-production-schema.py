#!/usr/bin/env python3
"""Generate and validate named CST production fields from the paired EBNF/profile."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent
PROFILE_PATH = ROOT / "cst-production-profile.json"


class GrammarError(ValueError):
    """Report a malformed grammar or an incomplete CST field profile."""


class _WireTags:
    """Derive stable non-zero UInt32 tags and reject every domain-local collision."""

    def __init__(self, profile: dict[str, Any]):
        config = profile["wireTags"]
        if config["algorithm"] != "sha256-domain-prefix-u32be-v1":
            raise GrammarError(f"unknown wire-tag algorithm {config['algorithm']!r}")
        if config["collisionRule"] != "reject":
            raise GrammarError("wire-tag collisions must be rejected")
        self.namespace = config["namespace"]
        self.reserved = set(config.get("reserved", []))
        self.overrides = config.get("overrides", {})
        self.used: dict[str, dict[int, str]] = defaultdict(dict)
        self.used_overrides: set[tuple[str, str]] = set()

    def get(self, domain: str, stable_key: str) -> int:
        """Return an override or the SHA-256 prefix for one stable semantic key."""

        override_domain = self.overrides.get(domain, {})
        if stable_key in override_domain:
            tag = override_domain[stable_key]
            self.used_overrides.add((domain, stable_key))
        else:
            encoded = f"{self.namespace}\0{domain}\0{stable_key}".encode("utf-8")
            tag = int.from_bytes(hashlib.sha256(encoded).digest()[:4], "big")
        if not isinstance(tag, int) or not 0 <= tag <= 0xFFFFFFFF:
            raise GrammarError(f"wire tag for {domain}:{stable_key} is not UInt32")
        if tag in self.reserved:
            raise GrammarError(f"wire tag for {domain}:{stable_key} is reserved: {tag}")
        previous = self.used[domain].get(tag)
        if previous is not None and previous != stable_key:
            raise GrammarError(
                f"wire-tag collision in {domain}: {previous!r} and {stable_key!r} -> {tag}"
            )
        self.used[domain][tag] = stable_key
        return tag

    def finish(self) -> None:
        """Reject a misspelled or obsolete explicit override instead of silently ignoring it."""

        known_domains = {"nodeKinds", "fields", "groups", "alternatives"}
        unknown_domains = set(self.overrides) - known_domains
        if unknown_domains:
            raise GrammarError(f"unknown wire-tag override domains: {sorted(unknown_domains)}")
        declared = {
            (domain, key)
            for domain, entries in self.overrides.items()
            for key in entries
        }
        unused = declared - self.used_overrides
        if unused:
            raise GrammarError(f"unused wire-tag overrides: {sorted(unused)}")


def _tokenize(text: str) -> list[tuple[str, str, int]]:
    """Tokenize the deliberately small EBNF dialect used by grammar.ebnf."""

    result: list[tuple[str, str, int]] = []
    index = 0
    while index < len(text):
        if text[index].isspace():
            index += 1
            continue
        if text.startswith("(*", index):
            end = text.find("*)", index + 2)
            if end < 0:
                raise GrammarError(f"unterminated EBNF comment at byte {index}")
            index = end + 2
            continue
        if text[index] == '"':
            end = index + 1
            while end < len(text):
                if text[end] == "\\":
                    end += 2
                elif text[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
            else:
                raise GrammarError(f"unterminated string literal at byte {index}")
            spelling = text[index:end]
            result.append(("string", json.loads(spelling), index))
            index = end
            continue
        identifier = re.match(r"[A-Za-z_][A-Za-z0-9_-]*", text[index:])
        if identifier:
            spelling = identifier.group(0)
            result.append(("identifier", spelling, index))
            index += len(spelling)
            continue
        if text[index] == "<":
            end = text.find(">", index + 1)
            if end < 0:
                raise GrammarError(f"unterminated EBNF predicate at byte {index}")
            result.append(("predicate", text[index + 1 : end].strip(), index))
            index = end + 1
            continue
        if text[index] in "=;,|{}[]()+-":
            result.append((text[index], text[index], index))
            index += 1
            continue
        raise GrammarError(f"unexpected EBNF character {text[index]!r} at byte {index}")
    result.append(("eof", "", len(text)))
    return result


class _Parser:
    """Parse EBNF into a structural expression tree without assigning CST field names."""

    def __init__(self, text: str):
        self.tokens = _tokenize(text)
        self.index = 0

    def _peek(self, kind: str | None = None) -> tuple[str, str, int]:
        token = self.tokens[self.index]
        if kind is not None and token[0] != kind:
            raise GrammarError(
                f"expected {kind!r} at byte {token[2]}, found {token[0]!r}"
            )
        return token

    def _take(self, kind: str) -> tuple[str, str, int]:
        token = self._peek(kind)
        self.index += 1
        return token

    def _accept(self, kind: str) -> bool:
        if self._peek()[0] != kind:
            return False
        self.index += 1
        return True

    def parse(self) -> dict[str, dict[str, Any]]:
        productions: dict[str, dict[str, Any]] = {}
        while self._peek()[0] != "eof":
            name = self._take("identifier")[1]
            if name in productions:
                raise GrammarError(f"duplicate production {name!r}")
            self._take("=")
            productions[name] = self._choice({";"})
            self._take(";")
        return productions

    def _choice(self, stops: set[str]) -> dict[str, Any]:
        alternatives = [self._sequence(stops | {"|"})]
        while self._accept("|"):
            alternatives.append(self._sequence(stops | {"|"}))
        if len(alternatives) == 1:
            return alternatives[0]
        return {"kind": "choice", "children": alternatives}

    def _sequence(self, stops: set[str]) -> dict[str, Any]:
        if self._peek()[0] in stops:
            raise GrammarError(f"empty EBNF sequence at byte {self._peek()[2]}")
        children = [self._item()]
        while self._accept(","):
            children.append(self._item())
        if self._peek()[0] not in stops:
            token = self._peek()
            raise GrammarError(
                f"expected EBNF comma or group end at byte {token[2]}, found {token[1]!r}"
            )
        if len(children) == 1:
            return children[0]
        return {"kind": "sequence", "children": children}

    def _item(self) -> dict[str, Any]:
        token = self._peek()
        if token[0] == "identifier":
            symbol = self._take("identifier")[1]
            if symbol == "SOFT":
                self._take("(")
                spelling = self._take("string")[1]
                self._take(")")
                node: dict[str, Any] = {
                    "kind": "leaf",
                    "leafKind": "soft",
                    "symbol": spelling,
                }
            else:
                node = {
                    "kind": "leaf",
                    "leafKind": "token" if symbol.upper() == symbol else "nonterminal",
                    "symbol": symbol,
                }
        elif token[0] == "string":
            node = {
                "kind": "leaf",
                "leafKind": "literal",
                "symbol": self._take("string")[1],
            }
        elif token[0] in {"(", "[", "{"}:
            opener = self._take(token[0])[0]
            closer = {"(": ")", "[": "]", "{": "}"}[opener]
            child = self._choice({closer})
            self._take(closer)
            node = {
                "kind": {"(": "group", "[": "optional", "{": "repeat"}[opener],
                "child": child,
            }
        elif token[0] == "predicate":
            node = {
                "kind": "predicate",
                "text": self._take("predicate")[1],
            }
        else:
            raise GrammarError(f"expected EBNF item at byte {token[2]}, found {token[1]!r}")
        if self._accept("-"):
            excluded = self._take("string")[1]
            node = {"kind": "difference", "child": node, "excluded": excluded}
        if self._accept("+"):
            node = {"kind": "oneOrMore", "child": node}
        return node


def _upper_camel(spelling: str) -> str:
    return "".join(part[:1].upper() + part[1:] for part in spelling.split("-") if part)


def _lower_camel_words(spelling: str) -> str:
    parts = [part for part in re.split(r"[^A-Za-z0-9]+", spelling.lstrip("_")) if part]
    if not parts:
        return "keyword"
    return parts[0].lower() + "".join(part[:1].upper() + part[1:] for part in parts[1:])


def _validate_schema_version(value: Any) -> dict[str, int]:
    """Validate the JSON spelling of chapter 3's SchemaVersion product."""

    if not isinstance(value, dict) or set(value) != {"major", "minor"}:
        raise GrammarError("schemaVersion must be exactly {major: UInt16, minor: UInt16}")
    for part in ("major", "minor"):
        if not isinstance(value[part], int) or not 0 <= value[part] <= 0xFFFF:
            raise GrammarError(f"schemaVersion.{part} is not UInt16")
    return value


def _production_id(
    production: str, schema_version: dict[str, int]
) -> dict[str, Any]:
    return {
        "grammarVersion": schema_version,
        "qualifiedName": f"slang.surface.{production}",
    }


def _production_kind(
    production: str,
    kind_name: str,
    tags: _WireTags,
) -> dict[str, Any]:
    stable_name = f"slang.cst.parsed.{kind_name}"
    return {
        "family": "NonTerminalNode",
        "wireTag": tags.get("nodeKinds", stable_name),
        "stableName": stable_name,
    }


def _field_name(production: str, name: str, tags: _WireTags) -> dict[str, Any]:
    stable_key = f"slang.surface.{production}.{name}"
    return {
        "text": name,
        "wireTag": tags.get("fields", stable_key),
    }


def _group_name(
    production: str,
    path: str,
    role: str,
    tags: _WireTags,
    include_field: bool = False,
    field_text: str | None = None,
) -> dict[str, Any]:
    stable_name = f"slang.surface.{production}.{path}.{role}"
    wire_tag = tags.get("groups", stable_name)
    result = {
        "stableName": stable_name,
        "wireTag": wire_tag,
    }
    if include_field:
        if field_text is None:
            raise GrammarError(f"stored group {stable_name} has no field name")
        result["field"] = {
            "name": _field_name(production, field_text, tags),
            "edge": "Structural",
            "stages": [{"concrete": "Parsed"}],
            "wire": "SerializedField",
            "access": "Editable",
        }
    return result


def _alternative_name(
    group: dict[str, Any],
    index: int,
    tags: _WireTags,
) -> dict[str, Any]:
    stable_name = f"{group['stableName']}.alternative.{index}"
    return {
        "stableName": stable_name,
        "wireTag": tags.get("alternatives", stable_name),
    }


def _enumerate_occurrences(
    production: str, expression: dict[str, Any]
) -> tuple[list[dict[str, Any]], dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    """Assign whitespace-independent paths and retain every choice/quantifier context."""

    occurrences: list[dict[str, Any]] = []
    choices: dict[str, dict[str, Any]] = {}
    quantifiers: dict[str, dict[str, Any]] = {}

    def visit(
        node: dict[str, Any],
        path: str,
        guards: list[dict[str, Any]],
        enclosing: list[dict[str, Any]],
    ) -> None:
        kind = node["kind"]
        if kind == "leaf":
            occurrences.append(
                {
                    "id": f"{production}#{path}",
                    "path": path,
                    "leafKind": node["leafKind"],
                    "symbol": node["symbol"],
                    "choiceGuards": list(guards),
                    "quantifiers": list(enclosing),
                    "sourceOrder": len(occurrences),
                }
            )
            return
        if kind == "predicate":
            return
        if kind == "sequence":
            for index, child in enumerate(node["children"]):
                visit(child, f"{path}/sequence/{index}", guards, enclosing)
            return
        if kind == "choice":
            group = f"{production}#{path}/choice"
            choices[group] = {"id": group, "alternativeCount": len(node["children"])}
            for index, child in enumerate(node["children"]):
                visit(
                    child,
                    f"{path}/choice/{index}",
                    guards + [{"group": group, "alternative": index}],
                    enclosing,
                )
            return
        if kind == "group":
            visit(node["child"], f"{path}/group", guards, enclosing)
            return
        if kind == "difference":
            visit(node["child"], f"{path}/difference", guards, enclosing)
            return
        if kind in {"optional", "repeat", "oneOrMore"}:
            group = f"{production}#{path}/{kind}"
            quantifiers[group] = {"id": group, "kind": kind}
            visit(
                node["child"],
                f"{path}/{kind}",
                guards,
                enclosing + [{"group": group, "kind": kind}],
            )
            return
        raise AssertionError(kind)

    visit(expression, "root", [], [])
    ordinal: Counter[tuple[str, str]] = Counter()
    for occurrence in occurrences:
        key = (occurrence["leafKind"], occurrence["symbol"])
        ordinal[key] += 1
        occurrence["selectorOrdinal"] = ordinal[key]
    return occurrences, choices, quantifiers


def _selector_matches(selector: dict[str, Any], occurrence: dict[str, Any]) -> bool:
    return (
        selector["kind"] == occurrence["leafKind"]
        and selector["symbol"] == occurrence["symbol"]
        and selector["ordinal"] == occurrence["selectorOrdinal"]
    )


def _are_exclusive(left: dict[str, Any], right: dict[str, Any]) -> bool:
    left_guards = {guard["group"]: guard["alternative"] for guard in left["choiceGuards"]}
    return any(
        group in left_guards and left_guards[group] != alternative
        for group, alternative in (
            (guard["group"], guard["alternative"]) for guard in right["choiceGuards"]
        )
    )


def _storage_type(base_type: str, quantifiers: list[dict[str, Any]]) -> str:
    result = base_type
    wrappers = {"optional": "Option", "repeat": "NodeList", "oneOrMore": "NonEmpty"}
    for quantifier in reversed(quantifiers):
        result = f"{wrappers[quantifier['kind']]}<{result}>"
    return result


def _default_base_name(occurrence: dict[str, Any], profile: dict[str, Any]) -> str:
    naming = profile["fieldNaming"]
    kind = occurrence["leafKind"]
    symbol = occurrence["symbol"]
    if kind == "soft":
        return _lower_camel_words(symbol) + "Keyword"
    if kind == "literal":
        try:
            return naming["literalRoles"][symbol]
        except KeyError as error:
            raise GrammarError(f"literal terminal {symbol!r} has no field role") from error
    if kind == "token":
        try:
            return naming["terminalRoles"][symbol]
        except KeyError as error:
            raise GrammarError(f"terminal kind {symbol!r} has no field role") from error
    return _lower_camel_words(symbol.replace("-", "_"))


def _default_base_type(occurrence: dict[str, Any]) -> str:
    if occurrence["leafKind"] != "nonterminal":
        return "TerminalNodeId<Parsed>"
    return f"NonTerminalNodeId<Parsed, Production({occurrence['symbol']})>"


def _make_field(
    name: str, base_type: str, occurrences: list[dict[str, Any]]
) -> dict[str, Any]:
    quantifiers = occurrences[0]["quantifiers"]
    if any(item["quantifiers"] != quantifiers for item in occurrences[1:]):
        raise GrammarError(f"field {name!r} merges occurrences with different cardinality")
    return {
        "name": name,
        "baseType": base_type,
        "effectiveType": _storage_type(base_type, quantifiers),
        "sourceOrder": min(item["sourceOrder"] for item in occurrences),
        "occurrences": [
            {
                "id": item["id"],
                "leafKind": item["leafKind"],
                "symbol": item["symbol"],
                "choiceGuards": item["choiceGuards"],
                "quantifiers": item["quantifiers"],
                "sourceOrder": item["sourceOrder"],
            }
            for item in occurrences
        ],
    }


def _node_kind_for_field_type(
    base_type: str,
    kind_overrides: dict[str, str],
    tags: _WireTags,
) -> dict[str, Any]:
    """Map a generated typed reference to the NodeKind constraint used on the wire."""

    if base_type == "TerminalNodeId<Parsed>":
        stable_name = "slang.cst.parsed.TerminalNode"
        return {
            "family": "TerminalNode",
            "wireTag": tags.get("nodeKinds", stable_name),
            "stableName": stable_name,
        }
    production = re.search(r"Production\(([^)]+)\)", base_type)
    if production:
        name = production.group(1)
        return _production_kind(
            name, kind_overrides.get(name, _upper_camel(name)), tags
        )
    category = {
        "ExprCSTNodeId<Parsed>": "ExprCSTCategory",
        "StmtCSTNodeId<Parsed>": "StmtCSTCategory",
        "DeclCSTNodeId<Parsed>": "DeclCSTCategory",
    }.get(base_type)
    if category is None:
        raise GrammarError(f"cannot compile CST field type {base_type!r} to NodeKindValue")
    return _category_kind(category, tags)


def _category_kind(category: str, tags: _WireTags) -> dict[str, Any]:
    """Return the abstract non-terminal base kind for one typed CST category."""

    stable_name = f"slang.cst.parsed.category.{category}"
    return {
        "family": "NonTerminalNode",
        "wireTag": tags.get("nodeKinds", stable_name),
        "stableName": stable_name,
    }


def _typed_reference(
    base_type: str, schema_version: dict[str, int]
) -> dict[str, Any]:
    """Emit the closed typed-reference alternative that the generated accessor exposes."""

    if base_type == "TerminalNodeId<Parsed>":
        return {"kind": "Terminal", "stage": "Parsed"}
    production = re.search(r"Production\(([^)]+)\)", base_type)
    if production:
        return {
            "kind": "Production",
            "stage": "Parsed",
            "production": _production_id(production.group(1), schema_version),
        }
    category = {
        "ExprCSTNodeId<Parsed>": "ExprCSTCategory",
        "StmtCSTNodeId<Parsed>": "StmtCSTCategory",
        "DeclCSTNodeId<Parsed>": "DeclCSTCategory",
    }.get(base_type)
    if category is None:
        raise GrammarError(f"unknown CST typed reference {base_type!r}")
    return {"kind": "Category", "stage": "Parsed", "category": category}


def _decorate_field(
    production: str,
    field: dict[str, Any],
    kind_overrides: dict[str, str],
    schema_version: dict[str, int],
    tags: _WireTags,
) -> dict[str, Any]:
    """Emit one occurrence-role descriptor with all generic schema policies explicit."""

    occurrences = []
    for occurrence in field["occurrences"]:
        variant_path = []
        for guard in occurrence["choiceGuards"]:
            path = guard["group"].split("#", 1)[1]
            group = _group_name(production, path, "choice", tags)
            variant_path.append(
                {
                    "group": group,
                    "alternative": _alternative_name(
                        group, guard["alternative"], tags
                    ),
                }
            )
        cardinality_path = []
        for quantifier in occurrence["quantifiers"]:
            path = quantifier["group"].split("#", 1)[1]
            cardinality_path.append(
                {
                    "group": _group_name(
                        production, path, quantifier["kind"], tags
                    ),
                    "kind": quantifier["kind"],
                }
            )
        occurrences.append(
            {
                "id": occurrence["id"],
                "leafKind": occurrence["leafKind"],
                "symbol": occurrence["symbol"],
                "sourceOrder": occurrence["sourceOrder"],
                "variantPath": variant_path,
                "cardinalityPath": cardinality_path,
            }
        )
    return {
        "name": _field_name(production, field["name"], tags),
        "valueKind": {
            "nodeKindValue": _node_kind_for_field_type(
                field["baseType"], kind_overrides, tags
            )
        },
        "typedReference": _typed_reference(field["baseType"], schema_version),
        "edge": "Structural",
        "stages": [{"concrete": "Parsed"}],
        "wire": "SerializedField",
        "access": "Editable",
        "sourceOrder": field["sourceOrder"],
        "occurrences": occurrences,
    }


def _assign_fields(
    production: str, occurrences: list[dict[str, Any]], profile: dict[str, Any]
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    """Assign every leaf exactly one field, applying explicit semantic overrides first."""

    override = profile.get("productionOverrides", {}).get(production)
    assignments: dict[str, str] = {}
    fields: list[dict[str, Any]] = []
    if override:
        for field_spec in override["fields"]:
            selected: list[dict[str, Any]] = []
            for selector in field_spec["select"]:
                matches = [item for item in occurrences if _selector_matches(selector, item)]
                if len(matches) != 1:
                    raise GrammarError(
                        f"{production}.{field_spec['name']}: selector {selector} matched "
                        f"{len(matches)} occurrence(s)"
                    )
                selected.extend(matches)
            if len({item["id"] for item in selected}) != len(selected):
                raise GrammarError(f"{production}.{field_spec['name']} selects an occurrence twice")
            if len(selected) > 1:
                if field_spec.get("merge") != "exclusiveAlternatives":
                    raise GrammarError(
                        f"{production}.{field_spec['name']} must declare exclusiveAlternatives"
                    )
                for index, left in enumerate(selected):
                    if any(not _are_exclusive(left, right) for right in selected[index + 1 :]):
                        raise GrammarError(
                            f"{production}.{field_spec['name']} merges non-exclusive occurrences"
                        )
            for item in selected:
                if item["id"] in assignments:
                    raise GrammarError(f"{item['id']} is assigned to two fields")
                assignments[item["id"]] = field_spec["name"]
            fields.append(_make_field(field_spec["name"], field_spec["baseType"], selected))
        if override.get("exact") and len(assignments) != len(occurrences):
            missing = [item["id"] for item in occurrences if item["id"] not in assignments]
            raise GrammarError(f"exact override for {production} omits {missing}")

    base_counts: Counter[str] = Counter()
    for item in occurrences:
        if item["id"] in assignments:
            continue
        base = _default_base_name(item, profile)
        base_counts[base] += 1
        name = base if base_counts[base] == 1 else f"{base}{base_counts[base]}"
        assignments[item["id"]] = name
        fields.append(_make_field(name, _default_base_type(item), [item]))

    names = [field["name"] for field in fields]
    if len(names) != len(set(names)):
        raise GrammarError(f"production {production} has duplicate field names: {names}")
    fields.sort(key=lambda field: field["sourceOrder"])
    return fields, assignments


def _render_shape(
    production: str,
    expression: dict[str, Any],
    assignments: dict[str, str],
    field_names: dict[str, dict[str, Any]],
    tags: _WireTags,
) -> dict[str, Any]:
    """Compile EBNF to a closed product/sum/cardinality algebra.

    In particular, a choice is one variant value rather than a collection of simultaneously
    required fields, and a repeated sequence is a list whose *element* is the sequence product.
    """

    group_field_counts: Counter[str] = Counter()

    def stored_group(path: str, role: str) -> dict[str, Any]:
        base = {
            "choice": "choiceAlternative",
            "optional": "optionalPart",
            "repeat": "repeatedElements",
            "oneOrMore": "nonEmptyElements",
        }[role]
        group_field_counts[base] += 1
        ordinal = group_field_counts[base]
        field_text = base if ordinal == 1 else f"{base}{ordinal}"
        return _group_name(
            production,
            path,
            role,
            tags,
            include_field=True,
            field_text=field_text,
        )

    def render(node: dict[str, Any], path: str) -> dict[str, Any]:
        kind = node["kind"]
        if kind == "leaf":
            occurrence = f"{production}#{path}"
            result = {
                "kind": "Field",
                "field": field_names[assignments[occurrence]],
                "occurrence": occurrence,
                "sort": "NonTerminal" if node["leafKind"] == "nonterminal" else "Terminal",
                "symbol": node["symbol"],
            }
            if node["leafKind"] != "nonterminal":
                result["terminalConstraint"] = {
                    "kind": node["leafKind"],
                    "symbol": node["symbol"],
                }
            return result
        if kind == "predicate":
            return {"kind": "SemanticPredicate", "rule": node["text"]}
        if kind == "sequence":
            return {
                "kind": "Product",
                "elements": [
                    render(child, f"{path}/sequence/{index}")
                    for index, child in enumerate(node["children"])
                ],
            }
        if kind == "choice":
            group = stored_group(f"{path}/choice", "choice")
            return {
                "kind": "ClosedVariant",
                "group": group,
                "alternatives": [
                    {
                        "tag": _alternative_name(group, index, tags),
                        "value": render(child, f"{path}/choice/{index}"),
                    }
                    for index, child in enumerate(node["children"])
                ],
            }
        if kind == "group":
            return render(node["child"], f"{path}/group")
        if kind == "difference":
            return {
                "kind": "Difference",
                "value": render(node["child"], f"{path}/difference"),
                "excludedTerminal": node["excluded"],
            }
        if kind in {"optional", "repeat", "oneOrMore"}:
            group = stored_group(f"{path}/{kind}", kind)
            value = render(node["child"], f"{path}/{kind}")
            if kind == "optional":
                return {"kind": "Optional", "group": group, "value": value}
            return {
                "kind": "List" if kind == "repeat" else "NonEmpty",
                "group": group,
                "element": value,
            }
        raise AssertionError(kind)

    return render(expression, "root")


def _exact_override_shape(
    production: str,
    fields: list[dict[str, Any]],
    field_names: dict[str, dict[str, Any]],
    tags: _WireTags,
) -> dict[str, Any]:
    """Compile a reviewed exact product override such as the requested IfStatement shape."""

    elements = []
    for field in fields:
        value: dict[str, Any] = {
            "kind": "Field",
            "field": field_names[field["name"]],
        }
        for quantifier in reversed(field["occurrences"][0]["quantifiers"]):
            wrapper = {
                "optional": "OptionalField",
                "repeat": "ListField",
                "oneOrMore": "NonEmptyField",
            }[quantifier["kind"]]
            group_path = quantifier["group"].split("#", 1)[1]
            value = {
                "kind": wrapper,
                "group": _group_name(
                    production, group_path, quantifier["kind"], tags
                ),
                "value" if wrapper == "OptionalField" else "element": value,
            }
        elements.append(value)
    return {"kind": "Product", "elements": elements}


def _validate_override_constraints(
    production: str,
    fields: list[dict[str, Any]],
    profile: dict[str, Any],
) -> list[dict[str, Any]]:
    override = profile.get("productionOverrides", {}).get(production, {})
    result = override.get("constraints", [])
    by_name = {field["name"]: field for field in fields}
    for constraint in result:
        if constraint["kind"] != "coPresent":
            raise GrammarError(f"unknown constraint kind {constraint['kind']!r}")
        try:
            selected = [by_name[name] for name in constraint["fields"]]
        except KeyError as error:
            raise GrammarError(f"constraint names unknown field {error.args[0]!r}") from error
        common: set[str] | None = None
        for field in selected:
            field_groups = {
                item["group"]
                for occurrence in field["occurrences"]
                for item in occurrence["quantifiers"]
                if item["kind"] == "optional"
            }
            common = field_groups if common is None else common & field_groups
        if not common:
            raise GrammarError(
                f"{production} coPresent fields do not share an optional EBNF group"
            )
    return result


def generate() -> dict[str, Any]:
    """Build the complete machine-readable production schema and enforce coverage laws."""

    profile = json.loads(PROFILE_PATH.read_text(encoding="utf-8"))
    schema_version = _validate_schema_version(profile["schemaVersion"])
    tags = _WireTags(profile)
    grammar_path = ROOT / profile["grammar"]
    # The grammar is textual schema input. Hash its canonical UTF-8/LF form so a checkout's
    # platform line-ending policy cannot masquerade as a language-schema change.
    grammar_text = grammar_path.read_text(encoding="utf-8")
    canonical_grammar_text = grammar_text.replace("\r\n", "\n").replace("\r", "\n")
    grammar_bytes = canonical_grammar_text.encode("utf-8")
    digest = hashlib.sha256(grammar_bytes).hexdigest()
    if digest != profile["grammarSha256"]:
        raise GrammarError(
            f"grammar digest changed: profile has {profile['grammarSha256']}, actual is {digest}"
        )
    productions = _Parser(canonical_grammar_text).parse()
    for expression in productions.values():
        occurrences, _, _ = _enumerate_occurrences("validation", expression)
        for occurrence in occurrences:
            if (
                occurrence["leafKind"] == "nonterminal"
                and occurrence["symbol"] not in productions
            ):
                raise GrammarError(f"unknown production reference {occurrence['symbol']!r}")

    kind_overrides = profile["productionKind"]["overrides"]
    generated = []
    production_map = []
    terminal_occurrence_count = 0
    nonterminal_occurrence_count = 0
    for production, expression in productions.items():
        occurrences, _, _ = _enumerate_occurrences(production, expression)
        fields, assignments = _assign_fields(production, occurrences, profile)
        if production == "if-statement":
            expected_if_fields = [
                ("ifKeyword", "TerminalNodeId<Parsed>"),
                ("leftParenthesis", "TerminalNodeId<Parsed>"),
                ("conditionExpr", "ExprCSTNodeId<Parsed>"),
                ("rightParenthesis", "TerminalNodeId<Parsed>"),
                ("trueBranch", "StmtCSTNodeId<Parsed>"),
                ("elseKeyword", "Option<TerminalNodeId<Parsed>>"),
                ("falseBranch", "Option<StmtCSTNodeId<Parsed>>"),
            ]
            actual_if_fields = [
                (field["name"], field["effectiveType"]) for field in fields
            ]
            if actual_if_fields != expected_if_fields:
                raise GrammarError(
                    f"IfStatement field contract changed: expected {expected_if_fields}, "
                    f"actual {actual_if_fields}"
                )
        node_kind_name = kind_overrides.get(production, _upper_camel(production))
        node_kind = _production_kind(production, node_kind_name, tags)
        production_id = _production_id(production, schema_version)
        decorated_fields = [
            _decorate_field(
                production, field, kind_overrides, schema_version, tags
            )
            for field in fields
        ]
        field_names = {
            field["name"]: decorated["name"]
            for field, decorated in zip(fields, decorated_fields)
        }
        override = profile.get("productionOverrides", {}).get(production, {})
        shape = (
            _exact_override_shape(production, fields, field_names, tags)
            if override.get("exact")
            else _render_shape(production, expression, assignments, field_names, tags)
        )
        constraints = _validate_override_constraints(production, fields, profile)
        compiled_constraints = [
            {
                "kind": "CoPresent",
                "fields": [field_names[name] for name in constraint["fields"]],
                "rule": "PAR-CST-COPRESENT",
            }
            for constraint in constraints
        ]
        generated.append(
            {
                "debugName": production,
                "production": production_id,
                "kind": node_kind,
                "fields": decorated_fields,
                "shape": shape,
                "constraints": compiled_constraints,
                "invariants": sorted(
                    {constraint["rule"] for constraint in compiled_constraints}
                ),
            }
        )
        production_map.append({"production": production_id, "kind": node_kind})
        terminal_occurrence_count += sum(
            item["leafKind"] != "nonterminal" for item in occurrences
        )
        nonterminal_occurrence_count += sum(
            item["leafKind"] == "nonterminal" for item in occurrences
        )

    # These are executable sentinels for the two easy-to-regress compilation laws. A choice must
    # never become a product with every alternative required, and a repeated delimiter/value pair
    # must never become parallel delimiter/value lists.
    by_name = {item["debugName"]: item for item in generated}
    if by_name["declaration"]["shape"]["kind"] != "ClosedVariant":
        raise GrammarError("root choice did not compile to ClosedVariant")
    dotted_shape = by_name["dotted-name"]["shape"]
    dotted_tail = dotted_shape["elements"][1]
    if not (
        dotted_tail["kind"] == "List"
        and dotted_tail["element"]["kind"] == "Product"
        and len(dotted_tail["element"]["elements"]) == 2
    ):
        raise GrammarError(
            "repeated dotted-name suffix did not compile to List<Product<dot, identifier>>"
        )
    if_shape = by_name["if-statement"]["shape"]
    if not (
        if_shape["kind"] == "Product"
        and [
            element.get("field", {}).get("text")
            if element["kind"] == "Field"
            else element.get("value", {}).get("field", {}).get("text")
            for element in if_shape["elements"]
        ]
        == [
            "ifKeyword",
            "leftParenthesis",
            "conditionExpr",
            "rightParenthesis",
            "trueBranch",
            "elseKeyword",
            "falseBranch",
        ]
    ):
        raise GrammarError("IfStatement compiled product no longer has the exact seven fields")
    category_descriptors = []
    for category, members in profile["categoryMembership"].items():
        if len(members) != len(set(members)):
            raise GrammarError(f"category {category} contains a duplicate production")
        for member in members:
            if member not in productions:
                raise GrammarError(f"category {category} names unknown production {member}")
        category_descriptors.append(
            {
                "category": category,
                "kind": _category_kind(category, tags),
                "members": [
                    _production_id(member, schema_version) for member in sorted(members)
                ],
            }
        )

    production_kind_names = [item["kind"]["stableName"] for item in generated]
    duplicate_kind_names = sorted(
        name for name, count in Counter(production_kind_names).items() if count != 1
    )
    if duplicate_kind_names:
        raise GrammarError(
            "grammar production kinds must be injective: "
            f"{duplicate_kind_names}"
        )
    tags.finish()

    return {
        "schemaKind": "NodeSchemaRegistryFragment",
        "schemaVersion": schema_version,
        "stage": profile["stage"],
        "grammar": profile["grammar"],
        "grammarSha256": digest,
        "wireTagPolicy": {
            key: profile["wireTags"][key]
            for key in ("algorithm", "namespace", "reserved", "collisionRule")
        },
        "counts": {
            "productions": len(generated),
            "terminalOccurrences": terminal_occurrence_count,
            "nonTerminalOccurrences": nonterminal_occurrence_count,
        },
        "registryFragment": {
            "version": schema_version,
            "cstCategories": category_descriptors,
            "grammarProductions": production_map,
            "cstProductionDescriptors": generated,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--emit", action="store_true", help="emit the complete generated schema as JSON"
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate without emitting JSON (the default; useful in scripted checks)",
    )
    parser.add_argument(
        "--production", help="emit one generated production descriptor as JSON"
    )
    args = parser.parse_args()
    try:
        schema = generate()
    except (GrammarError, KeyError, TypeError) as error:
        print(f"CST production schema validation failed: {error}", file=sys.stderr)
        return 1
    if args.production:
        matches = [
            item
            for item in schema["registryFragment"]["cstProductionDescriptors"]
            if item["debugName"] == args.production
        ]
        if not matches:
            print(f"unknown production {args.production!r}", file=sys.stderr)
            return 1
        print(json.dumps(matches[0], indent=2, ensure_ascii=False))
    elif args.emit:
        print(json.dumps(schema, indent=2, ensure_ascii=False))
    else:
        counts = schema["counts"]
        print(
            "CST production schema validation passed: "
            f"{counts['productions']} productions, "
            f"{counts['terminalOccurrences']} terminal occurrences, "
            f"{counts['nonTerminalOccurrences']} non-terminal occurrences"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
