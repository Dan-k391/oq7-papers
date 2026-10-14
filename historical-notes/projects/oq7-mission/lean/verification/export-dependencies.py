"""Export actual kernel proof/type edges and namespace closures from Lean logs."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()

def export(log_name: str, prefix: str, namespace: str, destination: str) -> dict:
    path = HERE / log_name
    text = path.read_text(encoding="utf-8-sig")
    nodes = {name: {"kind": kind, "typeConstants": set(), "valueConstants": set()}
             for kind, name in re.findall(prefix + r"-NODE (\S+) (\S+)", text)}
    for name, part, dependency in re.findall(prefix + r"-EDGE (\S+) (type|value) (\S+)", text):
        if name not in nodes:
            raise RuntimeError("Edge without kernel census node: " + name)
        nodes[name][part + "Constants"].add(dependency)
    def owned(name: str) -> bool:
        return name.startswith(namespace) or name.startswith("_private." + namespace)
    def closure(root: str) -> tuple[list[str], list[str]]:
        seen, external, pending = set(), set(), [root]
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            if name not in nodes:
                raise RuntimeError("Namespace dependency was not enumerated: " + name)
            seen.add(name)
            for dep in nodes[name]["typeConstants"] | nodes[name]["valueConstants"]:
                if owned(dep):
                    pending.append(dep)
                else:
                    external.add(dep)
        return sorted(seen - {root}), sorted(external)
    result = {
        "evidence": log_name,
        "evidenceSHA256": digest(path),
        "method": "Lean Expr.getUsedConstants on ConstantInfo.type and value?(allowOpaque := true)",
        "closureScope": namespace + " and its private module constants; all direct external edges are retained but not recursively expanded",
        "nodeCount": len(nodes),
        "directEdgeCount": sum(len(n["typeConstants"]) + len(n["valueConstants"]) for n in nodes.values()),
        "nodes": {},
    }
    for name, node in sorted(nodes.items()):
        internal, external = closure(name)
        result["nodes"][name] = {
            "kind": node["kind"],
            "typeConstants": sorted(node["typeConstants"]),
            "valueConstants": sorted(node["valueConstants"]),
            "transitiveNamespaceConstants": internal,
            "externalConstantsAcrossNamespaceClosure": external,
        }
    (HERE / destination).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return {key: result[key] for key in ("nodeCount", "directEdgeCount", "closureScope")}

def export_full(log_name: str, destination: str) -> dict:
    path = HERE / log_name
    text = path.read_text(encoding="utf-8-sig")
    marker = "OQ7FULL-JSON "
    if text.count(marker) != 1:
        raise RuntimeError("Missing or duplicate full kernel graph marker: " + log_name)
    payload = text.split(marker, 1)[1].strip()
    raw = json.loads(payload)
    nodes = {node["name"]: {k: v for k, v in node.items() if k != "name"} for node in raw["nodes"]}
    if len(nodes) != len(raw["nodes"]):
        raise RuntimeError("Duplicate full graph kernel node")
    result = {
        "evidence": log_name,
        "evidenceSHA256": digest(path),
        "method": "Recursively expand Expr.getUsedConstants on every referenced ConstantInfo.type and value?(allowOpaque := true), including imported Mathlib/Lean and private constants",
        "closureScope": "Full recursive named-constant closure of kernel type and proof/value expressions for the listed roots; metadata not represented as Expr is outside this graph",
        "nodeCount": len(nodes),
        "directEdgeCount": sum(len(n["typeConstants"]) + len(n["valueConstants"]) for n in nodes.values()),
        "nodes": dict(sorted(nodes.items())),
        "roots": {},
    }
    for name, node in nodes.items():
        for dep in node["typeConstants"] + node["valueConstants"]:
            if dep not in nodes:
                raise RuntimeError("Full closure missing referenced constant: " + dep)
    for root in raw["roots"]:
        seen, pending = set(), [root]
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            pending.extend(nodes[name]["typeConstants"] + nodes[name]["valueConstants"])
        result["roots"][root] = {
            "transitiveConstantCount": len(seen - {root}),
            "transitiveConstants": sorted(seen - {root}),
            "reachableAxioms": sorted(name for name in seen if nodes[name]["kind"] == "axiom"),
        }
    (HERE / destination).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return {key: result[key] for key in ("nodeCount", "directEdgeCount", "closureScope")}

new = export("inventory.log", "OQ7MISSION", "OQ7Mission.", "dependencies.json")
old = export("existing-dependencies.log", "OQ7EXISTING", "OQ7.", "theorem51-dependencies.json")
full_new = export_full("full-dependencies.log", "full-dependencies.json")
full_old = export_full("full-existing-dependencies.log", "full-theorem51-dependencies.json")
print(json.dumps({"newProject": new, "existingTheorem51": old,
                  "fullNewMainResults": full_new, "fullExistingTheorem51": full_old}))
