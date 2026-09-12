"""Render catalog/*.json (the raw exploration records of the Collatz line) into
docs/catalog.md with one row per record: id, status, one-line statement, evidence.
The records were written over months by different tools, so the schema varies; this
renderer is tolerant and never invents a field.  Usage: python scripts/render_catalog.py
"""
import glob
import json
import os
import re

RAIZ = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CAT = os.path.join(RAIZ, "catalog")
OUT = os.path.join(RAIZ, "docs", "catalog.md")


def uno(d, *claves):
    for k in claves:
        v = d.get(k)
        if isinstance(v, str) and v.strip():
            return v.strip()
    return ""


def estado(d, nombre):
    t = (uno(d, "tipo", "status", "estado", "nivel") + " " + nombre).lower()
    if "refut" in t or t.startswith("x"):
        return "refuted"
    if "p-lean" in t or "lean" in t:
        return "proved (Lean)"
    if t.startswith("p ") or "probado" in t or "proved" in t or "demostrad" in t:
        return "proved"
    if t.startswith("v ") or "verificad" in t or "verified" in t:
        return "verified (computation)"
    if "conjet" in t or "conjecture" in t or "sugerid" in t or "suggested" in t:
        return "conjecture / suggestion"
    if t.startswith("h ") or t.startswith("h-") or t.split(" ")[0] == "h":
        return "hypothesis (open)"
    return uno(d, "tipo", "status", "estado", "nivel") or "record"


filas = []
for ruta in sorted(glob.glob(os.path.join(CAT, "*.json"))):
    nombre = os.path.basename(ruta)[:-5]
    try:
        d = json.load(open(ruta, encoding="utf-8"))
    except Exception as e:
        filas.append((nombre, "unreadable", str(e)[:80], ""))
        continue
    if isinstance(d, list):
        d = d[0] if d and isinstance(d[0], dict) else {}
    if not isinstance(d, dict):
        filas.append((nombre, "record", str(d)[:120], ""))
        continue
    enun = uno(d, "enunciado", "statement", "titulo", "title", "resultado", "claim", "descripcion", "description", "resumen")
    evid = uno(d, "evidencia", "evidence", "verificacion", "verification", "prueba", "nota", "note")
    filas.append((nombre, estado(d, nombre), re.sub(r"\s+", " ", enun)[:300], re.sub(r"\s+", " ", evid)[:200]))

with open(OUT, "w", encoding="utf-8", newline="\n") as f:
    f.write("# Exploration catalog (Collatz line)\n\n")
    f.write("Raw records of the campaign, rendered by `scripts/render_catalog.py` from `catalog/*.json`. ")
    f.write("Refuted entries are kept on purpose. A record's status is what the record itself says; ")
    f.write("only the results listed in `results.md` are endorsed by this repository.\n\n")
    f.write("| record | status | statement | evidence |\n|---|---|---|---|\n")
    for n, s, e, v in filas:
        f.write("| `%s` | %s | %s | %s |\n" % (n, s, e.replace("|", "\\|"), v.replace("|", "\\|")))
    f.write("\n%d records.\n" % len(filas))
print(OUT, ":", len(filas), "records")
