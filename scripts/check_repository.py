#!/usr/bin/env python3
"""Check repository conventions and local Markdown links, without building Lean.

Supports ordinary inline/reference Markdown links, ATX/setext headings, and
GitHub line anchors. Fenced code and inline-code examples are ignored. This is
a small convention checker, not a full Markdown parser or Lean elaborator.
"""

from collections import Counter
from html import unescape
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit


HEADINGS = ["Problem", "Result and scope", "Formal statement", "Proof outline",
            "File guide", "Verification", "References and credits"]
LABEL = r"\[((?:\\.|[^\]\\\n])+)\]"
DEST = r'''(<[^>\n]+>|(?:\\.|[^\s()\\]|\([^()\n]*\))+)'''
INLINE = re.compile(LABEL + r"\(" + DEST + r'''(?:\s+(?:"[^"]*"|'[^']*'|\([^)]*\)))?\)''')
REFERENCE = re.compile(LABEL + r"\[([^\]\n]*)\]")
DEFINITION = re.compile(r"^ {0,3}" + LABEL + r":\s*" + DEST, re.M)


def unescape_md(value):
    return unescape(re.sub(r"\\([!\"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])", r"\1", value))


def prose(text):
    """Blank comments and fenced blocks while preserving line numbers."""
    text = re.sub(r"<!--[\s\S]*?-->", lambda m: "\n" * m[0].count("\n"), text)
    lines, fence = [], None
    for line in text.splitlines(keepends=True):
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)$", line)
        if fence:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= fence[1] and not marker[2].strip():
                fence = None
            lines.append("\n" if line.endswith("\n") else "")
        elif marker:
            fence = (marker[1][0], len(marker[1]))
            lines.append("\n" if line.endswith("\n") else "")
        else:
            lines.append(line)
    return "".join(lines)


def links(text, report):
    text = prose(text)
    code = [(m.start(), m.end()) for m in re.finditer(r"(`+)(?!`)[\s\S]*?(?<!`)\1(?!`)", text)]
    definitions, found, occupied = {}, [], list(code)
    normalize = lambda s: " ".join(unescape_md(s).split()).casefold()
    line = lambda m: text.count("\n", 0, m.start()) + 1
    for match in DEFINITION.finditer(text):
        definitions[normalize(match[1])] = match[2].strip("<>")
        found.append((match[1], match[2].strip("<>"), line(match)))
        occupied.append((match.start(), match.end()))
    for pattern in (INLINE, REFERENCE):
        for match in pattern.finditer(text):
            if any(a <= match.start() < b for a, b in occupied):
                continue
            if pattern is INLINE:
                destination = match[2].strip("<>")
            else:
                key = normalize(match[2] or match[1])
                destination = definitions.get(key)
                if destination is None:
                    report(f"{line(match)}: undefined link reference [{match[2] or match[1]}]")
            if destination is not None:
                found.append((match[1], destination, line(match)))
            occupied.append((match.start(), match.end()))
    for match in re.finditer(LABEL, text):
        if not any(a <= match.start() < b for a, b in occupied):
            destination = definitions.get(normalize(match[1]))
            if destination is not None:
                found.append((match[1], destination, line(match)))
    valid = []
    for label, destination, number in found:
        try:
            urlsplit(unescape_md(destination))
        except ValueError as error:
            report(f"{number}: malformed link {destination}: {error}")
        else:
            valid.append((label, destination, number))
    return valid


def anchors(text):
    text = prose(text)
    headings = re.findall(r"^ {0,3}#{1,6}\s+(.+?)(?:\s+#+)?\s*$", text, re.M)
    headings += re.findall(r"^([^\n]+)\n {0,3}(?:=+|-+)\s*$", text, re.M)
    result = set(re.findall(r'''\b(?:id|name)=["']([^"']+)["']''', text))
    for heading in headings:
        heading = re.sub(r"<[^>]+>", "", heading)
        heading = INLINE.sub(lambda m: m[1], heading)
        slug = re.sub(r"[^\w\- ]", "", unescape_md(heading).lower()).replace(" ", "-")
        candidate, suffix = slug, 0
        while candidate in result:
            suffix += 1
            candidate = f"{slug}-{suffix}"
        result.add(candidate)
    return result


def lean_code(text):
    """Remove Lean comments (including nested block comments) for simple scans."""
    depth, start, parts, line_comment = 0, 0, [], False
    for match in re.finditer(r"/-|-/|--|\n", text):
        if depth == 0 and not line_comment:
            parts.append(text[start:match.start()])
        if match[0] == "\n":
            parts.append("\n")
            line_comment = False
        elif line_comment:
            pass
        elif match[0] == "/-":
            parts.append(" ")
            depth += 1
        elif match[0] == "-/" and depth:
            depth -= 1
        elif match[0] == "--" and depth == 0:
            line_comment = True
        start = match.end()
    if depth == 0 and not line_comment:
        parts.append(text[start:])
    return "".join(parts)


def theorem_names(text):
    scopes, names = [], set()
    for line in lean_code(text).splitlines():
        scope = re.match(r"^(namespace|section)\b\s*([\w.']*)", line)
        if scope:
            scopes.append(scope[2] if scope[1] == "namespace" else "")
        elif re.match(r"^end\b", line) and scopes:
            scopes.pop()
        declaration = re.match(r"^(?:@\[[^\]]+\]\s*)?(?:protected\s+)?(?:theorem|lemma)\s+([\w.']+)", line)
        if declaration:
            names.add(".".join([s for s in scopes if s] + [declaration[1]]))
    return names


def check(root):
    root = root.resolve()
    errors = []
    report = lambda path, message: errors.append(f"{path}: {message}")
    tracked = subprocess.check_output(
        ["git", "-C", str(root), "ls-files", "--cached", "--others", "--exclude-standard", "-z"]
    ).decode().split("\0")
    files = {Path(p) for p in tracked if p and not {".lake", ".git"}.intersection(Path(p).parts)}
    read = lambda path: (root / path).read_text(encoding="utf-8") if (root / path).is_file() else ""
    markdown = {}
    for path in sorted(files):
        if path.suffix.lower() != ".md" or not (root / path).is_file():
            continue
        markdown[path] = links(read(path), lambda message, p=path: report(p, message))
        for _, destination, line in markdown[path]:
            url = urlsplit(unescape_md(destination))
            if url.scheme or url.netloc:
                continue
            target = (root / path).parent / unquote(url.path) if url.path else root / path
            target = target.resolve()
            if root != target and root not in target.parents:
                report(path, f"{line}: link leaves the repository: {destination}")
            elif not target.exists():
                report(path, f"{line}: broken link: {destination}")
            elif url.fragment:
                fragment = unquote(url.fragment)
                if target.is_dir():
                    target = target / "README.md"
                if target.suffix.lower() == ".md" and target.is_file():
                    valid = fragment in anchors(target.read_text(encoding="utf-8"))
                else:
                    match = re.fullmatch(r"L(\d+)(?:-L(\d+))?", fragment)
                    valid = bool(match and target.is_file() and
                                 1 <= int(match[1]) <= int(match[2] or match[1]) <=
                                 len(target.read_text(encoding="utf-8").splitlines()))
                if not valid:
                    report(path, f"{line}: missing or unsupported fragment: {destination}")

    problems = sorted({p.parts[2] for p in files if len(p.parts) > 3 and p.parts[:2] == ("Kourovka", "Problems")})
    if not problems:
        report("Kourovka/Problems", "no problem directories found")
    catalogue = markdown.get(Path("README.md"), [])
    endpoints = []
    for problem in problems:
        base = Path("Kourovka/Problems") / problem
        if not re.fullmatch(r"P[1-9]\d*_(?:0[1-9]|[1-9]\d+)", problem):
            report(base, "invalid problem ID; use P21_03 (at least two digits after the underscore)")
        for name in ("README.md", "Statement.lean", "Solution.lean", "Proof/README.md"):
            if not (root / base / name).is_file():
                report(base / name, "required file is missing")
        headings = re.findall(r"^## (.+?)\s*$", prose(read(base / "README.md")), re.M)
        if headings != HEADINGS:
            report(base / "README.md", f"expected H2 headings in order: {', '.join(HEADINGS)}")
        targets = []
        for label, destination, _ in catalogue:
            url = urlsplit(unescape_md(destination))
            if not url.scheme and not url.netloc:
                targets.append((label.strip("`"), (root / unquote(url.path)).resolve()))
        if not any(dest == root / base / "README.md" for _, dest in targets):
            report("README.md", f"missing catalogue link to {base}/README.md")
        public = [label for label, dest in targets if dest == root / base / "Solution.lean" and label.startswith("Kourovka.")]
        if not public:
            report("README.md", f"missing qualified public theorem link to {base}/Solution.lean")
        declared = theorem_names(read(base / "Solution.lean"))
        for name in public:
            if not name.startswith(f"Kourovka.{problem}.") or name not in declared:
                report("README.md", f"{name} is not a theorem declared in {base}/Solution.lean's public namespace")
        endpoints.extend(public)

    imports = Counter(re.findall(r"^import\s+(\S+)\s*$", lean_code(read(Path("Kourovka.lean"))), re.M))
    expected = Counter(f"Kourovka.Problems.{p}.Solution" for p in problems)
    for name in sorted(imports.keys() | expected.keys()):
        if imports[name] != expected[name]:
            report("Kourovka.lean", f"expected {expected[name]} import(s) of {name}; found {imports[name]}")
    audit = lean_code(read(Path("Audit.lean")))
    printed = Counter(re.findall(r"^#print axioms\s+(\S+)\s*$", audit, re.M))
    guarded = Counter(re.findall(r"^#guard_msgs\s+in\s*\n#print axioms\s+(\S+)\s*$", audit, re.M))
    expected = Counter(endpoints)
    for name in sorted(printed.keys() | expected.keys()):
        if printed[name] != 1 or guarded[name] != 1 or expected[name] != 1:
            report("Audit.lean", f"{name}: expected one catalogue entry and one guarded #print axioms; "
                   f"found {expected[name]} catalogue, {printed[name]} print, {guarded[name]} guarded")
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    if errors:
        print(f"Repository check failed: {len(errors)} error(s).", file=sys.stderr)
        return 1
    print(f"Repository check passed: {len(problems)} problems, {len(markdown)} Markdown files.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(check(Path(__file__).resolve().parents[1]))
    except (OSError, subprocess.CalledProcessError, UnicodeError) as error:
        sys.exit(f"Repository check could not run: {error}")
