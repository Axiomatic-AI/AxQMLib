"""Adds the library's own pages to the API documentation that doc-gen4 built.

    python3 pages.py DOC_DIR SOURCE_URL

`DOC_DIR` is doc-gen4's output, `.lake/build/doc`. `SOURCE_URL` is where the library's files are
browsed at the documented commit, such as `https://github.com/OWNER/REPO/blob/COMMIT`.

The home page `index.html` becomes the library's `README.md`, and `items.html` the index of the
book's numbered items, `AxQM/NC/README.md`, both read from the library's checkout in
`.lake/packages/axqm`. Links to a `.lean` file go to its module's page, and links to other files
of the library go to `SOURCE_URL`. Both pages keep doc-gen4's header,
search and navigation, and the navigation gains a link to `items.html`.

Only the Markdown these two files use is rendered: headings, paragraphs, bulleted lists, tables,
fenced code, code spans, links and emphasis.
"""

import html
import posixpath
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent / ".lake" / "packages" / "axqm"

# A code span, a link, or emphasis.
INLINE = re.compile(r"(`+)(.+?)\1|\[([^\]]*)\]\(([^)\s]+)\)|\*(?=\S)(.+?)(?<=\S)\*")
ESCAPE = re.compile(r"\\([\\`*_\[\]()#|<>!-])")


def text(s):
    return html.escape(ESCAPE.sub(r"\1", s), quote=False)


def inline(s, link):
    out, pos = [], 0
    for m in INLINE.finditer(s):
        out.append(text(s[pos : m.start()]))
        pos = m.end()
        if m[1]:
            out.append(f"<code>{html.escape(m[2].strip(), quote=False)}</code>")
        elif m[4]:
            out.append(f'<a href="{html.escape(link(m[4]))}">{inline(m[3], link)}</a>')
        else:
            out.append(f"<em>{inline(m[5], link)}</em>")
    out.append(text(s[pos:]))
    return "".join(out)


def cells(row):
    """The cells of a table row, split at the pipes that are not escaped."""
    parts = re.split(r"(?<!\\)\|", row.strip())
    return [c.strip().replace("\\|", "|") for c in parts[1:-1]]


def slug(s):
    return re.sub(r"[^\w]+", "-", re.sub(r"`|\[|\]\([^)]*\)", "", s).lower()).strip("-")


def render(md, link):
    lines, out, i = md.splitlines(), [], 0
    starts_block = re.compile(r"#{1,6} |- |```|\|")
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
        elif line.startswith("```"):
            j = i + 1
            while not lines[j].startswith("```"):
                j += 1
            code = html.escape("\n".join(lines[i + 1 : j]), quote=False)
            out.append(f"<pre><code>{code}</code></pre>")
            i = j + 1
        elif m := re.match(r"(#{1,6}) (.*)", line):
            n = len(m[1])
            out.append(f'<h{n} id="{slug(m[2])}">{inline(m[2], link)}</h{n}>')
            i += 1
        elif line.startswith("|") and i + 1 < len(lines) and re.match(r"\|[-:| ]+\|$", lines[i + 1]):
            align = ["right" if c.endswith(":") else "left" for c in cells(lines[i + 1])]
            head = "".join(f'<th style="text-align:{a}">{inline(c, link)}</th>'
                           for c, a in zip(cells(line), align))
            rows, i = [], i + 2
            while i < len(lines) and lines[i].startswith("|"):
                rows.append("<tr>" + "".join(f'<td style="text-align:{a}">{inline(c, link)}</td>'
                                             for c, a in zip(cells(lines[i]), align)) + "</tr>")
                i += 1
            out.append(f"<table><thead><tr>{head}</tr></thead><tbody>{''.join(rows)}</tbody></table>")
        elif line.startswith("- "):
            items = []
            while i < len(lines) and (lines[i].startswith("- ") or lines[i].startswith("  ")):
                if lines[i].startswith("- "):
                    items.append(lines[i][2:])
                else:
                    items[-1] += " " + lines[i].strip()
                i += 1
            out.append("<ul>" + "".join(f"<li>{inline(t, link)}</li>" for t in items) + "</ul>")
        else:
            para = []
            while i < len(lines) and lines[i].strip() and not starts_block.match(lines[i]):
                para.append(lines[i].strip())
                i += 1
            out.append(f"<p>{inline(' '.join(para), link)}</p>")
    return "\n".join(out)


def linker(doc_dir, source_url, base):
    """Resolves the links of a Markdown file in the directory `base` of the repository."""

    def link(target):
        if re.match(r"[a-z]+:|#", target):
            return target
        path = posixpath.normpath(posixpath.join(base, target))
        if path == "AxQM/NC/README.md":
            return "items.html"
        page = path.removesuffix(".lean") + ".html"
        if path.endswith(".lean") and (doc_dir / page).is_file():
            return page
        return f"{source_url}/{path}"

    return link


def page(template, title, body):
    main = f'<main class="axqm-page">\n{body}\n</main>'
    out = re.sub(r"<main>.*?</main>", lambda _: main, template, count=1, flags=re.S)
    out = re.sub(r"<title>.*?</title>", f"<title>{html.escape(title)}</title>", out, count=1)
    return re.sub(r'(<h2 class="header_filename[^"]*">).*?(</h2>)',
                  lambda m: m[1] + html.escape(title) + m[2], out, count=1, flags=re.S)


def main(doc_dir, source_url):
    doc_dir, source_url = Path(doc_dir), source_url.rstrip("/")
    index = doc_dir / "index.html"
    # doc-gen4's own home page, kept so that running this again starts from it. A home page
    # without this script's content is a fresh one from doc-gen4.
    original = doc_dir / "index.docgen.html"
    if "axqm-page" not in index.read_text():
        original.write_text(index.read_text())
    template = original.read_text()

    readme = render((REPO / "README.md").read_text(), linker(doc_dir, source_url, ""))
    index.write_text(page(template, "AxQM", readme))
    items = render((REPO / "AxQM/NC/README.md").read_text(), linker(doc_dir, source_url, "AxQM/NC"))
    (doc_dir / "items.html").write_text(page(template, "Nielsen & Chuang: the numbered items", items))

    navbar = doc_dir / "navbar.html"
    nav = navbar.read_text()
    if "items.html" not in nav:
        entry = '<div class="nav_link"><a href="./items.html">N&amp;C items</a></div>'
        nav = re.sub(r'(<div class="nav_link"><a href="\./">index</a></div>)',
                     lambda m: m[1] + entry, nav, count=1)
        navbar.write_text(nav)

    # doc-gen4 does not style tables.
    style = doc_dir / "style.css"
    css = style.read_text()
    if ".axqm-page" not in css:
        style.write_text(css + """
.axqm-page table { border-collapse: collapse; margin: 1em 0; }
.axqm-page th, .axqm-page td { border: 1px solid var(--hamburger-border-color); padding: 0.3em 0.6em; }
.axqm-page td code, .axqm-page th code { white-space: nowrap; }
""")


if __name__ == "__main__":
    main(*sys.argv[1:])
