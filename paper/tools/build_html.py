"""Render paper/Zambak_2026_CQRV.md to the print-ready HTML out/paper.html (markdown-it-py)."""
import os
from markdown_it import MarkdownIt

P = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
text = open(os.path.join(P, "Zambak_2026_CQRV.md"), encoding="utf-8").read()
md = MarkdownIt("commonmark", {"html": True}).enable("table")
body = md.render(text)

css = r"""
@page { size: A4; margin: 24mm 22mm 24mm 22mm; }
html { font-size: 10.4pt; }
body { font-family: 'Cambria', 'Cambria Math', 'Segoe UI Symbol', serif; line-height: 1.38; color: #000;
       text-align: justify; hyphens: auto; -webkit-print-color-adjust: exact; print-color-adjust: exact; }
p:has(+ .code), p:has(+ .thm), h2, h3 { break-after: avoid; page-break-after: avoid; }
.titleblock { text-align: center; margin: 4mm 0 6mm 0; }
.titleblock .ttl { font-size: 17.5pt; font-weight: bold; line-height: 1.25; margin-bottom: 9pt; }
.titleblock .auth { font-size: 12pt; margin-top: 4pt; }
.titleblock .aff { font-size: 10pt; color: #222; }
.titleblock .date { font-size: 9.5pt; color: #444; margin-top: 6pt; font-style: italic; }
.abstract { margin: 0 9mm 4mm 9mm; font-size: 9.6pt; }
.abstract p { margin: 0 0 5pt 0; }
.keywords { margin: 0 9mm 4mm 9mm; font-size: 9.2pt; }
.toc { margin: 0 9mm 2mm 9mm; font-size: 9.2pt; color: #222; border-top: 0.5pt solid #999; border-bottom: 0.5pt solid #999; padding: 4pt 0; }
.toc p { margin: 0; }
h2 { font-size: 13pt; margin: 16pt 0 5pt 0; page-break-after: avoid; break-after: avoid; }
h3 { font-size: 11pt; margin: 11pt 0 4pt 0; page-break-after: avoid; break-after: avoid; }
p { margin: 0 0 5.5pt 0; }
ul, ol { margin: 0 0 5.5pt 0; padding-left: 17pt; }
li { margin: 1pt 0; }
code { font-family: 'Consolas', 'Cambria Math', monospace; font-size: 8.6pt; }
.code { font-family: 'Consolas', 'Cambria Math', monospace; font-size: 8.1pt; white-space: pre-wrap; text-align: left;
        background: #f6f6f6; border: 0.4pt solid #ccc; padding: 4pt 6pt; margin: 4pt 0 7pt 0; line-height: 1.3;
        page-break-inside: avoid; break-inside: avoid; }
.thm { margin: 7pt 0 7pt 0; padding: 2pt 0 1pt 8pt; border-left: 1.6pt solid #4a6fa5; }
.thm p { margin: 0 0 4pt 0; }
.proof { margin: 3pt 0 8pt 0; font-size: 9.9pt; }
.proof p:last-child::after { content: "  ∎"; }
.eq { text-align: center; margin: 5pt 0 6pt 0; font-size: 10.4pt; }
.listing { margin: 8pt 0; }
table { border-collapse: collapse; width: 100%; margin: 3pt 0 9pt 0; font-size: 8.5pt; text-align: left; }
thead { display: table-header-group; }
tr { page-break-inside: avoid; break-inside: avoid; }
th, td { border-top: 0.4pt solid #888; border-bottom: 0.4pt solid #888; padding: 2.2pt 4pt; vertical-align: top; }
th { background: #eeeeee; font-weight: bold; }
p.caption { font-size: 9pt; margin: 8pt 0 2pt 0; text-align: left; }
figure { margin: 8pt 0 10pt 0; text-align: center; page-break-inside: avoid; break-inside: avoid; }
figcaption { font-size: 9pt; text-align: left; margin-top: 4pt; }
.refs { font-size: 8.9pt; }
.refs ul { list-style: none; padding-left: 0; }
.refs li { margin: 2pt 0; padding-left: 14pt; text-indent: -14pt; text-align: left; }
.appendix h2 { page-break-before: always; break-before: page; }
.appendix h2 ~ h2 { page-break-before: auto; break-before: auto; }
sup, sub { font-size: 72%; line-height: 0; }
a { color: #1f4e8c; text-decoration: none; }
"""

html = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<title>Certified Quantum Realization in Lean 4: A Two-Pattern Prototype</title>
<style>{css}</style></head>
<body>
{body}
</body></html>
"""
os.makedirs(os.path.join(P, "out"), exist_ok=True)
out = os.path.join(P, "out", "paper.html")
open(out, "w", encoding="utf-8").write(html)
words = len(text.split())
print("words", words, "html", len(html))
