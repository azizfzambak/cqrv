# The paper

*Certified Quantum Realization in Lean 4: A Two-Pattern Prototype with Measurement-Based
Uncomputation, Validated Routing, and Conditional Noise Bounds*, Aziz F. Zambak, November 2026.
Preprint, published on Zenodo. It describes this repository up to Phase 3; the code it describes is
commit `2f8200b`.

- `Zambak_2026_CQRV.pdf`: the paper (48 pages).
- `Zambak_2026_CQRV.md`: its source (Markdown with HTML blocks for the title, theorems, tables and
  the inline SVG figure).
- `fig1.png`: Figure 1 as an image, for the Word export.
- `tools/build.ps1`: rebuilds the PDF and a Word file into `out/` (git-ignored). Windows only:
  Python with `markdown-it-py`, `pymupdf` and `python-docx`, and Microsoft Edge for the headless
  print. Steps: `build_html.py` (Markdown to HTML), Edge (HTML to PDF), `pdf_post.py` (page numbers,
  metadata), `build_docx.py` (HTML to Word).
