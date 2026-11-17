"""Page numbers (embedded Arial) and metadata on the Edge-printed out/raw.pdf -> paper/Zambak_2026_CQRV.pdf."""
import os
import pymupdf as fitz

P = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FONT = os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts", "arial.ttf")
doc = fitz.open(os.path.join(P, "out", "raw.pdf"))
n = len(doc)
for i, pg in enumerate(doc):
    r = pg.rect
    pg.insert_text(fitz.Point(r.width / 2 - 12, r.height - 18), f"{i + 1} / {n}", fontsize=8.5,
                   fontname="pgnum", fontfile=FONT, color=(0.3, 0.3, 0.3))
doc.subset_fonts()
doc.set_metadata({
    "title": "Certified Quantum Realization in Lean 4: A Two-Pattern Prototype with Measurement-Based "
             "Uncomputation, Validated Routing, and Conditional Noise Bounds",
    "author": "Aziz F. Zambak",
    "subject": "Preprint, November 2026",
    "keywords": "certified compilation; Lean 4; quantum circuits; uncomputation; ancilla restoration; "
                "translation validation; noise bounds",
    "creator": "CQRV paper/tools", "producer": "Microsoft Edge (print), PyMuPDF"})
out = os.path.join(P, "Zambak_2026_CQRV.pdf")
doc.save(out, garbage=3, deflate=True)
print(n, "pages ->", out)
