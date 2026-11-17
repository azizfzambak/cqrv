"""Convert the rendered paper HTML (out/paper.html) to a native Word document (python-docx)."""
import os, re, sys
from html.parser import HTMLParser
from docx import Document
from docx.shared import Pt, Cm, RGBColor, Emu
from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_BREAK
from docx.enum.table import WD_TABLE_ALIGNMENT
from docx.enum.section import WD_SECTION
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

P = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(P, "out", "paper.html")
FIG = os.path.join(P, "fig1.png")
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(P, "out", "Zambak_2026_CQRV.docx")

BODY_FONT = "Cambria"
CODE_FONT = "Consolas"
BODY_PT = 10.5

# ---------------------------------------------------------------- tiny DOM
VOID = {"br", "img", "hr", "meta", "link", "input"}


class Node:
    def __init__(self, tag, attrs=None, parent=None):
        self.tag, self.attrs, self.parent, self.children = tag, dict(attrs or {}), parent, []

    @property
    def cls(self):
        return self.attrs.get("class", "")


class P(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Node("root")
        self.cur = self.root

    def handle_starttag(self, tag, attrs):
        n = Node(tag, attrs, self.cur)
        self.cur.children.append(n)
        if tag not in VOID:
            self.cur = n

    def handle_startendtag(self, tag, attrs):
        self.cur.children.append(Node(tag, attrs, self.cur))

    def handle_endtag(self, tag):
        n = self.cur
        while n is not None and n.tag != tag:
            n = n.parent
        if n is not None and n.parent is not None:
            self.cur = n.parent

    def handle_data(self, data):
        self.cur.children.append(data)


html = open(SRC, encoding="utf-8").read()
body = html[html.index("<body"):]
p = P()
p.feed(body)
root = p.root


def find(n, tag):
    for c in n.children:
        if isinstance(c, Node):
            if c.tag == tag:
                return c
            r = find(c, tag)
            if r:
                return r
    return None


bodynode = find(root, "body") or root

# ---------------------------------------------------------------- document setup
doc = Document()
sec = doc.sections[0]
sec.page_width, sec.page_height = Cm(21.0), Cm(29.7)
sec.left_margin = sec.right_margin = Cm(2.2)
sec.top_margin, sec.bottom_margin = Cm(2.0), Cm(2.0)
TEXT_W = sec.page_width - sec.left_margin - sec.right_margin

st = doc.styles
normal = st["Normal"]
normal.font.name = BODY_FONT
normal.font.size = Pt(BODY_PT)
normal.element.rPr.rFonts.set(qn("w:eastAsia"), BODY_FONT)
normal.paragraph_format.space_after = Pt(5)
normal.paragraph_format.space_before = Pt(0)
normal.paragraph_format.line_spacing = 1.12

for name, size, before, after in [("Heading 1", 15, 16, 6), ("Heading 2", 12, 11, 4), ("Heading 3", 11, 8, 3)]:
    h = st[name]
    h.font.name = BODY_FONT
    h.font.size = Pt(size)
    h.font.bold = True
    h.font.italic = False
    h.font.color.rgb = RGBColor(0x11, 0x11, 0x11)
    rpr = h.element.get_or_add_rPr()
    rf = rpr.find(qn("w:rFonts"))
    if rf is None:
        rf = OxmlElement("w:rFonts")
        rpr.append(rf)
    for a in ("w:ascii", "w:hAnsi", "w:eastAsia", "w:cs"):
        rf.set(qn(a), BODY_FONT)
    for a in ("w:asciiTheme", "w:hAnsiTheme", "w:eastAsiaTheme", "w:cstheme"):
        if rf.get(qn(a)) is not None:
            del rf.attrib[qn(a)]
    h.paragraph_format.space_before = Pt(before)
    h.paragraph_format.space_after = Pt(after)
    h.paragraph_format.keep_with_next = True

# footer: page X / Y


def add_field(run, instr):
    f1 = OxmlElement("w:fldChar"); f1.set(qn("w:fldCharType"), "begin")
    it = OxmlElement("w:instrText"); it.set(qn("xml:space"), "preserve"); it.text = instr
    f2 = OxmlElement("w:fldChar"); f2.set(qn("w:fldCharType"), "separate")
    t = OxmlElement("w:t"); t.text = "1"
    f3 = OxmlElement("w:fldChar"); f3.set(qn("w:fldCharType"), "end")
    for e in (f1, it, f2, t, f3):
        run._r.append(e)


fp = sec.footer.paragraphs[0]
fp.alignment = WD_ALIGN_PARAGRAPH.CENTER
for part in ("PAGE", " / ", "NUMPAGES"):
    r = fp.add_run()
    r.font.size = Pt(8.5)
    r.font.color.rgb = RGBColor(0x55, 0x55, 0x55)
    if part.strip() == "/":
        r.text = part
    else:
        add_field(r, part)

# ---------------------------------------------------------------- helpers


def shade(par, fill):
    pPr = par._p.get_or_add_pPr()
    shd = OxmlElement("w:shd")
    shd.set(qn("w:val"), "clear"); shd.set(qn("w:color"), "auto"); shd.set(qn("w:fill"), fill)
    pPr.append(shd)


def border(par, sides, color="888888", sz=8, space=4):
    pPr = par._p.get_or_add_pPr()
    b = pPr.find(qn("w:pBdr"))
    if b is None:
        b = OxmlElement("w:pBdr")
        pPr.append(b)
    for side in sides:
        e = OxmlElement("w:" + side)
        e.set(qn("w:val"), "single"); e.set(qn("w:sz"), str(sz)); e.set(qn("w:space"), str(space)); e.set(qn("w:color"), color)
        b.append(e)


def cell_shade(cell, fill):
    tcPr = cell._tc.get_or_add_tcPr()
    shd = OxmlElement("w:shd")
    shd.set(qn("w:val"), "clear"); shd.set(qn("w:color"), "auto"); shd.set(qn("w:fill"), fill)
    tcPr.append(shd)


def text_of(n):
    if isinstance(n, str):
        return n
    if n.tag == "br":
        return "\n"
    return "".join(text_of(c) for c in n.children)


class Ctx:
    """Block context: how new paragraphs are formatted."""

    def __init__(self, **kw):
        self.indent = kw.get("indent", 0.0)        # cm
        self.right = kw.get("right", 0.0)
        self.fill = kw.get("fill")
        self.bar = kw.get("bar")                   # left-bar colour
        self.size = kw.get("size")
        self.italic = kw.get("italic", False)
        self.align = kw.get("align")
        self.after = kw.get("after")

    def child(self, **kw):
        c = Ctx(**self.__dict__)
        c.__dict__.update(kw)
        return c


TARGET = {"t": None, "fresh": None}


def new_par(ctx, style=None):
    if TARGET["fresh"] is not None:
        par = TARGET["fresh"]
        TARGET["fresh"] = None
        if style:
            par.style = style
    elif TARGET["t"] is not None:
        par = TARGET["t"].add_paragraph(style=style)
    else:
        par = doc.add_paragraph(style=style)
    pf = par.paragraph_format
    if ctx.indent:
        pf.left_indent = Cm(ctx.indent)
    if ctx.right:
        pf.right_indent = Cm(ctx.right)
    if ctx.fill:
        shade(par, ctx.fill)
    if ctx.bar:
        border(par, ["left"], color=ctx.bar, sz=18, space=6)
    if ctx.align is not None:
        par.alignment = ctx.align
    if ctx.after is not None:
        pf.space_after = Pt(ctx.after)
    return par


WS = re.compile(r"\s+")


def add_inline(par, n, fmt, ctx, state):
    """Add inline content of node n to paragraph par. state['lead'] strips leading spaces."""
    if isinstance(n, str):
        if fmt.get("pre"):
            txt = n
        else:
            txt = WS.sub(" ", n)
            if state["lead"]:
                txt = txt.lstrip()
        if not txt:
            return
        state["lead"] = txt.endswith(" ") and not fmt.get("pre")
        r = par.add_run(txt)
        r.bold = fmt.get("b") or None
        r.italic = (bool(fmt.get("i")) ^ bool(ctx.italic)) or None
        if fmt.get("code"):
            r.font.name = CODE_FONT
            r._r.get_or_add_rPr().get_or_add_rFonts().set(qn("w:hAnsi"), CODE_FONT)
            r.font.size = Pt((ctx.size or BODY_PT) - 1.2)
        elif ctx.size:
            r.font.size = Pt(ctx.size)
        if fmt.get("va") == "sub":
            r.font.subscript = True
        elif fmt.get("va") == "sup":
            r.font.superscript = True
        if fmt.get("color"):
            r.font.color.rgb = fmt["color"]
        return
    t = n.tag
    f = dict(fmt)
    if t in ("strong", "b"):
        f["b"] = True
    elif t in ("em", "i"):
        f["i"] = not f.get("i", False)
    elif t == "code":
        f["code"] = True
    elif t == "sub":
        f["va"] = "sub"
    elif t == "sup":
        f["va"] = "sup"
    elif t == "br":
        par.add_run().add_break()
        state["lead"] = True
        return
    for c in n.children:
        add_inline(par, c, f, ctx, state)


INLINE = {"strong", "b", "em", "i", "code", "sub", "sup", "a", "span", "br"}


def inline_par(nodes, ctx, style=None, fmt=None):
    par = new_par(ctx, style)
    state = {"lead": True}
    for c in nodes:
        add_inline(par, c, fmt or {}, ctx, state)
    # strip trailing space of last run
    if par.runs and par.runs[-1].text.endswith(" "):
        par.runs[-1].text = par.runs[-1].text.rstrip()
    return par


def is_inline(c):
    return isinstance(c, str) or c.tag in INLINE


def emit_children(n, ctx):
    """Emit block children; group loose inline runs into paragraphs."""
    buf = []

    def flush():
        if any((isinstance(x, str) and x.strip()) or (not isinstance(x, str)) for x in buf):
            inline_par(buf, ctx)
        buf.clear()

    for c in n.children:
        if is_inline(c):
            buf.append(c)
        else:
            flush()
            emit_block(c, ctx)
    flush()


def emit_list(n, ctx, ordered, level=0):
    k = 0
    for li in n.children:
        if not isinstance(li, Node) or li.tag != "li":
            continue
        k += 1
        ind = ctx.indent + 0.55 + 0.55 * level
        sub_blocks = [c for c in li.children if isinstance(c, Node) and c.tag in ("ul", "ol", "p", "div")]
        inl = [c for c in li.children if is_inline(c)]
        c2 = ctx.child(indent=ind)
        par = new_par(c2)
        pf = par.paragraph_format
        pf.first_line_indent = Cm(-0.45)
        pf.space_after = Pt(2.5)
        mark = f"{k}." if ordered else "•"
        r = par.add_run(mark + "\t")
        if ctx.size:
            r.font.size = Pt(ctx.size)
        pf.tab_stops.add_tab_stop(Cm(ind))
        state = {"lead": True}
        first_p_used = False
        for c in inl:
            add_inline(par, c, {}, c2, state)
        if not inl:
            # li content wrapped in <p>: put first <p> into the bullet paragraph
            for c in sub_blocks:
                if c.tag == "p":
                    for cc in c.children:
                        add_inline(par, cc, {}, c2, state)
                    first_p_used = c
                    break
        for c in sub_blocks:
            if c is first_p_used:
                continue
            if c.tag in ("ul", "ol"):
                emit_list(c, ctx, c.tag == "ol", level + 1)
            else:
                emit_block(c, c2)


def col_weights(rows):
    ncol = max(len(r) for r in rows)
    w = [4.0] * ncol
    for r in rows:
        for j, c in enumerate(r):
            L = len(WS.sub(" ", text_of(c)).strip())
            w[j] = max(w[j], min(L, 70) + 4)
    return w


def emit_table(n, ctx, caption_par=None):
    rows = []
    heads = []
    for sect in n.children:
        if not isinstance(sect, Node):
            continue
        trs = [sect] if sect.tag == "tr" else [x for x in sect.children if isinstance(x, Node) and x.tag == "tr"]
        for tr in trs:
            cells = [x for x in tr.children if isinstance(x, Node) and x.tag in ("td", "th")]
            rows.append(cells)
            heads.append(all(c.tag == "th" for c in cells))
    ncol = max(len(r) for r in rows)
    size = 8.0 if ncol <= 5 else (7.4 if ncol <= 7 else 6.8)
    w = col_weights(rows)
    mw = [3] * ncol
    for r in rows:
        for j, c in enumerate(r):
            for word in WS.sub(" ", text_of(c)).split(" "):
                mw[j] = max(mw[j], len(word))
    # minimum width: the longest word (bold header counts a bit wider), plus cell margins
    mins = [int(((m + 1.5) * size * 0.56 + 10) * 12700) for m in mw]
    if sum(mins) > TEXT_W:
        f = TEXT_W / sum(mins)
        widths = [int(x * f) for x in mins]
    else:
        tot = sum(w)
        widths = [int(TEXT_W * x / tot) for x in w]
        # lift columns below their minimum, take the difference from the others proportionally
        for _ in range(5):
            short = [j for j in range(ncol) if widths[j] < mins[j]]
            if not short:
                break
            need = sum(mins[j] - widths[j] for j in short)
            for j in short:
                widths[j] = mins[j]
            rich = [j for j in range(ncol) if j not in short]
            spare = sum(widths[j] - mins[j] for j in rich if widths[j] > mins[j])
            for j in rich:
                if widths[j] > mins[j] and spare > 0:
                    widths[j] -= int(need * (widths[j] - mins[j]) / spare)
    tbl = doc.add_table(rows=len(rows), cols=ncol)
    tbl.style = doc.styles["Table Grid"]
    tbl.alignment = WD_TABLE_ALIGNMENT.CENTER
    tbl.autofit = False
    # grey borders
    tblPr = tbl._tbl.tblPr
    bd = OxmlElement("w:tblBorders")
    for side in ("top", "left", "bottom", "right", "insideH", "insideV"):
        e = OxmlElement("w:" + side)
        e.set(qn("w:val"), "single"); e.set(qn("w:sz"), "4"); e.set(qn("w:space"), "0"); e.set(qn("w:color"), "A6A6A6")
        bd.append(e)
    tblPr.append(bd)
    cm = OxmlElement("w:tblCellMar")
    for side, v in (("top", 30), ("bottom", 30), ("left", 70), ("right", 70)):
        e = OxmlElement("w:" + side); e.set(qn("w:w"), str(v)); e.set(qn("w:type"), "dxa"); cm.append(e)
    tblPr.append(cm)
    grid = tbl._tbl.tblGrid
    for j, gc in enumerate(grid.findall(qn("w:gridCol"))):
        gc.set(qn("w:w"), str(int(widths[j] / 635)))
    for i, r in enumerate(rows):
        row = tbl.rows[i]
        if heads[i]:
            trPr = row._tr.get_or_add_trPr()
            th = OxmlElement("w:tblHeader"); th.set(qn("w:val"), "true"); trPr.append(th)
        cant = OxmlElement("w:cantSplit"); cant.set(qn("w:val"), "true"); row._tr.get_or_add_trPr().append(cant)
        for j in range(ncol):
            cell = row.cells[j]
            cell.width = Emu(widths[j])
            par = cell.paragraphs[0]
            par.paragraph_format.space_after = Pt(0)
            par.paragraph_format.line_spacing = 1.0
            if j < len(r):
                c2 = Ctx(size=size)
                state = {"lead": True}
                fmt = {"b": True} if heads[i] else {}
                for c in r[j].children:
                    if isinstance(c, Node) and c.tag in ("ul", "ol", "p"):
                        for cc in c.children:
                            add_inline(par, cc, fmt, c2, state)
                    else:
                        add_inline(par, c, fmt, c2, state)
            if heads[i]:
                cell_shade(cell, "EDEDED")
    sp = doc.add_paragraph()
    sp.paragraph_format.space_after = Pt(2)
    sp.paragraph_format.line_spacing = 0.8


def emit_code(n, ctx):
    txt = text_of(n).strip("\n")
    lines = txt.split("\n")
    for k, line in enumerate(lines):
        par = new_par(ctx.child(fill="F3F3F3"))
        pf = par.paragraph_format
        pf.space_after = Pt(0) if k < len(lines) - 1 else Pt(6)
        pf.space_before = Pt(0)
        pf.line_spacing = 1.0
        pf.keep_with_next = k < len(lines) - 1
        pf.left_indent = Cm(ctx.indent + 0.2)
        r = par.add_run(line if line else " ")
        r.font.name = CODE_FONT
        r._r.get_or_add_rPr().get_or_add_rFonts().set(qn("w:hAnsi"), CODE_FONT)
        r.font.size = Pt(7.6)


pending_caption = []


def emit_block(n, ctx):
    if isinstance(n, str):
        if n.strip():
            inline_par([n], ctx)
        return
    t, cls = n.tag, n.cls
    if t == "h2":
        txt = WS.sub(" ", text_of(n)).strip()
        if txt.startswith("Appendix A") or txt == "References":
            doc.add_paragraph().add_run().add_break(WD_BREAK.PAGE)
        h = doc.add_heading(level=1)
        state = {"lead": True}
        for c in n.children:
            add_inline(h, c, {}, Ctx(), state)
        return
    if t == "h3":
        h = doc.add_heading(level=2)
        state = {"lead": True}
        for c in n.children:
            add_inline(h, c, {}, Ctx(), state)
        return
    if t == "h4":
        h = doc.add_heading(level=3)
        state = {"lead": True}
        for c in n.children:
            add_inline(h, c, {}, Ctx(), state)
        return
    if t == "p":
        if "caption" in cls:
            par = inline_par(n.children, ctx.child(size=9.0))
            par.paragraph_format.keep_with_next = True
            par.paragraph_format.space_before = Pt(4)
            return
        par = inline_par(n.children, ctx)
        if par.text.rstrip().endswith(":") or (par.runs and par.runs[0].bold and len(par.text) < 80):
            par.paragraph_format.keep_with_next = True
        return
    if t in ("ul", "ol"):
        emit_list(n, ctx, t == "ol")
        return
    if t == "table":
        emit_table(n, ctx)
        return
    if t == "figure":
        par = new_par(ctx.child(align=WD_ALIGN_PARAGRAPH.CENTER))
        par.paragraph_format.keep_with_next = True
        par.add_run().add_picture(FIG, width=TEXT_W)
        cap = find(n, "figcaption")
        if cap:
            inline_par(cap.children, ctx.child(size=9.0))
        return
    if t == "div":
        if "titleblock" in cls:
            for c in n.children:
                if not isinstance(c, Node):
                    continue
                cc = c.cls
                c2 = Ctx(align=WD_ALIGN_PARAGRAPH.CENTER, after=2)
                if cc == "ttl":
                    par = inline_par(c.children, c2.child(size=17, after=10), fmt={"b": True})
                    par.paragraph_format.space_before = Pt(18)
                elif cc == "auth":
                    inline_par(c.children, c2.child(size=12))
                elif cc == "aff":
                    inline_par(c.children, c2.child(size=10))
                elif cc == "date":
                    par = inline_par(c.children, c2.child(size=9.5, italic=True, after=14))
            return
        if "abstract" in cls:
            emit_children(n, ctx.child(indent=0.7, right=0.7, size=9.8))
            return
        if "keywords" in cls:
            emit_children(n, ctx.child(indent=0.7, right=0.7, size=9.5))
            return
        if "thm" in cls:
            box = doc.add_table(rows=1, cols=1)
            box.alignment = WD_TABLE_ALIGNMENT.CENTER
            box.autofit = False
            cell = box.rows[0].cells[0]
            cell.width = Emu(int(TEXT_W))
            box._tbl.tblGrid.findall(qn("w:gridCol"))[0].set(qn("w:w"), str(int(TEXT_W / 635)))
            cell_shade(cell, "F3F6FA")
            tcPr = cell._tc.get_or_add_tcPr()
            bd = OxmlElement("w:tcBorders")
            for side, val in (("top", "nil"), ("left", "single"), ("bottom", "nil"), ("right", "nil")):
                e = OxmlElement("w:" + side); e.set(qn("w:val"), val)
                if val == "single":
                    e.set(qn("w:sz"), "18"); e.set(qn("w:space"), "0"); e.set(qn("w:color"), "5B7DB1")
                bd.append(e)
            tcPr.append(bd)
            mar = OxmlElement("w:tcMar")
            for side, v in (("top", 60), ("bottom", 40), ("left", 140), ("right", 120)):
                e = OxmlElement("w:" + side); e.set(qn("w:w"), str(v)); e.set(qn("w:type"), "dxa"); mar.append(e)
            tcPr.append(mar)
            old = dict(TARGET)
            TARGET["t"], TARGET["fresh"] = cell, cell.paragraphs[0]
            emit_children(n, Ctx(indent=0.0, size=ctx.size))
            TARGET.update(old)
            last = cell.paragraphs[-1]
            last.paragraph_format.space_after = Pt(1)
            sp = doc.add_paragraph()
            sp.paragraph_format.space_after = Pt(0)
            sp.paragraph_format.line_spacing = Pt(7)
            return
        if "proof" in cls:
            emit_children(n, ctx.child(indent=ctx.indent + 0.4))
            return
        if "eq" in cls:
            inline_par(n.children, ctx.child(align=WD_ALIGN_PARAGRAPH.CENTER))
            return
        if cls == "code":
            emit_code(n, ctx)
            return
        if "refs" in cls:
            for c in n.children:
                if isinstance(c, Node) and c.tag == "ul":
                    for li in c.children:
                        if isinstance(li, Node) and li.tag == "li":
                            par = inline_par(li.children, ctx.child(size=9.2))
                            par.paragraph_format.left_indent = Cm(0.6)
                            par.paragraph_format.first_line_indent = Cm(-0.6)
                            par.paragraph_format.space_after = Pt(3)
                elif isinstance(c, Node):
                    emit_block(c, ctx.child(size=9.2))
            return
        emit_children(n, ctx)
        return
    if t in ("section", "article", "main", "body"):
        emit_children(n, ctx)
        return
    # fallback
    emit_children(n, ctx)


# python-docx creates an empty first paragraph? (Document() has none) -> start
emit_children(bodynode, Ctx())

# metadata
cp = doc.core_properties
cp.title = ("Certified Quantum Realization in Lean 4: A Two-Pattern Prototype with Measurement-Based "
            "Uncomputation, Validated Routing, and Conditional Noise Bounds")
cp.author = "Aziz F. Zambak"
cp.subject = "Preprint, November 2026"
cp.keywords = "certified compilation; Lean 4; quantum realization; measurement-based uncomputation; translation validation"
doc.save(OUT)
print("saved", OUT)
