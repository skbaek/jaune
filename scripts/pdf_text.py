#!/usr/bin/env python3
"""Deterministic plain-text extract of a text PDF, standard library only.

usage: pdf_text.py PDF OUT [--fonts]

The extract is the bindable form of a standards PDF for the naming source
lock: UTF-8, LF line ends, one form feed line between pages, no trailing
blanks. Supported input: unencrypted PDF with FlateDecode streams, object
streams, simple fonts (WinAnsi/MacRoman/Differences) and Type0 fonts, with or
without ToUnicode maps. Anything else raises. A character code with no
declared Unicode value is written as U+FFFD: the tool never guesses.

Text is emitted in content-stream order. A new line starts when the baseline
moves by more than 0.6 of the font size; a blank is inserted when the gap to
the previous glyph run exceeds 0.2 of the font size. Characters come only from
the fonts' ToUnicode maps or declared encodings.
"""
import re
import sys
import zlib

WS = b"\x00\t\n\x0c\r "
DELIM = b"()<>[]{}/%"


class Ref(tuple):
    pass


class Name(str):
    pass


class Stream:
    def __init__(self, dict_, raw):
        self.dict, self.raw = dict_, raw


class Op(str):
    pass


class Parser:
    def __init__(self, data, pos=0, content=False):
        self.d, self.p, self.content = data, pos, content

    def skip(self):
        d = self.d
        while self.p < len(d):
            c = d[self.p]
            if c in WS:
                self.p += 1
            elif c == 0x25:
                while self.p < len(d) and d[self.p] not in b"\r\n":
                    self.p += 1
            else:
                break

    def obj(self):
        self.skip()
        d, p = self.d, self.p
        if p >= len(d):
            raise EOFError
        c = d[p:p + 1]
        if d[p:p + 2] == b"<<":
            self.p += 2
            out = {}
            while True:
                self.skip()
                if d[self.p:self.p + 2] == b">>":
                    self.p += 2
                    return out
                key = self.obj()
                if not isinstance(key, Name):
                    raise ValueError(f"dictionary key at {self.p}")
                out[key] = self.obj()
        if c == b"[":
            self.p += 1
            out = []
            while True:
                self.skip()
                if d[self.p:self.p + 1] == b"]":
                    self.p += 1
                    return out
                out.append(self.obj())
        if c == b"/":
            m = re.compile(rb"/([^\x00\t\n\x0c\r ()<>\[\]{}/%]*)").match(d, p)
            self.p = m.end()
            raw = re.sub(rb"#([0-9A-Fa-f]{2})", lambda x: bytes([int(x.group(1), 16)]), m.group(1))
            return Name(raw.decode("latin-1"))
        if c == b"(":
            return self.literal()
        if c == b"<":
            end = d.index(b">", p)
            hexs = re.sub(rb"\s", b"", d[p + 1:end])
            if len(hexs) % 2:
                hexs += b"0"
            self.p = end + 1
            return bytes.fromhex(hexs.decode("ascii"))
        m = re.compile(rb"[+-]?(?:\d+\.?\d*|\.\d+)").match(d, p)
        if m:
            if not self.content:
                r = re.compile(rb"(\d+)[\x00\t\n\x0c\r ]+(\d+)[\x00\t\n\x0c\r ]+R(?![A-Za-z0-9])").match(d, p)
                if r:
                    self.p = r.end()
                    return Ref((int(r.group(1)), int(r.group(2))))
            self.p = m.end()
            text = m.group().decode()
            return float(text) if "." in text else int(text)
        m = re.compile(rb"[^\x00\t\n\x0c\r ()<>\[\]{}/%]+").match(d, p)
        if not m:
            raise ValueError(f"unparsable byte at {p}: {d[p:p + 20]!r}")
        self.p = m.end()
        word = m.group().decode("latin-1")
        if word in ("true", "false"):
            return word == "true"
        if word == "null":
            return None
        return Op(word)

    def literal(self):
        d, p = self.d, self.p + 1
        out, depth = bytearray(), 1
        esc = {0x6e: 10, 0x72: 13, 0x74: 9, 0x62: 8, 0x66: 12, 0x28: 0x28, 0x29: 0x29, 0x5c: 0x5c}
        while True:
            c = d[p]
            if c == 0x5c:
                n = d[p + 1]
                if n in esc:
                    out.append(esc[n])
                    p += 2
                elif 0x30 <= n <= 0x37:
                    m = re.compile(rb"[0-7]{1,3}").match(d, p + 1)
                    out.append(int(m.group(), 8) & 255)
                    p = m.end()
                elif n in (0x0a, 0x0d):
                    p += 3 if d[p + 1:p + 3] == b"\r\n" else 2
                else:
                    out.append(n)
                    p += 2
                continue
            if c == 0x28:
                depth += 1
            elif c == 0x29:
                depth -= 1
                if depth == 0:
                    self.p = p + 1
                    return bytes(out)
            out.append(c)
            p += 1


def mul(a, b):
    return (a[0] * b[0] + a[1] * b[2], a[0] * b[1] + a[1] * b[3],
            a[2] * b[0] + a[3] * b[2], a[2] * b[1] + a[3] * b[3],
            a[4] * b[0] + a[5] * b[2] + b[4], a[4] * b[1] + a[5] * b[3] + b[5])


GLYPHS = {
    "space": " ", "exclam": "!", "quotedbl": '"', "numbersign": "#", "dollar": "$", "percent": "%",
    "ampersand": "&", "quotesingle": "'", "parenleft": "(", "parenright": ")", "asterisk": "*",
    "plus": "+", "comma": ",", "hyphen": "-", "period": ".", "slash": "/", "zero": "0", "one": "1",
    "two": "2", "three": "3", "four": "4", "five": "5", "six": "6", "seven": "7", "eight": "8",
    "nine": "9", "colon": ":", "semicolon": ";", "less": "<", "equal": "=", "greater": ">",
    "question": "?", "at": "@", "bracketleft": "[", "backslash": "\\", "bracketright": "]",
    "asciicircum": "^", "underscore": "_", "grave": "`", "braceleft": "{", "bar": "|",
    "braceright": "}", "asciitilde": "~", "quoteleft": "‘", "quoteright": "’",
    "quotedblleft": "“", "quotedblright": "”", "endash": "–", "emdash": "—",
    "bullet": "•", "minus": "−", "multiply": "×", "periodcentered": "·",
    "fi": "fi", "fl": "fl", "ff": "ff", "ffi": "ffi", "ffl": "ffl", "prime": "′",
    "circleplus": "⊕", "logicaland": "∧", "logicalor": "∨", "logicalnot": "¬",
    "lessequal": "≤", "greaterequal": "≥", "notequal": "≠", "arrowright": "→",
    "arrowleft": "←", "element": "∈", "summation": "∑", "dotmath": "⋅",
    "ellipsis": "…", "section": "§", "copyright": "©", "degree": "°",
    "nbspace": " ", "dagger": "†", "radical": "√", "infinity": "∞",
}
for _i, _n in enumerate(("Alpha Beta Gamma Delta Epsilon Zeta Eta Theta Iota Kappa Lambda Mu Nu Xi Omicron Pi Rho "
                         "_ Sigma Tau Upsilon Phi Chi Psi Omega").split()):
    if _n != "_":
        GLYPHS[_n] = chr(0x391 + _i)
        GLYPHS[_n.lower()] = chr(0x3b1 + _i)
GLYPHS["sigma1"] = "ς"


def glyph(name):
    if len(name) == 1:
        return name
    if name in GLYPHS:
        return GLYPHS[name]
    m = re.fullmatch(r"uni([0-9A-F]{4})", name)
    if m:
        return chr(int(m.group(1), 16))
    raise ValueError(f"glyph name without a declared Unicode value: {name}")


class Font:
    def __init__(self, pdf, obj):
        self.name = str(obj.get("BaseFont", "?"))
        self.subtype = obj["Subtype"]
        self.two = self.subtype == "Type0"
        self.map, self.widths, self.default = {}, {}, 1000.0
        self.declared = None
        if "ToUnicode" in obj:
            self.cmap(pdf.stream(pdf.get(obj["ToUnicode"])))
        if self.two:
            if obj.get("Encoding") not in ("Identity-H",):
                raise ValueError(f"{self.name}: unsupported Type0 encoding {obj.get('Encoding')!r}")
            if "ToUnicode" not in obj:
                raise ValueError(f"{self.name}: Type0 font without ToUnicode")
            desc = pdf.get(pdf.get(obj["DescendantFonts"])[0])
            self.default = float(pdf.get(desc.get("DW", 1000)))
            w = pdf.get(desc.get("W", []))
            i = 0
            while i < len(w):
                first, second = w[i], pdf.get(w[i + 1])
                if isinstance(second, list):
                    for k, x in enumerate(second):
                        self.widths[first + k] = float(x)
                    i += 2
                else:
                    for code in range(first, second + 1):
                        self.widths[code] = float(w[i + 2])
                    i += 3
        else:
            first = pdf.get(obj.get("FirstChar", 0))
            for k, x in enumerate(pdf.get(obj.get("Widths", []))):
                self.widths[first + k] = float(pdf.get(x))
            desc = pdf.get(obj.get("FontDescriptor", {})) or {}
            self.default = float(desc.get("MissingWidth", 500))
            enc = pdf.get(obj.get("Encoding"))
            base = enc if isinstance(enc, Name) else (enc or {}).get("BaseEncoding")
            table = {}
            codec = {"WinAnsiEncoding": "cp1252", "MacRomanEncoding": "mac_roman"}.get(base)
            if codec:
                for code in range(32, 256):
                    try:
                        table[code] = bytes([code]).decode(codec)
                    except UnicodeDecodeError:
                        pass
            elif base is None:
                for code in range(32, 127):  # the ASCII range common to the built-in encodings
                    table[code] = chr(code)
            else:
                raise ValueError(f"{self.name}: unsupported base encoding {base}")
            if isinstance(enc, dict):
                code = 0
                for item in pdf.get(enc.get("Differences", [])):
                    if isinstance(item, int):
                        code = item
                    else:
                        table[code] = glyph(str(item))
                        code += 1
            self.declared = table

    def cmap(self, text):
        for block in re.findall(rb"beginbfchar(.*?)endbfchar", text, re.S):
            items = re.findall(rb"<([0-9A-Fa-f\s]*)>", block)
            for src, dst in zip(items[::2], items[1::2]):
                self.map[int(src, 16)] = bytes.fromhex(re.sub(rb"\s", b"", dst).decode()).decode("utf-16-be")
        for block in re.findall(rb"beginbfrange(.*?)endbfrange", text, re.S):
            for lo, hi, dst in re.findall(rb"<([0-9A-Fa-f]+)>\s*<([0-9A-Fa-f]+)>\s*(<[0-9A-Fa-f\s]*>|\[[^\]]*\])", block):
                lo, hi = int(lo, 16), int(hi, 16)
                if dst.startswith(b"["):
                    for k, item in enumerate(re.findall(rb"<([0-9A-Fa-f\s]*)>", dst)):
                        self.map[lo + k] = bytes.fromhex(re.sub(rb"\s", b"", item).decode()).decode("utf-16-be")
                else:
                    start = bytes.fromhex(re.sub(rb"\s", b"", dst[1:-1]).decode()).decode("utf-16-be")
                    for code in range(lo, hi + 1):
                        self.map[code] = start[:-1] + chr(ord(start[-1]) + code - lo)

    def decode(self, raw):
        """[(text, width in glyph units, is single-byte blank)]"""
        out = []
        step = 2 if self.two else 1
        for i in range(0, len(raw) - step + 1, step):
            code = int.from_bytes(raw[i:i + step], "big")
            if code in self.map:
                text = self.map[code]
            elif self.declared is not None and code in self.declared:
                text = self.declared[code]
            else:
                text = "\ufffd"  # no declared Unicode value: marked, never guessed
            out.append((text, self.widths.get(code, self.default), step == 1 and code == 32))
        return out


class PDF:
    def __init__(self, data):
        if b"/Encrypt" in data:
            raise ValueError("encrypted PDF")
        self.data, self.objects, self.fonts = data, {}, {}
        skip = 0
        for m in re.finditer(rb"(?<![0-9])(\d+)[\x00\t\n\x0c\r ]+(\d+)[\x00\t\n\x0c\r ]+obj(?![a-zA-Z])", data):
            if m.start() < skip:
                continue
            parser = Parser(data, m.end())
            value = parser.obj()
            parser.skip()
            if data[parser.p:parser.p + 6] == b"stream":
                start = parser.p + 6
                start += 2 if data[start:start + 2] == b"\r\n" else 1
                length = value.get("Length")
                if isinstance(length, int) and data[start + length:start + length + 20].lstrip(b"\r\n").startswith(b"endstream"):
                    end = start + length
                else:
                    end = data.index(b"endstream", start)
                    while end > start and data[end - 1] in b"\r\n":
                        end -= 1
                value = Stream(value, data[start:end])
                skip = end
            else:
                skip = parser.p
            self.objects[int(m.group(1))] = value
        for number, value in list(self.objects.items()):
            if isinstance(value, Stream) and value.dict.get("Type") == "ObjStm":
                body = self.stream(value)
                count, first = value.dict["N"], value.dict["First"]
                header = [int(x) for x in body[:first].split()]
                for k in range(count):
                    self.objects[header[2 * k]] = Parser(body, first + header[2 * k + 1]).obj()

    def get(self, value):
        seen = 0
        while isinstance(value, Ref):
            value = self.objects.get(value[0])
            seen += 1
            if seen > 50:
                raise ValueError("reference cycle")
        return value

    def stream(self, value):
        filters = self.get(value.dict.get("Filter", []))
        if isinstance(filters, Name):
            filters = [filters]
        data = value.raw
        for name in filters:
            if name != "FlateDecode":
                raise ValueError(f"unsupported stream filter {name}")
            data = zlib.decompress(data)
        if value.dict.get("DecodeParms") and self.get(value.dict["DecodeParms"]).get("Predictor", 1) != 1:
            raise ValueError("predictor on a content stream")
        return data

    def pages(self):
        root = [v for v in self.objects.values() if isinstance(v, dict) and v.get("Type") == "Catalog"]
        if len(root) != 1:
            raise ValueError("expected one document catalog")
        out = []

        def walk(node, inherited):
            node = self.get(node)
            res = self.get(node.get("Resources", inherited))
            if node.get("Type") == "Pages":
                for kid in self.get(node["Kids"]):
                    walk(kid, res)
            else:
                out.append((node, res))
        walk(root[0]["Pages"], {})
        return out

    def font(self, ref):
        key = ref if isinstance(ref, Ref) else id(ref)
        if key not in self.fonts:
            self.fonts[key] = Font(self, self.get(ref))
        return self.fonts[key]

    def content(self, node):
        contents = self.get(node.get("Contents", []))
        if isinstance(contents, Stream):
            contents = [contents]
        return b"\n".join(self.stream(self.get(c)) for c in contents)


class Page:
    def __init__(self, pdf):
        self.pdf, self.runs = pdf, []

    def run(self, data, resources, ctm):
        pdf = self.pdf
        fonts = pdf.get(resources.get("Font", {})) or {}
        xobjects = pdf.get(resources.get("XObject", {})) or {}
        parser = Parser(data, 0, content=True)
        stack, args = [], []
        tm = tlm = (1, 0, 0, 1, 0, 0)
        font, size, tc, tw, th, tl, rise = None, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0

        def show(raw):
            nonlocal tm
            for text, width, blank in font.decode(raw):
                m = mul((size * th, 0, 0, size, 0, rise), mul(tm, ctm))
                advance = (width / 1000.0 * size + tc + (tw if blank else 0.0)) * th
                end = mul((1, 0, 0, 1, advance, 0), mul(tm, ctm))
                scale = (m[2] ** 2 + m[3] ** 2) ** 0.5
                self.runs.append((m[4], m[5], end[4], scale, text))
                tm = mul((1, 0, 0, 1, advance, 0), tm)

        while True:
            try:
                item = parser.obj()
            except EOFError:
                break
            if not isinstance(item, Op):
                args.append(item)
                continue
            op = str(item)
            if op == "q":
                stack.append(ctm)
            elif op == "Q":
                if stack:
                    ctm = stack.pop()
            elif op == "cm":
                ctm = mul(tuple(args[-6:]), ctm)
            elif op == "BT":
                tm = tlm = (1, 0, 0, 1, 0, 0)
            elif op == "Tf":
                font, size = pdf.font(fonts[args[-2]]), float(args[-1])
            elif op == "Tc":
                tc = float(args[-1])
            elif op == "Tw":
                tw = float(args[-1])
            elif op == "Tz":
                th = float(args[-1]) / 100.0
            elif op == "TL":
                tl = float(args[-1])
            elif op == "Ts":
                rise = float(args[-1])
            elif op in ("Td", "TD"):
                if op == "TD":
                    tl = -float(args[-1])
                tm = tlm = mul((1, 0, 0, 1, args[-2], args[-1]), tlm)
            elif op == "Tm":
                tm = tlm = tuple(float(x) for x in args[-6:])
            elif op == "T*":
                tm = tlm = mul((1, 0, 0, 1, 0, -tl), tlm)
            elif op in ("Tj", "'", '"'):
                if op != "Tj":
                    if op == '"':
                        tw, tc = float(args[-3]), float(args[-2])
                    tm = tlm = mul((1, 0, 0, 1, 0, -tl), tlm)
                show(args[-1])
            elif op == "TJ":
                for part in args[-1]:
                    if isinstance(part, bytes):
                        show(part)
                    else:
                        tm = mul((1, 0, 0, 1, -float(part) / 1000.0 * size * th, 0), tm)
            elif op == "Do":
                target = pdf.get(xobjects.get(args[-1]))
                if isinstance(target, Stream) and target.dict.get("Subtype") == "Form":
                    matrix = tuple(float(x) for x in pdf.get(target.dict.get("Matrix", [1, 0, 0, 1, 0, 0])))
                    self.run(pdf.stream(target), pdf.get(target.dict.get("Resources", resources)), mul(matrix, ctm))
            elif op == "BI":
                end = parser.d.index(b"EI", parser.p)
                parser.p = end + 2
            args = []

    def text(self):
        lines, line = [], []
        base = last_end = last_scale = None
        for x, y, end, scale, text in self.runs:
            if base is None:
                base = y
            else:
                unit = max(scale, last_scale)
                if abs(y - base) > 0.6 * unit:
                    lines.append("".join(line))
                    line, base = [], y
                elif (x - last_end > 0.2 * unit or x < last_end - unit) and line and not line[-1].endswith(" ") \
                        and not text.startswith(" "):
                    line.append(" ")
            line.append(text)
            last_end, last_scale = end, scale
        lines.append("".join(line))
        return "\n".join(part.replace(" ", " ").rstrip() for part in lines)


def extract(data):
    pdf = PDF(data)
    pages = []
    for node, resources in pdf.pages():
        page = Page(pdf)
        page.run(pdf.content(node), resources, (1, 0, 0, 1, 0, 0))
        pages.append(page.text())
    return pdf, ("\n\f\n".join(pages) + "\n").encode("utf-8")


def main():
    pdf, text = extract(open(sys.argv[1], "rb").read())
    open(sys.argv[2], "wb").write(text)
    print(f"{text.count(bytes([12])) + 1} pages, {len(text)} bytes, {text.decode().count(chr(0xfffd))} undeclared codes")
    if "--fonts" in sys.argv:
        for font in pdf.fonts.values():
            print(font.name, font.subtype, "tounicode" if font.map else "declared")


if __name__ == "__main__":
    main()
