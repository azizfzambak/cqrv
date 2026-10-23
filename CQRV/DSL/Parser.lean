module

public import CQRV.DSL.Diagnostic

/-!
# CQRV.DSL.Parser

Report §7.1.4 — a hand-written lexer and recursive-descent parser for the concrete syntax of
the DSL (with the reviewer's `loop … while` and calls). Comments are `--` to end of line.

Precedence, loosest first: `or` < `xor` < `and` < `not` < atoms. Binary operators associate
to the left (`b0 and b3 and b7` is `(b0 and b3) and b7`, as in §7.2.3). `let`, `if`, `for`,
`loop` are atoms whose last sub-expression extends as far right as possible.

Both functions are total: the lexer and the parser run on fuel bounded by the input size
(DECISIONS.md 2026-10-23, Stage 3 interpretations).
-/

@[expose] public section

namespace CQRV.DSL

/-- Report §7.1.4 — lexical tokens. Keywords are `ident`s listed in `keywords`. -/
inductive Tok where
  | ident (s : String)
  | num (n : Nat)
  | sym (s : String)
  | eof
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.1.4 — a token with its source position. -/
structure Token where
  tok : Tok
  pos : Pos
  deriving Repr, Inhabited

/-- Report §7.1.4 — reserved words of the grammar (plus `loop`, `while`). -/
def keywords : List String :=
  ["fn", "let", "in", "for", "with", "do", "if", "then", "else", "not", "and", "or", "xor",
   "true", "false", "idx", "loop", "while", "Bool", "Vec", "Nat", "Unit"]

/-- Report §7.1.4 — a token as it appears in diagnostics. -/
def Tok.render : Tok → String
  | .ident s => s!"`{s}`"
  | .num n => s!"`{n}`"
  | .sym s => s!"`{s}`"
  | .eof => "end of input"

namespace Parser

def advancePos (p : Pos) (c : Char) : Pos :=
  if c = '\n' then ⟨p.line + 1, 1⟩ else ⟨p.line, p.col + 1⟩

def isIdStart (c : Char) : Bool := c.isAlpha || c = '_'
def isIdRest (c : Char) : Bool := c.isAlphanum || c = '_' || c = '\''

/-- Report §7.1.4 — symbols, longest first. -/
def symbols : List String :=
  ["..<", "->", "(", ")", "{", "}", "[", "]", ",", ":", "="]

def lexErr (p : Pos) (msg : String) : Diagnostic :=
  Diagnostic.at .parse .syntaxError p msg

/-- Lexer loop; `fuel` ≥ remaining characters (each step consumes at least one). -/
def lexAux : Nat → List Char → Pos → Array Token → Except Diagnostic (Array Token)
  | 0, _, p, _ => .error (lexErr p "lexer: out of fuel")
  | _ + 1, [], p, acc => .ok (acc.push ⟨.eof, p⟩)
  | fuel + 1, c :: cs, p, acc =>
    if c = ' ' || c = '\t' || c = '\r' || c = '\n' then
      lexAux fuel cs (advancePos p c) acc
    else if c = '-' && cs.head? = some '-' then
      let rest := cs.dropWhile (· ≠ '\n')
      lexAux fuel rest ⟨p.line, p.col + 1 + (cs.length - rest.length)⟩ acc
    else if isIdStart c then
      let w := cs.takeWhile isIdRest
      lexAux fuel (cs.drop w.length) ⟨p.line, p.col + 1 + w.length⟩
        (acc.push ⟨.ident (String.ofList (c :: w)), p⟩)
    else if c.isDigit then
      let w := cs.takeWhile Char.isDigit
      let n := (c :: w).foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0
      lexAux fuel (cs.drop w.length) ⟨p.line, p.col + 1 + w.length⟩ (acc.push ⟨.num n, p⟩)
    else
      match symbols.find? (fun s => (c :: cs).take s.length == s.toList) with
      | some s =>
        lexAux fuel ((c :: cs).drop s.length) ⟨p.line, p.col + s.length⟩
          (acc.push ⟨.sym s, p⟩)
      | none => .error (lexErr p s!"unexpected character `{c}`")

/-- Report §7.1.4 — tokenize a source text; the result ends with `Tok.eof`. -/
def lex (src : String) : Except Diagnostic (Array Token) :=
  let cs := src.toList
  lexAux (cs.length + 1) cs ⟨1, 1⟩ #[]

/-- Parser monad: the token array is read-only, the state is the current index. -/
abbrev P := ReaderT (Array Token) (StateT Nat (Except Diagnostic))

def peek : P Token := do
  let ts ← read
  let i ← get
  return ts[i]?.getD (ts.back?.getD ⟨.eof, ⟨1, 1⟩⟩)

def bump : P Unit := modify (· + 1)

def failAt {α : Type} (t : Token) (expected : String) : P α :=
  throw (Diagnostic.at .parse .syntaxError t.pos s!"expected {expected}, found {t.tok.render}")

def isKw (t : Token) (k : String) : Bool := t.tok == .ident k
def isSym (t : Token) (s : String) : Bool := t.tok == .sym s

/-- Consume keyword `k`, returning its position. -/
def expectKw (k : String) : P Pos := do
  let t ← peek
  if isKw t k then bump; return t.pos else failAt t s!"`{k}`"

/-- Consume symbol `s`, returning its position. -/
def expectSym (s : String) : P Pos := do
  let t ← peek
  if isSym t s then bump; return t.pos else failAt t s!"`{s}`"

/-- Consume a non-keyword identifier. -/
def expectIdent : P (Pos × String) := do
  let t ← peek
  match t.tok with
  | .ident s => if keywords.contains s then failAt t "an identifier" else bump; return (t.pos, s)
  | _ => failAt t "an identifier"

/-- Consume a natural-number literal. -/
def expectNum : P Nat := do
  let t ← peek
  match t.tok with
  | .num n => bump; return n
  | _ => failAt t "a natural-number literal"

/-- Report §7.1.4, `<type>`. -/
def parseTy : P Ty := do
  let t ← peek
  if isKw t "Bool" then bump; return .bool
  else if isKw t "Unit" then bump; return .unit
  else if isKw t "Nat" then bump; return .nat (← expectNum)
  else if isKw t "Vec" then
    bump
    let _ ← expectKw "Bool"
    return .vec (← expectNum)
  else failAt t "a type (`Bool`, `Vec Bool n`, `Nat n`, `Unit`)"

/-- Expression precedence levels, loosest first. -/
inductive Lvl where
  | or | xor | and | unary | atom
  deriving Repr, DecidableEq

/-- Report §7.1.4, `<expr>` at precedence level `lvl`. `fuel` bounds the recursion depth
(at most a constant number of levels between two consumed tokens). -/
def parseExprAt : Nat → Lvl → P Expr
  | 0, _ => do failAt (← peek) "a shallower expression (nesting limit reached)"
  | fuel + 1, lvl => do
    let binary (op : String) (next : Lvl) (mk : Pos → Expr → Expr → Expr) : P Expr := do
      let mut lhs ← parseExprAt fuel next
      for _ in List.range (← read).size do
        let t ← peek
        if isKw t op then
          bump
          lhs := mk t.pos lhs (← parseExprAt fuel next)
        else break
      return lhs
    match lvl with
    | .or => binary "or" .xor .or
    | .xor => binary "xor" .and .xor
    | .and => binary "and" .unary .and
    | .unary =>
      let t ← peek
      if isKw t "not" then bump; return .not t.pos (← parseExprAt fuel .unary)
      else parseExprAt fuel .atom
    | .atom =>
      let t ← peek
      let p := t.pos
      match t.tok with
      | .sym "(" =>
        bump
        let e ← parseExprAt fuel .or
        let _ ← expectSym ")"
        return e
      | .ident "true" => bump; return .lit p true
      | .ident "false" => bump; return .lit p false
      | .ident "idx" =>
        bump
        let _ ← expectSym "("
        let v ← parseExprAt fuel .or
        let _ ← expectSym ","
        let k ← peek
        let r ← match k.tok with
          | .num n => do bump; pure (IdxRef.lit k.pos n)
          | _ => do let (q, x) ← expectIdent; pure (IdxRef.var q x)
        let _ ← expectSym ")"
        return .idx p v r
      | .ident "let" =>
        bump
        let (_, x) ← expectIdent
        let _ ← expectSym "="
        let e₁ ← parseExprAt fuel .or
        let _ ← expectKw "in"
        return .letE p x e₁ (← parseExprAt fuel .or)
      | .ident "if" =>
        bump
        let c ← parseExprAt fuel .or
        let _ ← expectKw "then"
        let a ← parseExprAt fuel .or
        let _ ← expectKw "else"
        return .ite p c a (← parseExprAt fuel .or)
      | .ident "for" =>
        bump
        let (_, i) ← expectIdent
        let _ ← expectKw "in"
        let _ ← expectSym "["
        let lo ← peek
        if lo.tok != .num 0 then failAt lo "`0` (ranges are `[0 ..< n]`)"
        bump
        let _ ← expectSym "..<"
        let n ← expectNum
        let _ ← expectSym "]"
        let _ ← expectKw "with"
        let (_, acc) ← expectIdent
        let _ ← expectSym "="
        let init ← parseExprAt fuel .or
        let _ ← expectKw "do"
        return .forE p i n acc init (← parseExprAt fuel .or)
      | .ident "loop" =>
        bump
        let (_, acc) ← expectIdent
        let _ ← expectSym "="
        let init ← parseExprAt fuel .or
        let _ ← expectKw "while"
        let c ← parseExprAt fuel .or
        let _ ← expectKw "do"
        return .loopE p acc init c (← parseExprAt fuel .or)
      | .ident s =>
        if keywords.contains s then failAt t "an expression"
        bump
        if isSym (← peek) "(" then
          bump
          let mut args : Array Expr := #[]
          if !isSym (← peek) ")" then
            args := args.push (← parseExprAt fuel .or)
            for _ in List.range (← read).size do
              if isSym (← peek) "," then
                bump
                args := args.push (← parseExprAt fuel .or)
              else break
          let _ ← expectSym ")"
          return .call p s args.toList
        else return .var p s
      | _ => failAt t "an expression"

/-- Report §7.1.4, `fn <var>(<var>: <type>, …) -> <type> { <expr> }`. -/
def parseFn (fuel : Nat) : P FnDecl := do
  let p ← expectKw "fn"
  let (_, name) ← expectIdent
  let _ ← expectSym "("
  let mut params : Array Param := #[]
  if !isSym (← peek) ")" then
    for _ in List.range (← read).size do
      let (q, x) ← expectIdent
      let _ ← expectSym ":"
      params := params.push ⟨q, x, ← parseTy⟩
      if isSym (← peek) "," then bump else break
  let _ ← expectSym ")"
  let _ ← expectSym "->"
  let ret ← parseTy
  let _ ← expectSym "{"
  let body ← parseExprAt fuel .or
  let _ ← expectSym "}"
  return { pos := p, name, params := params.toList, ret, body }

/-- Report §7.1.4 — a program: one or more `fn`s, then end of input. -/
def parseProgram (fuel : Nat) : P Program := do
  let mut fns : Array FnDecl := #[]
  for _ in List.range (← read).size do
    if (← peek).tok == .eof then break
    fns := fns.push (← parseFn fuel)
  let t ← peek
  if t.tok != .eof then failAt t "`fn` or end of input"
  if fns.isEmpty then failAt t "at least one `fn`"
  return { fns := fns.toList }

end Parser

/-- Report §7.1.4 — `parse : String → Except Diagnostic Program` (stage `parse`). -/
def parse (src : String) : Except Diagnostic Program := do
  let ts ← Parser.lex src
  let (prog, _) ← (Parser.parseProgram (8 * ts.size + 8)).run ts |>.run 0
  return prog

end CQRV.DSL

end
