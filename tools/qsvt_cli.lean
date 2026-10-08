/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT
import Lean.Data.Json

/-!
# `qsvt`: command-line front end of the QSVT compiler (plan Phase 7 / CIRC-6)

"Write a program, get the cost report and the OpenQASM circuit."  This script is run by the
wrapper `tools/qsvt` as

```
lake env lean --run tools/qsvt_cli.lean <command> [options]
```

(no `lean_exe` target: the first run elaborates the script, later runs are faster).  Commands:

* `info <program> [--qubits n] [--pattern i=b,…]` : the report of `#qsvt_info` (LANG-1
  `QSVT.Lang.infoLines`) for a program written in the textual surface syntax
  `qsvt[φ₁,…] <p>`, `cheb[c₀,…] <p>`, `poly[a₀,…] <p>`, `iter[k] <step> <p>`, `U0`.
* `qasm <program> [--qubits n] [--pattern i=b,…]` : only the OpenQASM 3 program (CIRC-6
  `qasmOfWith`) of a single-step program `qsvt[Φ] U0`.
* `check --phases … [--target …] [--eps ε] [--depth n]` : evaluates the kernel-checkable
  certificate `QSVT.Certificate.checkRe` (CERT-B) in `IO` on rational data read from a solver
  JSON file (`tools/phases/examples/*.json`) or inline lists.  **Untrusted preview**: the trusted
  check is `decide +kernel` inside a Lean module, which `emit-cert` writes.
* `emit-cert … --name <Name>` : prints a Lean module declaring `<Name>Phases`, `<Name>Target`,
  `<Name>Eps`, `theorem <Name>_checkRe : checkRe … = true := by decide +kernel` and the derived
  `<Name>_phase_bound` in the shape of `QSVT.Certificate.sign21_phase_bound`.

Everything in this file is computable and untrusted (parsing and printing).  The theorems that
give the printed numbers their meaning live in the library (`queriesQ_eq`, `baseQ_eq`,
`checkRe_sound`, …).  The pure parts (`parseRat`, `parseProgram`, `parsePattern`, `parseArgs`)
are checked by the `#guard`s at the end of the file, which run whenever the script is elaborated.
-/

set_option autoImplicit false

namespace QSVT.Cli

open QSVT.Lang QSVT.Certificate Lean

/-! ### Rational numbers -/

/-- A nonempty string of decimal digits as a natural number (no `_` separators). -/
def digitsToNat? (s : String) : Option ℕ :=
  if s.isEmpty || !s.all Char.isDigit then none
  else some (s.foldl (fun acc c => 10 * acc + (c.toNat - '0'.toNat)) 0)

/-- `[+-]digits[.digits][e[+-]digits]` as an exact rational (`-0.25`, `1e-12`, `.5`, `3.`). -/
def parseDecimal (s : String) : Except String ℚ := do
  let (neg, body) :=
    if s.startsWith "-" then (true, (s.drop 1).copy)
    else if s.startsWith "+" then (false, (s.drop 1).copy)
    else (false, s)
  let (mant, expo) ← match body.toLower.splitOn "e" with
    | [m] => pure (m, (0 : ℤ))
    | [m, x] => do
      let (eneg, xs) :=
        if x.startsWith "-" then (true, (x.drop 1).copy)
        else if x.startsWith "+" then (false, (x.drop 1).copy)
        else (false, x)
      let some n := digitsToNat? xs | throw s!"malformed exponent in `{s}`"
      pure (m, if eneg then -(n : ℤ) else (n : ℤ))
    | _ => throw s!"malformed number `{s}`"
  let (ip, fp) ← match mant.splitOn "." with
    | [i] => pure (i, "")
    | [i, f] => pure (i, f)
    | _ => throw s!"malformed number `{s}`"
  if ip.isEmpty && fp.isEmpty then throw s!"malformed number `{s}`"
  let some i := (if ip.isEmpty then some 0 else digitsToNat? ip) | throw s!"malformed number `{s}`"
  let some f := (if fp.isEmpty then some 0 else digitsToNat? fp) | throw s!"malformed number `{s}`"
  let m : ℚ := ((i * 10 ^ fp.length + f : ℕ) : ℚ) / ((10 ^ fp.length : ℕ) : ℚ)
  let q : ℚ := if 0 ≤ expo then m * 10 ^ expo.toNat else m / 10 ^ (-expo).toNat
  pure (if neg then -q else q)

/-- A rational: a decimal (`parseDecimal`) or a fraction `p/q` of decimals. -/
def parseRat (s : String) : Except String ℚ := do
  let s := s.trimAscii.copy
  if s.isEmpty then throw "empty number"
  match s.splitOn "/" with
  | [a] => parseDecimal a
  | [a, b] =>
    let p ← (parseDecimal a.trimAscii.copy).mapError fun _ => s!"malformed rational `{s}`"
    let q ← (parseDecimal b.trimAscii.copy).mapError fun _ => s!"malformed rational `{s}`"
    if q = 0 then throw s!"zero denominator in `{s}`" else pure (p / q)
  | _ => throw s!"malformed rational `{s}`"

/-- A natural number. -/
def parseNat (s : String) : Except String ℕ :=
  match digitsToNat? s.trimAscii.copy with
  | some n => pure n
  | none => throw s!"expected a natural number, got `{s}`"

/-- A comma-separated rational list, optionally in brackets: `[1/2, -0.25]`. -/
def parseInlineList (s : String) : Except String (List ℚ) :=
  let s := s.trimAscii.copy
  let s := if s.startsWith "[" && s.endsWith "]" then ((s.drop 1).dropEnd 1).copy else s
  if s.trimAscii.copy.isEmpty then pure [] else (s.splitOn ",").mapM parseRat

/-- A rational as a Lean literal: an integer or `num / den`. -/
def ratLit (q : ℚ) : String := if q.den = 1 then toString q.num else s!"{q.num} / {q.den}"

/-- Bring `a > 0` into `[1, 10)` by powers of ten (fuel-bounded), returning the exponent. -/
def normalize10 : ℕ → ℚ → ℤ → ℚ × ℤ
  | 0, a, k => (a, k)
  | fuel + 1, a, k =>
    if 10 ≤ a then normalize10 fuel (a / 10) (k + 1)
    else if a < 1 then normalize10 fuel (a * 10) (k - 1)
    else (a, k)

/-- A rational in scientific notation with three decimals, e.g. `7.912e-14`. -/
def sciString (q : ℚ) : String :=
  if q = 0 then "0"
  else
    let (m, k) := normalize10 4000 |q| 0
    let sign := if q < 0 then "-" else ""
    let ms := Rat.toDecimalString m 3
    if ms == "10.000" then s!"{sign}1.000e{k + 1}" else s!"{sign}{ms}e{k}"

/-- Milliseconds as `s.mmm s`. -/
def msString (ms : ℕ) : String :=
  let frac := toString (ms % 1000)
  s!"{ms / 1000}.{String.ofList (List.replicate (3 - frac.length) '0')}{frac} s"

/-! ### The program parser -/

/-- Tokens of the surface syntax. -/
inductive Tok
  /-- An identifier (`U0`, `qsvt`, …). -/
  | ident (s : String)
  /-- A number, validated later by `parseRat`. -/
  | num (s : String)
  /-- `[` -/
  | lbrack
  /-- `]` -/
  | rbrack
  /-- `(` -/
  | lparen
  /-- `)` -/
  | rparen
  /-- `,` -/
  | comma
  deriving Repr, DecidableEq

/-- The source text of a token. -/
def Tok.render : Tok → String
  | .ident s => s
  | .num s => s
  | .lbrack => "["
  | .rbrack => "]"
  | .lparen => "("
  | .rparen => ")"
  | .comma => ","

/-- First character of a number token. -/
def isNumStart (c : Char) : Bool := c.isDigit || c == '-' || c == '+' || c == '.'

/-- Later characters of a number token. -/
def isNumChar (c : Char) : Bool := isNumStart c || c == '/' || c == 'e' || c == 'E'

/-- First character of an identifier. -/
def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

/-- Later characters of an identifier (`₀` so that `U₀` is one token). -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '₀'

/-- The tokenizer (fuel-bounded structural recursion; every step consumes a character). -/
def tokenize : ℕ → List Char → Except String (List Tok)
  | 0, _ => throw "tokenizer: out of fuel"
  | _, [] => pure []
  | fuel + 1, c :: cs =>
    if c.isWhitespace then tokenize fuel cs
    else if c == '[' then (Tok.lbrack :: ·) <$> tokenize fuel cs
    else if c == ']' then (Tok.rbrack :: ·) <$> tokenize fuel cs
    else if c == '(' then (Tok.lparen :: ·) <$> tokenize fuel cs
    else if c == ')' then (Tok.rparen :: ·) <$> tokenize fuel cs
    else if c == ',' then (Tok.comma :: ·) <$> tokenize fuel cs
    else if isIdentStart c then
      let w := cs.takeWhile isIdentChar
      (Tok.ident (String.ofList (c :: w)) :: ·) <$> tokenize fuel (cs.drop w.length)
    else if isNumStart c then
      let w := cs.takeWhile isNumChar
      (Tok.num (String.ofList (c :: w)) :: ·) <$> tokenize fuel (cs.drop w.length)
    else throw s!"unexpected character `{c}`"

/-- The content of a bracket after `[`: `q₀, q₁, …]`, returning the list and the rest. -/
def parseRatList : ℕ → List Tok → Except String (List ℚ × List Tok)
  | 0, _ => throw "parser: out of fuel"
  | _, .rbrack :: ts => pure ([], ts)
  | fuel + 1, .num s :: ts => do
    let q ← parseRat s
    match ts with
    | .comma :: ts' =>
      let (l, rest) ← parseRatList fuel ts'
      pure (q :: l, rest)
    | .rbrack :: ts' => pure ([q], ts')
    | t :: _ => throw s!"expected `,` or `]` after `{s}`, got `{t.render}`"
    | [] => throw "unterminated list: expected `]`"
  | _, t :: _ => throw s!"expected a number or `]`, got `{t.render}`"
  | _, [] => throw "unterminated list: expected `]`"

/-- A step `qsvt[Φ]`, `cheb[c]`, `poly[l]` or `iter[k] step`, as a program transformer. -/
def parseStep : ℕ → List Tok → Except String ((ExprQ → ExprQ) × List Tok)
  | 0, _ => throw "parser: out of fuel"
  | fuel + 1, .ident w :: .lbrack :: ts =>
    if w == "qsvt" || w == "cheb" || w == "poly" then do
      let (l, rest) ← parseRatList fuel ts
      let f : ExprQ → ExprQ :=
        if w == "qsvt" then ExprQ.qsvt l else if w == "cheb" then ExprQ.cheb l else ExprQ.poly l
      pure (f, rest)
    else if w == "iter" then
      match ts with
      | .num k :: .rbrack :: ts' => do
        let k ← parseNat k
        let (f, rest) ← parseStep fuel ts'
        pure (QSVT.Lang.iterate k f, rest)
      | _ => throw "iter[k] expects a natural number k"
    else throw s!"unknown step `{w}` (expected qsvt, cheb, poly or iter)"
  | _, .ident w :: _ => throw s!"expected `[` after `{w}`"
  | _, t :: _ => throw s!"unexpected `{t.render}` (expected a step or U0)"
  | _, [] => throw "unexpected end of input (expected a step or U0)"

/-- A program: steps applied to `U0`/`U₀`/`oracle`, or a parenthesised program. -/
def parseProgTokens : ℕ → List Tok → Except String (ExprQ × List Tok)
  | 0, _ => throw "parser: out of fuel"
  | _, .ident "U0" :: ts => pure (.oracle, ts)
  | _, .ident "U₀" :: ts => pure (.oracle, ts)
  | _, .ident "oracle" :: ts => pure (.oracle, ts)
  | fuel + 1, .lparen :: ts => do
    let (e, rest) ← parseProgTokens fuel ts
    match rest with
    | .rparen :: rest' => pure (e, rest')
    | _ => throw "expected `)`"
  | fuel + 1, ts@(.ident _ :: _) => do
    let (f, rest) ← parseStep fuel ts
    let (e, rest') ← parseProgTokens fuel rest
    pure (f e, rest')
  | _, [] => throw "unexpected end of input (expected a program ending in U0)"
  | _, t :: _ => throw s!"unexpected `{t.render}` (expected a step or U0)"

/-- The program parser: textual surface syntax to `QSVT.Lang.ExprQ`. -/
def parseProgram (s : String) : Except String ExprQ := do
  let ts ← tokenize (s.length + 1) s.toList
  let (e, rest) ← parseProgTokens (ts.length + 1) ts
  if rest.isEmpty then pure e
  else throw s!"trailing input after the program: `{" ".intercalate (rest.map Tok.render)}`"

/-- A control pattern `i=b, j=b', …` (`b ∈ {0, 1, false, true}`); `none` or empty is `Π = 1`. -/
def parsePattern (s : String) : Except String (List (ℕ × Bool)) :=
  let s := s.trimAscii.copy
  if s.isEmpty || s == "none" then pure []
  else (s.splitOn ",").mapM fun item =>
    match item.trimAscii.copy.splitOn "=" with
    | [i, b] => do
      let i ← parseNat i
      let b ← match b.trimAscii.copy with
        | "0" | "false" => pure false
        | "1" | "true" => pure true
        | _ => throw s!"control value must be 0 or 1 in `{item}`"
      pure (i, b)
    | _ => throw s!"control pattern entry `{item}` is not of the form i=b"

/-! ### Command-line arguments -/

/-- Parsed arguments: positional words and `--key value` / `--key=value` options. -/
structure Args where
  /-- Positional arguments in order. -/
  positional : List String
  /-- Options as `(key, value)` without the leading `--`; `--help`/`-h` is `("help", "")`. -/
  options : List (String × String)
  deriving Repr, DecidableEq

/-- Splits a word list into positional arguments and options. -/
def parseArgs : List String → Except String Args
  | [] => pure ⟨[], []⟩
  | a :: rest =>
    if a == "--help" || a == "-h" then do
      let r ← parseArgs rest
      pure ⟨r.positional, ("help", "") :: r.options⟩
    else if a.startsWith "--" then
      match (a.drop 2).copy.splitOn "=" with
      | [k] =>
        match rest with
        | v :: rest' => do
          let r ← parseArgs rest'
          pure ⟨r.positional, (k, v) :: r.options⟩
        | [] => throw s!"option `{a}` needs a value"
      | k :: vs => do
        let r ← parseArgs rest
        pure ⟨r.positional, (k, "=".intercalate vs) :: r.options⟩
      | [] => throw s!"malformed option `{a}`"
    else do
      let r ← parseArgs rest
      pure ⟨a :: r.positional, r.options⟩

/-- The value of option `k`, if given. -/
def Args.get? (a : Args) (k : String) : Option String := (a.options.find? (·.1 == k)).map (·.2)

/-- Rejects options outside `allowed`. -/
def checkOptions (a : Args) (allowed : List String) : Except String Unit :=
  match a.options.find? fun p => !(allowed.contains p.1) with
  | some (k, _) => throw s!"unknown option `--{k}` (allowed: {allowed.map ("--" ++ ·)})"
  | none => pure ()

/-- Is `s` a plain Lean identifier (letters, digits, `_`, `'`)? -/
def isLeanIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all fun d => d.isAlphanum || d == '_' || d == '\''

/-! ### The command monad -/

/-- Commands run in `IO` and fail with a message (printed to stderr, exit code `2`). -/
abbrev CliM := ExceptT String IO

/-- Lifts a pure parse result. -/
def liftE {α : Type} : Except String α → CliM α
  | .ok a => pure a
  | .error e => throw e

/-- The program given by the positional arguments (joined by spaces). -/
def programArg (cmd : String) (args : Args) : CliM ExprQ := do
  if args.positional.isEmpty then
    throw s!"{cmd}: missing program, e.g. \"qsvt[0.5,-0.3333] U0\" (see `qsvt help`)"
  liftE ((parseProgram (" ".intercalate args.positional)).mapError fun e => s!"{cmd}: {e}")

/-- `--qubits n` (default `1`) and `--pattern` (default `Π = |0…0⟩⟨0…0|`), checked against `n`. -/
def qubitsAndPattern (args : Args) : CliM ((n : ℕ) × List (Fin n × Bool)) := do
  let n ← match args.get? "qubits" with
    | some s => liftE ((parseNat s).mapError fun e => s!"--qubits: {e}")
    | none => pure 1
  match args.get? "pattern" with
  | none => pure ⟨n, zeroPattern n⟩
  | some s =>
    let l ← liftE ((parsePattern s).mapError fun e => s!"--pattern: {e}")
    match patternOfNat n l with
    | some cP => pure ⟨n, cP⟩
    | none => throw s!"--pattern: a control qubit index is not below --qubits n = {n} \
        (indices are 0-based)"

/-! ### Reading solver data (JSON or inline lists) -/

/-- Looks up `key` in a JSON value: at the top level, then inside nested objects (depth-bounded). -/
def findKey : ℕ → Json → String → Option Json
  | 0, _, _ => none
  | fuel + 1, .obj kvs, key =>
    match kvs.get? key with
    | some v => some v
    | none => kvs.foldl (fun acc _ v => acc <|> findKey fuel v key) none
  | _, _, _ => none

/-- A JSON element as an exact rational: a decimal string, a number, or an object
`{"num": p, "den_log2": k}` (dyadic `p / 2^k`) or `{"num": p, "den": q}`. -/
def jsonToRat (j : Json) : Except String ℚ :=
  match j with
  | .str s => parseRat s
  | .num n => pure (mkRat n.mantissa (10 ^ n.exponent))
  | .obj _ => do
    let num ← j.getObjValAs? Int "num"
    match j.getObjValAs? Nat "den_log2" with
    | .ok k => pure (mkRat num (2 ^ k))
    | .error _ =>
      match j.getObjValAs? Nat "den" with
      | .ok d => if d = 0 then throw "zero denominator in a JSON object" else pure (mkRat num d)
      | .error _ => throw s!"JSON object {j.compress} has neither `den_log2` nor `den`"
  | _ => throw s!"cannot read a rational from the JSON value {j.compress}"

/-- Keys tried for the phases (R-convention; the dyadic form is exact and preferred). -/
def phaseKeys : List String := ["phases_R_dyadic", "phases_R_decimal", "phases"]

/-- Keys tried for the target Chebyshev coefficients. -/
def targetKeys : List String := ["target_chebyshev_coeffs", "target_cheb_coeffs", "cheb_coeffs"]

/-- `path#key` → `(path, some key)`; otherwise `(spec, none)`. -/
def splitSpec (spec : String) : String × Option String :=
  match spec.splitOn "#" with
  | [p, k] => (p, some k)
  | _ => (spec, none)

/-- Reads a rational list from a JSON file (`path` or `path#key`) or from an inline list. -/
def loadRatList (what : String) (spec : String) (keys : List String) : CliM (List ℚ) := do
  let (path, key?) := splitSpec spec
  if ← System.FilePath.pathExists path then
    let text ← IO.FS.readFile path
    let j ← liftE ((Json.parse text).mapError fun e => s!"{what}: {path}: JSON parse error: {e}")
    let keys := match key? with | some k => [k] | none => keys
    let arr ← match j with
      | .arr a => pure a
      | _ =>
        match keys.findSome? (findKey 8 j) with
        | some (.arr a) => pure a
        | some v => throw s!"{what}: {path}: the value found is not an array: {v.compress}"
        | none => throw s!"{what}: {path}: none of the keys {keys} found (use {path}#<key>)"
    liftE ((arr.toList.mapM jsonToRat).mapError fun e => s!"{what}: {path}: {e}")
  else if spec.any (fun c => c == ',' || c == '[') || (parseRat spec).toOption.isSome then
    liftE ((parseInlineList spec).mapError fun e => s!"{what}: {e}")
  else
    throw s!"{what}: `{spec}` is neither an existing file nor an inline list such as 1/2,-0.25"

/-- The data of a phase certificate. -/
structure CertInput where
  /-- Reflection-convention phases. -/
  Φ : List ℚ
  /-- Target Chebyshev coefficients. -/
  t : List ℚ
  /-- Tolerance. -/
  ε : ℚ
  /-- Taylor depth of the `e^{iφ}` enclosures. -/
  depth : ℕ

/-- `--phases`, `--target` (default: the `--phases` file), `--eps` (default `10⁻¹²`), `--depth`
(default `30`). -/
def certInput (cmd : String) (args : Args) : CliM CertInput := do
  let some phSpec := args.get? "phases"
    | throw s!"{cmd}: --phases <file.json|list> is required"
  let tSpec ← match args.get? "target" with
    | some t => pure t
    | none =>
      let (path, _) := splitSpec phSpec
      if ← System.FilePath.pathExists path then pure path
      else throw s!"{cmd}: --target <file.json|list> is required when --phases is not a file"
  let Φ ← loadRatList "--phases" phSpec phaseKeys
  let t ← loadRatList "--target" tSpec targetKeys
  let ε ← match args.get? "eps" with
    | some s => liftE ((parseRat s).mapError fun e => s!"--eps: {e}")
    | none => pure ((1 : ℚ) / 10 ^ 12)
  let depth ← match args.get? "depth" with
    | some s => liftE ((parseNat s).mapError fun e => s!"--depth: {e}")
    | none => pure 30
  if Φ.isEmpty then throw "--phases: the phase list is empty"
  if ε ≤ 0 then throw s!"--eps: the tolerance must be positive, got {ratLit ε}"
  pure ⟨Φ, t, ε, depth⟩

/-! ### The emitted certificate module -/

/-- Appends `,` to every item but the last. -/
def withCommas : List String → List String
  | [] => []
  | [x] => [x]
  | x :: xs => (x ++ ",") :: withCommas xs

/-- Greedy line wrapping: the first line starts with `first`, later lines with `cont`. -/
def wrapItems (pieces : List String) (first cont : String) (width : ℕ) : List String :=
  let step := fun (acc : List String × String) (p : String) =>
    let (lines, cur) := acc
    let atStart := cur == first || cur == cont
    let cand := if atStart then cur ++ p else cur ++ " " ++ p
    if cand.length > width && !atStart then (lines ++ [cur], cont ++ p) else (lines, cand)
  let (lines, cur) := pieces.foldl step ([], first)
  lines ++ [cur]

/-- A rational list as a wrapped Lean literal (indented by two spaces). -/
def listLit (l : List ℚ) : String :=
  "\n".intercalate (wrapItems (withCommas (l.map ratLit)) "  [" "   " 98) ++ "]"

/-- The Lean module text of `emit-cert`, in the shape of `QSVT.Certificate.Sign21Phases`. -/
def certModule (name : String) (c : CertInput) : String :=
  let P := name ++ "Phases"
  let T := name ++ "Target"
  let E := name ++ "Eps"
  "\n".intercalate [
    "/-",
    "Copyright (c) 2026 shosonoda. All rights reserved.",
    "Released under MIT license as described in the file LICENSE.",
    "Authors: shosonoda",
    "-/",
    "import QSVT.Certificate.PhaseCheck",
    "import QSVT.SVT.RealPoly",
    "",
    "/-!",
    s!"# Kernel-checked QSP phases `{name}` (CERT-B; generated by `tools/qsvt emit-cert`)",
    "",
    s!"* `{P}` : {c.Φ.length} reflection-convention phases (exact rationals).",
    s!"* `{T}` : {c.t.length} Chebyshev coefficients of the target `∑ₖ tₖ Tₖ` (exact rationals).",
    s!"* `{name}_checkRe` : `checkRe {P} {T} {E} {c.depth} = true`,",
    s!"  checked by the Lean kernel (`decide +kernel`, Taylor depth `{c.depth}`): the only",
    "  numerics-dependent input.",
    s!"* `{name}_phase_bound` : by `checkRe_sound` and `eval_rePoly_ofReal` (SVT-8),",
    "  `‖Re[P_Φ̃](x) − (∑ₖ tₖ Tₖ)(x)‖ ≤ ε` on `[-1, 1]`,",
    s!"  with `ε = {ratLit c.ε} ≈ {sciString c.ε}`.",
    "",
    "`tools/qsvt check` evaluated the same Boolean in `IO` (untrusted preview); only the kernel",
    "proof below is trusted.",
    "-/",
    "",
    "namespace QSVT.Certificate",
    "",
    "open Polynomial QSVT.Poly QSVT.QSP QSVT.SVT",
    "",
    s!"/-- CERT-B. The {c.Φ.length} reflection-convention phases of `{name}` (exact rationals). -/",
    s!"def {P} : List ℚ :=",
    listLit c.Φ,
    "",
    s!"/-- CERT-B. The {c.t.length} Chebyshev coefficients of the target of `{name}`. -/",
    s!"def {T} : List ℚ :=",
    listLit c.t,
    "",
    "/-- CERT-B. The certified tolerance. -/",
    s!"def {E} : ℚ := {ratLit c.ε}",
    "",
    s!"theorem {P}_length : {P}.length = {c.Φ.length} := rfl",
    "",
    s!"theorem {T}_length : {T}.length = {c.t.length} := rfl",
    "",
    "/-- CERT-B. The phase certificate, checked by the Lean kernel (`decide +kernel`, Taylor",
    s!"depth `{c.depth}`). -/",
    s!"theorem {name}_checkRe :",
    s!"    checkRe {P} {T} {E} {c.depth} = true := by",
    "  decide +kernel",
    "",
    "/-- CERT-B. `‖Re[P_Φ̃](x) − (∑ₖ tₖ Tₖ)(x)‖ ≤ ε` on `[-1, 1]`, with",
    "`Re[P_Φ̃] = rePoly (qspPoly Φ̃).1` the polynomial realised by GSLW Cor 18 (SVT-8). -/",
    s!"theorem {name}_phase_bound :",
    "    ∀ x ∈ Set.Icc (-1 : ℝ) 1,",
    s!"      ‖(rePoly (qspPoly ({P}.map (↑))).1).eval (x : ℂ) -",
    s!"        (ChebC.target {T}).eval (x : ℂ)‖ ≤ {E} := by",
    "  intro x hx",
    "  rw [eval_rePoly_ofReal]",
    s!"  exact checkRe_sound {name}_checkRe x hx",
    "",
    "end QSVT.Certificate",
    ""]

/-! ### Commands -/

/-- The text of `qsvt help`. -/
def helpText : String :=
  "\n".intercalate [
    "qsvt: command-line front end of lean-qsvt (plan Phase 7 / CIRC-6).  Untrusted convenience",
    "layer: the theorems live in the Lean library; `check` is an IO preview of a kernel certificate.",
    "",
    "usage: tools/qsvt <command> [options]",
    "",
    "commands",
    "  info <program> [--qubits n] [--pattern i=b,...]",
    "      cost report (queries, ancilla, degree bound, scale, well-scaledness; gate counts and",
    "      OpenQASM 3 for single-step programs qsvt[...] U0), the text of #qsvt_info.",
    "  qasm <program> [--qubits n] [--pattern i=b,...]",
    "      the OpenQASM 3 program of a single-step program qsvt[...] U0 (nothing else on stdout).",
    "  check --phases <file.json|list> [--target <file.json|list>] [--eps 1e-12] [--depth 30]",
    "      evaluates QSVT.Certificate.checkRe on R-convention phases and a Chebyshev target;",
    "      prints true/false and the elapsed time; exit code 0 (true) / 1 (false).",
    "  emit-cert --phases ... [--target ...] [--eps ...] [--depth ...] --name <Name>",
    "      prints a Lean module with <Name>Phases, <Name>Target, <Name>Eps, the kernel certificate",
    "      <Name>_checkRe (decide +kernel) and <Name>_phase_bound; paste it into QSVT/Certificate/.",
    "  help",
    "",
    "program syntax (mirrors QSVT.Lang.Notation; steps nest to the right)",
    "  U0 | U₀                   the oracle encoding of A₀",
    "  qsvt[φ1,φ2,...] <p>       real-part QSVT step with phases (GSLW Cor 18)",
    "  cheb[c0,c1,...] <p>       Chebyshev-LCU step with Chebyshev coefficients",
    "  poly[a0,a1,...] <p>       Chebyshev-LCU step for the monomial polynomial ∑ aᵢ xⁱ",
    "  iter[k] <step> <p>        the step applied k times (QSVT.Lang.iterate)",
    "  numbers: integers, decimals (-0.25, 1e-3) and fractions (3/4), all exact rationals.",
    "",
    "options",
    "  --qubits n        system qubits of the OpenQASM output (default 1; ancilla is q[0])",
    "  --pattern i=b,... control pattern of Π, 0-based system qubit indices, e.g. 1=0,2=1",
    "                    (default: every qubit controlled on 0, Π = |0...0><0...0|; `none`: Π = 1)",
    "  --phases, --target",
    "                    a solver JSON file of tools/phases/examples (keys phases_R_dyadic,",
    "                    phases_R_decimal, target_chebyshev_coeffs; `file.json#key` picks a key),",
    "                    or an inline list 1/2,-0.25.  --target defaults to the --phases file.",
    "  --eps ε           tolerance of checkRe (default 1e-12)",
    "  --depth n         Taylor depth of the e^{iφ} enclosures in checkRe (default 30)",
    "",
    "exit codes: 0 success (check: true); 1 check: false; 2 usage or input error.",
    ""]

/-- `info`. -/
def cmdInfo (args : Args) : CliM UInt32 := do
  liftE (checkOptions args ["qubits", "pattern"])
  let prog ← programArg "info" args
  let ⟨n, cP⟩ ← qubitsAndPattern args
  IO.println ("\n".intercalate (infoLines prog n cP))
  return 0

/-- `qasm`. -/
def cmdQasm (args : Args) : CliM UInt32 := do
  liftE (checkOptions args ["qubits", "pattern"])
  let prog ← programArg "qasm" args
  let ⟨n, cP⟩ ← qubitsAndPattern args
  match qasmOfWith prog n cP with
  | some q =>
    IO.print q
    return 0
  | none =>
    throw s!"qasm: gate-level compilation is available for single-step programs qsvt[Φ] U0 \
      only (got `{prog}`)"

/-- `check`. -/
def cmdCheck (args : Args) : CliM UInt32 := do
  liftE (checkOptions args ["phases", "target", "eps", "depth"])
  let c ← certInput "check" args
  let t0 ← IO.monoMsNow
  let ok ← (IO.lazyPure fun _ => checkRe c.Φ c.t c.ε c.depth : IO Bool)
  let t1 ← IO.monoMsNow
  let bound ← (IO.lazyPure fun _ => ChebI.errBoundRe (ChebI.qspChebI c.depth c.Φ).1 c.t : IO ℚ)
  IO.println (if ok then "true" else "false")
  IO.println s!"checkRe Φ t ε depth = {ok}  (|Φ| = {c.Φ.length}, |t| = {c.t.length}, \
    ε = {ratLit c.ε} ≈ {sciString c.ε}, depth = {c.depth})"
  IO.println s!"interval bound errBoundRe ≈ {sciString bound} {if ok then "≤" else ">"} ε"
  IO.println s!"elapsed (checkRe, IO evaluation): {msString (t1 - t0)}"
  IO.println "note: untrusted preview; the trusted certificate is `decide +kernel` in a Lean \
    module (`qsvt emit-cert`)."
  return (if ok then 0 else 1)

/-- `emit-cert`. -/
def cmdEmitCert (args : Args) : CliM UInt32 := do
  liftE (checkOptions args ["phases", "target", "eps", "depth", "name"])
  let c ← certInput "emit-cert" args
  let some name := args.get? "name"
    | throw "emit-cert: --name <Name> is required (a Lean identifier such as demo)"
  unless isLeanIdent name do
    throw s!"emit-cert: `{name}` is not a Lean identifier (letters, digits, _ and ')"
  IO.print (certModule name c)
  return 0

/-- Dispatch on the subcommand. -/
def run : List String → CliM UInt32
  | [] => do
    IO.eprintln helpText
    return 2
  | cmd :: rest => do
    let args ← liftE (parseArgs rest)
    if args.get? "help" |>.isSome then
      IO.println helpText
      return 0
    match cmd with
    | "help" | "--help" | "-h" =>
      IO.println helpText
      return 0
    | "info" => cmdInfo args
    | "qasm" => cmdQasm args
    | "check" => cmdCheck args
    | "emit-cert" => cmdEmitCert args
    | _ => throw s!"unknown command `{cmd}` (run `qsvt help`)"

/-! ### Checks of the pure parts (run whenever the script is elaborated) -/

#guard (parseRat "-0.25").toOption == some (-1 / 4 : ℚ)
#guard (parseRat "3/4").toOption == some (3 / 4 : ℚ)
#guard (parseRat "-3/4").toOption == some (-3 / 4 : ℚ)
#guard (parseRat "1e-12").toOption == some (1 / 10 ^ 12 : ℚ)
#guard (parseRat "1.5E3").toOption == some (1500 : ℚ)
#guard (parseRat ".5").toOption == some (1 / 2 : ℚ)
#guard (parseRat "3.").toOption == some (3 : ℚ)
#guard (parseRat "1.53285885035200664106014301069080829620361328125").toOption ==
  some (215730704601777 / 140737488355328 : ℚ)
#guard (parseRat "abc").toOption == none
#guard (parseRat "1/0").toOption == none
#guard (parseRat "1_0").toOption == none
#guard (parseRat "").toOption == none
#guard (parseRat "1.2.3").toOption == none

#guard (parseProgram "U0").toOption == some ExprQ.oracle
#guard (parseProgram " U₀ ").toOption == some ExprQ.oracle
#guard (parseProgram "qsvt[1/2,-1/3] U0").toOption == some (ExprQ.qsvt [1 / 2, -1 / 3] .oracle)
#guard (parseProgram "qsvt[0.5, -0.3333] poly[0,-3,0,4] U₀").toOption ==
  some (ExprQ.qsvt [1 / 2, -3333 / 10000] (ExprQ.poly [0, -3, 0, 4] .oracle))
#guard (parseProgram "cheb[0,0,0,1] (U0)").toOption == some (ExprQ.cheb [0, 0, 0, 1] .oracle)
#guard (parseProgram "cheb[] U0").toOption == some (ExprQ.cheb [] .oracle)
#guard (parseProgram "iter[2] qsvt[1/2] U0").toOption == some (qsvtIter [1 / 2] 2)
#guard (parseProgram "iter[0] qsvt[1/2] U0").toOption == some ExprQ.oracle
#guard (parseProgram "qsvt[1/2]").toOption == none
#guard (parseProgram "qsvt[1/2] U0 U0").toOption == none
#guard (parseProgram "qsvt 1/2 U0").toOption == none
#guard (parseProgram "foo[1] U0").toOption == none
#guard (parseProgram "qsvt[1/x] U0").toOption == none
#guard (parseProgram "").toOption == none

#guard (parsePattern "1=0,2=1").toOption == some [(1, false), (2, true)]
#guard (parsePattern "none").toOption == some []
#guard (parsePattern "1=2").toOption == none
#guard (parseInlineList "[1/2, -0.25]").toOption == some [1 / 2, -1 / 4]
#guard (parseInlineList "").toOption == some []
#guard (parseArgs ["prog", "--qubits", "2", "--pattern=1=0", "-h"]).toOption ==
  some ⟨["prog"], [("qubits", "2"), ("pattern", "1=0"), ("help", "")]⟩
#guard (parseArgs ["--qubits"]).toOption == none
#guard ratLit (-3 / 4) == "-3 / 4"
#guard ratLit 5 == "5"
#guard sciString (1 / 10 ^ 12) == "1.000e-12"
#guard sciString 1500 == "1.500e3"
#guard msString 442 == "0.442 s"
#guard isLeanIdent "demo_1'" && !isLeanIdent "1demo" && !isLeanIdent "a-b"

end QSVT.Cli

/-- Entry point of `lake env lean --run tools/qsvt_cli.lean <args>`. -/
def main (args : List String) : IO UInt32 := do
  match ← (QSVT.Cli.run args).run with
  | .ok code => pure code
  | .error msg =>
    IO.eprintln s!"qsvt: {msg}"
    pure 2
