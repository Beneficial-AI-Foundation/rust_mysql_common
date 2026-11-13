import MysqlCommon

/-! Evidence for `Trusted.versionReCaptures_ascii` / `Trusted.mariadbVersionReCaptures_ascii`
(not part of the build; run from the repository root). `main.rs` prints, for each test
input, the captures of the crate's two regexes under the pinned `regex` 1.13.1; this
checks `Trusted.versionReMatch` and `Trusted.mariadbVersionReMatch` against them:

    cargo run --release --offline --manifest-path formal/trusted/evidence/RegexEval/Cargo.toml > /tmp/out.tsv
    cd formal && lake env lean --run trusted/evidence/RegexEval/Check.lean /tmp/out.tsv

Result (2026-11-13): `checked 621856, mismatches 0`. -/
open Aeneas Aeneas.Std mysql_common

def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87

def unhex (s : String) : List Std.U8 :=
  let cs := s.toList
  let rec go : List Char → List Std.U8
    | a :: b :: rest => (⟨BitVec.ofNat 8 (16 * hexVal a + hexVal b)⟩ : Std.U8) :: go rest
    | _ => []
  go cs

def hexOf (l : List Std.U8) : String :=
  String.join (l.map fun b =>
    let n := b.val
    let d (k : Nat) : Char := if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
    String.ofList [d (n / 16), d (n % 16)])

def render : Option (List Std.U8 × List Std.U8 × List Std.U8) → String
  | none => "-"
  | some (a, b, c) => hexOf a ++ "," ++ hexOf b ++ "," ++ hexOf c

def main (args : List String) : IO UInt32 := do
  let lines ← IO.FS.lines (args.getD 0 "out.tsv")
  let mut bad := 0
  let mut n := 0
  for l in lines do
    match l.splitOn "\t" with
    | [i, v, m] =>
      n := n + 1
      let bs := unhex i
      if render (Trusted.versionReMatch bs) != v || render (Trusted.mariadbVersionReMatch bs) != m then
        bad := bad + 1
        if bad ≤ 10 then IO.println s!"MISMATCH {i}: rust {v} {m}; lean {render (Trusted.versionReMatch bs)} {render (Trusted.mariadbVersionReMatch bs)}"
    | _ => pure ()
  IO.println s!"checked {n}, mismatches {bad}"
  return 0
