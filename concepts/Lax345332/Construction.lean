import Lax345332.ThreeFourSat

/-!
---
title: The reduction from satisfiability to (3,4)-satisfiability
type: definition
---
A CNF formula $F$ with $N$ literal occurrences over variables below $V$ is turned into a
(3,4) formula in two steps.

*Splitting.* The occurrence at position $p$ is replaced by a fresh variable $w_{v,p}$,
where $v$ is the variable occurring there. A clause becomes a chain through link variables
$z_p$: the clause $(l_0 \vee \dots \vee l_{L-1})$ becomes
$(l_0 \vee z_0), (\bar z_0 \vee l_1 \vee z_1), \dots, (\bar z_{L-2} \vee l_{L-1})$, and an
empty clause stays empty. For every $v$ the implications $w_{v,p+1} \to w_{v,p}$, taken
cyclically over all positions, force the copies of $v$ to agree. Clauses now have at most
three literals and every variable occurs at most three times.

*Padding.* Every clause with fewer than three literals is filled with literals $\bar y$,
each on a fresh variable $y$ that a private copy of Tovey's gadget forces to be true. The
gadget has thirteen clauses on $y$ and nine further variables; $y$ occurs three times in
it and every other variable four times.

The reduction on words decodes a formula, applies the two steps and encodes the result; a
word that encodes no formula is treated as the formula with one empty clause.

# Formalization notes

All copies $w_{v,p}$ with $v < V$ and $p < N$ are created and tied together, not only those
of pairs that occur. This makes the cyclic successor of a position simply the next
position, at the cost of an output of quadratic size.
-/

namespace Lax345332.Construction

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime Lax345332.ThreeFourSat

-- The gadget

/-- Tovey's thirteen clauses on the variables `g, g+1, …, g+9`; they force `g` to be true. -/
def gadget (g : ℕ) : Formula :=
  let y := g
  let a (j : ℕ) := g + 1 + 3 * j
  let b (j : ℕ) := g + 2 + 3 * j
  let d (j : ℕ) := g + 3 + 3 * j
  ((List.range 3).map fun j => [⟨y, true⟩, ⟨a j, true⟩, ⟨b j, true⟩]) ++
  ((List.range 3).flatMap fun j =>
    [[⟨d j, true⟩, ⟨a j, true⟩, ⟨b j, false⟩], [⟨d j, true⟩, ⟨a j, false⟩, ⟨b j, true⟩],
     [⟨d j, true⟩, ⟨a j, false⟩, ⟨b j, false⟩]]) ++
  [[⟨d 0, false⟩, ⟨d 1, false⟩, ⟨d 2, false⟩]]

-- Padding

/-- The base of the `t`-th gadget of the `k`-th clause, above the variables below `B`. -/
def ybase (B k t : ℕ) : ℕ := B + 30 * k + 10 * t

/-- The padding literals of a clause of length `n`. -/
def pads (B k n : ℕ) : Clause := (List.range (3 - n)).map fun t => ⟨ybase B k t, false⟩

/-- The `k`-th clause, padded, with its three gadgets. -/
def unit (B k : ℕ) (C : Clause) : Formula :=
  (C ++ pads B k C.length) ::
    (gadget (ybase B k 0) ++ gadget (ybase B k 1) ++ gadget (ybase B k 2))

/-- The padded formula. -/
def pad (B : ℕ) (G : Formula) : Formula :=
  (List.range G.length).flatMap fun k => unit B k (G.getD k [])

-- Splitting

/-- The copy of the variable `v` at position `p`. -/
def wv (V v p : ℕ) : ℕ := v + p * V

/-- The link variable after position `p`. -/
def zv (V N p : ℕ) : ℕ := V * N + p

def dflt : Literal := ⟨0, false⟩

/-- The `i`-th clause of the chain of `C`, whose first literal sits at position `o`. -/
def chainClause (V N o : ℕ) (C : Clause) (i : ℕ) : Clause :=
  (if i = 0 then [] else [⟨zv V N (o + i - 1), false⟩]) ++
    [⟨wv V (C.getD i dflt).index (o + i), (C.getD i dflt).positive⟩] ++
    (if i + 1 = C.length then [] else [⟨zv V N (o + i), true⟩])

def chainClauses (V N o : ℕ) (C : Clause) : Formula :=
  if C.length = 0 then [[]] else (List.range C.length).map (chainClause V N o C)

def chains (V N : ℕ) : ℕ → Formula → Formula
  | _, [] => []
  | o, C :: F => chainClauses V N o C ++ chains V N (o + C.length) F

/-- The cyclic successor on positions. -/
def next (N p : ℕ) : ℕ := if p + 1 < N then p + 1 else 0

/-- The implications `w v (next p) → w v p`. -/
def cycles (V N : ℕ) : Formula :=
  (List.range (V * N)).map fun k => [⟨k, true⟩, ⟨wv V (k % V) (next N (k / V)), false⟩]

/-- The number of literal occurrences. -/
def size (F : Formula) : ℕ := (F.map List.length).sum

/-- A strict bound on the variables. -/
def bound : Formula → ℕ
  | [] => 1
  | C :: F => max (C.foldr (fun l b => max (l.index + 1) b) 1) (bound F)

def split (F : Formula) : Formula :=
  chains (bound F) (size F) 0 F ++ cycles (bound F) (size F)

-- The reduction

/-- The reduction on formulas. -/
def transform (F : Formula) : Formula := pad (bound F * size F + size F) (split F)

/-- The formula a word stands for. -/
def parseF (w : Word) : Formula := (decodeCNF w).getD [[]]

/-- The reduction on words. -/
def reduce (w : Word) : Word := encodeCNF (transform (parseF w))

/-- The image is a (3,4) formula. -/
axiom transform_isThreeFour (F : Formula) : IsThreeFour (transform F)

/-- The image is satisfiable exactly when the formula is. -/
axiom transform_sat (F : Formula) : Satisfiable F ↔ Satisfiable (transform F)

/-- The reduction on words is correct. -/
axiom reduce_correct (w : Word) : w ∈ Lax429075.Satisfiability.SAT ↔ reduce w ∈ SAT34

/-- The reduction on words is computable in polynomial time. -/
axiom reduce_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduce)

end Lax345332.Construction
