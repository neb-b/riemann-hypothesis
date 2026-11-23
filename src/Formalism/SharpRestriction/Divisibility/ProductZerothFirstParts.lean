module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.MainNotions.product_zeroth_first_parts

open Formalism.BasicNotions

def rootsPrimeTo (l : ℕ) [Fact l.Prime] : Set ℂ_[l] :=
  {ζ | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1}

def Wfrac (l : ℕ) [Fact l.Prime] : Subalgebra ℚ_[l] ℂ_[l] :=
  (Algebra.adjoin ℚ_[l] (rootsPrimeTo l)).topologicalClosure

def Wint (l : ℕ) [Fact l.Prime] : Set ℂ_[l] := {x | x ∈ Wfrac l ∧ ‖x‖ ≤ 1}

def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

def gam (l : ℕ) : ℝ := (l : ℝ) / ((l : ℝ) ^ 2 - 1)

def expS (K : Type*) [Field K] [CharZero K] {τ : Type*} (f : MvPowerSeries τ K) : MvPowerSeries τ K :=
  PowerSeries.subst f (PowerSeries.exp K)

section Be

variable (l d : ℕ) [Fact l.Prime] [NeZero d]

def bideg (m : ZMod d →₀ ℕ) : ℕ × ℕ :=
  (m.sum fun s n => if Even s.val then n else 0, m.sum fun s n => if Even s.val then 0 else n)

def B1 (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ m, MvPowerSeries.coeff m be ∈ Wfrac l

def twist (u : ℂ_[l]) (s : ZMod d) : ℂ_[l] :=
  if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹

def B2 (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 → ∀ m : ZMod d →₀ ℕ,
    MvPowerSeries.coeff m be * (m.prod fun s n => twist l d u s ^ n) = MvPowerSeries.coeff m be

def B3 (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ m : ZMod d →₀ ℕ, MvPowerSeries.coeff m be ≠ 0 →
    (bideg d m).1 ≠ 0 ∧ (bideg d m).2 ≠ 0 ∧ bideg d m ≠ (1, 1)

def cobX (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l] :=
  MvPowerSeries.subst (fun s : ZMod d => if Even s.val then
      (MvPowerSeries.X (s, 0) + MvPowerSeries.X (s, 1) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])
      else MvPowerSeries.X (s, 0)) be -
    MvPowerSeries.subst (fun s : ZMod d => (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) be -
    MvPowerSeries.subst (fun s : ZMod d => if Even s.val then
      (MvPowerSeries.X (s, 1) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l]) else MvPowerSeries.X (s, 0)) be

def cobY (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l] :=
  MvPowerSeries.subst (fun s : ZMod d => if Even s.val then
      (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])
      else MvPowerSeries.X (s, 0) + MvPowerSeries.X (s, 1)) be -
    MvPowerSeries.subst (fun s : ZMod d => (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) be -
    MvPowerSeries.subst (fun s : ZMod d => if Even s.val then
      (MvPowerSeries.X (s, 0) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l]) else MvPowerSeries.X (s, 1)) be

def OverWOne {τ : Type*} (f : MvPowerSeries τ ℂ_[l]) : Prop :=
  (∀ m, MvPowerSeries.coeff m f ∈ Wint l) ∧ MvPowerSeries.constantCoeff f = 1

def B4 (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  OverWOne l (MvPowerSeries.subst (jetLogG l d (β := Fin 2)) (expS ℂ_[l] (cobX l d be))) ∧
    OverWOne l (MvPowerSeries.subst (jetLogG l d (β := Fin 2)) (expS ℂ_[l] (cobY l d be)))

end Be

section Kmap

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def minorXZ (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
    MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def Gxz (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen c) (I s c)

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((AddMonoidAlgebra.coeff P μ : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def KvalGe (l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ) : Prop :=
  ∀ (I : ColChoice N1 nu) (m : Lt × ℕ × Fin N0 →₀ ℕ),
    ‖AddMonoidAlgebra.coeff (applyAt0 N0 N1 l Th (Gxz N0 N1 nu I)) m‖ ≤ (l : ℝ) ^ (-B)

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

def ExpansionCoeffValuationGe (l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ) : Prop :=
  ∀ I : ColChoice N1 nu, ∃ c : ColChoice N0 nu →₀ ℂ_[l], (∀ J, ‖c J‖ ≤ (l : ℝ) ^ (-B)) ∧
    applyAt0 N0 N1 l Th (Gxz N0 N1 nu I) =
      c.sum fun J a => a • MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)

end Kmap

structure Loc where

  J : Formalism.BasicNotions.JetLoc

  rank_lt_alt : J.N0 < J.N1

  nu : ZMod J.d → YoungDiagram
  nu_rows : ∀ s, (nu s).colLen 0 ≤ J.N0

  TT : Finset (ZMod J.d)

namespace Loc

variable (L : Loc)

abbrev l : ℕ := L.J.l

abbrev d : ℕ := L.J.d

abbrev N0 : ℕ := L.J.N0

abbrev N1 : ℕ := L.J.N1

abbrev Th : MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l] := L.J.Th

def A (s : ZMod L.d) : ℕ := (L.nu s).rowLen 0

def size (s : ZMod L.d) : ℕ := (L.nu s).cells.card

def cap (s : ZMod L.d) : ℕ := if s ∈ L.TT then (L.nu s).rowLen 1 else (L.nu s).rowLen 0

def Dl (s : ZMod L.d) : ℕ := if s ∈ L.TT then L.size s - L.A s else L.size s

def dTop (s : ZMod L.d) : ℕ∞ := ⨅ (e : ℕ) (_ : Odd e ∧ s + (e : ZMod L.d) ∈ L.TT), (e : ℕ∞)

def Wc (s : ZMod L.d) : ℕ :=
  sSup {c : ℕ | ∃ i : ℕ, Odd i ∧ L.l ^ i ≤ L.size (s - (i : ZMod L.d)) ∧ c = L.cap (s - (i : ZMod L.d))}

def topTerm (s : ZMod L.d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ (e : ℕ∞) < L.dTop s then
      max ((L.A s : ℝ) / (L.l : ℝ) ^ e - (L.cap (s + (e : ZMod L.d)) : ℝ)) 0
    else if Odd e ∧ L.dTop s < (e : ℕ∞) then (L.A s : ℝ) / (L.l : ℝ) ^ e
    else 0

def baseTerm (s : ZMod L.d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ (e : ℕ∞) ≠ L.dTop s then
      max ((((L.nu s).rowLen 0 : ℝ) - ((L.nu s).rowLen 1 : ℝ)) / (L.l : ℝ) ^ e -
        (L.cap (s + (e : ZMod L.d)) : ℝ)) 0
    else 0

def FD : ℝ := lpF L.l L.d (fun s => (L.Dl s : ℝ))

def Tht (ep : ℂ_[L.l]) : MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l] :=
  MvPowerSeries.subst (fun v : ZMod L.d × Fin L.N0 × Fin L.N1 =>
    MvPowerSeries.C ep * jetLogG L.l L.d v) L.Th

def beSum (be : MvPowerSeries (ZMod L.d) ℂ_[L.l]) :
    MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l] :=
  ∑ a : Fin L.N0, ∑ b : Fin L.N1,
    MvPowerSeries.subst (fun s : ZMod L.d =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l])) be

def B0 (ep : ℂ_[L.l]) (be : MvPowerSeries (ZMod L.d) ℂ_[L.l]) : Prop :=
  ∃ sg : ℂ_[L.l], (sg = 1 ∨ sg = -1) ∧
    ∃ U : MvPowerSeries (ZMod L.d × Fin L.N0 × Fin L.N1) ℂ_[L.l],
      (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
      L.Tht ep = U * MvPowerSeries.subst (jetLogG L.l L.d (β := Fin L.N0 × Fin L.N1))
        (expS ℂ_[L.l] (sg • L.beSum be))

def AdmB : Prop :=
  ∃ ep : ℂ_[L.l], ‖ep‖ = 1 ∧ ∃ be : MvPowerSeries (ZMod L.d) ℂ_[L.l],
    L.B0 ep be ∧ B1 L.l L.d be ∧ B2 L.l L.d be ∧ B3 L.l L.d be ∧ B4 L.l L.d be

def HidaSetting (a : ℝ) : Prop :=
  (L.l : ℝ) ≤ a ∧ (∀ s, (L.size s : ℝ) ≤ a) ∧ 2 * Real.logb L.l a + 2 ≤ (L.N0 : ℝ) - 1

def ThmA (C : ℝ) : Prop :=
  ∀ a : ℝ, L.HidaSetting a →
    KvalGe L.N0 L.N1 L.l L.nu L.Th
      ((∑ s ∈ L.TT, (L.topTerm s - gam L.l * (L.Wc s : ℝ))) + L.FD -
        C * ((L.d : ℝ) * L.N0 * L.N1 * (Real.logb L.l a + 1)))

end Loc

structure Loc1 where

  J : Formalism.BasicNotions.JetLoc1

  rank_lt_alt : J.N0 < J.N1

  nu : YoungDiagram
  nu_rows : nu.colLen 0 ≤ J.N0

namespace Loc1

variable (L : Loc1)

abbrev l : ℕ := L.J.l

abbrev N0 : ℕ := L.J.N0

abbrev N1 : ℕ := L.J.N1

abbrev Th : MvPowerSeries (ZMod 1 × Fin L.N0 × Fin L.N1) ℂ_[L.l] := L.J.Th

def Tht (ep0 : ℂ_[L.l]) : MvPowerSeries (ZMod 1 × Fin L.N0 × Fin L.N1) ℂ_[L.l] :=
  MvPowerSeries.subst (fun v : ZMod 1 × Fin L.N0 × Fin L.N1 =>
    MvPowerSeries.C ep0 * jetLogG L.l 1 v) L.Th

def B0 (ep0 : ℂ_[L.l]) (be : MvPowerSeries (ZMod 2) ℂ_[L.l]) : Prop :=
  ∃ ep : ℂ_[L.l], ‖ep‖ = 1 ∧ ∃ sg : ℂ_[L.l], (sg = 1 ∨ sg = -1) ∧
    ∃ U : MvPowerSeries (ZMod 1 × Fin L.N0 × Fin L.N1) ℂ_[L.l],
      (∀ m, ‖MvPowerSeries.coeff m U‖ ≤ 1) ∧
      L.Tht ep0 = U * MvPowerSeries.subst (jetLogG L.l 1 (β := Fin L.N0 × Fin L.N1))
        (expS ℂ_[L.l] ((sg / 2) • ∑ a : Fin L.N0, ∑ b : Fin L.N1,
          MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
              (MvPowerSeries.X (0, a, b) : MvPowerSeries (ZMod 1 × Fin L.N0 × Fin L.N1) ℂ_[L.l])
            else MvPowerSeries.C ep * MvPowerSeries.X (0, a, b)) be))

def AdmB : Prop :=
  ∃ ep0 : ℂ_[L.l], ‖ep0‖ = 1 ∧ ∃ be : MvPowerSeries (ZMod 2) ℂ_[L.l],
    L.B0 ep0 be ∧ B1 L.l 2 be ∧ B2 L.l 2 be ∧ B3 L.l 2 be ∧ B4 L.l 2 be

def HidaSetting (a : ℝ) : Prop :=
  (L.l : ℝ) ≤ a ∧ (L.nu.cells.card : ℝ) ≤ a

def ThmOne (C : ℝ) : Prop :=
  ∀ a : ℝ, L.HidaSetting a →
    KvalGe L.N0 L.N1 L.l (fun _ : ZMod 1 => L.nu) L.Th
      (rho L.l * (L.nu.cells.card : ℝ) - C * ((L.N0 : ℝ) * L.N1 * (Real.logb L.l a + 1)))

end Loc1

structure Prov (D : Formalism.BasicNotions.D7) where

  nu : ∀ i : D.jet.Sit, ZMod (D.jet.loc i).d → YoungDiagram
  nu_rows : ∀ i s, (nu i s).colLen 0 ≤ (D.jet.loc i).N0

  TT : ∀ i : D.jet.Sit, Finset (ZMod (D.jet.loc i).d)

  nu1 : D.jet.Sit1 → YoungDiagram
  oneLetterPartitionColumnBound : ∀ i, (nu1 i).colLen 0 ≤ (D.jet.loc1 i).N0

theorem N_pred_lt (R : Formalism.BasicNotions.Ranks) (j : ℕ) (h : 1 ≤ j) : R.N (j - 1) < R.N j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Formalism.BasicNotions.Ranks.N, Nat.add_sub_cancel]
  nlinarith [Nat.zero_le R.t]

theorem N_even (R : Formalism.BasicNotions.Ranks) (j : ℕ) : Even (R.N j) := by
  unfold Formalism.BasicNotions.Ranks.N
  exact R.k_even.add (R.t_odd.add_one.mul_left j)

section OneRecord

variable (D : Formalism.BasicNotions.D7) (X : Prov D)

end OneRecord

abbrev ProvF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Type :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Prov (Fm.D x i)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ProvF Fm)

end Family

end Formalism.MainNotions.product_zeroth_first_parts

end
