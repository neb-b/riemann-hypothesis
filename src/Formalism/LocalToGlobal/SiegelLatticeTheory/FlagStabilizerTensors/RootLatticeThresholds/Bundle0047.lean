module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.InfCharDSGOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.Bundle0001
public import Formalism.FormalDegreeBessel.FinalIO
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTFr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsKpp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoefCap
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf

def CoefCapAll : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)))
    (hHC : ∀ w, Formalism.QuantumDeterminants.IsHCParam (X.B.lam w))
    (hgap : ∀ w, ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h),
    CoefCap (carrierInT X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c ν' m₀ Θ TP A₀)

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem coefCap_carrierInT [hF : Fact CoefCapAll] (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)))
    (hHC : ∀ w, Formalism.QuantumDeterminants.IsHCParam (X.B.lam w))
    (hgap : ∀ w, ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h) :
    CoefCap (carrierInT X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c ν' m₀ Θ TP A₀) :=
  hF.out X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀ hb hHC hgap

end Formalism.L2.SG.Pf.CarrierT
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTParNums
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

theorem half_lt_int {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : a < b) : a + 1 / 2 ≤ b := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : z < n := by
    have : (z : ℚ) < n := by linarith
    exact_mod_cast this
  have : (z : ℚ) + 1 ≤ n := by exact_mod_cast this
  linarith

theorem int_lt_half {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : b < a) : b + 1 / 2 ≤ a := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : n ≤ z := by
    have : (n : ℚ) < z + 1 := by linarith
    have : n < z + 1 := by exact_mod_cast this
    omega
  have : (n : ℚ) ≤ z := by exact_mod_cast this
  linarith

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppIdx
section
noncomputable section

open Matrix Finset

namespace Formalism.L2.SG.Pf.KppIdx

open Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.Pf.AllRowsKpp

variable {s kk r : ℕ}

def xI (hr : r = kk + 2 * s + 1) (a : Fin s) : Fin r := ⟨a.1, by omega⟩
def wI (hr : r = kk + 2 * s + 1) (i : Fin kk) : Fin r := ⟨s + i.1, by omega⟩
def zI (hr : r = kk + 2 * s + 1) : Fin r := ⟨s + kk, by omega⟩
def yI (hr : r = kk + 2 * s + 1) (a : Fin s) : Fin r := ⟨s + kk + 1 + a.1, by omega⟩

theorem kind_cases (hr : r = kk + 2 * s + 1) (j : Fin r) :
    (∃ a, j = xI hr a) ∨ (∃ i, j = wI hr i) ∨ j = zI hr ∨ ∃ a, j = yI hr a := by
  rcases lt_or_ge j.1 s with h | h
  · exact Or.inl ⟨⟨j.1, h⟩, Fin.ext rfl⟩
  rcases lt_or_ge j.1 (s + kk) with h' | h'
  · exact Or.inr (Or.inl ⟨⟨j.1 - s, by omega⟩, Fin.ext (by show j.1 = s + (j.1 - s); omega)⟩)
  rcases eq_or_lt_of_le h' with h'' | h''
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by show j.1 = s + kk; omega))))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨j.1 - (s + kk + 1), by omega⟩,
      Fin.ext (by show j.1 = s + kk + 1 + (j.1 - (s + kk + 1)); omega)⟩))

variable {g : ℕ}

theorem jPred_of (hr : r = kk + 2 * s + 1) {N : Matrix (Fin r) (Fin r) (ZMod g)}
    (hlow : ∀ a b : Fin r, b < a → N a b = 0) (hdiag : ∀ a, N a a = 1) (hwz : ∀ i, N (wI hr i) (zI hr) = 0) :
    JPred kk s N := by
  refine ⟨fun a b => ⟨hlow a b, fun h => h ▸ hdiag a⟩, fun a ha1 ha2 => ?_⟩
  unfold entN
  rw [dite_eq_left ⟨by omega, by omega⟩]
  have := hwz ⟨a - s, by omega⟩
  simpa only [wI, zI, Nat.add_sub_of_le ha1] using this

theorem low_of {N : Matrix (Fin r) (Fin r) (ZMod g)} (hJ : JPred kk s N) (a b : Fin r) (h : b < a) : N a b = 0 :=
  (hJ.1 a b).1 h

theorem diag_of {N : Matrix (Fin r) (Fin r) (ZMod g)} (hJ : JPred kk s N) (a : Fin r) : N a a = 1 :=
  (hJ.1 a a).2 rfl

theorem inv_super {N N' : Matrix (Fin r) (Fin r) (ZMod g)} (hJ : JPred kk s N) (hJ' : JPred kk s N')
    (h1 : N * N' = 1) (i : ℕ) (hi : i + 1 < r) : entN N' i (i + 1) = -entN N i (i + 1) := by
  have e := congrFun (congrFun h1 ⟨i, by omega⟩) ⟨i + 1, hi⟩
  rw [Matrix.mul_apply, Matrix.one_apply_ne (by intro h; have := congrArg Fin.val h; simp at this)] at e
  have hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, hi⟩ := by intro h; have := congrArg Fin.val h; simp at this
  rw [Finset.sum_eq_add (⟨i, by omega⟩ : Fin r) ⟨i + 1, hi⟩ hne (fun c _ hc => ?_) (by simp) (by simp)] at e
  · rw [diag_of hJ, diag_of hJ', one_mul, mul_one] at e
    unfold entN
    rw [dite_eq_left ⟨by omega, hi⟩, dite_eq_left ⟨by omega, hi⟩]
    linear_combination e
  · rcases lt_or_gt_of_ne (show c.1 ≠ i from fun h => hc.1 (Fin.ext h)) with h | h
    · rw [low_of hJ _ _ (show c < ⟨i, by omega⟩ from h), zero_mul]
    · have : i + 1 < c.1 := by
        rcases lt_or_gt_of_ne (show c.1 ≠ i + 1 from fun h => hc.2 (Fin.ext h)) with h' | h'
        · omega
        · exact h'
      rw [low_of hJ' _ _ (show (⟨i + 1, hi⟩ : Fin r) < c from this), mul_zero]

def dN (s kk : ℕ) (ob : Bool) (j : ℕ) : ZMod g :=
  if s + kk + 1 ≤ j then (-1) ^ (j - (s + kk + 1))
  else if ob = false ∧ s ≤ j ∧ j < s + kk then (-1) ^ (j - s) else 1

theorem dN_sq (ob : Bool) (j : ℕ) : dN (g := g) s kk ob j * dN s kk ob j = 1 := by
  unfold dN
  split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]

theorem index_diag_isotropic (ob : Bool) {j : ℕ} (h : j < s) : dN (g := g) s kk ob j = 1 := by
  unfold dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.2.1 (by omega))]

theorem dN_wt {j : ℕ} (h1 : s ≤ j) (h2 : j < s + kk) : dN (g := g) s kk true j = 1 := by
  unfold dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.1 (by simp))]

theorem dN_wf {j : ℕ} (h1 : s ≤ j) (h2 : j < s + kk) : dN (g := g) s kk false j = (-1) ^ (j - s) := by
  unfold dN; rw [if_neg (by omega), if_pos ⟨rfl, h1, h2⟩]

theorem dN_add_eq_one (ob : Bool) : dN (g := g) s kk ob (s + kk) = 1 := by
  unfold dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.2.2 (by omega))]

theorem dN_y (ob : Bool) {j : ℕ} (h : s + kk + 1 ≤ j) : dN (g := g) s kk ob j = (-1) ^ (j - (s + kk + 1)) := by
  unfold dN; rw [if_pos h]

theorem neg_one_sq (i : ℕ) : ((-1 : ZMod g) ^ i) * (-1) ^ i = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

def dM (s kk : ℕ) (ob : Bool) : Matrix (Fin r) (Fin r) (ZMod g) := Matrix.diagonal fun j => dN s kk ob j.1

theorem dM_sq (ob : Bool) : dM (r := r) (g := g) s kk ob * dM s kk ob = 1 := by
  rw [dM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  exact dN_sq ob j.1

theorem entN_conj (ob : Bool) (N : Matrix (Fin r) (Fin r) (ZMod g)) (a b : ℕ) :
    entN (dM s kk ob * N * dM s kk ob) a b = dN s kk ob a * entN N a b * dN s kk ob b := by
  unfold entN
  split_ifs with h
  · simp [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
  · simp

theorem jPred_conj (hr : r = kk + 2 * s + 1) (ob : Bool) {N : Matrix (Fin r) (Fin r) (ZMod g)}
    (hJ : JPred kk s N) : JPred kk s (dM s kk ob * N * dM s kk ob) := by
  refine jPred_of hr (fun a b h => ?_) (fun a => ?_) (fun i => ?_)
  · simp only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [low_of hJ a b h]; ring
  · simp only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [diag_of hJ a, mul_one]
    exact dN_sq ob a.1
  · have := (hJ.2 (s + i.1) (by omega) (by omega))
    unfold entN at this
    rw [dite_eq_left ⟨by omega, by omega⟩] at this
    simp only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have e : N (wI hr i) (zI hr) = 0 := this
    rw [e]; ring

theorem sum_range_pred (f : ℕ → ZMod g) (n : ℕ) :
    ∑ a ∈ range n, (if a + 1 < n then f a else 0) = ∑ a ∈ range (n - 1), f a := by
  cases n with
  | zero => simp
  | succ t =>
    rw [Finset.sum_range_succ, if_neg (by omega), add_zero, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun a ha => by rw [Finset.mem_range] at ha; rw [if_pos (by omega)]

theorem sum_range_last (c : ZMod g) (n : ℕ) :
    ∑ a ∈ range n, (if a + 1 < n then 0 else c) = if 1 ≤ n then c else 0 := by
  cases n with
  | zero => simp
  | succ t =>
    rw [Finset.sum_range_succ, if_neg (by omega), if_pos (by omega)]
    rw [Finset.sum_eq_zero fun a ha => by rw [Finset.mem_range] at ha; rw [if_pos (by omega)], zero_add]

theorem phi_key (hr : r = kk + 2 * s + 1) (ob : Bool) {N N' : Matrix (Fin r) (Fin r) (ZMod g)}
    (hinv : ∀ i, i + 1 < r → entN N' i (i + 1) = -entN N i (i + 1)) :
    phiJ kk s (dM s kk ob * N * dM s kk ob) =
      (∑ a ∈ range s, (if a + 1 < s then entN N a (a + 1) + entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a))
        else entN N a (s + kk) - entN N' (s + kk) (s + kk + 1))) +
      ∑ i ∈ range kk, (if i + 1 < kk then (if ob then entN N (s + i) (s + i + 1)
        else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) else 0) := by
  have split1 : ∀ a ∈ range s, (if a + 1 < s then entN N a (a + 1) + entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a))
        else entN N a (s + kk) - entN N' (s + kk) (s + kk + 1)) =
      (if a + 1 < s then entN N a (a + 1) else 0) +
      (if a + 1 < s then entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a)) else 0) +
      (if a + 1 < s then 0 else entN N (s - 1) (s + kk) - entN N' (s + kk) (s + kk + 1)) := by
    intro a ha
    rw [Finset.mem_range] at ha
    split_ifs with h
    · ring
    · have : a = s - 1 := by omega
      subst this; ring
  rw [Finset.sum_congr rfl split1, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_range_pred, sum_range_pred,
    sum_range_last, sum_range_pred (fun i => if ob then entN N (s + i) (s + i + 1)
        else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) kk]

  have ry : ∑ a ∈ range (s - 1), entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a)) =
      -∑ i ∈ range (s - 1), entN N (s + kk + 1 + i) (s + kk + 2 + i) := by
    rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    have e1 : s + kk + 1 + (s - 2 - (s - 1 - 1 - a)) = s + kk + 1 + a := by omega
    have e2 : s + kk + 1 + (s - 1 - (s - 1 - 1 - a)) = s + kk + 1 + a + 1 := by omega
    rw [e1, e2, hinv _ (by omega), show s + kk + 1 + a + 1 = s + kk + 2 + a by omega]
  have rw' : ∑ i ∈ range (kk - 1), (if ob then entN N (s + i) (s + i + 1)
        else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) =
      (if ob then 1 else -1) * ∑ a ∈ range (kk - 1), entN N (s + a) (s + a + 1) := by
    cases ob
    · simp only [Bool.false_eq_true, if_false, neg_one_mul]
      rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_range] at ha
      have e1 : s + (kk - 2 - (kk - 1 - 1 - a)) = s + a := by omega
      have e2 : s + (kk - 1 - (kk - 1 - 1 - a)) = s + a + 1 := by omega
      rw [e1, e2, hinv _ (by omega)]
    · simp
  rw [ry, rw']
  unfold phiJ
  simp only [entN_conj]

  have hx : ∀ i ∈ range (s - 1), dN (g := g) s kk ob i * entN N i (i + 1) * dN s kk ob (i + 1) = entN N i (i + 1) := by
    intro i hi; rw [Finset.mem_range] at hi
    rw [index_diag_isotropic ob (by omega), index_diag_isotropic ob (by omega)]; ring
  have hy : ∀ i ∈ range (s - 1), dN (g := g) s kk ob (s + kk + 1 + i) * entN N (s + kk + 1 + i) (s + kk + 2 + i) *
      dN s kk ob (s + kk + 2 + i) = -entN N (s + kk + 1 + i) (s + kk + 2 + i) := by
    intro i hi
    rw [dN_y ob (by omega), dN_y ob (by omega)]
    have e1 : s + kk + 1 + i - (s + kk + 1) = i := by omega
    have e2 : s + kk + 2 + i - (s + kk + 1) = i + 1 := by omega
    rw [e1, e2, pow_succ]
    linear_combination (-(entN N (s + kk + 1 + i) (s + kk + 2 + i))) * neg_one_sq (g := g) i
  have hw : ∀ a ∈ range (kk - 1), dN (g := g) s kk ob (s + a) * entN N (s + a) (s + a + 1) * dN s kk ob (s + a + 1) =
      (if ob then 1 else -1) * entN N (s + a) (s + a + 1) := by
    intro a ha; rw [Finset.mem_range] at ha
    cases ob
    · rw [dN_wf (by omega) (by omega), dN_wf (by omega) (by omega)]
      have e1 : s + a - s = a := by omega
      have e2 : s + a + 1 - s = a + 1 := by omega
      rw [e1, e2, pow_succ]
      simp only [Bool.false_eq_true, if_false]
      linear_combination (-(entN N (s + a) (s + a + 1))) * neg_one_sq (g := g) a
    · rw [dN_wt (by omega) (by omega), dN_wt (by omega) (by omega)]
      simp
  rw [Finset.sum_congr rfl hx, Finset.sum_congr rfl hy, Finset.sum_congr rfl hw, ← Finset.mul_sum]
  by_cases hs : 1 ≤ s
  · rw [if_pos hs, if_pos hs]
    have h1 : dN (g := g) s kk ob (s - 1) = 1 := index_diag_isotropic ob (by omega)
    have h2 : dN (g := g) s kk ob (s + kk) = 1 := dN_add_eq_one ob
    have h3 : dN (g := g) s kk ob (s + kk + 1) = 1 := by rw [dN_y ob le_rfl]; simp
    rw [h1, h2, h3, hinv _ (by omega), Finset.sum_neg_distrib]
    ring
  · rw [if_neg hs, if_neg hs]
    have : s - 1 = 0 := by omega
    rw [this]
    simp

end Formalism.L2.SG.Pf.KppIdx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OoQuotOfNuQPin
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem hfF (w' : D.what₂.Word) (a : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (frm X w' D.host.rdE v b) =
      if b = a.castSucc then ((D.host.rdE : ℂ) ^ (D.R.rS - a.1))⁻¹ else 0 := by
  induction b using Fin.lastCases with
  | last =>
    rw [frm_last, hfz_v, if_neg (Fin.castSucc_ne_last a).symm]
  | cast b =>
    rw [frm_castSucc, hJs_r, hfe_v]
    by_cases h : b = a
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e)), mul_zero]

theorem coord_eq (hw : OkPt X u u' w) (c : FreeE w → ℂ) (p : FreeE w) :
    stCoordV X u' w (gamW X u u' w) v (yU X u u' w v c hw) p = c p := by
  unfold stCoordV
  set a' : Fin D.R.rS := ⟨p.1.1.1, by have := p.2.1; omega⟩ with ha'
  have hcs : a'.castSucc = p.1.1 := Fin.ext rfl
  have hT : uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) *ᵥ frm X u' D.host.rdE v p.1.2 =
      frm X u' D.host.rdE v p.1.2 + ∑ b', (Cw w c - 1) b' p.1.2 • frm X u' D.host.rdE v b' := by
    have h1 := T_sub X u u' w v hw c (frm X u' D.host.rdE v p.1.2)
    rw [sub_one_mulVec, ← G_eq, TG_comb X u u' w v hw c] at h1
    rw [← h1]; abel
  rw [hT, hJ_add_r', hJ_sum_r', hfF, if_neg (fun e => (ne_of_lt p.2.1) (by rw [← hcs, e]))]
  rw [Finset.sum_eq_single a'.castSucc]
  · rw [hfF, if_pos rfl, zero_add, hcs, Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_lt p.2.1), sub_zero,
      Cw_apply_free]
    have hrd : (D.host.rdE : ℂ) ^ (D.R.rS - a'.1) ≠ 0 :=
      pow_ne_zero _ (Complex.ofReal_ne_zero.2 (rdE_pos_c (D := D)).ne')
    rw [show p.1.1.1 = a'.1 from rfl]
    field_simp
  · intro b _ hb
    rw [hfF, if_neg hb, mul_zero]
  · simp

theorem continuous_yM (hw : OkPt X u u' w) :
    Continuous fun c : FreeE w → ℂ => Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) := by

  have hC : Continuous fun c : FreeE w → ℂ => Cw w c := by
    refine continuous_matrix fun i j => ?_
    simp only [Cw, Matrix.of_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
    · exact continuous_const

  have hdet : ∀ c : FreeE w → ℂ, (Cw w c).det = 1 := by
    intro c
    rw [Matrix.det_of_upperTriangular]
    · simp [Cw]
    · intro i j hij
      simp only [Cw, Matrix.of_apply]
      have hji : j < i := hij
      rw [if_neg (ne_of_gt hji), dite_eq_right (fun h => absurd h.1 (lt_asymm hji))]

  have hinv : Continuous fun c : FreeE w → ℂ => (Cw w c)⁻¹ := by
    have h : (fun c : FreeE w → ℂ => (Cw w c)⁻¹) = fun c => (Cw w c).adjugate := by
      funext c
      rw [Matrix.inv_def, hdet c, Ring.inverse_one, one_smul]
    rw [h]
    exact hC.matrix_adjugate
  unfold Yc Ymat Mm Am
  exact continuous_const.add ((((continuous_const.matrix_mul (Continuous.matrix_fromBlocks
    (((continuous_const.matrix_mul hinv).matrix_mul continuous_const).matrix_conjTranspose.sub continuous_const)
    continuous_const continuous_const (hC.sub continuous_const))).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_mul continuous_const)

theorem stVSec_holds : StVSec X u u' := by
  intro w hw v
  refine ⟨fun c => yU X u u' w v c hw, ?_, fun c => ⟨inN_u X u u' w v hw c, inN_u' X u u' w v hw c⟩,
    fun c => funext fun p => coord_eq X u u' w v hw c p⟩
  have hY := continuous_yM X u u' w v hw
  unfold yU mkUJ
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hY, ?_⟩) _
  exact (continuous_const.matrix_mul hY.matrix_conjTranspose).matrix_mul continuous_const

theorem ooQuot_of_nuQPin (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl :=
  ooQuot_geo X u u' νq hN (stRel_holds X u u') (stVGeo_of_sec X u u' (stVSec_holds X u u'))

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairAmpConstWd
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem ooIntAll_of (hWD : Formalism.L2.SG.WuDecay.WuDecay X) (w w' : D.what₂.Word) :
    OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w') :=
  Formalism.L2.SG.Closed.OOIntAllC_outright D X Y w w'
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w' (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Pf.fundExistsC_holds D X Y w w')

variable {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

theorem pvalForm_holds (hWD : Formalism.L2.SG.WuDecay.WuDecay X) : ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists_oi W hI (ooIntAll_of hWD) (Formalism.L2.SG.Pf.FibreEq.FibreCountEq_holds hF)

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

