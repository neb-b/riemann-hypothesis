module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
section
open NumberField Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

open Formalism.MainNotions.S

def gLie {n : ℕ} (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Formalism.REAL.inG ε X}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Formalism.REAL.inG] at *
    rw [conjTranspose_add, add_mul, mul_add]
    calc _ = (aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * a) + (bᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * b) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  zero_mem' := by simp [Formalism.REAL.inG]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Formalism.REAL.inG] at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, ha, smul_zero]

def expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_exp (X : Matrix (Fin n) (Fin n) ℂ)).unit, Formalism.REAL.f1alg_exp_inUJ ε X.1 X.2⟩

@[simp] theorem uMat_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) :
    uMat (expU X) = NormedSpace.exp (X : Matrix (Fin n) (Fin n) ℂ) := rfl

def IsONBasis {n m : ℕ} {ε : Fin n → Bool} (E : Fin m → gLie ε) : Prop :=
  (∀ i j, (((E i : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re =
      if i = j then 1 else 0) ∧
    Submodule.span ℝ (Set.range E) = ⊤

variable (B : RowsAut)

abbrev gInf : Type := ∀ v : InfinitePlace B.I.F, gLie (B.I.ε v)


open Classical in
def atPlace (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)) : gInf B := Pi.single v X

def orbit (E : gInf B) (w : B.Hs) (t : ℝ) : B.Hs := B.σs (fun v => expU (t • E v)) w

def dAct (E : gInf B) (w : B.Hs) : B.Hs := deriv (orbit B E w) 0

def wordAct (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (w : B.Hs) : B.Hs :=
  l.foldr (fun X y => dAct B (atPlace B X.1 X.2) y) w

def VP (P : ℕ) : Submodule ℂ B.Hs :=
  Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (u : ∀ v, B.H v),
    l.length ≤ P ∧ (∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧ y = wordAct B l (B.tens u)}

def beP (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt n * b ^ 2 + 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ)

def StepBoundAt (b : ℝ) (P : ℕ) : Prop :=
  FiniteDimensional ℂ (VP B P) ∧
  (∀ k : B.I.Ginf, (∀ v, uMat (k v) ∈ Formalism.REAL.Kset (B.I.ε v)) → ∀ w ∈ VP B P, B.σs k w ∈ VP B P) ∧
  (∀ (E : gInf B), ∀ w ∈ VP B P, DifferentiableAt ℝ (orbit B E w) 0) ∧
  (∀ (v : InfinitePlace B.I.F) (m : ℕ) (E : Fin m → gLie (B.I.ε v)), IsONBasis E → ∀ w ∈ VP B P,
    ∑ i, ‖dAct B (atPlace B v (E i)) w‖ ^ 2 ≤ beP B.I.n b P ^ 2 * ‖w‖ ^ 2) ∧
  (∀ (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)), ∀ w ∈ VP B P,
    ‖dAct B (atPlace B v X) w‖ ≤ Real.sqrt (Formalism.REAL.hs X.1) * beP B.I.n b P * ‖w‖) ∧
  (∀ (E : gInf B), ∀ w ∈ VP B P,
    ‖dAct B E w‖ ≤ Real.sqrt B.I.f * Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * beP B.I.n b P * ‖w‖) ∧
  ∀ (E : gInf B), ∀ w ∈ VP B P, dAct B E w ∈ VP B (P + 1)

open NumberField Matrix in
variable (B : _root_.Formalism.MainNotions.S.RowsAut) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.stepSpan_mono {P Q : ℕ} (h : P ≤ Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B P ≤ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B Q :=
  Submodule.span_mono fun _ ⟨l, u, hl, hu, hy⟩ => ⟨l, u, hl.trans h, hu, hy⟩


open NumberField Matrix in
variable (B : _root_.Formalism.MainNotions.S.RowsAut) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem {d : InfinitePlace B.I.F → ℝ}
    (h : _root_.GlobalTheory.Count.IsDSData B d) (P : ℕ) :
    B.tens B.w ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B P ∧ ‖B.tens B.w‖ = 1 := by
  have hd := h
  unfold _root_.GlobalTheory.Count.IsDSData at hd
  have hunit : ∀ v, ‖B.w v‖ = 1 ∧ B.w v ∈ _root_.Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v) := fun v => by
    have hv := (hd v).2.2.1
    unfold _root_.Formalism.MainNotions.S.IsLowUnit at hv
    exact hv
  refine ⟨Submodule.subset_span ⟨[], B.w, Nat.zero_le _, fun v => (hunit v).2, rfl⟩, ?_⟩
  have hs := B.tens_spec
  unfold _root_.Formalism.MainNotions.S.AutInst.IsHilbTensor at hs
  have hinner : inner ℂ (B.tens B.w) (B.tens B.w) = 1 := by
    rw [hs.1]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [inner_self_eq_norm_sq_to_K, (hunit v).1]
    simp
  have hsq : ‖B.tens B.w‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hinner, RCLike.one_re]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

end GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.RareFlags
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RareFlags

open Formalism.MainNotions.S GlobalTheory.Count

def FlagRare : Prop :=
  ∃ n₀ : ℕ, ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → n₀ ≤ B.I.n → q ^ 2 ≤ B.I.n →
    Real.log B.I.rd ≤ Real.exp B.I.n → Real.log B.I.f ≤ Real.sqrt B.I.n →
    prob B {x | least B.I x < 1 / 2} ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n))

end GlobalTheory.IndefiniteRowSideFullHecke.RareFlags
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SaturatedPerpDuality
section
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality

open Formalism.MainNotions.S GlobalTheory.Count

def SatIn (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

end GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality
end
end

