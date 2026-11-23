module

public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.StatementJC
public import Mathlib

@[expose] public section

-- bundled from Formalism.HermitianCurvature.CapelliDeterminantAndBranching
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.Qr

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section Defs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def Stab {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) : Prop :=
  ∀ a b, ∀ v ∈ S, E a b v ∈ S

def Irr {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  Nontrivial V ∧ ∀ S : Submodule ℂ V, Stab E S → S = ⊥ ∨ S = ⊤

def cpol {n : ℕ} (m : Fin n → ℂ) (w : ℂ) : ℂ := ∏ j, (w + m j)

def CapSp {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ) : Submodule ℂ V :=
  ⨅ w : ℂ, LinearMap.ker (qdet E w - cpol m w • (1 : Module.End ℂ V))

theorem mem_CapSp {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {m : Fin n → ℂ} {v : V} :
    v ∈ CapSp E m ↔ ∀ w, qdet E w v = cpol m w • v := by
  simp only [CapSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

def SDec {n : ℕ} (m : Fin n → ℂ) : Prop := ∀ a b : Fin n, a < b → ∃ N : ℕ, m a - m b = (N : ℂ) + 1

def hval {n : ℕ} (θ : Fin n → ℂ) : ℝ := ∑ a : Fin n, ((n : ℝ) - ((a : ℕ) : ℝ)) * (θ a).re

def mono {n : ℕ} (f : Fin n → Module.End ℂ V) (a : Fin n → ℕ) : Module.End ℂ V :=
  (List.ofFn fun x => f x ^ a x).prod

def dualE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ (Module.Dual ℂ V) :=
  fun a b => (E b a).dualMap

end Defs

def subA {A : Type*} {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) : Fin n → Fin n → A :=
  fun a b => E a.castSucc b.castSucc

def etaK {A : Type*} {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (x : Fin n) : A := E x.castSucc (Fin.last n)

def yK {A : Type*} {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (x : Fin n) : A := E (Fin.last n) x.castSucc

def Box {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) : Prop := ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc

def shf {n : ℕ} (β : ℂ) (M : Fin n → ℤ) : Fin n → ℂ := fun j => β + (M j : ℂ)

structure Hyp {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (β : ℂ)
    (L : Fin (n + 1) → ℤ) : Prop where
  gl : GlRel E
  irr : Irr E
  anti : StrictAnti L
  cap : ∀ (w : ℂ) (v : V), qdet E w v = cpol (shf β L) w • v

def ExistsSingMax : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V),
    GlRel E → ∀ S : Submodule ℂ V, Stab E S → S ≠ ⊥ →
    ∃ (ν : Fin n → ℂ) (v : V), v ∈ S ∧ v ≠ 0 ∧ IsHW E ν v ∧
      ∀ (θ : Fin n → ℂ) (x : V), x ∈ S → x ≠ 0 → (∀ a, E a a x = θ a • x) → hval θ ≤ hval ν

def SingDom : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v → v ≠ 0 → ∀ a b : Fin n, a < b → ∃ N : ℕ, ν a - ν b = (N : ℂ)

def SepPoly : Prop :=
  ∀ (n : ℕ) (m m' : Fin n → ℂ), (∀ w, cpol m w = cpol m' w) → SDec m' →
    Function.Injective m ∧ (SDec m → m = m')

def CapStab : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ), GlRel E →
    Stab E (CapSp E m) ∧
      ∀ X : Module.End ℂ V, (∀ a b, X * E a b = E a b * X) → ∀ v ∈ CapSp E m, X v ∈ CapSp E m

def CapSing : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (m : Fin n → ℂ), GlRel E → CapSp E m ≠ ⊥ →
    Function.Injective m ∧
      (SDec m → ∀ (ν : Fin n → ℂ) (v : V), v ∈ CapSp E m → v ≠ 0 → IsHW E ν v → ∀ j, ν j = m j + ((j : ℕ) : ℂ))

def TopWeightSing : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (m : Fin n → ℂ), GlRel E → SDec m → ∀ x ∈ CapSp E m, (∀ a, E a a x = (m a + ((a : ℕ) : ℂ)) • x) →
      IsHW E (fun a => m a + ((a : ℕ) : ℂ)) x

def QminorPoly : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin t → Fin n),
    ∃ c : ℕ → A, ∀ u : ℂ, qminor E a b u = ∑ s ∈ Finset.range (t + 1), (u ^ s) • c s

def PolyVanish : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (d : ℕ) (c : ℕ → X) (F : Finset ℂ),
    (∀ u : ℂ, u ∉ F → ∑ s ∈ Finset.range d, (u ^ s) • c s = 0) → ∀ s ∈ Finset.range d, c s = 0

def CovUp : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (η : Fin n → Module.End ℂ V),
    GlRel E → IsCov E η → ∀ m : Fin n → ℂ, Function.Injective m → ∀ v ∈ CapSp E m,
    ∃ Ψ : Fin n → Fin n → V,
      (∀ x, ∑ i, Ψ i x = η x v) ∧
      (∀ i x, Ψ i x ∈ CapSp E (Function.update m i (m i + 1))) ∧
      ∀ (i x : Fin n) (u : ℂ),
        ∑ a : Fin n, ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • qminor E (skip1 a) (skip1 x) u (Ψ i a) =
          (∏ j ∈ Finset.univ.erase i, (u + m j)) • Ψ i x

def VecDown : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (y : Fin n → Module.End ℂ V),
    GlRel E → IsVec E y → (∀ a b, y a * y b = y b * y a) → ∀ m : Fin n → ℂ, Function.Injective m → ∀ v ∈ CapSp E m,
    ∃ Φ : Fin n → Fin n → V,
      (∀ x, ∑ i, Φ i x = y x v) ∧
      (∀ i x, Φ i x ∈ CapSp E (Function.update m i (m i - 1))) ∧
      ∀ (i x : Fin n) (u : ℂ),
        ∑ l : Fin n, ((-1 : ℂ) ^ ((x : ℕ) + (l : ℕ))) • qminor E (skip1 x) (skip1 l) (u - 1) (Φ i l) =
          (∏ j ∈ Finset.univ.erase i, (u + m j)) • Φ i x

def BorderLast : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → A), GlRel E → ∀ u : ℂ,
    qdet E u = qdet (subA E) u * Tm E (u - (n : ℂ)) (Fin.last n) (Fin.last n) -
      ∑ w : Fin n, ∑ x : Fin n, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (yK E x * qminor (subA E) (skip1 w) (skip1 x) u * etaK E w)

def BorderFirst : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → A), GlRel E → ∀ u : ℂ,
    qdet E u = Tm E u (Fin.last n) (Fin.last n) * qdet (subA E) (u - 1) -
      ∑ w : Fin n, ∑ x : Fin n, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (etaK E w * qminor (subA E) (skip1 w) (skip1 x) (u - 2) * yK E x)

def SubRel : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → A), GlRel E →
    GlRel (subA E) ∧ IsCov (subA E) (etaK E) ∧ IsVec (subA E) (yK E) ∧ (∀ a b, etaK E a * etaK E b = etaK E b * etaK E a) ∧
      (∀ a b, yK E a * yK E b = yK E b * yK E a) ∧
      ∀ a b, E (Fin.last n) (Fin.last n) * subA E a b = subA E a b * E (Fin.last n) (Fin.last n)

def RaiseNZ : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (l : Fin (n + 1) → ℂ), GlRel E → (∀ (w : ℂ) (v : V), qdet E w v = cpol l w • v) →
    ∀ m : Fin n → ℂ, Function.Injective m → CapSp (subA E) m ≠ ⊥ → ∀ i : Fin n, (∀ j, m i ≠ l j) →
      CapSp (subA E) (Function.update m i (m i + 1)) ≠ ⊥

def LowerNZ : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (l : Fin (n + 1) → ℂ), GlRel E → (∀ (w : ℂ) (v : V), qdet E w v = cpol l w • v) →
    ∀ m : Fin n → ℂ, Function.Injective m → CapSp (subA E) m ≠ ⊥ → ∀ i : Fin n, (∀ j, m i - 1 ≠ l j) →
      CapSp (subA E) (Function.update m i (m i - 1)) ≠ ⊥

def Decomp : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (β : ℂ) (L : Fin (n + 1) → ℤ), Hyp E β L →
    (∀ M, Box L M → CapSp (subA E) (shf β M) ≠ ⊥) ∧
      (⨆ (M : Fin n → ℤ) (_ : Box L M), CapSp (subA E) (shf β M)) = ⊤

def CapIndep : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (β : ℂ),
    iSupIndep fun M : {M : Fin n → ℤ // StrictAnti M} => CapSp E (shf β M.1)

def DualMinor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
    GlRel (dualE E) ∧ ∀ (t : ℕ) (a b : Fin t → Fin n) (w : ℂ), qminor (dualE E) a b w = (qminor E b a w).dualMap

def SpanTop : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (ν : Fin (n + 1) → ℂ) (v₀ : V), GlRel E → Irr E → IsHW E ν v₀ → v₀ ≠ 0 → ∀ ξ : Module.Dual ℂ V,
    (∀ a b : Fin n, b < a → ∀ v, ξ (subA E a b v) = 0) → (∀ a : Fin n → ℕ, ξ (mono (yK E) a v₀) = 0) → ξ = 0

def SpanSing : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (ξ₀ : Module.Dual ℂ V) (μ : Fin n → ℂ) (w : V),
    GlRel E → Irr E → ξ₀ ≠ 0 → (∀ a b : Fin (n + 1), b < a → ∀ v, ξ₀ (E a b v) = 0) → IsHW (subA E) μ w →
    (∀ a : Fin n → ℕ, ξ₀ (mono (etaK E) a w) = 0) → w = 0

def MultOne : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (μ : Fin n → ℂ) (w₁ w₂ : V), GlRel E → Irr E →
    IsHW (subA E) μ w₁ → IsHW (subA E) μ w₂ → w₁ ≠ 0 → ∃ c : ℂ, w₂ = c • w₁

def IrredCap : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (β : ℂ) (L : Fin (n + 1) → ℤ), Hyp E β L →
    ∀ M, Box L M → ∀ S' : Submodule ℂ V, S' ≤ CapSp (subA E) (shf β M) → Stab (subA E) S' →
      S' = ⊥ ∨ S' = CapSp (subA E) (shf β M)

def BranchingAlg : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (β : ℂ) (L : Fin (n + 1) → ℤ), Hyp E β L →
    DirectSum.IsInternal (fun M : {M : Fin n → ℤ // Box L M} => CapSp (subA E) (shf β M.1)) ∧
      ∀ M : {M : Fin n → ℤ // Box L M}, CapSp (subA E) (shf β M.1) ≠ ⊥ ∧
        ∀ S' : Submodule ℂ V, S' ≤ CapSp (subA E) (shf β M.1) → Stab (subA E) S' →
          S' = ⊥ ∨ S' = CapSp (subA E) (shf β M.1)

end Formalism.FourierDecayAlt.Qr
end
end

-- bundled from Formalism.HermitianCurvature.FrameMinor
section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Qr

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FrameMinor : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (D : Set (Mx k r)), IsOpen D →
    ∀ (Bs : Fin m → Fin (2 * r + k + 1) → ℂ), (∀ a, inWb k r (Bs a)) →
    ∀ (P Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ)
      (ι : Fin m → Fin (mdim k r (Fin.last r))), Function.Injective ι →
    (∀ a c, P c (ι a) = Bs a (posL k r (Fin.last r) c)) →
    (∀ b d, Q (ι b) d = herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) →
    ∀ (w : ℂ) (φ : SV k r (Fin.last r) D E), ∀ g ∈ Glev k r (Fin.last r) ∩ D,
      (qminor (Econj (EV k r (Fin.last r) D E) P Q) ι ι w φ).1 g = capR k r Bs w φ.1 g

end Formalism.FourierDecayAlt.Qr
end
end

-- bundled from Formalism.HermitianCurvature.StatementJCCpt
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.JC

open Formalism.FourierDecayAlt

section densityCpt

open scoped ComplexOrder

def PosDensityCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ) (ε : ℝ),
    0 < ε → P5.Auser P0 w.length + 1 ≤ A → P5.mmUser P0 w.length ≤ mm →
    (∀ ε' : ℝ, 0 < ε' → ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, NiceCoef (T.bs j) ε' (x a) ∧ HasCompactSupport (x a)) → 0 ≤ D.formLev T s j w x x) →
    ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, CCCoefM (T.bs j) A mm ε (x a)) → 0 ≤ D.formLev T s j w x x

def ThmPModuleOfActualCpt : Prop :=
  P5.ThmPActualCpt → RadialModuleForm → PosDensityCpt → FormLevSesqMM →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (l0 N : ℕ) (admitted : List C.Letter → Prop) (A : ℝ) (mm : ℕ),
    1 ≤ l0 → l0 ≤ P0.k → (∀ w, admitted w → w.length ≤ N) → P5.Auser P0 N + 1 ≤ A → P5.mmUser P0 N ≤ mm →
    (∀ j : Fin (P0.r + 1),
      ∃ (X : Q.ActualOps (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
        (μ : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt (parLev P0 j).k (parLev P0 j).r))
        (L : R.LevelData (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
          (T.bs j).π')) (parLev P0 j).r)
        (st : Fr.Start (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
          (T.bs j).π'))),
        P5.IsData (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 ∧
        ∀ w, admitted w → P5.WordOK (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' st l0 (D.positionted w)) →
    ∃ KK : ∀ j : Fin (P0.r + 1), Submodule ℂ (B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
      D.ThmPModule T (M.sgn P0 l0) admitted KK ∧
      ∀ (j : Fin (P0.r + 1)) (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → B.InCC A mm F →
        B.CkOn (mm : ℕ∞) (B.GV P0.k (P0.r - j)) F →
        (∀ g ∈ B.GV P0.k (P0.r - j), F g ≠ 0 → ε ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' g) →
        F ∈ KK j

end densityCpt

end Formalism.FourierDecayAlt.JC
end
end

-- bundled from Formalism.HermitianCurvature.StatementJCT
section
namespace Formalism.FourierDecayAlt.JCT

open Finset Filter Topology NumberField MeasureTheory

open scoped ComplexConjugate

noncomputable section

open Classical

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def jvModel (S : C.HidaSetting E Wp Wq)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT) (Cm : Fin S.f → ℝ) :
    Fin S.f → ℝ := fun v =>
  Cm v * (∫ q, ∑ ρ, ‖(j v ρ : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q‖ ^ 2
      ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT) /
    D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0

variable [∀ x, FiniteDimensional ℂ (Wq x)]

def LevelsActual (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) :
    Prop :=
  ∀ v (j : Fin (S.G.r + 1)),
    ∃ (X : Q.ActualOps (JC.parLev (D.parOf S v) j).k (JC.parLev (D.parOf S v) j).r ((T v).bs j).z ((T v).bs j).z'
        ((T v).bs j).π ((T v).bs j).π')
      (μ : Measure (Formalism.QuantumDeterminants.Mt (JC.parLev (D.parOf S v) j).k (JC.parLev (D.parOf S v) j).r))
      (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev (D.parOf S v) j).k (JC.parLev (D.parOf S v) j).r ((T v).bs j).z
        ((T v).bs j).z' ((T v).bs j).π ((T v).bs j).π')) (JC.parLev (D.parOf S v) j).r)
      (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev (D.parOf S v) j).k (JC.parLev (D.parOf S v) j).r ((T v).bs j).z
        ((T v).bs j).z' ((T v).bs j).π ((T v).bs j).π'))),
      P5.IsData (JC.parLev (D.parOf S v) j) ((T v).bs j).z ((T v).bs j).z' ((T v).bs j).π ((T v).bs j).π' X μ L st (S.l + 1) ∧
      ∀ w, D.AdmAt S v w → P5.WordOK (JC.parLev (D.parOf S v) j) ((T v).bs j).z ((T v).bs j).z' ((T v).bs j).π
        ((T v).bs j).π' st (S.l + 1) (D.positionted w)

def SlicesCC (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) : Prop :=
  ∀ v, ∀ ε, 0 < ε → ∀ (i : ℕ) (hi : i ≤ S.G.r) (w : List C.Letter), D.AdmAt S v w → ∀ (p : C.LPt)
    (hp : D.IsLocPt p i) (a : Wd.Ix (Fin w.length)), ∃ ε' : ℝ, 0 < ε' ∧
      JC.CCCoefM ((T v).bs (⟨i, by omega⟩ : Fin (S.G.r + 1))) (P5.Auser (D.parOf S v) S.Ntop + 1)
        (P5.mmUser (D.parOf S v) S.Ntop) ε'
        (D.castF (by simp [hp.2])
          (D.sliceAt S.G.k S.G.r (T v).base.z (T v).base.z'
            (D.uwG S.G.k S.G.r (T v).base.z (T v).base.z' (D.cutF (T v).base χ (f v) ε) i hi w a) p))

def VtTensor (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) : Prop :=
  ∀ p q : TB.Pt E, TB.IsPt p (S.G.r + 1) → TB.IsPt q (S.G.r + 1) →
    inner ℂ (Vt q) (Vt p) = ∏ v,
      ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) p)) *
          √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        inner ℂ (JC.vecPlace S T f ν' m₀ v (C.loc (S.σ v) q)) (JC.vecPlace S T f ν' m₀ v (C.loc (S.σ v) p))

def BuiltInputs (C₄ C₆ : ℝ) (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
    (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : Fin S.f → ℝ)
    (Lw : ℕ → Fin S.f → ℝ) (Ll Ll' : ℕ → ℕ → Fin S.f → ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) : Prop :=
  1 ≤ S.l ∧ S.l + 2 ≤ S.G.k ∧ LevelsActual S T ∧ SlicesCC S T f χ ∧
  (∀ v, D.TopPSD (T v) (f v) χ (D.AdmAt S v) (top v)) ∧
  C.GridsOK S ∧
  JC.WaveByPlaces S Lw ∧ JC.HidaCurvatureBarriers S Lw ∧
  JC.LiftBelowTop S Ll ∧ JC.LiftTopDiag S Ll' ∧ JC.ThresholdsLift S Ll Ll' ∧
  JC.SumFormConcrete S C₄ ∧
  (∀ v, B.CkOn ⊤ (B.GV S.G.k S.G.r) (f v)) ∧
  (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
    S.cutHi v - S.cutLo v) ∧
  (∀ v, JC.IsModelPlace S T f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) ∧
  VtTensor S T f ν' m₀ Vt

end defs

section closed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def LongCut (Cc : ℝ) (S : C.HidaSetting E Wp Wq) : Prop :=
  ∀ v, Cc * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
    (S.Ntop : ℝ) ^ 3) ≤ S.cutHi v - S.cutLo v

def IsBuiltPlace (Cc : ℝ) (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) : Prop :=
  0 < S.G.g1 ∧ 0 < S.G.g2 ∧ S6.Unram E ∧ D.IsBuilt S T f χ ν' m₀ top A₀ ∧ 1 ≤ S.l ∧ S.l + 2 ≤ S.G.k ∧
    C.GridsOK S ∧ LongCut Cc S ∧ Cc ≤ S.CA ∧ (∀ v, B.CkOn ⊤ (B.GV S.G.k S.G.r) (f v)) ∧ 2 ≤ S.G.k ∧
    Cc * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ ∧
    ∀ v, ∀ Y ∈ Set.Icc (S.cutLo v) (S.cutHi v), I.OnCut (D.parOf S v).u (D.parOf S v).u' (S.l + 1) Y

def SliceBudget (S : C.HidaSetting E Wp Wq) (A₀ : ℝ) : Prop :=
  ∀ v, ∀ i ≤ S.G.r,
    9 * ((i : ℝ) + 1) * (P5.Auser (D.parOf S v) S.Ntop + 1) + (S.Ntop : ℝ) * (1 + 3 * ((S.G.r : ℝ) + 1)) * i +
      (6 * (i : ℝ) + 3 * ((S.G.r : ℝ) + 1)) * (P5.mmUser (D.parOf S v) S.Ntop : ℝ) ≤ A₀

end closed

def LevelsActualBuilt : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → LevelsActual S T

def SlicesCCBuilt : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → SliceBudget S A₀ → SlicesCC S T f χ

def BetaCutLimit : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → ∀ v, B.normSq (T v).base (f v) ≠ ⊤ ∧
      Filter.Tendsto (fun ε => B.beta (T v).base (D.cutF (T v).base χ (f v) ε) (D.cutF (T v).base χ (f v) ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (((B.normSq (T v).base (f v)).toReal : ℝ) : ℂ))

def EnergyOfLemmaE : Prop :=
  BetaCutLimit →
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (jv : Fin S.f → ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → C.LemmaE S jv →
    ∀ v, jv v = (B.normSq (T v).base (f v)).toReal /
      D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0

def ModelPlaceBuilt2 : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → (∀ v, (S.G.place (S.pl v)).Ok) →
    Sz.IsWord S.G.k S.de → Sz.IsWord S.G.k S.de' → ∀ c : LE.Cut, c.χ = χ → ∀ v : Fin S.f,
      ∃ (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
        (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
        (lam : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : ℝ),
        JC.IsModelPlace S T f χ v L j lam c Cm σ

end

end Formalism.FourierDecayAlt.JCT
end

