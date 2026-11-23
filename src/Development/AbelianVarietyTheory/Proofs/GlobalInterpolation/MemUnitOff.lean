module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Formalism.LocalToGlobal.Columns.DecoFin

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)

instance mulActPP {q : ℕ} {F : Type} [Field F] (Lc : LocF q F) (n : ℕ) : MulAction (GL (Fin n) Lc.K) (LocF.PP Lc n) where
  smul := LevModel.actPP
  one_smul p := LevModel.isAct_unique (LevModel.isAct_actPP 1 p) (fun x => by simp)
  mul_smul g h p := LevModel.isAct_unique (LevModel.isAct_actPP (g * h) p) (fun x => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have h1 := LevModel.isAct_actPP g (LevModel.actPP h p) (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) x)
    have h2 := LevModel.isAct_actPP h p x
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

def valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) : Subring K :=
  (Q.valuation K).valuationSubring.toSubring

theorem mem_valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ valO Q ↔ Q.valuation K x ≤ 1 :=
  Iff.rfl

def unitGL (K : Type) [Field K] [StarRing K] (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K)ᴴ * (g : Matrix (Fin n) (Fin n) K) = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (g : Matrix (Fin n) (Fin n) K), hg,
      Matrix.one_mul, hh]
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K)ᴴ := by
      rw [← Matrix.one_mul ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ← hg, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [h1, Matrix.conjTranspose_conjTranspose, ← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]

structure Ar (D : D7) (T : ℕ) [Fact T.Prime] where
  Lc : LocF T (ZMod T)
  [st : StarRing Lc.K]
  j : Lc.K →+* D.what₂.LL
  j_star : ∀ x, D.what₂.embLL (j (star x)) = starRingEnd ℂ (D.what₂.embLL (j x))
  seen : D.what₂.places.Pl → Bool
  int_on : ∀ w, D.what₂.places.resChar w = T → ∀ x, j (if seen w then x else star x) ∈ Ow D w ↔ x ∈ Lc.O
  Γ : ∀ n, Subgroup (GL (Fin n) Lc.K)
  unit : ∀ n, Γ n ≤ unitGL Lc.K n
  int_off : ∀ n, ∀ g ∈ Γ n, ∀ w, D.what₂.places.resChar w ≠ T → ∀ a b, j ((g : Matrix (Fin n) (Fin n) Lc.K) a b) ∈ Ow D w
  free : ∀ n, ∀ g ∈ Γ n, ∀ p : LocF.PP Lc n, g • p = p → g = 1
  fin : ∀ n, Finite (MulAction.orbitRel.Quotient (Γ n) (LocF.PP Lc n))

attribute [instance] Ar.st

end GlobalTheory.LvT.Inh
