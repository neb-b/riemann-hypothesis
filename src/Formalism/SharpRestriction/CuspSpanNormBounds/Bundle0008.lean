module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
public import Formalism.HermitianLattices.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.ChainLength
section
noncomputable section

namespace Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

section LocalTheory

open Formalism.MainNotions.S.Loc MeasureTheory ComplexConjugate


def FamilyVolumeFourth {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r k n : ℕ) (C : ℝ) : Prop :=
  ∀ (ϖ : 𝒪[F]), Irreducible ϖ →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  (∀ (t : Term V M r), H.IsGeneric t →
    |H.dens ϖ t.abelian₂ (H.gram (H.MMfam t)) - 1| ≤
      C * (2 * (r : ℝ) + 2) * (Nat.card 𝓀[F] : ℝ) ^ (-((k : ℤ) - 2 * r - 2))) ∧
  (∀ (t₁ t₂ : Term V M r), H.IsGeneric t₁ → H.IsGeneric t₂ → H.IsScalarPair t₁ t₂ →
    H.dens ϖ t₁.abelian₂ (H.gram (H.MMfam t₁)) = H.dens ϖ t₂.abelian₂ (H.gram (H.MMfam t₂)))

end LocalTheory

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ U : ∀ p : PlF D, AddSubgroup (D.s.atP p).Ep, (∀ p, IsOpen (U p : Set (D.s.atP p).Ep)) →
    {p | (U p : Set (D.s.atP p).Ep) ≠ ((D.s.atP p).O : Set (D.s.atP p).Ep)}.Finite →
    ∀ x : ∀ p, (D.s.atP p).Ep, {p | x p ∉ (D.s.atP p).O}.Finite →
      ∃ t : D.host.E, ∀ p, (D.s.atP p).ιE t - x p ∈ U p

def adm7 (D : Formalism.BasicNotions.D7) : Prop :=
  (∀ M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep, (∀ p, (M p).OK) →
    ∀ x : D.host.E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((D.s.atP p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((D.s.atP p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))))

def Gfin (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ) : Prop :=
  (∀ (n : ℕ) (w w' : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => locK M δ T T' p n w w').Finite) ∧
  (∀ (n : ℕ) (h : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => detNrmP M δ T T' p h).Finite) ∧
  (∀ (a s : ℕ) (t : D.host.E), t ≠ 0 → 1 ≤ a → 1 ≤ s → a + s - 1 ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => (M p).modK (blkMod δ T T' p a s t)).Finite) ∧
  (∀ w w' : Point D.host.E (D.R.rS + 1), (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}

end Family

end Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.DMiMulVecApply
section
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Alg2

variable {k r : ℕ} {κ τ : ℝ}

theorem tV_eI (a : Fin r) : tV k r κ τ (eI k r a) = tF r κ τ a.val := by
  unfold tV eI; rw [if_pos a.isLt]

theorem tV_esI (a : Fin r) : tV k r κ τ (esI k r a) = (tF r κ τ a.val)⁻¹ := by
  unfold tV esI
  have h := a.isLt
  rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
  congr 2; simp only; omega

theorem tV_wb (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : tV k r κ τ i = 1 := by
  unfold tV; rw [if_neg (by omega), if_pos h2]

theorem dM_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dM k r κ τ *ᵥ v) i = ((tV k r κ τ i : ℝ) : ℂ) * v i := by
  rw [dM, Matrix.mulVec_diagonal]

theorem dMi_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dMi k r κ τ *ᵥ v) i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) * v i := by
  rw [dMi, Matrix.mulVec_diagonal]

theorem dM_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dM k r κ τ *ᵥ z = z := by
  funext i; rw [dM_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dMi_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dMi k r κ τ *ᵥ z = z := by
  funext i; rw [dMi_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dM_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dM k r κ τ *ᵥ bvec i = ((tV k r κ τ i : ℝ) : ℂ) • bvec i := by
  funext j; rw [dM_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem dMi_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dMi k r κ τ *ᵥ bvec i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) • bvec i := by
  funext j; rw [dMi_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem inWb_smul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : ℂ) : inWb k r (a • z) := by
  intro i hi; rw [Pi.smul_apply, hz i hi, smul_zero]

theorem cj_mulVec (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    cj k r κ τ x *ᵥ v = dMi k r κ τ *ᵥ (x *ᵥ (dM k r κ τ *ᵥ v)) := by
  rw [cj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem dM_mulVec_fvec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin (r + 1)) :
    dM k r κ τ *ᵥ fvec k r ((τ : ℂ) • z) a = ((tF r κ τ a.val : ℝ) : ℂ) • fvec k r z a := by
  unfold fvec
  by_cases h : a.val < r
  · rw [dite_eq_left h, dite_eq_left h, dM_mulVec_bvec, tV_eI]
  · rw [dite_eq_right h, dite_eq_right h, dM_mulVec_wb (inWb_smul hz _)]
    have : a.val = r := by omega
    simp [tF, this]

theorem ell_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Mx k r) :
    ell k r ((τ : ℂ) • z) (cj k r κ τ x) = (κ : ℂ)⁻¹ * ell k r z x := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a.val + 1 < r
  · rw [dite_eq_left h, dite_eq_left h, cj_apply, tV_eI, tV_eI]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have hk := pow_pos hκ (r - (a.val + 1))
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    have hkc : (κ : ℂ) ^ (r - (a.val + 1)) ≠ 0 := pow_ne_zero _ hκc
    simp only [tF]
    rw [e, pow_succ]
    push_cast
    field_simp
  · rw [dite_eq_right h, dite_eq_right h, cj_mulVec, dM_mulVec_wb (inWb_smul hz _), Matrix.mulVec_smul,
      dMi_mulVec_apply, tV_eI, Pi.smul_apply, smul_eq_mul]
    have e : r - a.val = 1 := by omega
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    simp only [tF, e, pow_one]
    push_cast
    field_simp

theorem psi_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (x : Mx k r) :
    psi k r ((τ : ℂ) • z) ((κ : ℂ) * c) (cj k r κ τ x) = psi k r z c x := by
  unfold psi
  rw [ell_cj hκ hτ hz]
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have : (κ : ℂ) * c * ((κ : ℂ)⁻¹ * ell k r z x) = c * ell k r z x := by
    field_simp
  rw [this]

theorem delta_iff {s y : ℂ} {i j : Fin (2 * r + k + 1)} (hs : s ≠ 0) (h1 : i = j → s = 1) :
    (s * y = if i = j then 1 else 0) ↔ (y = if i = j then 1 else 0) := by
  by_cases h : i = j
  · rw [h1 h, one_mul]
  · simp only [h, if_false, mul_eq_zero, hs, false_or]

theorem cj_fac_ne (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) ≠ 0 := by
  have := tV_pos (k := k) (r := r) hκ hτ i
  have := tV_pos (k := k) (r := r) hκ hτ j
  exact_mod_cast (mul_pos (inv_pos.mpr ‹0 < tV k r κ τ i›) this).ne'

theorem cj_fac_diag (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) (h : i = j) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) = 1 := by
  subst h; rw [inv_mul_cancel₀ (tV_pos hκ hτ i).ne']; simp

theorem cj_mem_Nset_iff (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) :
    cj k r κ τ x ∈ Nset k r ↔ x ∈ Nset k r := by
  simp only [Nset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ, cj_apply]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' fun a => forall_congr' fun i => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)
  · refine forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)

theorem UWset_smul {z : Fin (2 * r + k + 1) → ℂ} (hτ : 0 < τ) : UWset k r ((τ : ℂ) • z) = UWset k r z := by
  ext g
  simp only [UWset, Set.mem_ofPred_eq, Matrix.mulVec_smul]
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact smul_right_injective _ hτ' h

theorem cj_fix_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (hs : s ≠ 0)
    (h1 : dM k r κ τ *ᵥ v = s • v) (h2 : dMi k r κ τ *ᵥ v = s⁻¹ • v) :
    cj k r κ τ g *ᵥ v = v ↔ g *ᵥ v = v := by
  rw [cj_mulVec, h1, Matrix.mulVec_smul, Matrix.mulVec_smul]
  constructor
  · intro h
    have h3 : dM k r κ τ *ᵥ (s • (dMi k r κ τ *ᵥ (g *ᵥ v))) = dM k r κ τ *ᵥ v := by rw [h]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, dM_mul_dMi hκ hτ, Matrix.one_mulVec, h1] at h3
    exact smul_right_injective _ hs h3
  · intro h; rw [h, h2, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem cj_fix_bvec_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (i : Fin (2 * r + k + 1)) :
    cj k r κ τ g *ᵥ bvec i = bvec i ↔ g *ᵥ bvec i = bvec i := by
  refine cj_fix_iff hκ hτ g _ ((tV k r κ τ i : ℝ) : ℂ) (by exact_mod_cast (tV_pos hκ hτ i).ne')
    (dM_mulVec_bvec i) ?_
  rw [dMi_mulVec_bvec, Complex.ofReal_inv]

theorem cj_mem_UWset_iff (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mx k r) :
    cj k r κ τ g ∈ UWset k r z ↔ g ∈ UWset k r z := by
  simp only [UWset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ]
  refine and_congr Iff.rfl (and_congr (forall_congr' fun a =>
    and_congr (cj_fix_bvec_iff hκ hτ g _) (cj_fix_bvec_iff hκ hτ g _)) ?_)
  exact cj_fix_iff hκ hτ g z 1 one_ne_zero (by rw [one_smul, dM_mulVec_wb hz])
    (by rw [inv_one, one_smul, dMi_mulVec_wb hz])

theorem cj_mem_RStab_iff (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) :
    cj k r κ τ a ∈ RStab k r (cj k r κ τ g) ↔ a ∈ RStab k r g := by
  simp only [RStab, Set.mem_ofPred_eq]
  rw [← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, cj_mem_Nset_iff hκ hτ, cj_mem_Nset_iff hκ hτ]

end Alg2

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.DoubleBoundAndExtensionOfSmooth
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Side

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def FI (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (u v : H) : Mt k r × Mt k r → (Wp →L[ℂ] Wp) := fun p =>
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

end Side

end Formalism.MainNotions.DoubleDerivativeSmoothness
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusProjectedBounds
section
noncomputable section

namespace Formalism.MainNotions.FrobeniusProjectedBounds

open Formalism.BasicNotions Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Letters

variable (D : D7)

def kR : ℝ := D.R.k

def mR : ℝ := D.R.m

def fR : ℝ := D.R.f

def rR : ℝ := D.R.rS

def nR : ℝ := D.R.r

def du (u : D.what₂.Word) : ℝ := D.duS u

def Dall : ℝ := D.what₂.Dall

def Dst : ℝ := D.what₂.Dstar

def Gam : ℝ := (D.mem D.u₀).A.GamP

end Letters

section Flags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

end Flags

section Parts

variable (D : D7)

end Parts

def Hyp (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ StandingNumericalData D C0 ∧ 1 ≤ C0

section Statements

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ)

def adm5 (c C : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u u' : D.what₂.Word, hsNormSq (KOf D.s u u' (famNG D.s)) ≤
    (Real.exp (-(c * kR D * fR D * Real.log (kR D))) +
      (2 : ℝ) ^ (-(kR D - 2 * rR D - 5)) * Real.exp (C * mR D ^ 5 * fR D * large₂.sc.L)) *
      (du D u * du D u') / Dst D

def adm7 (c : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  |Dall D - Dst D| ≤ Real.exp (-(c * nR D * fR D * Real.log (nR D))) * Dst D

def eF (D : D7) (C0 : ℝ) : ℝ := 2 * C0 / Gam D + 2 * Real.exp (-(kR D * fR D * Real.log (kR D)))

end Statements

section LinAlg

variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

end LinAlg

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Cg cb Cu cT CT C0 : ℝ)

end Family

end Formalism.MainNotions.FrobeniusProjectedBounds
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
section
noncomputable section

open ValuativeRel NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.NonGenericAndKTwoTheorems

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NonGenericLocalBound (k r : ℕ) (C : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → LocNG.NGAt k P C

def Conclusion1 (D : D7) (C : ℝ) : Prop := 4 * D.R.rS + 7 ≤ D.R.k → NonGenericLocalBound D.R.k D.R.rS C

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

def KTwoParameterConditions (Cl Cg CT : ℝ) : Prop :=
  Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  (∀ i : Fin 2, ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ large₂.sc.b ^ Cg) ∧
  (∀ (τ : D.what₂.Tau) (a c : Fin D.R.r), a ≠ c →
    Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 < |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) c|) ∧
  Cl * Real.log D.host.rdE ≤ large₂.sc.L ∧
  Real.log (D.R.f : ℝ) ≤ (D.R.rS : ℝ) ^ 2 ∧
  (∀ u : D.what₂.Word, ((D.mem u).A.T : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) ∧
    Nat.Coprime (D.mem u).A.T (D.host.g 0 * D.host.g 1)) ∧
  Formalism.HermitianLatticesTheory.IsCMUnram D.host.E

def KTwoHypotheses (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ KTwoParameterConditions D large₂ Cl Cg CT

end Hyps

section Terms

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Terms

def adm7 : Prop :=
  ∀ (k : ℕ) (u u' : Fin k → ℝ) (H H' : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (ρ : Matrix (Fin k) (Fin k) ℂ → (H' →L[ℂ] H')),
    IsHCTypeU k u π → IsHCTypeU k u' ρ → u ≠ u' →
    ∀ P : H' →L[ℂ] H, (∀ h ∈ UJset (allPos k), P.comp (ρ h) = (π h).comp P) → P = 0

section Size

variable (D : D7) (large₂ : SizeData₂ D)

end Size

section Mass

end Mass

section L3

variable (D : D7)

end L3

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Gv : GaugeVol D)

def NonGenericLocalBoundOfLargeRank (CN : ℝ) : Prop := Conclusion1 D CN

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, GaugeVol (Fm.D x i))

def Conclusion1Family (CN : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i) CN

def FamilyNonGenericLocalBound (CN : ℝ) : Prop := Conclusion1Family Fm CN

end Family

end Formalism.MainNotions.NonGenericAndKTwoTheorems

end
end

