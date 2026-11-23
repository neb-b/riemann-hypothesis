module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvaria
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetDepthBasis

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

def kerMat {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s t : Σ _ : Fin i, Fin i) : C :=
  if s.1 = t.1 then g t.2 s.2 else 0

def linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s : Σ _ : Fin i, Fin i) :
    MvPolynomial (Σ _ : Fin i, Fin i) C :=
  ∑ t, MvPolynomial.C (kerMat g s t) * MvPolynomial.X t

theorem isHomogeneous_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s : Σ _ : Fin i, Fin i) :
    (linP g s).IsHomogeneous 1 := by
  unfold linP
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun t _ => MvPolynomial.isHomogeneous_C_mul_X _ _

theorem coe_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s : Σ _ : Fin i, Fin i) :
    ((linP g s : MvPolynomial (Σ _ : Fin i, Fin i) C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) =
      ∑ t, kerMat g s t • (X t : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [linP, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_C, MvPolynomial.coe_X, smul_eq_C_mul]

theorem hasSubst_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) :
    HasSubst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
  hasSubst_of_constantCoeff_zero fun s => by simp [coe_linP, map_sum]

theorem coeff_prod_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (d e : (Σ _ : Fin i, Fin i) →₀ ℕ)
    (h : e.degree ≠ d.degree) :
    coeff e (d.prod fun s n => ((linP g s : MvPolynomial _ C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ n) = 0 := by
  have hc : (d.prod fun s n => ((linP g s : MvPolynomial _ C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ n) =
      ((d.prod fun s n => linP g s ^ n : MvPolynomial _ C) : MvPowerSeries _ C) := by
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, Finsupp.prod, Finsupp.prod, map_prod]
    simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  rw [hc, MvPolynomial.coeff_coe]
  have hh : (d.prod fun s n => linP g s ^ n : MvPolynomial _ C).IsHomogeneous d.degree := by
    have := MvPolynomial.IsHomogeneous.prod d.support (fun s => linP g s ^ d s) (fun s => 1 * d s)
      fun s _ => (isHomogeneous_linP g s).pow _
    rw [Finsupp.prod]
    convert this using 1
    · simp only [one_mul]
      first | rfl | simp [Finsupp.degree_apply]
  exact hh.coeff_eq_zero h

end

end GlobalTheory.DetDepthBasis

namespace GlobalTheory.DetDepthBasis

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

theorem derivAt0_eq_sum {σ : Type} (P : MvPolynomial σ C) (h : MvPowerSeries σ C) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) : derivAt0 P h = ∑ α ∈ S, P.coeff α * mfact α * coeff α h := by
  unfold derivAt0
  refine Finset.sum_subset hS fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.1 hα]
  simp

theorem derivAt0_coe_eq_pair {σ : Type} (P Q : MvPolynomial σ C) :
    derivAt0 P (Q : MvPowerSeries σ C) = GlobalTheory.PolyPairingAdjoint.pair P Q := by
  simp only [derivAt0, GlobalTheory.PolyPairingAdjoint.pair, MvPolynomial.coeff_coe]
  rfl

theorem apply_le_degree {σ : Type} (α : σ →₀ ℕ) (s : σ) : α s ≤ α.degree := by
  rw [Finsupp.degree_apply]
  by_cases hs : s ∈ α.support
  · exact Finset.single_le_sum (f := fun x => α x) (fun _ _ => Nat.zero_le _) hs
  · rw [Finsupp.notMem_support_iff.1 hs]
    exact Nat.zero_le _

theorem le_const_of_degree_le {σ : Type} [Fintype σ] {α : σ →₀ ℕ} {N : ℕ} (h : α.degree ≤ N) :
    α ≤ Finsupp.equivFunOnFinite.symm (fun _ => N) := by
  intro s
  simpa using le_trans (apply_le_degree α s) h

theorem degree_le_totalDegree {σ : Type} {P : MvPolynomial σ C} {α : σ →₀ ℕ} (h : α ∈ P.support) :
    α.degree ≤ P.totalDegree := by
  have := MvPolynomial.le_totalDegree h
  rw [Finsupp.degree_apply]
  exact this

theorem derivAt0_subst_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C)
    (P : MvPolynomial (Σ _ : Fin i, Fin i) C) (h : MvPowerSeries (Σ _ : Fin i, Fin i) C) :
    derivAt0 P (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h) =
      derivAt0 (GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) P) h := by
  classical
  set P' := GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) P
  set N := max P.totalDegree P'.totalDegree
  set n : (Σ _ : Fin i, Fin i) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => N)
  set Q := trunc' C n h
  have hL := hasSubst_linP g

  have h1 : ∀ e : (Σ _ : Fin i, Fin i) →₀ ℕ, e.degree ≤ N →
      coeff e (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h) =
      coeff e (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (Q : MvPowerSeries _ C)) := by
    intro e he
    rw [coeff_subst hL, coeff_subst hL]
    refine finsum_congr fun d => ?_
    by_cases hd : e.degree = d.degree
    · rw [MvPolynomial.coeff_coe, coeff_trunc', if_pos (le_const_of_degree_le (hd ▸ he))]
    · rw [coeff_prod_linP g d e hd, smul_zero, smul_zero]
  have h2 : subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (Q : MvPowerSeries _ C) =
      ((GlobalTheory.PolyPairingAdjoint.subst (kerMat g) Q : MvPolynomial _ C) : MvPowerSeries _ C) := by
    rw [subst_coe]
    have := congrArg (fun φ => φ Q) (MvPolynomial.comp_aeval (fun s => linP g s)
      (MvPolynomial.coeToMvPowerSeries.algHom (σ := Σ _ : Fin i, Fin i) (R := C) C))
    simp only [AlgHom.comp_apply] at this
    rw [GlobalTheory.PolyPairingAdjoint.subst]
    exact this.symm
  calc derivAt0 P (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h)
      = derivAt0 P ((GlobalTheory.PolyPairingAdjoint.subst (kerMat g) Q : MvPolynomial _ C) : MvPowerSeries _ C) := by
        rw [← h2]
        unfold derivAt0
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [h1 α (le_trans (degree_le_totalDegree hα) (le_max_left _ _))]
    _ = GlobalTheory.PolyPairingAdjoint.pair P' Q := by
        rw [derivAt0_coe_eq_pair, GlobalTheory.PolyPairingAdjoint.pair_subst]
    _ = derivAt0 P' h := by
        rw [← derivAt0_coe_eq_pair]
        unfold derivAt0
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [MvPolynomial.coeff_coe, coeff_trunc',
          if_pos (le_const_of_degree_le (le_trans (degree_le_totalDegree hα) (le_max_right _ _)))]

end

end GlobalTheory.DetDepthBasis

namespace GlobalTheory.DetDepthBasis

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

theorem derivAt0_C_mul {σ : Type} (k : C) (P : MvPolynomial σ C) (h : MvPowerSeries σ C) :
    derivAt0 (MvPolynomial.C k * P) h = k * derivAt0 P h := by
  rw [derivAt0_eq_sum _ h P.support (by rw [← MvPolynomial.smul_eq_C_mul]; exact MvPolynomial.support_smul),
    derivAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_C_mul]
  ring

theorem subst_detPow {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (c : ℕ) :
    GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) (detPow C i c) =
      MvPolynomial.C (g.det ^ c) * detPow C i c := by
  classical
  have hM : (GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s)).mapMatrix
      (Matrix.of fun a b : Fin i => (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C)) =
      (g.map MvPolynomial.C) * Matrix.of fun a b : Fin i => (MvPolynomial.X ⟨b, a⟩ : MvPolynomial _ C) := by
    ext a b
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      GlobalTheory.PolyPairingAdjoint.subst_X, Fintype.sum_sigma, kerMat]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [hb']
    · simp
  have hdet : (g.map MvPolynomial.C).det = (MvPolynomial.C g.det : MvPolynomial (Σ _ : Fin i, Fin i) C) :=
    (RingHom.map_det _ _).symm
  rw [detPow, map_pow, AlgHom.map_det, hM, Matrix.det_mul, hdet, mul_pow, map_pow]

theorem subst_linP_lin {i d : ℕ} (g : Matrix (Fin i) (Fin i) C) (u : Fin i → Fin d → C) (b : Fin i)
    (e : Fin d) :
    subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C))
      (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) =
    ∑ a, (fun a => ∑ a', g a a' • u a') a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  classical
  have inner : ∀ a : Fin i, (↑(linP g ⟨b, a⟩) : MvPowerSeries (Σ _ : Fin i, Fin i) C) =
      ∑ a2, g a2 a • (X ⟨b, a2⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
    intro a
    rw [coe_linP, Fintype.sum_sigma, Finset.sum_eq_single b]
    · simp [kerMat]
    · intro b' _ hb'
      simp [kerMat, Ne.symm hb']
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom (hasSubst_linP g), map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X (hasSubst_linP g), inner, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a2 _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp [Finset.sum_apply, mul_comm]

theorem main : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ)
    (G : LogFGL v d) (u : Fin i → Fin d → C) (g : Matrix (Fin i) (Fin i) C), v g.det = 0 →
    detDepth G (fun a => ∑ a', g a a' • u a') c = detDepth G u c := by
  intro C _ _ v i d c G u g hg
  unfold detDepth depth
  have hE : expAlong (fun _ : Fin i => G) (fun _ => fun a => ∑ a', g a a' • u a') =
      fun x => subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C))
        (expAlong (fun _ : Fin i => G) (fun _ => u) x) := by
    funext x
    simp only [expAlong]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero
      (GlobalTheory.DepthField.hasSubst_lin (fun _ : Fin i => u) x.1)) (hasSubst_linP g)]
    congr 1
    funext e
    exact (subst_linP_lin g u x.1 e).symm
  refine iInf_congr fun f => ?_
  rw [hE, ← subst_comp_subst_apply (GlobalTheory.DepthField.hasSubst_expAlong _ _) (hasSubst_linP g),
    derivAt0_subst_linP, subst_detPow, derivAt0_C_mul, v.map_mul, v.map_pow, hg, smul_zero, zero_add]

end

end GlobalTheory.DetDepthBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormScaledEqSignAbsInv
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussNorm

open GlobalTheory.SplitWeil (cball)

section Ball

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_cball_sup (a b : Fˣ) : ∃ s : Fˣ, cball a ⊆ cball s ∧ cball b ⊆ cball s := by
  rcases le_total (ValuativeRel.valuation F (a : F)) (ValuativeRel.valuation F (b : F)) with h | h
  · exact ⟨b, fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _),
      Set.Subset.rfl⟩
  · exact ⟨a, Set.Subset.rfl,
      fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _)⟩

theorem exists_cball_of_isCompact {K : Set F} (hK : IsCompact K) : ∃ s : Fˣ, K ⊆ cball s := by
  have hcov : K ⊆ ⋃ s : Fˣ, cball s := by
    intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [cball, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [cball]⟩
  have hd : Directed (· ⊆ ·) (fun s : Fˣ => cball s) := by
    intro a b
    obtain ⟨s, h1, h2⟩ := exists_cball_sup a b
    exact ⟨s, h1, h2⟩
  exact hK.elim_directed_cover _ (fun s => GlobalTheory.SplitWeil.isOpen_cball s) hcov hd

theorem mul_mem_cball_iff (t s : Fˣ) (x : F) : (t : F) * x ∈ cball s ↔ x ∈ cball (t⁻¹ * s) := by
  simp only [cball, Set.mem_setOf_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [le_inv_mul_iff₀ (by simp [zero_lt_iff])]

end Ball

section Polar

variable {F : Type} [Field F] [CharZero F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E} {δ : E}

theorem algebraMap_norm_add (hE : IsQuad c δ) (x y : E) :
    algebraMap F E (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y) = x * c y + y * c x := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  rw [map_sub, map_sub, hE.algebraMap_norm, hE.algebraMap_norm, hE.algebraMap_norm, map_add (f := _)]
  ring

def polar (hE : IsQuad c δ) : E →ₗ[F] E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y)
    (fun x x' y => hE.algebraMap_injective (by
      simp only [map_add (f := _), algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (a • x + y) - Algebra.norm F (a • x) - Algebra.norm F y) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def, map_mul,
        AlgHom.commutes]; ring))
    (fun x y y' => hE.algebraMap_injective (by
      simp only [map_add (f := _), algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (x + a • y) - Algebra.norm F x - Algebra.norm F (a • y)) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def, map_mul,
        AlgHom.commutes]; ring))

theorem polar_apply (hE : IsQuad c δ) (x y : E) :
    polar hE x y = Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y := rfl

theorem algebraMap_polar (hE : IsQuad c δ) (x y : E) : algebraMap F E (polar hE x y) = x * c y + y * c x :=
  algebraMap_norm_add hE x y

theorem polar_symm (hE : IsQuad c δ) (x y : E) : polar hE x y = polar hE y x := by
  rw [polar_apply, polar_apply, add_comm x y]; ring

theorem polar_nondeg (hE : IsQuad c δ) (y : E) (hy : ∀ x, polar hE x y = 0) : y = 0 := by
  have h1 := congrArg (algebraMap F E) (hy y)
  rw [algebraMap_polar, map_zero] at h1
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]; exact (map_ne_zero _).mpr two_ne_zero
  have h3 : (2 : E) * (y * c y) = 0 := by rw [two_mul]; exact h1
  rcases mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2) with h | h
  · exact h
  · rw [← hE.invol y, h, map_zero]

theorem polar_half (hE : IsQuad c δ) (z : E) : polar hE ((2 : F)⁻¹ • z) z = Algebra.norm F z := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  apply hE.algebraMap_injective
  rw [algebraMap_polar, hE.algebraMap_norm, Algebra.smul_def, map_mul, AlgHom.commutes]
  have h2 : algebraMap F E (2 : F)⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  linear_combination (z * c z) * h2

theorem norm_add_eq (hE : IsQuad c δ) (x y : E) :
    Algebra.norm F (x + y) = Algebra.norm F x + Algebra.norm F y + polar hE x y := by
  rw [polar_apply]; ring

end Polar

end GlobalTheory.KSp.GaussNorm

namespace GlobalTheory.KSp

open GlobalTheory.KSp.GaussNorm GlobalTheory.SplitWeil

theorem hasGauss_norm_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : Fˣ, HasGauss μ (fun z => ψ ((t : F) * Algebra.norm F z)) (g * (sgn E t * ((nabs F t)⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _
  obtain ⟨hfin, htr, -, -, -, hNc, -, -⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  haveI := hfin
  haveI := htr
  have hgood : Good E := _root_.GlobalTheory.KSp.good_of_finiteDimensional F E
  have hpair : IsPair fun x y => ψ (polar hE x y) :=
    _root_.GlobalTheory.KSp.isPair_addChar_form F E ψ hψ hψ1 hψ0 (polar hE) (polar_symm hE) (polar_nondeg hE)
  set f : E → ℂ := fun z => ψ (Algebra.norm F z) with hf
  have hlc : IsLocallyConstant f := by
    have h := hpair.lc.comp_continuous (show Continuous fun z : E => ((2 : F)⁻¹ • z, z) by fun_prop)
    have heq : ((fun p : E × E => ψ (polar hE p.1 p.2)) ∘ fun z : E => ((2 : F)⁻¹ • z, z)) = f := by
      funext z; simp only [Function.comp_apply, f, polar_half]
    rwa [heq] at h
  have hf0 : f 0 = 1 := by simp [f]
  have hfadd : ∀ x y, f (x + y) = f x * f y * ψ (polar hE x y) := by
    intro x y
    simp only [f]
    rw [norm_add_eq hE, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  obtain ⟨γ, K₁, hK₁, hγ⟩ := _root_.GlobalTheory.KSp.gauss_integral_eventually_const E hgood μ _ hpair f hlc hf0 hfadd
  have hG : HasGauss μ f γ := by
    intro K hK
    obtain ⟨L, hLc, hLo, hL⟩ := hgood.large (K ∪ K₁) (hK.union hK₁)
    exact ⟨L, hLc, hLo, Set.subset_union_left.trans hL, hγ L hLc hLo (Set.subset_union_right.trans hL)⟩
  refine ⟨γ, fun t => ?_⟩
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · obtain ⟨w, hw⟩ := ht
    let T : E ≃ₜ+ E :=
      { toFun := fun z => (w : E) * z
        invFun := fun z => ((w⁻¹ : Eˣ) : E) * z
        left_inv := fun z => by simp
        right_inv := fun z => by simp
        map_add' := fun x y => mul_add _ _ _
        continuous_toFun := continuous_const.mul continuous_id
        continuous_invFun := continuous_const.mul continuous_id }
    have hT : μ.map T = (distribHaarChar F t)⁻¹ • μ := by
      have h := _root_.GlobalTheory.KSp.map_mul_left_eq_norm_smul F E c δ hE μ w
      rw [hw] at h
      exact h
    have h := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale E E μ μ T _ f γ hT hG
    have e1 : (fun z : E => ψ ((t : F) * Algebra.norm F z)) = fun x => f (T x) := by
      funext z
      show ψ ((t : F) * Algebra.norm F z) = ψ (Algebra.norm F ((w : E) * z))
      rw [MonoidHom.map_mul (Algebra.norm F) (w : E) z, ← hw, Units.coe_map]
    have hs : sgn E t = 1 := by rw [sgn, if_pos ⟨w, hw⟩]
    have e2 : γ * (sgn E t * (((nabs F t)⁻¹ : ℝ) : ℂ)) = (((((distribHaarChar F t)⁻¹ : NNReal) : ℝ)) : ℂ) * γ := by
      rw [hs, one_mul, mul_comm]
      simp [nabs]
    rw [e1, e2]
    exact h
  · obtain ⟨s₀, hcan⟩ := _root_.GlobalTheory.KSp.Cancel.gauss_cancel F E c δ hE ψ hψ hψ1 hψ0 μ t ht
    have hs : sgn E t = -1 := by rw [sgn, if_neg ht]
    intro K hK
    obtain ⟨a₁, ha₁⟩ := exists_cball_of_isCompact (hK.image hNc)
    obtain ⟨a₂, ha₂⟩ := exists_cball_of_isCompact (hK₁.image hNc)
    obtain ⟨s', hs'1, hs'2⟩ := exists_cball_sup (t * a₁) a₂
    obtain ⟨s, hs1, hs2⟩ := exists_cball_sup s' s₀
    obtain ⟨L, hLeq, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE (t⁻¹ * s)
    obtain ⟨L₁, hL₁eq, hL₁c, hL₁o⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE s
    have hset : {z : E | (t : F) * Algebra.norm F z ∈ cball s} = (L : Set E) := by
      rw [hLeq]; ext z; exact mul_mem_cball_iff t s _
    have hK₁L₁ : K₁ ⊆ L₁ := by
      intro z hz
      rw [hL₁eq]
      exact hs1 (hs'2 (ha₂ ⟨z, hz, rfl⟩))
    have hKL : K ⊆ L := by
      intro z hz
      rw [← hset]
      have h1 : Algebra.norm F z ∈ cball a₁ := ha₁ ⟨z, hz, rfl⟩
      have h2 : (t : F) * Algebra.norm F z ∈ cball (t * a₁) := by
        rw [mul_mem_cball_iff, inv_mul_cancel_left]; exact h1
      exact hs1 (hs'1 h2)
    have hs₀ : (s₀ : F) ∈ cball s := hs2 (show ValuativeRel.valuation F (s₀ : F) ≤ ValuativeRel.valuation F (s₀ : F) from le_refl _)
    have h1 := hcan s hs₀
    rw [← hL₁eq, hγ L₁ hL₁c hL₁o hK₁L₁, hset] at h1
    refine ⟨L, hLc, hLo, hKL, ?_⟩
    have hn : (nabs F t : ℂ) ≠ 0 := by exact_mod_cast (nabs_pos F t).ne'
    rw [hs, Complex.ofReal_inv]
    field_simp
    linear_combination h1
end GlobalTheory.KSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem hx_of_isONFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ IsUnitFr X x ∧ ∀ z w : Fin g → ℂ, hx X bas idx x z w = ∑ j, (X.c (idx j).1 : ℂ) * z j * conj (w j) := by
  intro E _ _ _ r g n X bas idx hs _ x ho
  have hsg : ∀ a : ℕ, FD.sgn X.p0 a = 1 ∨ FD.sgn X.p0 a = -1 := fun a => by
    unfold FD.sgn; split_ifs <;> simp
  have e (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [ho τ, sgnM, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  have h0 (i : ℕ) : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => by rcases hsg a with h | h <;> rw [h] <;> norm_num
  have hd : x ∈ X.dom := by
    refine fun τ => ⟨fun h => ?_, fun i => ?_⟩
    · have h1 : FD.gram τ.1 X.Gm (mat x τ) =
          (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by
        ext a b
        simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.map_apply, Finset.sum_mul]
        exact Finset.sum_comm
      have h2 := congrArg Matrix.det (h1.symm.trans (ho τ))
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul, sgnM,
        Matrix.det_diagonal] at h2
      refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h2.symm
      rcases hsg a with h | h <;> rw [h] <;> norm_num
    · rw [e, Complex.ofReal_re]
      exact mul_self_pos.2 (h0 _)
  refine ⟨hd, fun τ i => ?_, (GlobalTheory.Dict.hx_ortho E r X g bas idx hs x hd ho).1⟩
  rw [e, psgn]
  push_cast
  rw [norm_prod]
  exact Finset.prod_eq_one fun a _ => by rcases hsg a with h | h <;> rw [h] <;> simp

end GlobalTheory.AdTh
end

