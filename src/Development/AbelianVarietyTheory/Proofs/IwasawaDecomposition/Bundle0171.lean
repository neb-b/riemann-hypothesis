module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffXMulOfNotMem
section
noncomputable section

open Matrix MvPowerSeries GlobalTheory.FockSeq

namespace GlobalTheory.GaussInner

variable {σ : Type} [DecidableEq σ]

theorem coeff_X_mul_add (l : σ) (E : MvPowerSeries σ ℂ) (β : σ →₀ ℕ) :
    coeff (β + Finsupp.single l 1) (X l * E) = coeff β E := by
  rw [X_def, add_comm, coeff_add_monomial_mul, one_mul]

theorem coeff_X_mul_of_notMem (l : σ) (E : MvPowerSeries σ ℂ) {α : σ →₀ ℕ}
    (h : α ∉ Set.range fun β : σ →₀ ℕ => β + Finsupp.single l 1) : α l = 0 ∧ coeff α (X l * E) = 0 := by
  have h' : ¬ Finsupp.single l 1 ≤ α := fun hle => h ⟨_, tsub_add_cancel_of_le hle⟩
  refine ⟨by rw [Finsupp.single_le_iff] at h'; omega, ?_⟩
  rw [X_def, coeff_monomial_mul, if_neg h']

def dil (σ : Type) : Submodule ℂ (MvPowerSeries σ ℂ) where
  carrier := {E | ∀ r : ℝ, 0 ≤ r → r < 1 →
    Summable fun α : σ →₀ ℕ => r ^ α.degree * ((mfact α : ℝ) * ‖coeff α E‖ ^ 2)}
  zero_mem' r _ _ := by simp
  add_mem' {E E'} h h' r h0 h1 := by
    refine .of_nonneg_of_le (fun α => by positivity) (fun α => ?_) (((h r h0 h1).add (h' r h0 h1)).mul_left 2)
    rw [map_add (f := _), ← mul_add, ← mul_add, mul_left_comm 2, mul_left_comm 2]
    gcongr
    nlinarith [norm_add_le (coeff α E) (coeff α E'), norm_nonneg (coeff α E + coeff α E'),
      sq_nonneg (‖coeff α E‖ - ‖coeff α E'‖)]
  smul_mem' c E h r h0 h1 := by
    refine ((h r h0 h1).mul_left (‖c‖ ^ 2)).congr fun α => ?_
    rw [coeff_smul, norm_mul]; ring

theorem X_mul_mem {E : MvPowerSeries σ ℂ} (h : E ∈ dil σ) (l : σ) : X l * E ∈ dil σ := by
  intro r h0 h1
  have hρ0 := Real.sqrt_nonneg r
  have hρ1 : √r < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using h1)
  obtain ⟨C, hC⟩ := (tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1).bddAbove_range
  rw [← (add_left_injective (Finsupp.single l 1)).summable_iff
    fun α hα => by simp [(coeff_X_mul_of_notMem l E hα).2]]
  refine .of_nonneg_of_le (fun α => by dsimp; positivity) (fun β => ?_) ((h _ hρ0 hρ1).mul_left C)
  have h2 : ((β.degree + 1 : ℕ) : ℝ) * √r ^ (β.degree + 1) ≤ C := hC ⟨_, rfl⟩
  have h3 : (β l : ℝ) ≤ β.degree := Nat.cast_le.2 (Finsupp.le_degree l β)
  have h4 : r ^ (β.degree + 1) = √r ^ (β.degree + 1) * √r ^ (β.degree + 1) := by
    rw [← mul_pow, Real.mul_self_sqrt h0]
  have h5 : √r ^ (β.degree + 1) ≤ √r ^ β.degree := pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ _)
  simp only [Function.comp, coeff_X_mul_add, map_add (f := _), Finsupp.degree_single, Oscillator.mfact_add_single, h4]
  push_cast at h2 ⊢
  calc _ = (((β l : ℝ) + 1) * √r ^ (β.degree + 1)) *
        (√r ^ (β.degree + 1) * ((mfact β : ℝ) * ‖coeff β E‖ ^ 2)) := by ring
    _ ≤ (((β.degree : ℝ) + 1) * √r ^ (β.degree + 1)) *
        (√r ^ β.degree * ((mfact β : ℝ) * ‖coeff β E‖ ^ 2)) := by gcongr
    _ ≤ _ := by gcongr

def mulX (l : σ) : dil σ →ₗ[ℂ] dil σ := (LinearMap.mulLeft ℂ (X l)).restrict fun _ h => X_mul_mem h l

@[simp] theorem coe_mulX (l : σ) (E : dil σ) : (mulX l E : MvPowerSeries σ ℂ) = X l * (E : MvPowerSeries σ ℂ) := rfl

def term (t : ℝ) (E E' : MvPowerSeries σ ℂ) (α : σ →₀ ℕ) : ℂ :=
  (t : ℂ) ^ α.degree * ((mfact α : ℂ) * coeff α E * coeff α E')


omit [DecidableEq σ] in
theorem norm_term_le {t : ℝ} (ht : 0 ≤ t) (E E' : MvPowerSeries σ ℂ) (α : σ →₀ ℕ) :
    ‖term t E E' α‖ ≤ t ^ α.degree * ((mfact α : ℝ) * ‖coeff α E‖ ^ 2) +
      t ^ α.degree * ((mfact α : ℝ) * ‖coeff α E'‖ ^ 2) := by
  rw [term, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht,
    Complex.norm_natCast, ← mul_add, ← mul_add, mul_assoc]
  gcongr
  nlinarith [sq_nonneg (‖coeff α E‖ - ‖coeff α E'‖), norm_nonneg (coeff α E), norm_nonneg (coeff α E')]


omit [DecidableEq σ] in
theorem summable_norm_term {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (E E' : dil σ) :
    Summable fun α => ‖term t E.1 E'.1 α‖ :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le ht.1.le _ _)
    ((E.2 t ht.1.le ht.2).add (E'.2 t ht.1.le ht.2))

def pr {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : dil σ →ₗ[ℂ] dil σ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun E E' => ∑' α, term t E.1 E'.1 α)
    (fun E₁ E₂ E' => by
      rw [← (summable_norm_term ht E₁ E').of_norm.tsum_add (summable_norm_term ht E₂ E').of_norm]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_add, map_add (f := _)]; ring)
    (fun c E E' => by
      rw [smul_eq_mul, ← tsum_mul_left]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_smul, coeff_smul]; ring)
    (fun E E₁ E₂ => by
      rw [← (summable_norm_term ht E E₁).of_norm.tsum_add (summable_norm_term ht E E₂).of_norm]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_add, map_add (f := _)]; ring)
    (fun c E E' => by
      rw [smul_eq_mul, ← tsum_mul_left]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_smul, coeff_smul]; ring)

variable {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)


omit [DecidableEq σ] in
theorem pr_apply (E E' : dil σ) : pr ht E E' = ∑' α, term t E.1 E'.1 α := rfl


omit [DecidableEq σ] in
theorem pr_comm (E E' : dil σ) : pr ht E E' = pr ht E' E :=
  tsum_congr fun α => by simp only [term]; ring

def IsPDer (l : σ) (E D : MvPowerSeries σ ℂ) : Prop :=
  ∀ α : σ →₀ ℕ, ((α l : ℂ) + 1) * coeff (α + Finsupp.single l 1) E = coeff α D

theorem pr_mulX {l : σ} (E : dil σ) {E' D : dil σ} (h : IsPDer l E'.1 D.1) :
    pr ht (mulX l E) E' = t * pr ht E D := by
  rw [pr_apply, pr_apply, ← (add_left_injective (Finsupp.single l 1)).tsum_eq
    (fun α hα => by
      by_contra h'
      exact hα (by simp [term, (coeff_X_mul_of_notMem l _ h').2])), ← tsum_mul_left]
  refine tsum_congr fun β => ?_
  simp only [term, coe_mulX, coeff_X_mul_add, map_add (f := _), Finsupp.degree_single, Oscillator.mfact_add_single, ← h β]
  push_cast
  ring

theorem IsPDer.coeff_X_mul {l : σ} {E D : MvPowerSeries σ ℂ} (h : IsPDer l E D) (α : σ →₀ ℕ) :
    coeff α (X l * D) = (α l : ℂ) * coeff α E := by
  by_cases hα : α ∈ Set.range fun β : σ →₀ ℕ => β + Finsupp.single l 1
  · obtain ⟨β, rfl⟩ := hα
    simp [coeff_X_mul_add, ← h β]
  · simp [coeff_X_mul_of_notMem l D hα]

theorem IsPDer.X_mul {k : σ} {E D : MvPowerSeries σ ℂ} (h : IsPDer k E D) (m : σ) :
    IsPDer k (X m * E) (X m * D + (if k = m then (1 : ℂ) else 0) • E) := by
  intro α
  by_cases hk : k = m
  · subst hk
    rw [coeff_X_mul_add, map_add (f := _), h.coeff_X_mul]; simp; ring
  rw [if_neg hk, zero_smul, add_zero]
  by_cases hα : α ∈ Set.range fun β : σ →₀ ℕ => β + Finsupp.single m 1
  · obtain ⟨β, rfl⟩ := hα
    simp only
    rw [coeff_X_mul_add, add_right_comm, coeff_X_mul_add, ← h β]
    simp [Finsupp.single_apply, Ne.symm hk]
  · obtain ⟨h1, h2⟩ := coeff_X_mul_of_notMem m D hα
    rw [h2, (coeff_X_mul_of_notMem m E _).2, mul_zero]
    rintro ⟨β, hβ⟩
    have := congrArg (fun γ : σ →₀ ℕ => γ m) hβ
    simp [h1, hk] at this

variable [Fintype σ]

theorem hasDerivAt_pairing (E E' : dil σ) (D D' : σ → dil σ)
    (h : ∀ l, IsPDer l E.1 (D l).1) (h' : ∀ l, IsPDer l E'.1 (D' l).1) :
    HasDerivAt (fun s : ℝ => ∑' α, term s E.1 E'.1 α) (∑ l, pr ht (D l) (D' l)) t := by
  have hterm : ∀ s α, ∑ l, term s (mulX l (D l)).1 E'.1 α = (α.degree : ℂ) * term s E.1 E'.1 α := fun s α => by
    simp only [term, coe_mulX, (h _).coeff_X_mul, Finsupp.degree_eq_sum]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨r, htr, hr1⟩ := exists_between ht.2
  have hr : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1.trans htr, hr1⟩
  have hsum : Summable fun α : σ →₀ ℕ => r⁻¹ * ‖(α.degree : ℂ) * term r E.1 E'.1 α‖ := by
    refine Summable.mul_left _ ?_
    simp only [← hterm]
    exact (summable_sum fun l _ => (summable_norm_term hr (mulX l (D l)) E').of_norm).norm
  set c : (σ →₀ ℕ) → ℂ := fun α => (mfact α : ℂ) * coeff α (E : MvPowerSeries σ ℂ) *
    coeff α (E' : MvPowerSeries σ ℂ) with hc
  have hpow : ∀ s : ℝ, s ≠ 0 → ∀ n : ℕ, (n : ℂ) * (s : ℂ) ^ (n - 1) = (s : ℂ)⁻¹ * (n * (s : ℂ) ^ n) := by
    intro s hs n
    have : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; field_simp
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun α (s : ℝ) => term s E.1 E'.1 α)
    (g' := fun α (s : ℝ) => (α.degree : ℂ) * (s : ℂ) ^ (α.degree - 1) * c α) hsum isOpen_Ioo
    (isPreconnected_Ioo (a := 0) (b := r))
    (fun α s _ => ((hasDerivAt_pow α.degree (s : ℂ)).comp_ofReal).mul_const (c α))
    (fun α s hs => by
      have e : r⁻¹ * ‖(α.degree : ℂ) * term r E.1 E'.1 α‖ = ‖(α.degree : ℂ) * (r : ℂ) ^ (α.degree - 1) * c α‖ := by
        rw [hpow r hr.1.ne', mul_assoc, mul_assoc, norm_mul (r : ℂ)⁻¹, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg hr.1.le]
        rfl
      rw [e]
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.1.le, Real.norm_of_nonneg hs.1.le]
      gcongr
      exacts [hs.1.le, hs.2.le])
    ⟨ht.1, htr⟩ (summable_norm_term ht E E').of_norm ⟨ht.1, htr⟩
  refine key.congr_deriv ?_
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.1.ne'
  apply mul_left_cancel₀ ht0
  rw [Finset.mul_sum, ← tsum_mul_left]
  simp only [← fun l => pr_mulX ht (D l) (h' l)]
  simp only [pr_apply]
  rw [← Summable.tsum_finsetSum fun l _ => (summable_norm_term ht (mulX l (D l)) E').of_norm]
  refine tsum_congr fun α => ?_
  rw [hterm, hpow t ht.1.ne', term]
  simp only [hc]
  field_simp

theorem moments : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ) (E E' : MvPowerSeries σ ℂ), Summable (fun α : σ →₀ ℕ => (mfact α : ℝ) * ‖coeff α E‖ ^ 2) → Summable (fun α : σ →₀ ℕ => (mfact α : ℝ) * ‖coeff α E'‖ ^ 2) → (∀ l α, ((α l : ℂ) + 1) * coeff (α + Finsupp.single l 1) E = coeff α (x l • E + ∑ k, S l k • (X k * E))) → (∀ l α, ((α l : ℂ) + 1) * coeff (α + Finsupp.single l 1) E' = coeff α (y l • E' + ∑ k, T l k • (X k * E'))) → let f : ℝ → ℂ := fun s => ∑' α : σ →₀ ℕ, (s : ℂ) ^ α.degree * ((mfact α : ℂ) * coeff α E * coeff α E'); ContinuousOn f (Set.Icc 0 1) ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ (p q : σ → ℂ) (m n : Matrix σ σ ℂ), p = (t : ℂ) • (f t • y + T *ᵥ q) ∧ q = (t : ℂ) • (f t • x + S *ᵥ p) ∧ m = ((t : ℂ) * f t) • (1 : Matrix σ σ ℂ) + (t : ℂ) • vecMulVec y q + (t : ℂ) • (T * n) ∧ n = (t : ℂ) • vecMulVec x q + (t : ℂ) • (S * m) ∧ HasDerivAt f (f t * (x ⬝ᵥ y) + x ⬝ᵥ T *ᵥ q + y ⬝ᵥ S *ᵥ p + (S * m * Tᵀ).trace) t := by
  intro σ _ _ S T x y E E' hE hE' hd hd' f
  have hm : ∀ {G : MvPowerSeries σ ℂ}, Summable (fun α : σ →₀ ℕ => (mfact α : ℝ) * ‖coeff α G‖ ^ 2) →
      G ∈ dil σ := fun hG r h0 h1 =>
    .of_nonneg_of_le (fun α => by positivity)
      (fun α => mul_le_of_le_one_left (by positivity) (pow_le_one₀ h0 h1.le)) hG
  refine ⟨continuousOn_tsum (fun α => by fun_prop) (hE.add hE') fun α s hs => ?_, fun t ht => ?_⟩
  · refine (norm_term_le hs.1 E E' α).trans (add_le_add ?_ ?_) <;>
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hs.1 hs.2)
  let e : dil σ := ⟨E, hm hE⟩
  let e' : dil σ := ⟨E', hm hE'⟩
  have hD : ∀ l, IsPDer l (e : MvPowerSeries σ ℂ) (x l • e + ∑ k, S l k • mulX k e : dil σ).1 := fun l α => by
    simpa [e] using hd l α
  have hD' : ∀ l, IsPDer l (e' : MvPowerSeries σ ℂ) (y l • e' + ∑ k, T l k • mulX k e' : dil σ).1 :=
    fun l α => by simpa [e'] using hd' l α
  have hf : f t = pr ht e e' := rfl
  refine ⟨fun l => pr ht (mulX l e) e', fun l => pr ht e (mulX l e'),
    .of fun k m => pr ht (mulX k e) (mulX m e'), .of fun k m => pr ht e (mulX k (mulX m e')), ?_, ?_, ?_, ?_, ?_⟩
  · ext l
    simp [pr_mulX ht _ (hD' l), hf, mulVec, dotProduct, mul_comm]
  · ext l
    rw [pr_comm, pr_mulX ht _ (hD l), pr_comm]
    simp [hf, mulVec, dotProduct, mul_comm]
  · ext k m
    have h1 : IsPDer k (mulX m e' : MvPowerSeries σ ℂ) (mulX m (y k • e' + ∑ j, T k j • mulX j e') +
      (if k = m then (1 : ℂ) else 0) • e' : dil σ).1 := (hD' k).X_mul m
    have h2 : ∀ j, mulX m (mulX j e') = mulX j (mulX m e') := fun j => Subtype.ext (by simp [mul_left_comm])
    rw [of_apply, pr_mulX ht _ h1]
    by_cases hk : k = m <;> simp [hf, h2, hk, Matrix.mul_apply, vecMulVec_apply] <;> ring
  · ext k m
    rw [of_apply, pr_comm, pr_mulX ht _ (hD k), pr_comm]
    simp [Matrix.mul_apply, vecMulVec_apply, mul_add]
  · refine (hasDerivAt_pairing ht e e' _ _ hD hD').congr_deriv ?_
    simp only [hf, mulVec, dotProduct, trace, Matrix.diag_apply, Matrix.mul_apply, transpose_apply, of_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    have h1 : ∀ (g : σ → ℂ) (G : σ → σ → ℂ) (c : ℂ), ∑ m, T l m * (c * g m + ∑ k, S l k * G k m) =
        c * ∑ m, T l m * g m + ∑ m, (∑ k, S l k * G k m) * T l m := fun g G c => by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [h1 (fun m => pr ht e (mulX m e')) (fun k m => pr ht (mulX k e) (mulX m e'))]
    ring

end GlobalTheory.GaussInner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PointAtPlaceHom

open GlobalTheory.PointAtPlace

variable {D : D7} {θ : InfF D}

theorem infMat_mul (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    infMat D.sp.cm.sig V.gram φ (a * b) = infMat D.sp.cm.sig V.gram φ a * infMat D.sp.cm.sig V.gram φ b :=
  archM_mul V φ a b

theorem infMat_one (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    infMat D.sp.cm.sig V.gram φ 1 = 1 := archM_one V φ

theorem atTau_spec (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : IsAtTau θ V τ g (atTau θ V τ g) := by
  have hu := existsUnique_isAtTau V τ θ hθ g hg
  unfold atTau
  rw [dite_eq_left hu.exists]
  exact hu.exists.choose_spec

theorem atTau_mem (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem one_mem_UH {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH H := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H
  simp

theorem mul_mem_UH {n : ℕ} {H g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH H) : g * g' ∈ Formalism.QuantumDeterminants.UH H := by
  have h1 : gᴴ * H * g = H := hg
  have h2 : g'ᴴ * H * g' = H := hg'
  show (g * g')ᴴ * H * (g * g') = H
  calc (g * g')ᴴ * H * (g * g') = g'ᴴ * (gᴴ * H * g) * g' := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [h1, h2]

theorem atTau_one (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : atTau θ V τ 1 = 1 :=
  (existsUnique_isAtTau V τ θ hθ 1 (one_mem_UH _)).unique (atTau_spec hθ V τ (one_mem_UH _))
    ⟨one_mem _, infMat_one V _, fun _ _ => infMat_one V _⟩

theorem atTau_mul (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g' := by
  have a := atTau_spec hθ V τ hg
  have b := atTau_spec hθ V τ hg'
  refine (existsUnique_isAtTau V τ θ hθ _ (mul_mem_UH hg hg')).unique (atTau_spec hθ V τ (mul_mem_UH hg hg'))
    ⟨mul_mem a.1 b.1, ?_, fun τ' h => ?_⟩
  · rw [infMat_mul, a.2.1, b.2.1]
  · rw [infMat_mul, a.2.2 τ' h, b.2.2 τ' h, Matrix.one_mul]

theorem comm_of_mem (V : HSp D) {a k : GA D V} (ha : a ∈ GinfC V) (hk : k ∈ GfC V) : a * k = k * a := by
  have a2 : finHom V a = 1 := ha
  have k1 : infHom V k = 1 := hk
  refine mul_inv_eq_one.1 (eq_one_of_mem V _ ?_ ?_)
  · show infHom V _ = 1
    simp only [map_mul, map_inv, k1, mul_one, one_mul, mul_inv_cancel]
  · show finHom V _ = 1
    simp only [map_mul, map_inv, a2, mul_one, one_mul, mul_inv_cancel]


open Classical in
theorem entry_eq {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {h : GA D V} (hh : IsAtTau θ V τ g h) (i j : Fin V.rank) :
    (matHom V h).1 i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ' => ?_)
  · have a2 : (finHom V h).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val hh.1
    have e : finPart D ((matHom V h).1 i j) = finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
      congrFun (congrFun a2 i) j
    rw [RingHom.map_sub, RingHom.map_add (f := _), hσ.fin, e, add_zero, sub_self]
  · have e1 : θ τ' (infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := congrFun (congrFun (infMat_one V (θ τ')) i) j
    have e2 : θ τ' (infPart D ((matHom V h).1 i j)) = infMat D.sp.cm.sig V.gram (θ τ') h i j := rfl
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_add (f := _), hσ.comp, e1, e2]
    by_cases c : τ' = τ
    · subst c
      rw [hh.2.1, Pi.single_eq_same]; ring
    · rw [hh.2.2 τ' c, Pi.single_eq_of_ne c]; ring

theorem isAtTau_inv (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {h : GA D V} (hh : IsAtTau θ V τ g h) :
    IsAtTau θ V τ ((gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ) h⁻¹ := by
  have hu : IsUnit (gramAt D V τ).det := by
    have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
    rw [this]
    exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit
  have h1 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h2 : (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Matrix.nonsing_inv_mul _ hu]
  have k : ∀ φ, infMat D.sp.cm.sig V.gram φ h * infMat D.sp.cm.sig V.gram φ h⁻¹ = 1 := fun φ => by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  refine ⟨inv_mem hh.1, ?_, fun τ' c => ?_⟩
  · have := k (θ τ)
    rw [hh.2.1] at this
    rw [← Matrix.one_mul (infMat _ _ _ h⁻¹), ← h2, Matrix.mul_assoc _ g, this, Matrix.mul_one]
  · have := k (θ τ')
    rwa [hh.2.2 τ' c, Matrix.one_mul] at this

theorem continuousOn_atTau (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  have key : ∀ (i j : Fin V.rank), Continuous fun g : Matrix (Fin V.rank) (Fin V.rank) ℂ =>
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
        σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := fun i j =>
    continuous_const.add (hσ.cont.comp ((continuous_single (A := fun _ : D.what₂.Tau => ℂ) τ).comp
      ((continuous_id.matrix_elem i j).sub continuous_const)))
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    refine ((key i j).comp continuous_subtype_val).congr fun g => ?_
    exact (entry_eq hσ V τ (atTau_spec hθ V τ g.2) i j).symm
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have c : Continuous fun g : Formalism.QuantumDeterminants.UH (gramAt D V τ) => (gramAt D V τ)⁻¹ * g.1ᴴ * gramAt D V τ :=
      (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul continuous_const
    refine ((key i j).comp c).congr fun g => ?_
    exact (entry_eq hσ V τ (isAtTau_inv V τ g.2 (atTau_spec hθ V τ g.2)) i j).symm

theorem atTau_laws : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau), (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃! h, IsAtTau θ V τ g h) ∧ atTau θ V τ 1 = 1 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g') ∧ (∀ g, ∀ k ∈ GfC V, atTau θ V τ g * k = k * atTau θ V τ g) ∧ ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) :=
  fun _ θ hθ V τ => ⟨fun g hg => existsUnique_isAtTau V τ θ hθ g hg, atTau_one hθ V τ,
    fun _ hg _ hg' => atTau_mul hθ V τ hg hg', fun g _ hk => comm_of_mem V (atTau_mem V τ g) hk,
    continuousOn_atTau hθ V τ⟩

end GlobalTheory.PointAtPlaceHom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineCoverSquarePolarisationSectionsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_square_polarisation_sections : AmpleSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 2 ≤ n → ∃ (κ : Type) (s : κ → H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  first | exact @GlobalTheory.SquarePolCover.exists_cover | exact GlobalTheory.SquarePolCover.exists_cover | (intros; apply GlobalTheory.SquarePolCover.exists_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_adelicUnitaryEmbedding : ∀ (D : D7) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι → ∃ s : GA D B →* GA D A, Continuous s ∧ (∀ h g, EmbRel A B ι g h ↔ g = s h) ∧ ∀ γ ∈ GQ B, s γ ∈ GQ A := by
  first | exact @GlobalTheory.Mem.UnitaryEmb.exists_embHom | exact GlobalTheory.Mem.UnitaryEmb.exists_embHom | (intros; apply GlobalTheory.Mem.UnitaryEmb.exists_embHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadOfMatrixTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem sharp_iota_eq (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [PrimeDegreeVariant.sharp_downTo]
  rfl

theorem exists_read_of_matrix_tie (D : D7) {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} (X : CxData A)
    (fc : DefSub A → DefFace Bs) (cr : Crd A fc) (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0)
    (hv : Bs.v0 = InfinitePlace.mk D.what₂.embLL) {n : ℕ}
    (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ)
    (H E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin ((fc X.zs).Df1.nV Bs.μ0)) D.what₂.LL)
    (wU : D.what₂.Word → (fc X.zs).Dc.Mem)
    (eNu : ∀ u, (Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
    (eRR : (Fin (X.data cr true).D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V)
    (hF : FormsTie D.what₂.embLL (W := (RowSide.sharp D).Amb μ) jA H E ((RowSide.sharp D).eOp μ))
    (hE : LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin)
    (hι : ∀ y, (RowSide.sharp D).iota μ (jA (V.mulVec y)) =
      (RowSide.sharp D).jEE (eRR (((X.data cr true).ι Bs.μ0).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec y))))
    (hNu : ∀ u, ∃ L, HLatTie (D.div.Nu u) L ((fc X.zs).Dc.Xc (wU u)) (eNu u)) :
    ∃ Rd : Read D X fc (twAt D.what₂.embLL Bs.v0), HEq Rd.wU wU ∧ HEq Rd.eNu eNu ∧ HEq Rd.eRR eRR ∧
      (∀ y, HEq (Rd.jV y) (jA (V.mulVec y))) ∧ Rd.ReadingFormsSpanGoodSubspace ∧ Rd.IotaRd cr ∧ Rd.NuTie ∧
      ((∃ L, HLatTie D.div.RR L (X.data cr true).XE eRR) → Rd.RRTie cr) ∧
      ((∀ (u : D.what₂.Word) (x : Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL)
          (y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL),
          D.what₂.embLL ((fc X.zs).Dc.Pt (wU u) Bs.μ0 x y) =
            D.what₂.perCol u μ (D.jN u (eNu u x)) (jA (V.mulVec y))) → Rd.DcPt) := by
  subst hμ
  refine ⟨⟨wU, eNu, eRR, jA.comp V.mulVecLin, hv, fun a => ?_⟩, HEq.rfl, HEq.rfl, HEq.rfl, fun _ => HEq.rfl,
    ?_, fun y => ?_, hNu, fun h => h, fun h => h⟩
  · rw [emb_eq D.what₂.embLL Bs.v0 a, sgAt_mk D.what₂.embLL hv]
  · exact (GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (W := (RowSide.sharp D).Amb D.what₂.mu0) jA H E _ V hF hE).symm
  · have h := hι y
    rw [sharp_iota_eq] at h
    exact h

end GlobalTheory.Mem.SJ
end

