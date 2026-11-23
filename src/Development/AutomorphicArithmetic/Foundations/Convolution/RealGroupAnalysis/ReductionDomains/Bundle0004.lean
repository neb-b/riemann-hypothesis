module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.AbLeOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem UpperTheory.ConvolutionTheory.R2.M.pow_form {F : Type} [Field F] [NumberField F] (b : A F) (a : (A F)ˣ) (n : ℕ) :
    ∃ c : A F, (nU b * mD a) ^ n = nU c * mD (a ^ n) := by
  induction n with
  | zero => exact ⟨0, by simp [M.nU_zero, M.mD_one]⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + ((a ^ n : (A F)ˣ) : A F) ^ 2 * b, ?_⟩
    rw [pow_succ (nU b * mD a), hc, pow_succ a, M.mD_mul, M.nU_add]
    simp only [mul_assoc]
    rw [← mul_assoc (mD (a ^ n)) (nU b), M.mD_mul_nU]
    simp only [mul_assoc]

private theorem UpperTheory.ConvolutionTheory.R2.M.inv_form {F : Type} [Field F] [NumberField F] (b : A F) (a : (A F)ˣ) :
    ∃ c : A F, (nU b * mD a)⁻¹ = nU c * mD a⁻¹ := by
  refine ⟨((a⁻¹ : (A F)ˣ) : A F) ^ 2 * (-b), ?_⟩
  rw [_root_.mul_inv_rev, ← M.mD_inv, ← M.nU_neg, M.mD_mul_nU]

private theorem UpperTheory.ConvolutionTheory.R2.M.ab_pow {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (n : ℕ) :
    ab (a ^ n) = ab a ^ n := by
  induction n with
  | zero => simp [M.ab_one]
  | succ n ih => rw [pow_succ, pow_succ, M.ab_mul, ih]

private theorem UpperTheory.ConvolutionTheory.R2.M.ab_le_one {F : Type} [Field F] [NumberField F] (U : Set (IdeleGroup F)) (hU : IsCompact U)
    (a : (A F)ˣ) (h : ∀ n : ℕ, a ^ n ∈ U) : ab a ≤ 1 := by
  obtain ⟨C, hC⟩ := (hU.image (M.continuous_ab (F := F))).bddAbove
  by_contra hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.mp hlt)
  have := hC (Set.mem_image_of_mem _ (h n))
  rw [M.ab_pow] at this
  exact absurd hn (not_lt.mpr this)

theorem UpperTheory.ConvolutionTheory.R2.M.borK :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ U : Set (IdeleGroup F), IsCompact U ∧ ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → a ∈ U ∧ ab a = 1 := by
  intro F _ _ _
  obtain ⟨hK, hKc⟩ := M.kkCpt F
  obtain ⟨hB, e, he⟩ := M.borHomeo F
  have hemb : IsClosedEmbedding (Subtype.val : M.Bor F → G1 F) := hB.isClosedEmbedding_subtypeVal
  have hK' : IsCompact ((Subtype.val : M.Bor F → G1 F) ⁻¹' KK F) := hemb.isCompact_preimage hKc
  let U : Set (IdeleGroup F) := Prod.fst '' (e.symm '' ((Subtype.val : M.Bor F → G1 F) ⁻¹' KK F))
  have hU : IsCompact U := (hK'.image e.symm.continuous).image continuous_fst
  have mem : ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → a ∈ U := by
    intro b a h
    refine ⟨(a, b), ⟨e (a, b), ?_, e.symm_apply_apply _⟩, rfl⟩
    change ((e (a, b) : M.Bor F) : G1 F) ∈ KK F
    rw [he]; exact h
  have le : ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → ab a ≤ 1 := by
    intro b a h
    refine M.ab_le_one U hU a fun n => ?_
    obtain ⟨c, hc⟩ := M.pow_form b a n
    refine mem c _ ?_
    rw [← hc, hK]
    rw [hK] at h
    exact (M.Ks F).pow_mem h n
  refine ⟨U, hU, fun b a h => ⟨mem b a h, le_antisymm (le b a h) ?_⟩⟩
  obtain ⟨c, hc⟩ := M.inv_form b a
  have h2 : nU c * mD a⁻¹ ∈ KK F := by
    rw [← hc, hK]
    rw [hK] at h
    exact (M.Ks F).inv_mem h
  have h3 := le c _ h2
  rw [M.ab_inv] at h3
  exact (inv_le_one₀ (M.ab_pos a)).mp h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.FromGL
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.fromGL :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ (g : G1 F), ∀ b ∈ Reduction.adelicBorel (K := F) (n := 2), ∀ k ∈ Reduction.maxCompact (K := F) (n := 2), gl g = b * k → ∃ (x : A F) (a : (A F)ˣ), ∃ k' ∈ KK F, g = nU x * mD a * k' ∧ (a : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 ∧ Reduction.adeleAbs ((b : Matrix (Fin 2) (Fin 2) (A F)) 1 1) = (ab a)⁻¹ := by
  intro F _ _ _ g b hb k hk hg
  obtain ⟨hdk, hab⟩ := M.detK F k hk
  set t := Matrix.GeneralLinearGroup.det k with ht
  have hk' : (dM t)⁻¹ * k ∈ Reduction.maxCompact (K := F) (n := 2) := mul_mem (inv_mem hdk) hk
  have hd : Matrix.GeneralLinearGroup.det (dM t) = t := by
    refine Units.ext ?_
    simp [dM, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdet : Matrix.GeneralLinearGroup.det ((dM t)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hd, ← ht, inv_mul_cancel]
  let s : G1 F := ⟨((dM t)⁻¹ * k).val, by
    have h1 := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1⟩
  have hs : gl s = (dM t)⁻¹ * k := Units.ext rfl
  have hsK : s ∈ KK F := by
    rw [(M.kkCpt F).1]
    show gl s ∈ Reduction.maxCompact (K := F) (n := 2)
    rw [hs]
    exact hk'
  have hc : gl (g * s⁻¹) = b * dM t := by
    have hm : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
    have h1 : gl (g * s⁻¹) = gl g * (gl s)⁻¹ := by
      rw [hm, eq_inv_of_mul_eq_one_left (a := gl s⁻¹) (b := gl s) (by rw [← hm, inv_mul_cancel]; exact map_one _)]
    rw [h1, hs, hg]
    group
  have hv : (g * s⁻¹).1 = (b : Matrix (Fin 2) (Fin 2) (A F)) * (dM t).val :=
    congrArg Units.val hc
  have hlow : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 0 = 0 :=
    (Reduction.mem_adelicBorel.1 hb) (show (0 : Fin 2) < 1 by decide)
  have e00 : (g * s⁻¹).1 0 0 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * s⁻¹).1 0 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * s⁻¹).1 1 0 = 0 := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two, hlow]
  have e11 : (g * s⁻¹).1 1 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F) := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet2 : (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 * ((b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F)) = 1 := by
    have h1 := (g * s⁻¹).det_coe
    rw [Matrix.det_fin_two, e00, e01, e10, e11, mul_zero, sub_zero] at h1
    exact h1
  let a : (A F)ˣ := (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 0).unit
  have ha : (a : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := IsUnit.unit_spec _
  have hinv : ((a⁻¹ : (A F)ˣ) : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [ha]; exact hdet2)
  have hh : g * s⁻¹ = nU ((b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F)) * mD a := by
    refine Subtype.ext ?_
    rw [M.val_mul (nU _) (mD a)]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, ha] using e00
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using e01
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two] using e10
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, hinv] using e11
  refine ⟨(b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F), a, s, hsK, ?_, ha, ?_⟩
  · rw [← hh, inv_mul_cancel_right]
  · have hb11 : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 = ((a⁻¹ * t⁻¹ : (A F)ˣ) : A F) := by
      rw [Units.val_mul, hinv, mul_assoc, Units.mul_inv, mul_one]
    rw [hb11, Reduction.adeleAbs_units]
    show ab (a⁻¹ * t⁻¹) = _
    rw [M.ab_mul, M.ab_inv, M.ab_inv, hab, inv_one, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.UnfL
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.unfL :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (σ) (u : G1 F → ℝ≥0∞), M.RowSec (F := F) σ → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ = M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) := by
  intro F _ _ M₀ σ u hσ hu hinv
  obtain ⟨β, hβ⟩ := M.wtEx F
  exact (M.cosetSum F M₀ σ β u hσ hβ hu hinv).symm.trans (M.wtInt F M₀ β u hβ hu hinv)
end

