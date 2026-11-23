module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0004
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormIndexQuadratic

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.FourValues
section
open NumberField Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem four_values (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Δ x : F)
    (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (hx : ∀ σ : F →+* ℝ, 0 < σ x) :
    x ≠ 0 ∧ ∃ a b c d : F, x = a ^ 2 - Δ * b ^ 2 + (c ^ 2 - Δ * d ^ 2) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let σ : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have hx0 : x ≠ 0 := fun h => by simpa [h] using hx σ
  have hΔ0 : Δ ≠ 0 := fun h => by simpa [h] using hΔ σ
  refine ⟨hx0, ?_⟩
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt F (ι := Fin 5) ![1, -Δ, 1, -Δ, -x]
    (by simp) (fun i => by fin_cases i <;> simp [hx0, hΔ0])
    (fun s => ⟨4, 0, by simpa using hx s, by simp⟩)
  simp [Fin.sum_univ_succ] at hy
  have hy' : y 0 ^ 2 - Δ * y 1 ^ 2 + (y 2 ^ 2 - Δ * y 3 ^ 2) = x * y 4 ^ 2 := by
    linear_combination hy
  have he : y 4 ≠ 0 := by
    intro h
    apply hy0
    have h1 := congrArg σ hy'
    simp only [h, map_add (f := _), map_sub, map_mul, map_pow, map_zero] at h1
    have hn := hΔ σ
    have p1 : 0 ≤ -σ Δ * σ (y 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have p3 : 0 ≤ -σ Δ * σ (y 3) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have p0 := sq_nonneg (σ (y 0))
    have p2 := sq_nonneg (σ (y 2))
    have e0 : σ (y 0) ^ 2 = 0 := by nlinarith
    have e2 : σ (y 2) ^ 2 = 0 := by nlinarith
    have e1 : -σ Δ * σ (y 1) ^ 2 = 0 := by nlinarith
    have e3 : -σ Δ * σ (y 3) ^ 2 = 0 := by nlinarith
    have z0 : y 0 = 0 := by simpa using e0
    have z2 : y 2 = 0 := by simpa using e2
    have z1 : y 1 = 0 := by simpa [hΔ0] using e1
    have z3 : y 3 = 0 := by simpa [hΔ0] using e3
    funext i
    fin_cases i
    exacts [z0, z1, z2, z3, h]
  refine ⟨y 0 / y 4, y 1 / y 4, y 2 / y 4, y 3 / y 4, ?_⟩
  field_simp
  linear_combination -hy'

private theorem ex_DX {K : Type} [Field K] (Δ x : K) (hx : x ≠ 0) (a b : Lsq K Δ)
    (h : a * star a + b * star b = algebraMap K _ x) : ∃ g : DX Δ, (mt g).det = algebraMap K _ x := by
  have hd : (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = algebraMap K _ x := by
    rw [det_fin_two_of, ← h]; ring
  have hu : IsUnit (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, hd]
    exact (IsUnit.mk0 x hx).map _
  refine ⟨⟨hu.unit, ?_⟩, hd⟩
  show GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) hu.unit = (wJ Δ)⁻¹ * hu.unit * (wJ Δ)⁻¹⁻¹
  rw [inv_inv]
  apply Units.ext
  show (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd (Lsq K Δ)) =
    !![0, -1; 1, 0] * !![a, b; -star b, star a] * !![0, 1; -1, 0]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]

theorem UpperTheory.V.Z.Sym.Glob.normD :
    UpperTheory.V.Z.Sym.Glob.NormD := by
  intro F _ _ Δ D hD x hx
  haveI := hD.real
  obtain ⟨hx0, a, b, c, d, h⟩ := four_values F Δ x hD.neg hx
  refine ex_DX Δ x hx0 ⟨a, b⟩ ⟨c, d⟩ ?_
  ext
  · simp; linear_combination -h
  · simp; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GlobNegOne
section
open NumberField IsDedekindDomain Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem mk_el {K : Type} [Field K] {Δ : K} (a b : Lsq K Δ) (h : a * star a + b * star b = 1) :
    ∃ γ : DX Δ, mt γ = !![a, b; -star b, star a] := by
  let g : GL (Fin 2) (Lsq K Δ) := ⟨!![a, b; -star b, star a], !![star a, -b; star b, a], by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    ext1 i; fin_cases i <;> (ext1 j; fin_cases j) <;> simp <;> first | ring1 | linear_combination h, by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    ext1 i; fin_cases i <;> (ext1 j; fin_cases j) <;> simp <;> first | ring1 | linear_combination h⟩
  refine ⟨⟨g, ?_⟩, rfl⟩
  change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * ((wJ Δ)⁻¹)⁻¹
  rw [inv_inv]
  refine Units.ext ?_
  change (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) =
    !![0, -1; 1, 0] * !![a, b; -star b, star a] * !![0, 1; -1, 0]
  ext1 i j
  fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]

private theorem el_shape {K : Type} [Field K] {Δ : K} (γ : DX Δ) :
    mt γ 1 1 = star (mt γ 0 0) ∧ mt γ 1 0 = -star (mt γ 0 1) := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) γ.1 = (wJ Δ)⁻¹ * γ.1 * ((wJ Δ)⁻¹)⁻¹ := γ.2
  rw [inv_inv] at h
  have h' : (mt γ).map (starRingEnd _) = !![0, -1; 1, 0] * mt γ * !![0, 1; -1, 0] := congrArg Units.val h
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] at h0 h1
  exact ⟨h0.symm, by rw [h1, neg_neg]⟩

private theorem loc_neg_one {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (hD : D.Ok) (h0 : Δ ≠ 0) (v : Pl F) :
    ∃ a b : Kv v, -1 = a ^ 2 - cv v Δ * b ^ 2 := by
  by_cases hv : v ∈ D.Sg
  · have : CharZero (Kv v) := charZero_of_injective_algebraMap (cv v).injective
    exact GlobalTheory.Published.HasseNormSt.of_isSquare ((map_ne_zero _).2 h0) (hD.split v hv) _
  · obtain ⟨ν, -, hν⟩ := Loc.normEx _ _ _ (hD.off v hv) (-1)
    refine ⟨ν.re, ν.im, ?_⟩
    rw [QuadraticAlgebra.norm_def] at hν
    simp only [Units.val_neg, Units.val_one, map_neg, map_one] at hν
    linear_combination -hν

private theorem glob_neg_one {F : Type} [Field F] [NumberField F] {Δ d : F} (h0 : Δ ≠ 0)
    (hl : ∀ v : Pl F, ∃ a b : Kv v, -1 = a ^ 2 - cv v Δ * b ^ 2) (σ₀ : F →+* ℝ) (hd : ∀ σ : F →+* ℝ, σ d < 0) :
    ∃ p₀ p₁ q₀ q₁ : F, p₀ ^ 2 + d * p₁ ^ 2 - Δ * (q₀ ^ 2 + d * q₁ ^ 2) = -1 ∧ p₀ * p₁ = Δ * q₀ * q₁ :=
  _root_.UpperTheory.Reformulated.B.NormIndexQuadratic.glob_neg_one h0 hl σ₀ hd

theorem UpperTheory.V.Z.Sym.Glob.embEx :
    UpperTheory.V.Z.Sym.Glob.EmbEx := by
  intro F _ _ Δ D hD τ
  have := hD.real
  obtain ⟨σ₀⟩ : Nonempty (F →+* ℝ) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩
  have h0 : Δ ≠ 0 := fun h => by simpa [h] using hD.neg σ₀
  refine ⟨fun hτ => ?_, fun γ hγ hτ σ => ?_⟩
  · obtain ⟨p₀, p₁, q₀, q₁, e₁, e₂⟩ := glob_neg_one h0 (loc_neg_one D hD h0) σ₀ hτ
    have hA : p₁ ^ 2 - Δ * q₁ ^ 2 ≠ 0 := fun h => by
      have h1 : p₀ ^ 2 + 1 - Δ * q₀ ^ 2 = 0 := by linear_combination e₁ - (τ ^ 2 - 4) * h
      have h2 := congrArg σ₀ h1
      simp only [map_sub, map_add (f := _), map_mul, map_pow, map_one, map_zero] at h2
      nlinarith [hD.neg σ₀, sq_nonneg (σ₀ p₀), sq_nonneg (σ₀ q₀)]
    obtain ⟨A, hAe⟩ : ∃ A, A = p₁ ^ 2 - Δ * q₁ ^ 2 := ⟨_, rfl⟩
    rw [← hAe] at hA
    have key : p₁ ^ 2 - Δ * (p₀ * q₁ - q₀ * p₁) ^ 2 - Δ * q₁ ^ 2 = -(τ ^ 2 - 4) * A ^ 2 := by
      rw [hAe]
      linear_combination (p₁ ^ 2 - Δ * q₁ ^ 2) * e₁ - (p₀ * p₁ - Δ * q₀ * q₁) * e₂
    let a : Lsq F Δ := ⟨τ / 2, (p₀ * q₁ - q₀ * p₁) / (2 * A)⟩
    let b : Lsq F Δ := ⟨p₁ / (2 * A), q₁ / (2 * A)⟩
    have hab : a * star a + b * star b = 1 := by
      ext
      · simp [a, b, QuadraticAlgebra.re_one]
        field_simp
        linear_combination key
      · simp [a, b, QuadraticAlgebra.im_one]
        ring
    obtain ⟨γ, hγ⟩ := mk_el a b hab
    refine ⟨γ, ?_, ?_⟩
    · rw [hγ, Matrix.det_fin_two_of]
      linear_combination hab
    · rw [hγ, Matrix.trace_fin_two_of]
      ext <;> simp [a]
  · obtain ⟨s₁, s₂⟩ := el_shape γ
    obtain ⟨hd, ht⟩ := hγ
    rw [Matrix.det_fin_two, s₁, s₂] at hd
    rw [Matrix.trace_fin_two, s₁] at ht
    generalize mt γ 0 0 = a at hd ht
    generalize mt γ 0 1 = b at hd
    have h1 := congrArg (fun x => σ (QuadraticAlgebra.re x)) hd
    have h2 := congrArg (fun x => σ (QuadraticAlgebra.re x)) ht
    simp [QuadraticAlgebra.re_one] at h1 h2
    refine lt_of_le_of_ne ?_ ((map_ne_zero σ).2 hτ)
    simp only [map_sub, map_pow, map_ofNat]
    rw [← h2]
    nlinarith [mul_nonneg (neg_pos.2 (hD.neg σ)).le (mul_self_nonneg (σ a.im)),
      mul_nonneg (neg_pos.2 (hD.neg σ)).le (mul_self_nonneg (σ b.im)), mul_self_nonneg (σ b.re)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsHasse
section
open UpperTheory.V.Z.Sym.Loc in
private theorem hs_eq_one_iff {K : Type} [Field K] (d x : K) :
    hs d x = 1 ↔ ∃ a b : K, x = a ^ 2 - d * b ^ 2 := by
  unfold hs
  constructor
  · intro h
    by_contra hn
    rw [if_neg (fun ⟨a, b, e⟩ => hn ⟨a, b, e.symm⟩)] at h
    norm_num at h
  · rintro ⟨a, b, e⟩
    exact if_pos ⟨a, b, e.symm⟩

theorem UpperTheory.V.Z.Sym.Glob.hsHasse :
    UpperTheory.V.Z.Sym.Glob.HsHasse := by
  intro F _ _ d x hd hx hr hf
  rw [hs_eq_one_iff]
  exact GlobalTheory.QNorm.hasseNormSt F d x hd hx (fun σ => (hs_eq_one_iff _ _).1 (hr σ))
    (fun v => (hs_eq_one_iff _ _).1 (hf v))
end

