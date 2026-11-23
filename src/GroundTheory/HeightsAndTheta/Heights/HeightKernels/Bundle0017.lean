module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PMultiHomogMemCoord
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace MultiHomogMemCoordinate

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mapDomain_fst_eq (m : (Σ k, ι k) →₀ ℕ) (a : K → ℕ) (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    Finsupp.mapDomain Sigma.fst m = Finsupp.equivFunOnFinite.symm a := by
  ext k
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [hm]
  · intro b _ hb
    simp [hb]
  · simp

theorem cone_monomial (y : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (a : K → ℕ)
    (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    mConeMap y (monomial m c) =
      C (aeval y (monomial m c)) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  have hX : (monomial (Finsupp.mapDomain Sigma.fst m) (1 : Ω) : MvPolynomial K Ω) =
      m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e := by
    rw [← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]
    simp only [map_pow, rename_X]
  rw [← mapDomain_fst_eq m a hm, hX]
  simp only [mConeMap, aeval_monomial, mul_pow, Finsupp.prod_mul, MvPolynomial.algebraMap_apply, map_finsuppProd,
    map_pow, map_mul]
  ring

theorem cone_eq (y : (Σ k, ι k) → Ω) (g : MRing ι) (a : K → ℕ) (hg : IsMultiHomog g a) :
    mConeMap y g = C (aeval y g) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m hm => cone_monomial y m _ a (hg m hm)

end MultiHomogMemCoordinate


open MultiHomogMemCoordinate in
theorem MultiHomogMemCoord.proof : MultiHomogMemCoord.Statement := by
  intro K _ ι _ Ω _ y g a hg
  rw [mCoordIdeal, RingHom.mem_ker, cone_eq y g a hg, C_mul_monomial, mul_one,
    monomial_eq_zero]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootAnchorNonzero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootAnchorNonzeroAlt

theorem anchorMinor_eq_one {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 =
      Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

theorem rootCoord_isIntegral {f j m : ℕ} {ζ : Fin f → Matrix (Fin j) (Fin m) ℂ} (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  classical
  apply IsIntegral.det
  intro a b
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  generalize p.2.1.orderEmbOfFin p.2.2 b = c
  refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  · rw [Fin.append_left]
    by_cases h : a = c
    · subst h; rw [Matrix.one_apply_eq]; exact isIntegral_one
    · rw [Matrix.one_apply_ne h]; exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hpow⟩ := hζ p.1 a c
    exact IsIntegral.of_pow hk (by rw [hpow]; exact isIntegral_one)

def homForm {f j m : ℕ} (q : Polynomial ℤ) (τ : Fin f) (I : PlIdx j m) : MRing (plBlocks f j m) :=
  ∑ k ∈ Finset.range (q.natDegree + 1),
    C (q.coeff k) * X ⟨τ, I⟩ ^ k * X ⟨τ, plAnchor j m⟩ ^ (q.natDegree - k)

theorem homForm_mem {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (q : Polynomial ℤ) (τ : Fin f)
    (I : PlIdx j m) (hq : Polynomial.aeval (rootCoord ζ ⟨τ, I⟩) q = 0) :
    homForm q τ I ∈ rootPointIdeal ζ := by
  show mConeMap (rootCoord ζ) (homForm q τ I) = 0
  have hA : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchorMinor_eq_one j m (ζ τ)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [homForm, mConeMap, map_sum, map_mul, map_pow, aeval_X, aeval_C, hA, map_one, one_mul]
  rw [Polynomial.aeval_eq_sum_range] at hq
  calc _ = ∑ k ∈ Finset.range (q.natDegree + 1),
        C (q.coeff k • rootCoord ζ ⟨τ, I⟩ ^ k) * (X τ : MvPolynomial (Fin f) ℂ) ^ q.natDegree := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [← pow_mul_pow_sub (X τ : MvPolynomial (Fin f) ℂ) hk', zsmul_eq_mul, map_mul, map_pow,
          eq_intCast, map_intCast, mul_pow]
        ring
    _ = 0 := by rw [← Finset.sum_mul, ← map_sum, hq, map_zero, zero_mul]

theorem eval_homForm {f j m : ℕ} {q : Polynomial ℤ} (hq : q.Monic) {τ : Fin f} {I : PlIdx j m}
    {z : (Σ _ : Fin f, PlIdx j m) → ℂ} (hz : z ⟨τ, plAnchor j m⟩ = 0) :
    eval z (map (Int.castRingHom ℂ) (homForm q τ I)) = z ⟨τ, I⟩ ^ q.natDegree := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [homForm, map_sum, map_mul, map_pow, map_C, map_X, eval_C, eval_X, hz]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp [hq.coeff_natDegree]
  · intro k hk
    have : q.natDegree - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
    simp [zero_pow this]

end RootAnchorNonzeroAlt

theorem RootAnchorNonzero.proof : RootAnchorNonzero.Statement := by
  intro f j m ζ hζ z hz τ h0
  obtain ⟨I, hI⟩ := hz.1 τ
  obtain ⟨q, hqm, hq⟩ := RootAnchorNonzeroAlt.rootCoord_isIntegral hζ ⟨τ, I⟩
  have hmem := RootAnchorNonzeroAlt.homForm_mem ζ q τ I (by rwa [Polynomial.aeval_def])
  have h := hz.2 _ hmem
  rw [RootAnchorNonzeroAlt.eval_homForm hqm h0] at h
  exact hI (pow_eq_zero_iff'.mp h).1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootDenseAlt

theorem aeval_grassPolyCoord {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval x (grassPolyCoord f j m p) = rootCoord (fun τ a b => x (τ, a, b)) p := by
  simp only [grassPolyCoord, rootCoord]
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp only [colsOf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
    onePipe, Matrix.of_apply]
  generalize (p.2.1.orderEmbOfFin p.2.2) b = c
  induction c using Fin.addCases with
  | left c => simp [Fin.append_left, Matrix.one_apply, apply_ite]
  | right c => simp [Fin.append_right]

theorem aeval_rootCoord {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ) (g : MRing (plBlocks f j m)) :
    aeval (rootCoord (fun τ a b => x (τ, a, b))) g = aeval x (aeval (grassPolyCoord f j m) g) := by
  rw [show aeval x (aeval (grassPolyCoord f j m) g) =
      ((aeval x).restrictScalars ℤ).comp (aeval (grassPolyCoord f j m)) g from rfl, comp_aeval]
  exact congrArg (fun y => aeval y g) (funext fun p => (aeval_grassPolyCoord x p).symm)

theorem aeval_comp_ringHom {σ τ Ω : Type*} [Field Ω] (φ : MvPolynomial σ ℚ →+* Ω)
    (P : τ → MvPolynomial σ ℚ) (g : MvPolynomial τ ℤ) :
    aeval (fun i => φ (P i)) g = φ (aeval P g) := by
  have : (aeval (fun i => φ (P i)) : MvPolynomial τ ℤ →ₐ[ℤ] Ω).toRingHom =
      φ.comp (aeval P).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  exact congrArg (fun ψ : MvPolynomial τ ℤ →+* Ω => ψ g) this

end RootDenseAlt

theorem RootDense.proof (h₁ : MultiHomogMemCoord.Statement) (h₂ : RootsOfUnityDense.Statement) :
    RootDense.Statement := by
  intro f j m g ⟨a, ha⟩ hg
  have hQ0 : aeval (grassPolyCoord f j m) g ≠ 0 := by
    intro h0
    apply hg
    rw [grassIdeal, h₁ (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) g a ha]
    exact (RootDenseAlt.aeval_comp_ringHom
      (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)) _ g).trans
      (by rw [h0, map_zero])
  let e := Fintype.equivFin (Fin f × Fin j × Fin m)
  have hP : rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g)) ≠ 0 := by
    intro h
    apply hQ0
    apply map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    apply rename_injective e e.injective
    simpa using h
  obtain ⟨z, hz, hzQ⟩ : ∃ z : Fin (Fintype.card (Fin f × Fin j × Fin m)) → ℂ,
      (∀ i, ∃ k : ℕ, 0 < k ∧ z i ^ k = 1) ∧
        eval z (rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g))) ≠ 0 := by
    by_contra! H
    exact hP (h₂ _ _ H)
  refine ⟨rootPointIdeal (fun τ a b => (z ∘ e) (τ, a, b)), ⟨_, fun τ a b => hz _, rfl⟩, ?_⟩
  show g ∉ mCoordIdeal _
  rw [h₁ (Fin f) (plBlocks f j m) ℂ _ g a ha]
  refine fun h => hzQ ?_
  rw [eval_rename, eval_map, ← aeval_def, ← RootDenseAlt.aeval_rootCoord]
  exact h

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootLogNormBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootLogNormBoundAlt

theorem norm_block_le (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) :
    ‖WithLp.toLp 2 v‖ ≤ ‖a‖ * Real.sqrt ((1 + m : ℝ) ^ j) := by
  rw [EuclideanSpace.norm_eq]
  have hs : ∑ I, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PlIdx j m)) I‖ ^ 2
      = ‖a‖ ^ 2 * ∑ I : PlIdx j m, ‖(colsOf (onePipe Z) I).det‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [hv, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (h₃ j m Z hZ)) (norm_nonneg _)

theorem log_block (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (ha : a ≠ 0) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) (hv0 : 0 < ‖WithLp.toLp 2 v‖) :
    -((j : ℝ) / 2 * Real.log (1 + m)) ≤ Real.log (‖a‖ / ‖WithLp.toLp 2 v‖) := by
  have hb := norm_block_le h₃ j m Z hZ a v hv
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hm : (0 : ℝ) < (1 + m : ℝ) ^ j := by positivity
  have hl := Real.log_le_log hv0 hb
  rw [Real.log_mul ha'.ne' (Real.sqrt_pos.mpr hm).ne', Real.log_sqrt hm.le, Real.log_pow] at hl
  rw [Real.log_div ha'.ne' hv0.ne']
  linarith

end RootLogNormBoundAlt


open RootLogNormBoundAlt in
theorem RootLogNormBound.proof (h₁ : RootAnchorNonzero.Statement) (h₂ : RootPointConj.Statement)
    (h₃ : PlueckerKernel.Statement) : RootLogNormBound.Statement := by
  intro f j m ζ hζ z hz
  have hpos : ∀ τ : Fin f, 0 < ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ := fun τ =>
    (fsMetric (ι := PlIdx j m)).pos _ fun h0 => by
      obtain ⟨i, hi⟩ := hz.1 τ
      exact hi (congrFun h0 i)
  have key : ∀ τ : Fin f, -((j : ℝ) / 2 * Real.log (1 + m)) ≤
      Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    intro τ
    obtain ⟨ζ', hζ', hz'⟩ := h₂ f j m ζ hζ z hz τ
    exact log_block h₃ j m ζ' (fun a b => by
        obtain ⟨k, hk, h⟩ := hζ' a b
        exact Complex.norm_eq_one_of_pow_eq_one h hk.ne')
      _ (h₁ f j m ζ hζ z hz τ) _ hz' (hpos τ)
  have hne : ∀ τ ∈ (Finset.univ : Finset (Fin f)),
      ‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ ≠ 0 := fun τ _ =>
    div_ne_zero (norm_ne_zero_iff.mpr (h₁ f j m ζ hζ z hz τ)) (hpos τ).ne'
  have e : logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z =
      ∑ τ, Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    rw [← Real.log_prod hne]
    simp [logNorm, fsMulti, HermLine.ofMetrics, fsMetric, rootAnchorSection, Finset.prod_div_distrib]
  rw [e]
  calc -grassConst f j m = ∑ _τ : Fin f, -((j : ℝ) / 2 * Real.log (1 + m)) := by
        simp [grassConst]; ring
    _ ≤ _ := Finset.sum_le_sum fun τ _ => key τ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaFirstCoordSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

namespace KThetaFirstCoordSplit

theorem term_le {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ)
    (hY : Y.PosDef) (hρ : 0 < ρ) (hρY : Y⁻¹ 0 0 = ρ ^ 2) (k : Fin g → ℤ) :
    exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := by
  set v := intVec k + (a + u₁) with hv
  have hassoc : intVec k + a + u₁ = v := add_assoc _ _ _
  rw [hassoc]
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) with hδ
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg
  have hv0 : v 0 = (k 0 : ℝ) + (a 0 + u₁ 0) := by simp [hv, intVec]
  have hδle : δ ≤ |v 0| := by
    have h := Metric.infDist_le_dist_of_mem (x := u₁ 0 + a 0)
      (Set.mem_range_self (f := ((↑) : ℤ → ℝ)) (-(k 0)))
    refine h.trans (le_of_eq ?_)
    rw [Real.dist_eq, hv0]
    congr 1
    push_cast
    ring
  have hδsq : δ ^ 2 ≤ v 0 ^ 2 := by
    rw [← sq_abs (v 0)]
    exact pow_le_pow_left₀ hδ0 hδle 2
  have hcoord : v 0 ^ 2 ≤ ρ ^ 2 * qf Y v := by
    have := KCoord.sq_coord_le Y hY 0 v
    rwa [hρY] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hkey : δ ^ 2 / ρ ^ 2 ≤ qf Y v := by
    rw [div_le_iff₀ hρ2]
    linarith [mul_comm (ρ ^ 2) (qf Y v)]
  have hexp : exp (-(π / 2) * qf Y v) ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := by
    apply exp_le_exp.2
    have h1 : (π / (2 * ρ ^ 2)) * δ ^ 2 = (π / 2) * (δ ^ 2 / ρ ^ 2) := by
      field_simp
    have h2 : (π / 2) * (δ ^ 2 / ρ ^ 2) ≤ (π / 2) * qf Y v :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    linarith
  have hsplit : exp (-π * qf Y v) = exp (-(π / 2) * qf Y v) * exp (-(π / 2) * qf Y v) := by
    rw [← exp_add]
    ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hexp (exp_pos _).le

end KThetaFirstCoordSplit

theorem ThetaFirstCoordSplit.proof : ThetaFirstCoordSplit.Statement := by
  intro g _ Y ρ a u₁ hY hρ hρY
  have hs1 : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hs2 : Summable fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + (a + u₁))) :=
    KTheta.summable_exp_qf Y hY (π / 2) (by positivity) (a + u₁)
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun k => KThetaFirstCoordSplit.term_le Y ρ a u₁ hY hρ hρY k) hs1 (hs2.mul_left _)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaInnerMean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

namespace KThetaInnerMean

theorem thetaSummand_shift {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ)
    (k : Fin g → ℤ) :
    thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k =
      Complex.exp (((2 * π * ∑ i, a i * u₂ i : ℝ) : ℂ) * Complex.I) *
        (thetaSummand X Y a b
            (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k *
          torusChar k u₂) := by
  unfold thetaSummand torusChar
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [dotProduct, Pi.add_apply, Pi.zero_apply, intVec, Complex.ofReal_zero, add_zero,
    mul_add, add_mul, Finset.sum_add_distrib, Complex.ofReal_add, Complex.ofReal_intCast,
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat]
  ring

end KThetaInnerMean


open KThetaInnerMean in
theorem ThetaInnerMean.proof (h₁ : ThetaSummandNorm.Statement) (h₂ : ThetaCubeParseval.Statement) :
    ThetaInnerMean.Statement := by
  intro g X Y a b u₁ hY
  have hS : Y.IsSymm := by
    have h := hY.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set E : ℝ := exp (-π * qf Y u₁) with hE
  have hEpos : 0 < E := exp_pos _
  set c : (Fin g → ℤ) → ℂ := fun k => thetaSummand X Y a b
    (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((0 : Fin g → ℝ) i : ℂ)) k with hc
  have hcE : ∀ k, ‖c k‖ * E = exp (-π * qf Y (intVec k + a + u₁)) := fun k =>
    h₁ g X Y a b u₁ 0 k hS
  have hcs : Summable fun k => ‖c k‖ := by
    have hs := (KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)).mul_right E⁻¹
    refine hs.congr fun k => ?_
    rw [← add_assoc, ← hcE k, mul_assoc, mul_inv_cancel₀ hEpos.ne', mul_one]
  have hN : ∀ u₂, thetaNorm X Y a b u₁ u₂ ^ 2 = ‖∑' k, c k * torusChar k u₂‖ ^ 2 * E ^ 2 := by
    intro u₂
    have h : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ * E := rfl
    rw [h, tsum_congr (fun k => thetaSummand_shift X Y a b u₁ u₂ k), tsum_mul_left, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_pow _ _ _
  simp only [hN]
  rw [integral_mul_const, h₂ g c hcs, ← tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [← mul_pow, hcE k, ← exp_nat_mul]
  congr 1
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassFibreDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

def GrassFibreDegree.Statement : Prop :=
  ∀ (n p : ℕ), p.Prime →
    vertR (grassIdeal 1 1 n) (fun _ : Fin n => fsMulti (plBlocks 1 1 n)) (C (p : ℤ)) = Real.log p

end

end GroundTheory.Heights₂.Heights
end

