module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.ImInnerSelf
section
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted.BoundedOperators

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def aop (D : Submodule ℂ H) (T : H → H) (hadd : ∀ u ∈ D, ∀ v ∈ D, T (u + v) = T u + T v)
    (hsm : ∀ (c : ℂ), ∀ v ∈ D, T (c • v) = c • T v) : D →ₗ[ℂ] H where
  toFun u := T u + Complex.I • (u : H)
  map_add' u v := by
    simp only [Submodule.coe_add, hadd u u.2 v v.2, smul_add]
    abel
  map_smul' c u := by
    simp only [Submodule.coe_smul, hsm c u u.2, RingHom.id_apply, smul_add, smul_comm c Complex.I]

theorem aop_apply (D : Submodule ℂ H) (T : H → H) (hadd : ∀ u ∈ D, ∀ v ∈ D, T (u + v) = T u + T v)
    (hsm : ∀ (c : ℂ), ∀ v ∈ D, T (c • v) = c • T v) (u : D) :
    aop D T hadd hsm u = T u + Complex.I • (u : H) := rfl

theorem im_inner_self (T : H → H) (u : H) (h : ⟪T u, u⟫_ℂ = ⟪u, T u⟫_ℂ) : (⟪T u, u⟫_ℂ).im = 0 := by
  rw [← Complex.conj_eq_iff_im, inner_conj_symm]
  exact h.symm

theorem norm_le_aop (T : H → H) (u : H) (h : ⟪T u, u⟫_ℂ = ⟪u, T u⟫_ℂ) : ‖u‖ ≤ ‖T u + Complex.I • u‖ := by
  have h1 : ‖T u + Complex.I • u‖ ^ 2 = ‖T u‖ ^ 2 + ‖u‖ ^ 2 := by
    rw [@norm_add_sq ℂ, inner_smul_right, norm_smul, Complex.norm_I, one_mul]
    have h2 : RCLike.re (Complex.I * ⟪T u, u⟫_ℂ) = 0 := by
      show (Complex.I * ⟪T u, u⟫_ℂ).re = 0
      rw [Complex.mul_re, Complex.I_re, Complex.I_im, im_inner_self T u h]
      ring
    rw [h2]
    ring
  have h3 : ‖u‖ ^ 2 ≤ ‖T u + Complex.I • u‖ ^ 2 := by
    rw [h1]
    nlinarith [sq_nonneg ‖T u‖]
  nlinarith [norm_nonneg u, norm_nonneg (T u + Complex.I • u)]

end Formalism.L2.SG.Pf.admitted.BoundedOperators

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX Formalism.L2.SG.Pf.admitted.BoundedOperators

theorem c3 : SchurSymmetricDense := by
  intro n ε H _ _ _ σ hU hI D _hD hst T hadd hsm hsym hcomm
  by_cases h0 : ∀ v ∈ D, v = 0
  · refine ⟨0, fun v hv => ?_⟩
    rw [h0 v hv]
    have := hsm 0 0 D.zero_mem
    simpa using this
  push Not at h0
  obtain ⟨u0, hu0D, hu0⟩ := h0
  let A := aop D T hadd hsm
  have hbd : ∀ u : D, ‖D.subtype u‖ ≤ 1 * ‖A u‖ := by
    intro u
    rw [one_mul]
    exact norm_le_aop T u (hsym u u.2 u u.2)

  have hAg : ∀ (g : UJ ε) (u : D), σ (umat g) (A u) = A ⟨σ (umat g) u, hst g u u.2⟩ := by
    intro g u
    rw [aop_apply, aop_apply, map_add (f := _), map_smul, hcomm g u u.2]

  set S := (LinearMap.range A)ᗮ with hS
  have hSst : ∀ (g : UJ ε), ∀ x ∈ S, σ (umat g) x ∈ S := by
    intro g x hx
    rw [Submodule.mem_orthogonal]
    rintro y ⟨u, rfl⟩
    rw [← inv_inv g, ← rep_inner_left hU g⁻¹, hAg]
    exact (Submodule.mem_orthogonal _ _).1 hx _ ⟨_, rfl⟩
  have hdense : DenseRange A := by
    rcases Formalism.MainNotions.BridgeCSchur.irr_of hI S (Submodule.isClosed_orthogonal _) hSst with h | h
    · have h2 : (LinearMap.range A).topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 h
      have h3 := (Submodule.dense_iff_topologicalClosure_eq_top).2 h2
      exact h3
    · exfalso
      have hm : A ⟨u0, hu0D⟩ ∈ S := by rw [h]; trivial
      have hz : ⟪A ⟨u0, hu0D⟩, A ⟨u0, hu0D⟩⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hm _ ⟨_, rfl⟩
      rw [inner_self_eq_zero] at hz
      have := hbd ⟨u0, hu0D⟩
      rw [hz, norm_zero, mul_zero] at this
      exact hu0 (norm_le_zero_iff.1 this)
  let R : H →L[ℂ] H := LinearMap.extendOfNorm D.subtype A
  have hR : ∀ u : D, R (A u) = u := fun u => LinearMap.extendOfNorm_eq hdense ⟨1, hbd⟩ u
  have hRg : ∀ (g : UJ ε), R.comp (σ (umat g)) = (σ (umat g)).comp R := by
    intro g
    ext x
    refine hdense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro u
    simp only [ContinuousLinearMap.comp_apply]
    rw [hAg, hR, hR]
  let U : Set (H →L[ℂ] H) := Set.range (fun g : UJ ε => σ (umat g))
  have hstar : ∀ V ∈ U, star V ∈ U := by
    rintro V ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [rep_inner_left hU, inv_inv]
  have hirr : ∀ S' : Submodule ℂ H, IsClosed (S' : Set H) → (∀ V ∈ U, ∀ v ∈ S', V v ∈ S') → S' = ⊥ ∨ S' = ⊤ :=
    fun S' hS' h => Formalism.MainNotions.BridgeCSchur.irr_of hI S' hS' (fun g v hv => h _ ⟨g, rfl⟩ v hv)
  have hcommR : ∀ V ∈ U, Commute R V := by
    rintro V ⟨g, rfl⟩
    exact hRg g
  obtain ⟨lam, hlam⟩ := Formalism.MainNotions.BridgeCSchur.schur_bounded U hstar hirr R hcommR
  have hkey : ∀ u : D, (u : H) = lam • (T u + Complex.I • (u : H)) := by
    intro u
    have h1 := hR u
    rw [hlam, _root_.smul_apply, one_apply_eq_self] at h1
    exact h1.symm
  have hlam0 : lam ≠ 0 := by
    intro hl
    have := hkey ⟨u0, hu0D⟩
    rw [hl, zero_smul] at this
    exact hu0 this
  set mu : ℂ := lam⁻¹ - Complex.I with hmu
  have hT : ∀ v ∈ D, T v = mu • v := by
    intro v hv
    have h1 : v = lam • (T v + Complex.I • v) := hkey ⟨v, hv⟩
    have h2 : lam⁻¹ • v = T v + Complex.I • v := by
      calc lam⁻¹ • v = lam⁻¹ • (lam • (T v + Complex.I • v)) := congrArg _ h1
        _ = T v + Complex.I • v := by rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    rw [hmu, sub_smul, h2]
    abel
  have hreal : mu.im = 0 := by
    have h1 := hsym u0 hu0D u0 hu0D
    rw [hT u0 hu0D, inner_smul_left, inner_smul_right] at h1
    have hne : ⟪u0, u0⟫_ℂ ≠ 0 := by rwa [ne_eq, inner_self_eq_zero]
    have h2 := mul_right_cancel₀ hne h1
    exact Complex.conj_eq_iff_im.1 h2
  refine ⟨mu.re, fun v hv => ?_⟩
  rw [hT v hv]
  congr 1
  exact Complex.ext (by simp) (by simp [hreal])

end Formalism.L2.SG.Pf.admitted
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.IntegralSumCoef
section
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CoefficientIntegrals

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem re_coef_ge {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {g : UJ ε} {v : H} (hv : ‖v‖ = 1)
    (h : ‖σ (umat g) v - v‖ ≤ ‖v‖ / 2) : (1 / 2 : ℝ) ≤ (coefOn σ v v g).re := by
  have h1 : coefOn σ v v g = ⟪v, v⟫_ℂ + ⟪v, σ (umat g) v - v⟫_ℂ := by
    simp [coefOn]
  have h2 : ‖⟪v, σ (umat g) v - v⟫_ℂ‖ ≤ 1 / 2 := by
    calc _ ≤ ‖v‖ * ‖σ (umat g) v - v‖ := norm_inner_le_norm _ _
      _ ≤ 1 / 2 := by rw [hv] at h ⊢; linarith
  have h4 := (abs_le.1 ((Complex.abs_re_le_norm _).trans h2)).1
  have h5 : (⟪v, v⟫_ℂ).re = 1 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [hv] at this
    simpa using this
  rw [h1, Complex.add_re, h5]
  linarith

def sumCoef {ι : Type} [Fintype ι] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : ι → H) (g : UJ ε) : ℂ :=
  ∑ i, coefOn σ (v i) (v i) g

theorem re_sumCoef_ge {ι : Type} [Fintype ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H}
    {v : ι → H} (hv : Orthonormal ℂ v) (hW : ∀ i, v i ∈ W) {g : UJ ε}
    (hg : ∀ w ∈ W, ‖σ (umat g) w - w‖ ≤ ‖w‖ / 2) :
    (Fintype.card ι : ℝ) / 2 ≤ (sumCoef σ v g).re := by
  unfold sumCoef
  rw [Complex.re_sum]
  have hi : ∀ i, (1 / 2 : ℝ) ≤ (coefOn σ (v i) (v i) g).re := fun i =>
    re_coef_ge (hv.1 i) (hg _ (hW i))
  calc (Fintype.card ι : ℝ) / 2 = ∑ _i : ι, (1 / 2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hi i

theorem integral_sumCoef {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {d : ℝ} (hd : IsFdeg (muG ε) σ d) {v : ι → H} (hv : Orthonormal ℂ v) :
    Integrable (fun g => sumCoef σ v g * star (sumCoef σ v g)) (muG ε) ∧
      ∫ g, sumCoef σ v g * star (sumCoef σ v g) ∂(muG ε) = (Fintype.card ι : ℂ) / (d : ℂ) := by
  have hexp : (fun g : UJ ε => sumCoef σ v g * star (sumCoef σ v g)) = fun g =>
      ∑ i, ∑ j, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) := by
    funext g
    unfold sumCoef
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hint : ∀ i j, Integrable
      (fun g => coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g)) (muG ε) :=
    fun i j => (hd.2 _ _ _ _).1
  have hij : ∀ i j, ∫ g, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) ∂(muG ε) =
      if i = j then 1 / (d : ℂ) else 0 := by
    intro i j
    rw [(hd.2 _ _ _ _).2, orthonormal_iff_ite.mp hv j i, orthonormal_iff_ite.mp hv i j]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  refine ⟨?_, ?_⟩
  · rw [hexp]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  · rw [hexp, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    calc _ = ∑ i, ∑ j, ∫ g, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) ∂(muG ε) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact integral_finsetSum _ fun j _ => hint i j
      _ = _ := by
          simp only [hij, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          ring

theorem card_le {ι : Type} [Fintype ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (muG ε) σ d) {W : Submodule ℂ H} {K : Set (UJ ε)} (hKm : MeasurableSet K)
    (hKf : muG ε K ≠ ⊤) (hKpos : 0 < (muG ε).real K)
    (hK : ∀ g ∈ K, ∀ w ∈ W, ‖σ (umat g) w - w‖ ≤ ‖w‖ / 2)
    {v : ι → H} (hv : Orthonormal ℂ v) (hW : ∀ i, v i ∈ W) :
    (Fintype.card ι : ℝ) ≤ 4 / (d * (muG ε).real K) := by
  classical
  set m := (Fintype.card ι : ℝ) with hmdef
  obtain ⟨hint, hval⟩ := integral_sumCoef hd hv
  let f : UJ ε → ℝ := fun g => (sumCoef σ v g * star (sumCoef σ v g)).re
  have hfint : Integrable f (muG ε) := hint.re
  have hfn : ∀ g, f g = Complex.normSq (sumCoef σ v g) := fun g => by
    simp [f, Complex.mul_conj]
  have hf0 : ∀ g, 0 ≤ f g := fun g => by rw [hfn]; exact Complex.normSq_nonneg _
  have hm0 : 0 ≤ m := by positivity
  have hK' : ∀ g ∈ K, (m / 2) ^ 2 ≤ f g := by
    intro g hg
    have h1 := re_sumCoef_ge hv hW (hK g hg)
    rw [hfn, Complex.normSq_apply]
    nlinarith [sq_nonneg (sumCoef σ v g).im]
  have hset : (m / 2) ^ 2 * (muG ε).real K ≤ ∫ g in K, f g ∂(muG ε) :=
    by
      have := setIntegral_ge_of_const_le hKm hKf hK' hfint.integrableOn
      rwa [smul_eq_mul, mul_comm] at this
  have hle : ∫ g in K, f g ∂(muG ε) ≤ ∫ g, f g ∂(muG ε) :=
    setIntegral_le_integral hfint (Filter.Eventually.of_forall hf0)
  have htot : ∫ g, f g ∂(muG ε) = m / d := by
    show ∫ g, (sumCoef σ v g * star (sumCoef σ v g)).re ∂(muG ε) = m / d
    have hc : ((Fintype.card ι : ℂ) / (d : ℂ)) = ((m / d : ℝ) : ℂ) := by
      rw [hmdef]
      push_cast
      ring
    have hr := integral_re hint
    simp only [RCLike.re_to_complex] at hr
    rw [hr, hval, hc, Complex.ofReal_re]
  have hd0 := hd.1
  rcases eq_or_lt_of_le hm0 with h0 | hpos
  · rw [← h0]
    exact div_nonneg (by norm_num) (mul_pos hd0 hKpos).le
  · rw [le_div_iff₀ (mul_pos hd0 hKpos)]
    have hA : (m / 2) ^ 2 * (muG ε).real K ≤ m / d := (hset.trans hle).trans_eq htot
    have hB : (m / 2) ^ 2 * (muG ε).real K * d ≤ m := by
      have := mul_le_mul_of_nonneg_right hA hd0.le
      rwa [div_mul_cancel₀ _ hd0.ne'] at this
    nlinarith [hB, hpos, mul_pos hd0 hKpos]

end CoefficientIntegrals

open CoefficientIntegrals in
theorem c7 : FormalDegreeFiniteDim := by
  intro n ε H _ _ _ σ _ d hd W U hU hUW
  classical
  haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKf : muG ε K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < (muG ε).real K :=
    ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds (muG ε) hKn).ne' hKf
  have hbound : ∀ (m : ℕ) (v : Fin m → H), Orthonormal ℂ v → (∀ i, v i ∈ W) →
      (m : ℝ) ≤ 4 / (d * (muG ε).real K) := by
    intro m v hv hvW
    simpa using card_le hd hKm hKf hKpos (fun g hg => hUW g (hKU hg)) hv hvW
  by_contra hfin
  obtain ⟨m, hm⟩ := exists_nat_gt (4 / (d * (muG ε).real K))
  let bW := Module.Basis.ofVectorSpace ℂ W
  have hI : (Module.Basis.ofVectorSpaceIndex ℂ W).Infinite := by
    intro hfinI
    haveI : Finite (Module.Basis.ofVectorSpaceIndex ℂ W) := hfinI.to_subtype
    exact hfin (Module.Finite.of_basis bW)
  obtain ⟨t, htsub, htcard⟩ := hI.exists_subset_card_eq m
  let u : t → W := fun x => bW ⟨x.1, htsub x.2⟩
  have hu : LinearIndependent ℂ u :=
    bW.linearIndependent.comp _ (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  let F : Submodule ℂ W := Submodule.span ℂ (Set.range u)
  haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have hF : Module.finrank ℂ F = m := by
    rw [finrank_span_eq_card hu]
    simp [htcard]
  let ob := stdOrthonormalBasis ℂ F
  let v : Fin (Module.finrank ℂ F) → H := fun i => ((ob i : F) : W)
  have hv : Orthonormal ℂ v :=
    (ob.orthonormal.comp_linearIsometry F.subtypeₗᵢ).comp_linearIsometry W.subtypeₗᵢ
  have h := hbound _ v hv (fun i => ((ob i : F) : W).2)
  rw [hF] at h
  linarith

end Formalism.L2.SG.Pf.admitted
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.SgCases
section
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GeneratorWeights

variable {n : ℕ}

theorem sg_cases (ε : Fin n → Bool) (p : Fin n × Fin n) : sg ε p = 1 ∨ sg ε p = -1 := by
  unfold sg
  split_ifs <;> simp

theorem wt_ge (p : Fin n × Fin n) : 1 / 2 ≤ wt p := by
  unfold wt
  split_ifs <;> norm_num

theorem wt_le (p : Fin n × Fin n) : wt p ≤ 1 := by
  unfold wt
  split_ifs <;> norm_num

theorem gen_mem (ε : Fin n → Bool) (p : Fin n × Fin n) : inG ε (gen ε p) := by
  obtain ⟨a, b⟩ := p
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ i j, star (X j i) * (if ε j = true then 1 else -1) +
      (if ε i = true then 1 else -1) * X i j = 0) → inG ε X := by
    intro X hX
    unfold inG
    ext i j
    simpa [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using hX i j
  apply key
  intro i j
  unfold gen sg
  by_cases hab : a = b
  · subst hab
    simp only [if_true, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
    by_cases h : a = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h
      cases ha : ε a <;> simp [ha]
    · have h' : ¬ (a = j ∧ a = i) := fun h2 => h ⟨h2.2, h2.1⟩
      simp [h, h']
  · have hba : ¬ b = a := Ne.symm hab
    by_cases hlt : a < b
    · simp only [hab, hlt, if_false, if_true, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.single_apply]
      by_cases h1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := h1
        cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba]
      · by_cases h2 : b = i ∧ a = j
        · obtain ⟨rfl, rfl⟩ := h2
          cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba]
        · have h1' : ¬ (a = j ∧ b = i) := fun h => h2 ⟨h.2, h.1⟩
          have h2' : ¬ (b = j ∧ a = i) := fun h => h1 ⟨h.2, h.1⟩
          simp [h1, h2, h1', h2']
    · simp only [hab, hlt, if_false, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.single_apply]
      by_cases h1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := h1
        cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba] <;> ring1
      · by_cases h2 : b = i ∧ a = j
        · obtain ⟨rfl, rfl⟩ := h2
          cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, hab, hba] <;> ring1
        · have h1' : ¬ (a = j ∧ b = i) := fun h => h2 ⟨h.2, h.1⟩
          have h2' : ¬ (b = j ∧ a = i) := fun h => h1 ⟨h.2, h.1⟩
          simp [h1, h2, h1', h2']

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}

theorem sum_eq (hC : Calc ε σ D) {c : ℝ} (hc : ∀ v ∈ D, Cas ε σ v = (c : ℂ) • v) {v : H} (hv : v ∈ D) :
    ∑ p : Fin n × Fin n, wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 = c * ‖v‖ ^ 2 := by
  have hgen : ∀ p, inG ε (gen ε p) := gen_mem ε
  have key : ⟪Cas ε σ v, v⟫_ℂ =
      ∑ p, ((wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ) := by
    unfold Cas
    rw [inner_neg_left, sum_inner, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_smul_left, hC.skew _ (hgen p) _ (hC.mem _ (hgen p) v hv) v hv,
      inner_self_eq_norm_sq_to_K]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have h2 : ((c * ‖v‖ ^ 2 : ℝ) : ℂ) =
      ((∑ p, wt p * sg ε p * ‖dS σ (gen ε p) v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← key, hc v hv, inner_smul_left, inner_self_eq_norm_sq_to_K]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  exact (Complex.ofReal_inj.1 h2).symm

end GeneratorWeights

open GeneratorWeights in
theorem c4 : CasimirScalarBounded := by
  intro n ε H _ _ _ σ D hC c hc W C hW
  set K : ℝ := 2 * ((Fintype.card (Fin n × Fin n) : ℝ) * C ^ 2 + |c|) with hK
  refine ⟨max C (Real.sqrt K), fun p v hvD hvW => ?_⟩
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  by_cases hp : ε p.1 = ε p.2
  · exact (hW p hp v hvW).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv0)
  · have hsum := sum_eq hC hc hvD
    have hsgp : sg ε p = -1 := by simp [sg, hp]
    have hterm : ∀ q, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
      intro q
      have h3 := wt_le q
      have h4 := wt_ge q
      rcases sg_cases ε q with h | h
      · have hq : ε q.1 = ε q.2 := by
          by_contra hne
          simp [sg, hne] at h
          norm_num at h
        have h1 := hW q hq v hvW
        have h2 : ‖dS σ (gen ε q) v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        rw [h, mul_one]
        have h5 : wt q * ‖dS σ (gen ε q) v‖ ^ 2 ≤ 1 * ‖dS σ (gen ε q) v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
        nlinarith [h2, h5]
      · rw [h]
        have h5 : 0 ≤ wt q * ‖dS σ (gen ε q) v‖ ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        nlinarith [sq_nonneg (C * ‖v‖), h5]
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun q => wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2) (Finset.mem_univ p)
    have hrest : ∑ q ∈ Finset.univ.erase p, wt q * sg ε q * ‖dS σ (gen ε q) v‖ ^ 2 ≤
        (Fintype.card (Fin n × Fin n) : ℝ) * (C ^ 2 * ‖v‖ ^ 2) := by
      calc _ ≤ ∑ q ∈ Finset.univ.erase p, C ^ 2 * ‖v‖ ^ 2 :=
            Finset.sum_le_sum fun q _ => hterm q
        _ = ((Finset.univ.erase p).card : ℝ) * (C ^ 2 * ‖v‖ ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Finset.card_erase_le.trans (le_of_eq Finset.card_univ)))
            (by positivity)
    have hwp := wt_ge p
    rw [hsgp] at hsplit
    have e2 : (1 / 2) * ‖dS σ (gen ε p) v‖ ^ 2 ≤ wt p * ‖dS σ (gen ε p) v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hwp (sq_nonneg _)
    have e3 : -c * ‖v‖ ^ 2 ≤ |c| * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_le_abs c) (sq_nonneg _)
    have hsq : ‖dS σ (gen ε p) v‖ ^ 2 ≤ K * ‖v‖ ^ 2 := by
      rw [hK]
      nlinarith [hsplit, hsum, hrest, e2, e3]
    have hK0 : 0 ≤ K := by positivity
    have hle : ‖dS σ (gen ε p) v‖ ≤ Real.sqrt K * ‖v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (dS σ (gen ε p) v)), ← Real.sqrt_sq hv0,
        ← Real.sqrt_mul hK0]
      exact Real.sqrt_le_sqrt hsq
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hv0)

end Formalism.L2.SG.Pf.admitted
end
end

