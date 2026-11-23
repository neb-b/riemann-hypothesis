module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AffineChartIdealPrimeAndSaturated
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0024

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerFromAffineChart
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (cycBlockWt cyc_exists_blockComponent cyc_isHomogeneous_of_isMultiHomogIdeal)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

theorem mdeg_add (m n : (Σ k, ι k) →₀ ℕ) : mdeg (m + n) = mdeg m + mdeg n := by
  funext k
  simp [mdeg, Finset.sum_add_distrib]


open Classical in
def part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) : MvPolynomial (Σ k, ι k) ℂ :=
  ∑ m ∈ s.support.filter (fun m => mdeg m = b), monomial m (AddMonoidAlgebra.coeff s m)

open Classical in
theorem coeff_part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) (m : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (part b s) m = if mdeg m = b then AddMonoidAlgebra.coeff s m else 0 := by
  unfold part
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : mdeg m = b
  · by_cases hs : m ∈ s.support
    · simp [h, hs]
    · have : AddMonoidAlgebra.coeff s m = 0 := by simpa using hs
      simp [this]
  · simp [h]

open Classical in
theorem sum_part (s : MvPolynomial (Σ k, ι k) ℂ) :
    ∑ b ∈ s.support.image mdeg, part b s = s := by
  unfold part
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact s.support_sum_monomial_coeff

theorem isMultiHomog_part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) :
    IsMultiHomog (part b s) b := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_part] at hm
  by_contra hk
  refine hm (if_neg fun h => hk ?_)
  exact congrFun h k

theorem isMultiHomog_mul {s f : MvPolynomial (Σ k, ι k) ℂ} {b a : K → ℕ}
    (hs : IsMultiHomog s b) (hf : IsMultiHomog f a) : IsMultiHomog (s * f) (b + a) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul s f hm)
  have := congrFun (mdeg_add m₁ m₂) k
  simp only [mdeg, Pi.add_apply] at this
  rw [this, hs m₁ h₁ k, hf m₂ h₂ k]
  rfl

theorem coeff_mul_eq_zero {r f : MvPolynomial (Σ k, ι k) ℂ} {b a : K → ℕ}
    (hr : ∀ m ∈ r.support, mdeg m ≠ b) (hf : IsMultiHomog f a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : mdeg m = b + a) : AddMonoidAlgebra.coeff (r * f) m = 0 := by
  classical
  by_contra h
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul r f (mem_support_iff.2 h))
  refine hr m₁ h₁ (funext fun k => ?_)
  have e := congrFun hm k
  have e' := congrFun (mdeg_add m₁ m₂) k
  have e'' : mdeg m₂ k = a k := hf m₂ h₂ k
  simp only [Pi.add_apply] at e e'
  omega

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem part_mul_mem [DecidableEq K] {I : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hI : ∀ k, I.IsHomogeneous (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι := ι) k)))
    {s f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (h : s * f ∈ I)
    (b : K → ℕ) : part b s * f ∈ I := by
  classical
  obtain ⟨g, hgI, hg⟩ := cyc_exists_blockComponent hI (b + a) Finset.univ h
  have hgeq : g = part b s * f := by
    ext m
    rw [hg m]
    by_cases hm : mdeg m = b + a
    · have e : ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k :=
        fun k _ => congrFun hm k
      rw [if_pos e]
      have hr : ∀ m' ∈ (s - part b s).support, mdeg m' ≠ b := by
        intro m' hm' hb
        rw [mem_support_iff, coeff_sub, coeff_part, if_pos hb, sub_self] at hm'
        exact hm' rfl
      have e2 : s * f = part b s * f + (s - part b s) * f := by ring
      rw [e2, MvPolynomial.coeff_add, coeff_mul_eq_zero hr hf hm, add_zero]
    · have e : ¬ ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k :=
        fun h' => hm (funext fun k => h' k (Finset.mem_univ k))
      rw [if_neg e]
      by_contra hne
      exact hm (funext fun k => isMultiHomog_mul (isMultiHomog_part b s) hf m
        (mem_support_iff.2 (Ne.symm hne)) k)
  exact hgeq ▸ hgI

theorem isHomogeneous_pow {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {I : Ideal A} (hI : I.IsHomogeneous 𝒜) (n : ℕ) :
    (I ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact (⊤ : HomogeneousIdeal 𝒜).isHomogeneous
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hI

theorem ren_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {p : (k : K) → ι k}
    {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ ReciprocityTheory.AnForm.R.chartIdeal S p) :
    renR (Σ k, ι k) g ∈ ideal S p := by
  unfold ideal
  rw [mem_map_renR_iff, RingEquiv.symm_apply_apply]
  exact hg

theorem lift_sub_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (q : Σ k, ι k) :
    lift p q - renR (Σ k, ι k) (X q) ∈ ideal S p := by
  classical
  obtain ⟨k, i⟩ := q
  unfold lift
  split_ifs with h
  · simp only at h
    subst h
    have hm : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ ReciprocityTheory.AnForm.R.chartIdeal S p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    have h2 : renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ ideal S p := ren_mem hm
    have h3 := (ideal S p).neg_mem h2
    rw [map_sub, map_one, neg_sub] at h3
    exact h3
  · have : renR (Σ k, ι k) (X (⟨k, i⟩ : Σ k, ι k)) = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
      simp [renameEquiv_apply]
    rw [this, sub_self]
    exact zero_mem _

theorem deh_sub_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (g : MvPolynomial (Σ k, ι k) ℂ) :
    bind₁ (lift p) g - renR (Σ k, ι k) g ∈ ideal S p := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    have e : renR (Σ k, ι k) (C c) = C c := by simp [renameEquiv_apply]
    rw [e, bind₁_C_right, sub_self]
    exact zero_mem _
  | add g h hg hh =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact add_mem hg hh
  | mul_X g q hg =>
    rw [map_mul, map_mul, bind₁_X_right]
    have e : bind₁ (lift p) g * lift p q - renR (Σ k, ι k) g * renR (Σ k, ι k) (X q) =
        (bind₁ (lift p) g - renR (Σ k, ι k) g) * lift p q +
          renR (Σ k, ι k) g * (lift p q - renR (Σ k, ι k) (X q)) := by ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ (lift_sub_mem S p q))

theorem map_deh_le (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal.map (bind₁ (lift p) : _ →ₐ[ℂ] _) S ≤ ideal S p := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  have hm : renR (Σ k, ι k) g ∈ ideal S p := ren_mem (Ideal.mem_sup_left hg)
  rw [Ideal.mem_comap]
  have := add_mem (deh_sub_mem S p g) hm
  rwa [sub_add_cancel] at this

theorem relation_dehom : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (f s : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ), IsMultiHomogIdeal P →
    IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) →
    IsMultiHomog f a → s ∉ Q → s * f ∈ Q ^ n ⊔ P →
    ∃ s' ∉ SncRes.ideal Q p, s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p := by
  intro K _ ι _ P Q p f s a n hP hQ hQp hX hf hs hrel
  classical
  have hI : ∀ k, (Q ^ n ⊔ P).IsHomogeneous
      (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι := ι) k)) := fun k =>
    (isHomogeneous_pow _ (cyc_isHomogeneous_of_isMultiHomogIdeal hQ k) n).sup
      (cyc_isHomogeneous_of_isMultiHomogIdeal hP k)
  obtain ⟨b, hb⟩ : ∃ b, part b s ∉ Q := by
    by_contra hall
    push_neg at hall
    exact hs (sum_part s ▸ Ideal.sum_mem _ fun b _ => hall b)
  have hmem := part_mul_mem hI hf hrel b
  refine ⟨bind₁ (lift p) (part b s), ?_, ?_⟩
  · rw [((_root_.GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.ideal_isPrime_and_mem_iff K ι Q p hQ hQp hX).2 _ b (isMultiHomog_part b s))]
    exact hb
  · have h1 := Ideal.mem_map_of_mem (bind₁ (lift p) : _ →ₐ[ℂ] _) hmem
    rw [map_mul, Ideal.map_sup, Ideal.map_pow] at h1
    exact (sup_le_sup (Ideal.pow_right_mono (map_deh_le Q p) n) (map_deh_le P p)) h1

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeModelCritChartEqZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit

open MvPolynomial MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.ModelFibreSumAlmostEverywhere

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e)

theorem fib_finite (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (modelQ M Ψ ⁻¹' {y} ∩ {x | Ψ (segre (modelLift M x x)) 0 ≠ 0}).Finite := by
  refine Set.Finite.of_finite_image (f := modelW M Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((modelW_injOn M Ψ).mono fun x hx => hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := modelW_mem_fibre M Ψ hP.1 hP.2.1.2.1 hx.2
  rwa [show modelQ M Ψ x = y from hx.1] at this

theorem psi_lift_eq {x z : M.Xc} (hz : z ∈ modelU M x)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (modelLift M z z)) = μ • Ψ (segre (modelLift M x z)) := by
  obtain ⟨c, hc, hzc⟩ := lift_compat M hz
  exact ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, by rw [hzc, segre_smul, map_smul]⟩

theorem not_flat (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin M.atlas.n) {O : Set (Fin e → ℂ)}
    (hO : IsOpen O) (hOt : O ⊆ (M.atlas.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO hne han hdet
  refine (fib_finite M Ψ hP hΨ y).not_infinite ((Set.Infinite.image
    (Set.InjOn.mono (s₁ := O ∩ (modelQ M Ψ ∘ (M.atlas.chart j).symm) ⁻¹' {y})
      (fun u hu => hOt hu.1) (M.atlas.chart j).symm.injOn) hy).mono ?_)
  rintro _ ⟨u, ⟨huO, hqu⟩, rfl⟩
  exact ⟨hqu, h0 u huO⟩

theorem det_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : M.Xc}
    {j k : Fin M.atlas.n} (hj : x ∈ (M.atlas.chart j).source) (hk : x ∈ (M.atlas.chart k).source)
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (M.atlas.chart k ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  set u := M.atlas.chart j x
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  set T := M.atlas.chart k ∘ (M.atlas.chart j).symm with hTdef
  have huk : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (M.atlas.chart k).source :=
    ⟨(M.atlas.chart j).map_source hj, by rw [mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := M.atlas.holo j k u huk
  have hTu : T u = M.atlas.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_modelQ M Ψ x k hk h0
  have heq : modelQ M Ψ ∘ (M.atlas.chart j).symm =ᶠ[𝓝 u] (modelQ M Ψ ∘ (M.atlas.chart k).symm) ∘ T := by
    filter_upwards [((M.atlas.chart j).isOpen_inter_preimage_symm (M.atlas.chart k).open_source).mem_nhds
      huk] with v hv
    simp only [hTdef, Function.comp_apply, (M.atlas.chart k).left_inv hv.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt,
    hTu]
  exact LinearMap.det_comp _ _

theorem ram_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin M.atlas.n) :
    volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' {x | Ψ (segre (modelLift M x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (M.atlas.chart k).source ∧
        LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (M.atlas.chart j).symm u0
  set V := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x0 with hVdef
  have hV : IsOpen V := (M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hl0 : Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u0))) 0 ≠ 0 := h00
  have hu0O : u0 ∈ O := ⟨⟨hu0, mem_modelU M x0⟩, hl0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r,
      Ψ (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hu).1.2 Ψ
    rw [hμeq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_modelQ M Ψ _ j ((M.atlas.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(M.atlas.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat M Ψ hP hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_chart M Ψ (j := j) ((M.atlas.chart j).map_target hwt) hk hw0
    rw [(M.atlas.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) w :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem psi0_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin M.atlas.n) :
    volume ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' {x | Ψ (segre (modelLift M x x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (M.atlas.chart j).symm u0
  set V := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x0 with hVdef
  have hV : IsOpen V := (M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x0)
  have hu0V : u0 ∈ V := ⟨hu0, mem_modelU M x0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0 with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (lift_mem M x0)
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (modelLift M x0 x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin e := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (modelLift M x0 x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O,
        Ψ' (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hu.1).2 Ψ'
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) O := by
      intro u hu
      have := analyticAt_modelQ M Ψ' _ j ((M.atlas.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(M.atlas.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, modelQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hu.1).2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m)
          (0 : (Fin e → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact not_flat M Ψ' hP hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO
  · rintro w ⟨⟨hwt, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hwb).2 Ψ
    have := congrFun hμeq 0
    rw [Pi.smul_apply, smul_eq_mul] at this
    have hw0' : Ψ (segre (modelLift M ((M.atlas.chart j).symm w) ((M.atlas.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hμ

theorem modelCrit_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (j : Fin M.atlas.n),
    IsArithVar P (n + 1) → IsGoodProj P Q →
      volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelCrit M Q) = 0 := by
  intro K _ ι _ P n M Q j hP hQ
  refine measure_mono_null ?_ (measure_union_null (psi0_null M Q hP hQ j) (ram_null M Q hP hQ j))
  rintro u ⟨hu, hc⟩
  by_cases h0 : Q (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 = 0
  · exact Or.inl ⟨hu, h0⟩
  · refine Or.inr ⟨hu, h0, ?_⟩
    rcases hc with h | ⟨k, hk, hbad⟩
    · exact absurd h h0
    · refine ⟨k, hk, ?_⟩
      by_contra hd
      exact hbad ⟨analyticAt_modelQ M Q _ k hk h0, hd⟩

end GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit
end
end

