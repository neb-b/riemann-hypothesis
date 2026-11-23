module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0012
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralAgainstPositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

noncomputable section

namespace IntegralAgainstPositive

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem finsum_nonpos_of {α : Sort*} {f : α → ℝ} (h : ∀ x, f x ≤ 0) : ∑ᶠ x, f x ≤ 0 := by
  have h0 : 0 ≤ ∑ᶠ x, -f x := finsum_nonneg fun x => neg_nonneg.2 (h x)
  rw [finsum_neg_distrib] at h0
  exact neg_nonneg.1 h0


omit [∀ k, Fintype (ι k)] in
theorem isOpen_blocksNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem isConeTangent_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y
    hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun T => T ξ) (hd.unique h0)
  simpa [smul_eq_mul] using this

theorem maDensity_nonneg_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hsp : ∀ j, IsSemipositiveRel P0 P (L j))
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun j y' => Real.log ((L j).h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j => ?_
  have hh : ContDiffAt ℝ 2 (L j).h (γ y) :=
    ((hsp j).1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log ((L j).h z)) (γ y) :=
    hh.log ((L j).pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log ((L j).h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log ((L j).h z)) ξ hA hlog
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log ((L j).h z)) ∘ γ) y ξ
  rw [hl]
  exact (hsp j).2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)

theorem proof : IntegralAgainstPositive.Statement := by
  intro K _ ι _ P P0 e L g hP0 hsp hg
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y => ?_
    have key : ∀ w, sheetDensity P hΨ.choose (pot L) g y w ≤ 0 := by
      intro w
      unfold sheetDensity
      split_ifs with hγ
      · have hsh := hγ.choose_spec
        have hz : hγ.choose y ∈ mcPts P := hsh.2.self_of_nhds.2.1
        exact mul_nonpos_of_nonpos_of_nonneg (hg _ hz) (maDensity_nonneg_of_sheet hP0 hsp hsh)
      · exact le_rfl
    exact finsum_nonpos_of fun w => finsum_nonpos_of fun _ => key w
  · exact le_rfl

end IntegralAgainstPositive

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial BlockImageHilb

noncomputable section

namespace PullConeDegree

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]


omit [CharZero Ω] in
theorem isWeightedHomogeneous_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a := by
  intro m hm
  funext k
  rw [weight_blockWeight_apply]
  exact hf m (mem_support_iff.mpr hm) k


omit [CharZero Ω] in
theorem isMultiHomog_of_isWeightedHomogeneous {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a := by
  intro m hm k
  rw [← weight_blockWeight_apply, hf (mem_support_iff.mp hm)]


omit [DecidableEq K] [CharZero Ω] in
theorem prod_X_pow_eq_monomial (a : K → ℕ) :
    (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) = monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp

theorem coeff_mConeMapQ (y : (Σ k, ι k) → Ω) (f : MvPolynomial (Σ k, ι k) ℚ) (n : K → ℕ) :
    AddMonoidAlgebra.coeff (mConeMapQ y f) (Finsupp.equivFunOnFinite.symm n) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) n f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m r rfl
    rw [mConeMapQ_eq y hm, prod_X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial,
      weightedHomogeneousComponent_of_mem (n := Finsupp.weight (NumbersDVR.blockWeight ι) m) hm]
    by_cases h : n = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm), map_zero]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, map_add (f := _), map_add (f := _)]


omit [DecidableEq K] [CharZero Ω] in
theorem exists_dvd_monomial (N : ℕ) (hne : ∀ k, Nonempty (ι k)) (μ : (Σ k, ι k) →₀ ℕ)
    (hμ : ∀ k, N * Fintype.card (ι k) ≤ ∑ i, μ ⟨k, i⟩) (r : ℚ) :
    ∃ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∣ monomial μ r := by
  have hc : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := ι k)) (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at hlt
    exact absurd (hμ k) (not_le.mpr hlt)
  choose c hc using hc
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fintype.prod_sigma, ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans
    (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) ℚ) ^ μ ⟨k, i⟩) (Finset.mem_univ (c k)))

end Lemmas

theorem proof : PullConeDegree.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L N hy hL hN d g hg hd
  have hne : ∀ k, Nonempty (ι k) := fun k => (hy k).elim fun i _ => ⟨i⟩

  have hgI : g ∈ coneNullIdeal y L := by
    rw [g.as_sum]
    refine Ideal.sum_mem _ fun μ hμ => ?_
    obtain ⟨c, hc⟩ := exists_dvd_monomial N hne μ
      (fun k => by rw [hg μ hμ k]; have := hd k; omega) (AddMonoidAlgebra.coeff g μ)
    exact Ideal.mem_of_dvd _ hc (hN c)
  have hI : coneNullIdeal y L = RingHom.ker (mConeMapQ y) ⊔
      Ideal.span (Set.range fun j => map (Int.castRingHom ℚ) (L j)) := by
    rw [coneNullIdeal, Ideal.span_union, ← map_mCoordIdeal]
    rfl
  rw [hI, Submodule.mem_sup] at hgI
  obtain ⟨u, hu, v, hv, huv⟩ := hgI
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv

  have hmapL : ∀ j, mConeMapQ y (map (Int.castRingHom ℚ) (L j)) =
      monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    intro j
    have h : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (map (Int.castRingHom ℚ) (L j)) e := fun m hm => hL j m (support_map_subset _ _ hm)
    rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog h), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
      ← algebraMap_int_eq, aeval_map_algebraMap]
  have hψg : mConeMapQ y g =
      ∑ j, mConeMapQ y (b j) * monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← huv, map_add (f := _), RingHom.mem_ker.mp hu, zero_add, ← hb, map_sum]
    simp only [map_mul, hmapL]

  refine ⟨fun j => weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (d - e) (b j),
    fun j => isMultiHomog_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm d)) hψg
  rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog hg), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
    coeff_monomial, if_pos rfl, coeff_sum] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle : Finsupp.equivFunOnFinite.symm e ≤ Finsupp.equivFunOnFinite.symm d :=
    Finsupp.le_def.mpr fun k => by simp only [Finsupp.coe_equivFunOnFinite_symm]; have := hd k; omega
  have hsub : Finsupp.equivFunOnFinite.symm d - Finsupp.equivFunOnFinite.symm e =
      Finsupp.equivFunOnFinite.symm (d - e) := by
    ext k
    simp
  rw [coeff_mul_monomial', if_pos hle, hsub, coeff_mConeMapQ]

end PullConeDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionFormsIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

theorem ResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    ResolutionFormsIndependent.Statement := by
  intro D Ω _ _ κ _ d n r b hb a ha
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set F : (Ix κ → ℂ) → ℂ := fun z => ∑ k, a k * secFun (b k) z with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_secFun _)

  have hoff : ∀ z, z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨y, c, hc, hyz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 : resPt d y = c () • z := by
      funext p
      simp [resPt, hyz]
    have h2 : F (resPt d y) = 0 := ha y
    rw [h1, hF] at h2
    simp only at h2
    rw [sum_secFun_smul hb.1] at h2
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ (hc ()))

  have hpts : ∀ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x), F z = 0 := by
    intro z hz
    have hcl := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hz
    have hsub : {z' | z' ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧
        eval z' (map (Int.castRingHom ℂ) g) ≠ 0} ⊆ {z' | F z' = 0} := by
      intro z' hz'
      exact hoff z' hz'.1 hz'.2
    exact closure_minimal hsub (isClosed_eq hFc continuous_const) hcl

  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨y₀⟩ : Nonempty d.R.X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := d.dV)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  have hz₀ : resPt d y₀ ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := d.R.mem y₀ y₀ (d.R.mem_U y₀)
  refine coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb) fun z hz => ?_
  by_cases h0 : z = 0
  · have h1 := hpts _ hz₀
    rw [hF] at h1
    simp only at h1
    rw [h0, ← zero_smul ℂ (resPt d y₀), sum_secFun_smul hb.1, h1, mul_zero]
  · refine hpts z ⟨fun k => ?_, hz⟩
    by_contra hk
    push Not at hk
    exact h0 (funext fun p => by obtain ⟨⟨⟩, i⟩ := p; exact hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormGoodPrimeIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormGoodPrimeIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ (p : ℕ) (hp : p.Prime), ¬ HasCommonZeroModP y L p hp →
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
        (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
          ∀ m : Fin (D + 1) →₀ ℕ, 0 ≤ padicValRat p ((c (Module.finrank (pullField y L) Ω)).coeff m)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocIdealKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def LocIdealKer.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (T : Submonoid (MRingOver S ι)) (d : K → ℤ),
    KH.IsMGraded S ι 𝓜 → IsMultiHomogIdeal P → (∀ t ∈ T, ∃ a : K → ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a) →
    ∀ w ∈ KH.locPart ι 𝓜 T d,
      (w ∈ locIdealPart 𝓜 T P d ↔
        IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
          (LocalizedModule.mkLinearMap T (M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M)))
          (P • ⊤ : Submodule (MRingOver S ι) M).mkQ w = 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibreDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameFibreDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))))
      (i : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) → fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k),
      IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) i →
      ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) i = projDeg x e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibrePt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameFibrePt.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))),
      IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNullModP
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def coneNullIdealZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : Ideal (MRing ι) :=
  Ideal.span ((mCoordIdeal y : Set (MRing ι)) ∪ Set.range L)

def PullConeNullModP.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ (p : ℕ) (hp : p.Prime), ¬ HasCommonZeroModP y L p hp →
      ∃ N M : ℕ, ¬ p ∣ M ∧ ∀ c : ∀ k, ι k,
        (M : MRing ι) * (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∈ coneNullIdealZ y L

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatioFieldDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RatioFieldDeg.Statement : Prop :=
  ∀ (ι : Type) (E₁ E₂ : Type) [Field E₁] [CharZero E₁] [Field E₂] [CharZero E₂] (u : ι → E₁) (v : ι → E₂)
    (D : ℕ) (e : Fin (D + 1) → ι), coordIdeal ℤ u = coordIdeal ℤ v → projDeg u e = projDeg v e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

