module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SetIntegralFderivEqZeroOfLatticePeriodic
section
open Complex Matrix
open scoped ContDiff BigOperators Real
open MeasureTheory Module
open scoped Pointwise

namespace GlobalTheory

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]


omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem setIntegral_comp_add_of_lattice_periodic [SecondCountableTopology E]
    (L : Submodule ℤ E) [Countable L] {D : Set E}
    (hD : IsAddFundamentalDomain L D μ) {F : E → ℂ} (hF : ∀ (l : L) z, F (z + l) = F z) (c : E) :
    ∫ z in D, F (z + c) ∂μ = ∫ z in D, F z ∂μ := by
  have : VAddInvariantMeasure L E μ := ⟨fun g s _ => measure_preimage_add μ (g : E) s⟩
  have hpres := measurePreserving_add_right μ c
  have hD' : IsAddFundamentalDomain L ((fun x => x + c) '' D) μ :=
    hD.image_of_equiv (Equiv.addRight c)
      (measurePreserving_add_right μ (-c)).quasiMeasurePreserving (Equiv.refl _)
      (fun g x => add_assoc _ _ _)
  rw [← hpres.setIntegral_image_emb (MeasurableEquiv.addRight c).measurableEmbedding]
  refine (hD'.setIntegral_eq hD fun g x => ?_)
  show F ((g : E) + x) = F x
  rw [add_comm]
  exact hF g x

theorem setIntegral_fderiv_eq_zero_of_lattice_periodic
    (L : Submodule ℤ E) [Countable L] {D : Set E}
    (hD : IsAddFundamentalDomain L D μ) (hm : MeasurableSet D) (hb : Bornology.IsBounded D)
    {F : E → ℂ} (hF1 : ContDiff ℝ 1 F) (hF : ∀ (l : L) z, F (z + l) = F z) (v : E) :
    ∫ z in D, fderiv ℝ F z v ∂μ = 0 := by
  have hcont : Continuous (fderiv ℝ F) := hF1.continuous_fderiv one_ne_zero
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hK : IsCompact (Metric.closedBall (0 : E) (R + ‖v‖)) := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hfin : μ D < ⊤ := hb.measure_lt_top
  have : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hfin.ne
  have hint : ∀ G : E → ℂ, Continuous G → Integrable G (μ.restrict D) := fun G hG =>
    (hG.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) R)).mono_set hR
  have hmem : ∀ z ∈ D, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      z + t • v ∈ Metric.closedBall (0 : E) (R + ‖v‖) := by
    intro z hz t ht
    rw [mem_closedBall_zero_iff]
    have h1 : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 (hR hz)
    have ht' : ‖t‖ < 1 := by simpa using ht
    have h2 : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul]
      nlinarith [norm_nonneg v, norm_nonneg t]
    calc ‖z + t • v‖ ≤ ‖z‖ + ‖t • v‖ := norm_add_le _ _
      _ ≤ R + ‖v‖ := add_le_add h1 h2
  have hderiv : ∀ (z : E) (t : ℝ),
      HasDerivAt (fun s : ℝ => F (z + s • v)) (fderiv ℝ F (z + t • v) v) t := by
    intro z t
    have hd : HasFDerivAt F (fderiv ℝ F (z + t • v)) (z + t • v) :=
      (hF1.differentiable one_ne_zero _).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => z + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add z
    exact hd.comp_hasDerivAt t hl
  have hmeas : ∀ᶠ s in nhds (0 : ℝ), AEStronglyMeasurable (fun z => F (z + s • v)) (μ.restrict D) :=
    Filter.Eventually.of_forall fun s =>
      (hF1.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hint0 : Integrable (fun z => F (z + (0 : ℝ) • v)) (μ.restrict D) :=
    hint _ (hF1.continuous.comp (continuous_id.add continuous_const))
  have hmeas' : AEStronglyMeasurable (fun z => fderiv ℝ F (z + (0 : ℝ) • v) v) (μ.restrict D) :=
    ((hcont.comp (continuous_id.add continuous_const)).clm_apply continuous_const).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(μ.restrict D), ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖fderiv ℝ F (z + s • v) v‖ ≤ M * ‖v‖ := by
    refine (ae_restrict_iff' hm).2 (Filter.Eventually.of_forall fun z hz s hs => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM _ (hmem z hz s hs)) (norm_nonneg _))
  have hdiff : ∀ᵐ z ∂(μ.restrict D), ∀ s ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F (z + t • v)) (fderiv ℝ F (z + s • v) v) s :=
    Filter.Eventually.of_forall fun z s _ => hderiv z s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := μ.restrict D)
    (F := fun (s : ℝ) (z : E) => F (z + s • v)) (x₀ := 0) (bound := fun _ => M * ‖v‖)
    (F' := fun (s : ℝ) (z : E) => fderiv ℝ F (z + s • v) v)
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) hmeas hint0 hmeas' hbound (integrable_const _) hdiff
  have hconst : (fun s : ℝ => ∫ z in D, F (z + s • v) ∂μ) = fun _ => ∫ z in D, F z ∂μ :=
    funext fun s => setIntegral_comp_add_of_lattice_periodic μ L hD hF (s • v)
  have h3 : HasDerivAt (fun _ : ℝ => ∫ z in D, F z ∂μ)
      (∫ z in D, fderiv ℝ F (z + (0 : ℝ) • v) v ∂μ) 0 := by
    rw [← hconst]
    exact key.2
  simpa using h3.unique (hasDerivAt_const _ _)

theorem const_eq_zero_of_sum_fderiv_lattice_periodic
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    {F : ι → E → ℂ} {a : ι → ℂ} {v : ι → E} {C : ℂ}
    (hF : ∀ k, ContDiff ℝ 1 (F k) ∧ ∀ (l : L) z, F k (z + l) = F k z)
    (hC : ∀ z, ∑ k, a k * fderiv ℝ (F k) z (v k) = C) : C = 0 := by
  classical
  let μ : Measure E := Measure.addHaar
  let b := Module.Free.chooseBasis ℤ L
  have hD : IsAddFundamentalDomain L (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) μ :=
    ZLattice.isAddFundamentalDomain b μ
  have hm : MeasurableSet (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_measurableSet _
  have hb : Bornology.IsBounded (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_isBounded _
  set D := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) with hDdef
  have hzero : ∀ k, ∫ z in D, fderiv ℝ (F k) z (v k) ∂μ = 0 := fun k =>
    setIntegral_fderiv_eq_zero_of_lattice_periodic μ L hD hm hb (hF k).1 (hF k).2 (v k)
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hint : ∀ k, IntegrableOn (fun z => a k * fderiv ℝ (F k) z (v k)) D μ := fun k =>
    ((continuous_const.mul
      (((hF k).1.continuous_fderiv one_ne_zero).clm_apply continuous_const)).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : E) R)).mono_set hR
  have hsum : ∫ z in D, (∑ k, a k * fderiv ℝ (F k) z (v k)) ∂μ = 0 := by
    rw [integral_finsetSum _ (fun k _ => hint k)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_const_mul, hzero k, mul_zero]
  simp_rw [hC] at hsum
  rw [setIntegral_const] at hsum
  have : VAddInvariantMeasure L E μ := ⟨fun g s _ => measure_preimage_add μ (g : E) s⟩
  have hne : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)
  have hfin : μ D ≠ ⊤ := hb.measure_lt_top.ne
  rcases smul_eq_zero.1 hsum with h | h
  · exact absurd h (ENNReal.toReal_ne_zero.2 ⟨hne, hfin⟩)
  · exact h

end General

theorem const_eq_zero_of_sum_fderiv_periodic :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (n : ℕ) (F : Fin n → (Fin g → ℂ) → ℂ) (a : Fin n → ℂ) (v : Fin n → (Fin g → ℂ)) (C : ℂ),
      (∀ k, ContDiff ℝ 1 (F k) ∧ ∀ (l : Λ) z, F k (z + l) = F k z) →
      (∀ z, ∑ k, a k * fderiv ℝ (F k) z (v k) = C) → C = 0 := by
  intro g Λ hdisc hspan n F a v C hF hC
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  exact const_eq_zero_of_sum_fderiv_lattice_periodic Λ hF hC

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TracePowerSumModEq
section
open Polynomial

namespace GlobalTheory.TraceAeval

open Module

theorem trace_aeval_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (g : Module.End ℂ V) (μ : ℂ) (h : IsNilpotent (g - algebraMap ℂ _ μ)) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval g p) = (finrank ℂ V : ℂ) * p.eval μ := by
  have hk : ∀ k : ℕ, LinearMap.trace ℂ V (g ^ k) = (finrank ℂ V : ℂ) * μ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
        ((Commute.refl g).pow_left k) h
      rw [pow_succ, Module.End.mul_eq_comp, this, ih]; ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq, eval_add]; ring
  | monomial k a =>
    rw [aeval_monomial, ← Algebra.smul_def, map_smul, hk, eval_monomial, smul_eq_mul]; ring

theorem coe_aeval_restrict {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (p : ℂ[X]) (x : N) :
    ((aeval (f.restrict hf) p x : N) : V) = aeval f p x := by
  have hk : ∀ (k : ℕ) (x : N), ((((f.restrict hf) ^ k) x : N) : V) = (f ^ k) x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro x; simp [pow_succ, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a => simp [aeval_monomial, hk]

theorem trace_aeval_end {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (f : Module.End ℂ V) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval f p) = (f.charpoly.roots.map fun z => p.eval z).sum := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top f)
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hf : ∀ μ, ∀ x ∈ f.maxGenEigenspace μ, f x ∈ f.maxGenEigenspace μ :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hp : ∀ μ, Set.MapsTo (aeval f p) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) := by
    intro μ x hx
    rw [show aeval f p x = _ from (coe_aeval_restrict f _ (hf μ) p ⟨x, hx⟩).symm]
    exact Subtype.mem _
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hp]
  have h1 : ∀ μ, LinearMap.trace ℂ _ ((aeval f p).restrict (hp μ))
      = (f.charpoly.rootMultiplicity μ : ℂ) * p.eval μ := by
    intro μ
    have e : (aeval f p).restrict (hp μ) = aeval (f.restrict (hf μ)) p := by
      ext x
      rw [coe_aeval_restrict]; rfl
    have hn := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    have e2 : f.restrict (hf μ) - algebraMap ℂ _ μ = (f - algebraMap ℂ _ μ).restrict
        (f.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) := by
      ext x
      rfl
    rw [e, trace_aeval_of_isNilpotent _ μ (e2 ▸ hn), LinearMap.finrank_maxGenEigenspace_eq]
  simp_rw [h1]
  rw [Finset.sum_multiset_map_count]
  have hs : h_fin.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Multiset.mem_toFinset, Set.mem_setOf_eq,
      ← Multiset.count_ne_zero, count_roots, ← LinearMap.finrank_maxGenEigenspace_eq,
      Ne, Ne, Submodule.finrank_eq_zero]
  rw [hs]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, nsmul_eq_mul]

theorem trace_aeval_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ[X]) :
    (aeval A p).trace = (A.charpoly.roots.map fun z => p.eval z).sum := by
  rw [← Matrix.charpoly_toLin', ← trace_aeval_end, ← Matrix.trace_toLin'_eq]
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)) A p).symm

noncomputable def powMat {R : Type*} [CommRing R] (n : ℕ) (ψ : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ((X ^ ((j : ℕ) + 1)) %ₘ ψ).coeff i

open Polynomial in
open Module in
theorem _root_.GlobalTheory.TraceAeval.powMat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) {ψ : R[X]} (h : ψ.Monic) :
    (_root_.GlobalTheory.TraceAeval.powMat n ψ).map f = _root_.GlobalTheory.TraceAeval.powMat n (ψ.map f) := by
  ext i j
  simp only [_root_.GlobalTheory.TraceAeval.powMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic f h, Polynomial.map_pow,
    Polynomial.map_X]

theorem charpoly_powMat {ψ : ℂ[X]} (h : ψ.Monic) : (powMat ψ.natDegree ψ).charpoly = ψ := by
  have h1 := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h)
  have h2 : minpoly ℂ (AdjoinRoot.powerBasis' h).gen = ψ := by
    rw [AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root h.ne_zero, h.leadingCoeff]
    simp
  rw [h2] at h1
  refine Eq.trans ?_ h1
  congr 1
  ext i j
  refine Eq.trans ?_ (Algebra.leftMulMatrix_eq_repr_mul _ _ i j).symm
  have h3 := (AdjoinRoot.powerBasis' h).basis_eq_pow j
  refine Eq.trans ?_ (congrArg (fun t => (AdjoinRoot.powerBasis' h).basis.repr
    ((AdjoinRoot.powerBasis' h).gen * t) i) h3).symm
  simp only [← pow_succ']
  change _ = (AdjoinRoot.powerBasisAux' h).repr ((AdjoinRoot.root ψ) ^ ((j : ℕ) + 1)) i
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun, ← AdjoinRoot.mk_X, ← map_pow,
    AdjoinRoot.modByMonicHom_mk]
  rfl

end GlobalTheory.TraceAeval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfFlatOfFormallyUnramified
section
open scoped TensorProduct

namespace GlobalTheory

theorem isBezout_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W] [IsBezout W]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : IsBezout B := by
  refine ⟨fun J hJ => ?_⟩
  have hfin : Module.Finite B J := Module.Finite.iff_fg.2 hJ
  have htB : Submodule.torsion W B = ⊥ :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.1 inferInstance
  have hW : Module.Flat W J := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have hx : (x : B) ∈ Submodule.torsion W B := ⟨a, congrArg Subtype.val ha⟩
    rw [htB, Submodule.mem_bot] at hx
    exact (Submodule.mem_bot W).2 (Subtype.ext hx)
  have hB : Module.Flat B J := Algebra.FormallyUnramified.flat_of_restrictScalars W B J
  have hfree : Module.Free B J := Module.free_of_flat_of_isLocalRing
  rw [← Submodule.rank_le_one_iff_isPrincipal]
  exact (Submodule.rank_le J).trans (Module.rank_self B).le

theorem isAlgebraic_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W]
    [CommRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : Algebra.IsAlgebraic W B := by
  let K := FractionRing W
  have hfin : Module.Finite K (K ⊗[W] B) := Algebra.FormallyUnramified.finite_of_free K _
  have halg : Algebra.IsAlgebraic K (K ⊗[W] B) := inferInstance
  have hK : Algebra.IsAlgebraic W K := IsLocalization.isAlgebraic K (nonZeroDivisors W)
  have halgW : Algebra.IsAlgebraic W (K ⊗[W] B) := Algebra.IsAlgebraic.trans W K _
  exact Algebra.IsAlgebraic.of_injective
    (Algebra.TensorProduct.includeRight (R := W) (A := K) (B := B))
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective W K))

theorem valuationRing_of_flat_of_formallyUnramified :
    ∀ (W B : Type) [CommRing W] [IsDomain W] [ValuationRing W] [CommRing B] [IsDomain B]
      [IsLocalRing B] [Algebra W B] [Module.Flat W B] [Algebra.EssFiniteType W B]
      [Algebra.FormallyUnramified W B], ValuationRing B ∧ Algebra.IsAlgebraic W B := by
  intro W B _ _ _ _ _ _ _ _ _ _
  have := isBezout_of_flat_of_formallyUnramified W B
  exact ⟨inferInstance, isAlgebraic_of_flat_of_formallyUnramified W B⟩

end GlobalTheory
end

