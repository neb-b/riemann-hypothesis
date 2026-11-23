module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitary
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem sesq_eq_sum_repr {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (he : ∀ i j, H (e i) (e j) = if i = j then 1 else 0) (z w : V) :
    H z w = ∑ i, e.repr z i * conj (e.repr w i) := by
  conv_lhs => rw [← e.sum_repr z, ← e.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, he,
    smul_eq_mul, RingHom.id_apply, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem repr_apply_of_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (b : V →ₗ[ℂ] V) (l : Fin n → ℂ) (hl : ∀ i, b (e i) = l i • e i) (z : V)
    (i : Fin n) : e.repr (b z) i = l i * e.repr z i := by
  conv_lhs => rw [← e.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hl]
  simp [Finsupp.single_apply, mul_comm]

theorem det_of_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (b : V →ₗ[ℂ] V) (l : Fin n → ℂ) (hl : ∀ i, b (e i) = l i • e i) :
    LinearMap.det b = ∏ i, l i := by
  rw [← LinearMap.det_toMatrix e, ← Matrix.det_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, hl]
  simp [Matrix.diagonal_apply, Finsupp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all

theorem integral_gaussian_unitary : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet
  obtain ⟨n, e, l, he, hl⟩ := GlobalTheory.UnitaryTheta.unitary_exists_orthonormal_eigenbasis V H hH a ha
  have hb : ∀ i, (1 - (a : V →ₗ[ℂ] V)) (e i) = (1 - l i) • e i := fun i => by
    simp [(hl i).2, sub_smul]
  have hd := det_of_eigen e _ _ hb
  have hr : ∀ z i, e.repr (z - a z) i = (1 - l i) * e.repr z i := fun z i => by
    simpa using repr_apply_of_eigen e _ _ hb z i
  have hne : ∀ i, 1 - l i ≠ 0 := fun i => by
    rw [hd] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hre : ∀ i, 0 < (1 - l i).re := fun i => by
    have h1 : (l i).re ≤ 1 := (hl i).1 ▸ re_le_norm (l i)
    have h2 : (l i).re ≠ 1 := by
      intro h
      apply hne i
      have h3 : (l i).re * (l i).re + (l i).im * (l i).im = 1 := by
        rw [← normSq_apply, normSq_eq_norm_sq, (hl i).1]; norm_num
      have h4 : (l i).im = 0 := by
        rw [h] at h3
        exact mul_self_eq_zero.1 (by linarith)
      apply Complex.ext <;> simp [h, h4]
    simp only [sub_re, one_re]
    exact sub_pos.2 (lt_of_le_of_ne h1 h2)
  let T : V ≃L[ℂ] (Fin n → ℂ) := e.equivFun.toContinuousLinearEquiv
  let Tm : V ≃ᵐ (Fin n → ℂ) := T.toHomeomorph.toMeasurableEquiv
  have hT : ∀ z i, Tm z i = e.repr z i := fun z i => rfl
  haveI : (μ.map Tm).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul (μ.map Tm) (volume : Measure (Fin n → ℂ))
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map Tm) (volume : Measure (Fin n → ℂ))
  set c := Measure.addHaarScalarFactor (μ.map Tm) (volume : Measure (Fin n → ℂ)) with hc
  refine ⟨(c : ℝ), by exact_mod_cast hpos.ne', fun y v => ?_⟩
  let g : Fin n → ℂ → ℂ := fun i z => cexp (-(π : ℂ) * (1 - l i) * (z * conj z) +
    π * (((1 - l i) * e.repr y i) * conj z) + π * (z * conj (e.repr v i)))
  have hg := fun i => _root_.GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane (1 - l i) ((1 - l i) * e.repr y i) (e.repr v i) (hre i)
  have hF : (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) =
      (fun x : Fin n → ℂ => ∏ i, g i (x i)) ∘ Tm := by
    funext z
    simp only [Function.comp, g, hT, ← Complex.exp_sum, sesq_eq_sum_repr H e he, hr, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : Integrable (fun x : Fin n → ℂ => ∏ i, g i (x i)) volume :=
    Integrable.fintype_prod (f := g) fun i => (hg i).1
  rw [hF]
  refine ⟨?_, ?_⟩
  · rw [← integrable_map_equiv, hν]
    exact hint.smul_measure_nnreal
  · have h1 := integral_map_equiv (μ := μ) Tm (fun x : Fin n → ℂ => ∏ i, g i (x i))
    simp only [Function.comp_def]
    rw [← h1, hν, integral_smul_nnreal_measure, integral_fintype_prod_volume_eq_prod, hd,
      sesq_eq_sum_repr H e he, Finset.mul_sum, Complex.exp_sum]
    have h2 : ∀ i, ∫ z, g i z = (1 - l i)⁻¹ * cexp (π * (e.repr y i * conj (e.repr v i))) := fun i => by
      rw [show ∫ z, g i z = _ from (hg i).2]
      congr 2
      field_simp [hne i]
    simp only [h2, Finset.prod_mul_distrib, Finset.prod_inv_distrib, NNReal.smul_def, real_smul]
    ring

end GlobalTheory.UnitaryTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators IntermediateField

noncomputable section

namespace GlobalTheory.CurveAlgebraic

theorem exists_algHom_apply_eq {k : Type} [Field k] [Algebra k ℂ] {x x' : ℂ}
    (hx : Transcendental k x) (hx' : Transcendental k x')
    (hm : x ∈ (algebraicClosure k⟮x⟯ ℂ)) :
    ∃ σ : (algebraicClosure k⟮x⟯ ℂ) →ₐ[k] ℂ, σ ⟨x, hm⟩ = x' := by
  let τ : k⟮x⟯ →ₐ[k] ℂ := (k⟮x'⟯.val).comp
    ((RatFunc.algEquivOfTranscendental x' hx').toAlgHom.comp
      (RatFunc.algEquivOfTranscendental x hx).symm.toAlgHom)
  have hτ : τ (IntermediateField.AdjoinSimple.gen k x) = x' := by
    change ((RatFunc.algEquivOfTranscendental x' hx')
      ((RatFunc.algEquivOfTranscendental x hx).symm
        (IntermediateField.AdjoinSimple.gen k x)) : ℂ) = x'
    rw [RatFunc.algEquivOfTranscendental_symm_gen, RatFunc.algEquivOfTranscendental_X]
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := k) (L := k⟮x⟯)
    (M := ℂ) (E := algebraicClosure k⟮x⟯ ℂ) τ
  refine ⟨σ, ?_⟩
  rw [← hτ, ← hσ]
  rfl

theorem isAlgebraic_of_torsion {k : Type} [Field k] [CharZero k] [Algebra k ℂ]
    (W : WeierstrassCurve.Affine k) (V : WeierstrassCurve.Affine ℂ) (hV : W.baseChange ℂ = V)
    (m : ℕ) (S : Set ℂ) (hS : S.Finite)
    (hmem : ∀ x y (h : V.Nonsingular x y),
      m • (WeierstrassCurve.Affine.Point.some x y h) = 0 → x ∈ S)
    {x y : ℂ} (h : V.Nonsingular x y) (h0 : m • (WeierstrassCurve.Affine.Point.some x y h) = 0)
    (hy : IsAlgebraic k⟮x⟯ y) : IsAlgebraic k x := by
  subst hV
  by_contra hx
  let F := algebraicClosure k⟮x⟯ ℂ
  have hxF : x ∈ F := F.algebraMap_mem (IntermediateField.AdjoinSimple.gen k x)
  have hyF : y ∈ F := mem_algebraicClosure_iff.mpr hy
  let ι : F →ₐ[k] ℂ := F.val.restrictScalars k
  have hι : Function.Injective ι := ι.toRingHom.injective
  have hF : (W.baseChange F).Nonsingular ⟨x, hxF⟩ ⟨y, hyF⟩ :=
    (W.baseChange_nonsingular hι _ _).mp h
  have h1 : m • (WeierstrassCurve.Affine.Point.some _ _ hF) = 0 := by
    apply WeierstrassCurve.Affine.Point.map_injective (W' := W) ι
    rw [map_nsmul, map_zero, WeierstrassCurve.Affine.Point.map_some]
    exact h0
  have h2 : ∀ n : ℕ, x + n ∈ S := fun n => by
    have hn : Transcendental k (x + n) := fun ha => hx (by
      have := ha.sub (isAlgebraic_natCast (R := k) (A := ℂ) n)
      simpa using this)
    obtain ⟨σ, hσ⟩ := exists_algHom_apply_eq hx hn hxF
    have h3 := congrArg (WeierstrassCurve.Affine.Point.map (W' := W) σ) h1
    rw [map_nsmul, map_zero, WeierstrassCurve.Affine.Point.map_some] at h3
    exact hσ ▸ hmem _ _ _ h3
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => x + n) ?_ h2 hS
  intro a b hab
  simpa using hab

theorem weierstrassP_mem (L : PeriodPair) (h2 : L.g₂ ∈ Qbar) (h3 : L.g₃ ∈ Qbar) {m : ℕ}
    (hm : 0 < m) {t : ℂ} (ht : t ∉ L.lattice) (hmt : (m : ℂ) * t ∈ L.lattice) :
    L.weierstrassP t ∈ Qbar ∧ L.derivWeierstrassP t ∈ Qbar := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmul : ∀ z : ℂ, m • latticePoint L z = latticePoint L ((m : ℂ) * z) := fun z => by
    rw [← latticePointHom_apply, ← latticePointHom_apply, ← map_nsmul, nsmul_eq_mul]
  obtain ⟨A, D, -, -, hD, -, -, -, -, hroot, -⟩ := exists_weierstrassP_mul_eq_div (L := L) (L' := L)
    hm0 (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl m) ⊤ trivial trivial trivial
    (fun _ _ _ => trivial)
  have hsq := L.derivWeierstrassP_sq t ht
  have hx : IsAlgebraic Qbar (L.weierstrassP t) := by
    refine isAlgebraic_of_torsion
      (⟨0, 0, 0, -⟨L.g₂, h2⟩ / 4, -⟨L.g₃, h3⟩ / 4⟩ : WeierstrassCurve Qbar) (latticeCurve L).toAffine ?_ m
      (D.rootSet ℂ) (D.rootSet_finite ℂ) ?_ (latticeCurve_nonsingular L ht) ?_ ?_
    · ext <;> simp [latticeCurve, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange] <;> rfl
    · intro x y h h0
      obtain ⟨z, hz⟩ := latticePoint_surjective L (.some x y h)
      have hz' : z ∉ L.lattice := fun hc => by
        rw [latticePoint_of_mem L hc] at hz
        exact WeierstrassCurve.Affine.Point.some_ne_zero _ hz.symm
      rw [← hz, hmul, latticePoint_eq_zero_iff] at h0
      rw [latticePoint_of_notMem L hz'] at hz
      obtain ⟨rfl, -⟩ := WeierstrassCurve.Affine.Point.some.inj hz
      rw [Polynomial.mem_rootSet]
      exact ⟨hD.ne_zero, (hroot z hz').mpr h0⟩
    · rw [← latticePoint_of_notMem L ht, hmul, latticePoint_eq_zero_iff]
      exact hmt
    · set F := (↥Qbar)⟮L.weierstrassP t⟯
      have e1 : L.weierstrassP t ∈ F := IntermediateField.mem_adjoin_simple_self _ _
      have e2 : L.g₂ ∈ F := F.algebraMap_mem ⟨L.g₂, h2⟩
      have e3 : L.g₃ ∈ F := F.algebraMap_mem ⟨L.g₃, h3⟩
      have e4 : (L.derivWeierstrassP t / 2) ^ 2 ∈ F := by
        rw [div_pow, hsq]
        refine div_mem (sub_mem (sub_mem (mul_mem (ofNat_mem F 4) (pow_mem e1 3)) (mul_mem e2 e1)) e3)
          (pow_mem (ofNat_mem F 2) 2)
      exact IsAlgebraic.of_pow two_pos (isAlgebraic_algebraMap (⟨_, e4⟩ : F))
  have hx' : L.weierstrassP t ∈ Qbar :=
    haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
    mem_algebraicClosure_iff.mpr (hx.restrictScalars ℚ)
  refine ⟨hx', mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)⟩
  rw [hsq, ← mem_algebraicClosure_iff]
  exact sub_mem (sub_mem (mul_mem (ofNat_mem _ 4) (pow_mem hx' 3)) (mul_mem h2 hx')) h3

theorem exists_periodPair (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (h : Crv D cc δ) : ∃ L : PeriodPair, (∀ z, z ∈ lamOf D cc δ ↔ z ∈ L.lattice) ∧
      L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 ∧ IsIntegral ℤ (1728 * L.g₂ ^ 3) := by
  obtain ⟨⟨w₁, w₂, hw, he⟩, -, hΔ, -, hcm⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ h
  let L : PeriodPair := ⟨w₁, w₂, hw⟩
  have hL : ∀ z, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := fun z => by
    rw [he, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨e2, e3, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  have hΔ' : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by rw [← e2, ← e3]; exact hΔ
  refine ⟨L, hL, hΔ', ?_⟩
  have := CMCurves.isIntegral_latticeJ (Formalism.L2.Pj.LPb.finrank_K D)
    (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) L
    (fun a z hz => (hL _).mp (hcm a z ((hL _).mpr hz)))
  rwa [CMCurves.latticeJ, hΔ', div_one] at this

theorem integral_j_and_algebraic_data : ∀ (D : D7), admG1 D → GL3Theta.admJ D ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → DataIn D (tor0 D cc δ) Qbar ∧ ∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ Qbar ∧ wpD (lamOf D cc δ) t ∈ Qbar := by
  intro D hD
  refine ⟨fun cc δ h1 h2 => ?_, fun cc δ h => ?_⟩
  · obtain ⟨L, hL, -, hj⟩ := exists_periodPair D hD cc δ ⟨h1, h2⟩
    rwa [(GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL).1]
  obtain ⟨L, hL, hΔ, hj⟩ := exists_periodPair D hD cc δ h
  obtain ⟨e2, e3, -, -, hp, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  have hj' : 1728 * L.g₂ ^ 3 ∈ Qbar :=
    mem_algebraicClosure_iff.mpr (hj.tower_top (A := ℚ)).isAlgebraic
  have hc : L.g₂ ^ 3 ∈ Qbar := by
    have := div_mem hj' (ofNat_mem Qbar 1728)
    rwa [mul_div_cancel_left₀ _ (by norm_num)] at this
  have h2 : L.g₂ ∈ Qbar :=
    mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow three_pos (mem_algebraicClosure_iff.mp hc))
  have h3 : L.g₃ ∈ Qbar := by
    refine mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)
    rw [← mem_algebraicClosure_iff,
      show L.g₃ ^ 2 = (L.g₂ ^ 3 - 1) / 27 by linear_combination (-1 / 27 : ℂ) * hΔ]
    exact div_mem (sub_mem hc (one_mem _)) (ofNat_mem _ 27)
  refine ⟨⟨fun τ x => ?_, e2 ▸ h2, e3 ▸ h3⟩, ?_⟩
  · exact mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)
  · rintro t ⟨m, hm, hmt⟩ ht
    rw [(hp t ht).1, (hp t ht).2]
    exact weierstrassP_mem L h2 h3 hm (fun hc => ht ((hL _).mpr hc)) ((hL _).mp hmt)

end GlobalTheory.CurveAlgebraic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralSeriesOfCommonDivisorLineProducts
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem dvd_pow_prod_sub {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ] (d : R) (a : ι → R)
    (b : κ → R) (ha : d ∣ (∏ i, a i) ^ 2) (hb : d ∣ ∏ j, b j) :
    ∃ N : ℕ, d ∣ (∏ i, ∏ j, (b j - a i)) ^ N := by
  have h : (∏ i, ∏ j, (b j - a i)) ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hle, hP⟩
    have h1 : (∏ i, a i) ∈ P := hP.mem_of_pow_mem 2 (hle (Ideal.mem_span_singleton.2 ha))
    have h2 : (∏ j, b j) ∈ P := hle (Ideal.mem_span_singleton.2 hb)
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h1
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.1 h2
    exact Ideal.IsPrime.prod_mem_iff.2 ⟨i, Finset.mem_univ _,
      Ideal.IsPrime.prod_mem_iff.2 ⟨j, Finset.mem_univ _, P.sub_mem hj hi⟩⟩
  obtain ⟨N, hN⟩ := h
  exact ⟨N, Ideal.mem_span_singleton.1 hN⟩

noncomputable def bddSubring (p : ℕ) [Fact p.Prime] : Subring (PowerSeries ℂ_[p]) where
  carrier := {f | BddSer f}
  mul_mem' ha hb := ((_root_.GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 _ _ ha hb).2.2
  add_mem' ha hb := ((_root_.GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 _ _ ha hb).1
  one_mem' := by simpa using ((_root_.GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 1).1
  zero_mem' := by simpa using ((_root_.GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 0).1
  neg_mem' {x} hx := by
    obtain ⟨B, hB⟩ := hx
    exact ⟨B, fun n => by simpa using hB n⟩

theorem intSer_of_common_divisor (p : ℕ) [Fact p.Prime] (m n : ℕ) (e Ψ A B : PowerSeries ℂ_[p])
    (y : Fin m → ℂ_[p]) (y' : Fin n → ℂ_[p]) (he : BddSer e) (hΨ : BddSer Ψ) (hA : BddSer A)
    (hB : BddSer B) (h1 : PowerSeries.constantCoeff Ψ = 1)
    (hΨA : Ψ * A = (∏ i, lineSer e (y i)) ^ 2) (hΨB : Ψ * B = ∏ j, lineSer e (y' j))
    (hy : ∀ i j, y i ≠ y' j) : IntSer Ψ := by
  have hl : ∀ x : ℂ_[p], lineSer e x ∈ bddSubring p := fun x =>
    (bddSubring p).sub_mem he ((bddSubring p).mul_mem ((_root_.GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 x).1
      ((bddSubring p).pow_mem (show BddSer _ from ⟨1, (_root_.GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1⟩) 2))
  obtain ⟨N, H, hH⟩ := dvd_pow_prod_sub (R := bddSubring p) ⟨Ψ, hΨ⟩
    (fun i => ⟨lineSer e (y i), hl _⟩) (fun j => ⟨lineSer e (y' j), hl _⟩)
    ⟨⟨A, hA⟩, Subtype.ext (by simpa using hΨA.symm)⟩
    ⟨⟨B, hB⟩, Subtype.ext (by simpa using hΨB.symm)⟩
  set c : ℂ_[p] := (∏ i, ∏ j, (y i - y' j)) ^ N with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ =>
    Finset.prod_ne_zero_iff.2 fun j _ => sub_ne_zero.2 (hy i j))
  have key : Ψ * (H : PowerSeries ℂ_[p]) = PowerSeries.monomial (2 * n * m * N) c := by
    have h := congrArg Subtype.val hH
    have e1 : ∀ i j, lineSer e (y' j) - lineSer e (y i) =
        PowerSeries.C (y i - y' j) * PowerSeries.X ^ 2 := fun i j => by
      simp only [lineSer, map_sub]; ring
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul, SubmonoidClass.coe_finsetProd,
      AddSubgroupClass.coe_sub, e1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_pow, ← pow_mul] at h
    rw [← h, PowerSeries.monomial_eq_C_mul_X_pow, hc]
    simp only [map_pow, map_prod, mul_assoc]
  have hHc : PowerSeries.coeff (2 * n * m * N) (H : PowerSeries ℂ_[p]) = c := by
    have hinv : Ψ⁻¹ * Ψ = 1 := PowerSeries.inv_mul_cancel _ (by simp [h1])
    have : (H : PowerSeries ℂ_[p]) = PowerSeries.X ^ (2 * n * m * N) * (PowerSeries.C c * Ψ⁻¹) := by
      have h2 := congrArg (Ψ⁻¹ * ·) key
      simp only [← mul_assoc, hinv, one_mul, PowerSeries.monomial_eq_C_mul_X_pow] at h2
      rw [h2]; ring
    rw [this, PowerSeries.coeff_X_pow_mul']
    simp [h1]
  intro i
  have := _root_.GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p Ψ H ‖c‖ hΨ H.2 (fun k => by
    rw [key, PowerSeries.coeff_monomial]
    split_ifs <;> simp) i (2 * n * m * N)
  rw [hHc] at this
  exact le_of_mul_le_mul_right (by simpa using this) (norm_pos_iff.2 hc0)

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReImMapSurjective
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped NNReal

noncomputable section

namespace GlobalTheory.CompactDualOmega

theorem Jpq_mul_self (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem Jpq_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem mem_lieU {P Q : ℕ} (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ lieU P Q ↔ Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 := Iff.rfl

def reImMap (P Q : ℕ) :
    (lieU P Q × lieU P Q) →ₗ[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) where
  toFun ab := Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' x y := by
    funext ij
    simp [Formalism.BasicNotions.entries]
    ring
  map_smul' c x := by
    funext ij
    simp [Formalism.BasicNotions.entries]
    ring

theorem reImMap_injective (P Q : ℕ) : Function.Injective (reImMap P Q) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h
  have h1 : a + Complex.I • b = 0 := by
    ext i j
    exact congrFun h (i, j)
  have h2 : a = -(Complex.I • b) := eq_neg_of_add_eq_zero_left h1
  have ha' := (mem_lieU a).1 ha
  have hb' := (mem_lieU b).1 hb
  have h3 : bᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * b) := eq_neg_of_add_eq_zero_left hb'
  have h4 : (-(2 * Complex.I)) • (Formalism.UG.Jpq P Q * b) = 0 := by
    rw [← ha', h2]
    simp only [conjTranspose_neg, conjTranspose_smul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.smul_mul, Matrix.mul_smul, h3, Complex.star_def, Complex.conj_I]
    module
  have h5 : Formalism.UG.Jpq P Q * b = 0 :=
    (smul_eq_zero.1 h4).resolve_left (by simp)
  have h6 : b = 0 := by
    have := congrArg (Formalism.UG.Jpq P Q * ·) h5
    simpa [← Matrix.mul_assoc, Jpq_mul_self] using this
  have h7 : a = 0 := by rw [h2, h6]; simp
  subst h6
  subst h7
  rfl

theorem reImMap_surjective (P Q : ℕ) : Function.Surjective (reImMap P Q) := by
  intro f
  let Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := Matrix.of fun i j => f (i, j)
  have hJ := Jpq_mul_self P Q
  have hH := Jpq_conjTranspose P Q
  have hl : ∀ X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ,
      Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨(⟨(1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q), ?_⟩,
    ⟨(-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q), ?_⟩), ?_⟩
  · rw [mem_lieU]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, this, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hJ, hl, Matrix.mul_one]
    module
  · rw [mem_lieU]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [neg_div]
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, this, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, hJ, hl, Matrix.mul_one]
    module
  · have h1 : Complex.I * (-(Complex.I / 2)) = 1 / 2 := by
      have := Complex.I_mul_I
      linear_combination (-1 / 2 : ℂ) * this
    have h2 : (1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) +
        Complex.I • (-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) = Z := by
      rw [smul_smul, h1]
      module
    exact (congrArg Formalism.BasicNotions.entries h2).trans rfl

theorem exists_isOmegaLeb : ∀ P Q : ℕ, ∃ lam : Measure (lieU P Q), IsOmegaLeb lam := by
  intro P Q
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : LocallyCompactSpace (lieU P Q) :=
    (Submodule.closed_of_finiteDimensional (lieU P Q)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (lieU P Q) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : FiniteDimensional ℝ (lieU P Q × lieU P Q) :=
    FiniteDimensional.of_injective (reImMap P Q) (reImMap_injective P Q)
  let e : (lieU P Q × lieU P Q) ≃L[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) :=
    (LinearEquiv.ofBijective (reImMap P Q)
      ⟨reImMap_injective P Q, reImMap_surjective P Q⟩).toContinuousLinearEquiv
  let l : Measure (lieU P Q) := Measure.addHaar
  have : ((l.prod l).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  let t : ℝ≥0 := Measure.addHaarScalarFactor volume ((l.prod l).map e)
  have ht : volume = t • (l.prod l).map e := Measure.isAddLeftInvariant_eq_smul _ _
  have ht0 : 0 < t := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hs : NNReal.sqrt t ≠ 0 := by simpa using ht0.ne'
  refine ⟨NNReal.sqrt t • l, Measure.IsAddHaarMeasure.nnreal_smul l hs, ?_⟩
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, NNReal.mul_self_sqrt,
    Measure.map_smul]
  · exact ht.symm
  · change AEMeasurable e (l.prod l)
    exact e.continuous.measurable.aemeasurable

end GlobalTheory.CompactDualOmega
end
end

