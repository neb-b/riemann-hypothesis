module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageTop
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockImageTop

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]

theorem isMultiHomog_blockForms (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (q : Σ k, GlobalTheory κ k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (blockForms k₀ M q) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk, Sigma.ext_iff]

theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (i : ι k₀) :
    X ⟨k₀, i⟩ - ∑ j, C (N i j) * blockForms k₀ M j ∈ mCoordIdeal y := by
  have hf : ∀ j, mConeMap y (blockForms k₀ M j) = MvPolynomial.C (x j) * MvPolynomial.X k₀ := by
    intro j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h.1 j, map_sum, Finset.sum_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [blockForms, mConeMap, map_sum, mul_assoc]
  have hX : mConeMap y (X ⟨k₀, i⟩) = MvPolynomial.C (y ⟨k₀, i⟩) * MvPolynomial.X k₀ := by
    simp [mConeMap]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_sum]
  simp only [map_mul, hf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hX, h.2 i, map_sum, Finset.sum_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mConeMap, mul_assoc]

theorem isBasePtFree_blockForms {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) :
    IsBasePtFree (mCoordIdeal y) (blockForms k₀ M) := by
  intro k₂ i
  refine ⟨1, ?_⟩
  rw [pow_one, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k₀)]
  refine Ideal.mul_mem_right _ _ ?_
  have hspan : ∑ j, C (N (i k₀) j) * blockForms k₀ M j ∈
      Ideal.span (Set.range fun j : GlobalTheory κ k₂ => blockForms k₀ M ⟨k₂, j⟩) := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j.2, ?_⟩)
    cases k₂
    rfl
  have := Ideal.add_mem _ (Ideal.mem_sup_left (sub_mem_mCoordIdeal h (i k₀))) (Ideal.mem_sup_right hspan)
  rwa [sub_add_cancel] at this

theorem isSmoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  refine hm.mono fun z hz => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 => hi (congrFun h0 _)

theorem formApply_blockForms (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (z : (Σ k, ι k) → ℂ) :
    formApply (blockForms k₀ M) z = blockMapC k₀ M z := by
  funext q
  simp [formApply, blockForms, blockMapC]

end BlockImageTop


open BlockImageTop in
theorem BlockImageTop.proof (hCM : GraphChangeOfModel.Statement) (hIm : BlockGraphImage.Statement)
    (hDeg : BlockGraphDeg.Statement) : BlockImageTop.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ I y k₀ A M N x m hI hP hB hx hBI ha hA hm hh
  obtain ⟨G, J, hJ, hJ1⟩ := hDeg D K ι Ω κ y k₀ M N x hP hB hx hBI
  have himg := hIm K ι Ω κ y k₀ M N x hBI
  have key := hCM I hI K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) G J
    (fun _ => HermLine.ofCone m) (fun _ => A) hP (isMultiHomog_blockForms k₀ M) (isBasePtFree_blockForms hBI)
    (by rw [himg]; exact hx) hJ (fun _ => isSmoothHerm_ofCone hm) (fun _ => hA)
    (fun _ k => by
      rw [ha]
      by_cases hk : k = k₀ <;> simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, blockDeg, HermLine.ofCone, hk])
    (fun _ z hz => by rw [hh z hz, formApply_blockForms]; rfl)
  rw [himg, hJ1] at key
  simpa [top] using key

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfModel
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ChangeOfModel

variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]


open Classical in
def blockDeg (k₂ : K) : K → ℕ := fun k => if k = k₂ then 1 else 0


omit [Fintype K] [∀ k, Fintype (ι₂ k)] in
theorem isMultiHomog_linForm (A : ∀ k, ι₂ k → ι k → ℤ) (q : Σ k, ι₂ k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A q) (blockDeg q.1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  obtain ⟨k₀, j⟩ := q
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk]


omit [∀ k, Fintype (ι₂ k)] in
theorem exists_linForm_not_mem {P : Ideal (MRing ι)} {d : ℕ} {A : ∀ k, ι₂ k → ι k → ℤ} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A)) : ∀ k₂, ∃ j, ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A ⟨k₂, j⟩ ∉ P := by
  intro k₂
  by_contra hall
  push Not at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k₂ i
  have hle : Ideal.span (Set.range fun j : ι₂ k₂ => ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A ⟨k₂, j⟩) ≤ P :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle] at hN
  have := hprime
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp (hprime.mem_of_pow_mem N hN)
  exact hi k hk

end ChangeOfModel


open ChangeOfModel IndefiniteRowSideFullHecke.Inter in
theorem ChangeOfModel.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hIso : IsomInvariance.Statement) (hGI : GraphIsometric.Statement) : ChangeOfModelStatement := by
  intro I hI K _ ι ι₂ _ _ P d A G J L L₁ hP hBP hImg hJ hL hL₁ ha hh
  obtain ⟨hΓ, himg, hdeg⟩ := hGr K ι K ι₂ P d (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A) blockDeg hP
    (isMultiHomog_linForm A) (exists_linForm_not_mem hP hBP)
  obtain ⟨G'⟩ := hGF K ι (K ⊕ K) (Sum.elim ι ι₂) Sum.inl inlV _ d isBlockMap_inl hΓ
  obtain ⟨J', hJ', -⟩ := hEU G'.Φ _ (fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K))
  have e1 := hAI3 I hI K ι (K ⊕ K) (Sum.elim ι ι₂) Sum.inl inlV _ d G' J' L₁
    (fun j => pullHerm isBlockMap_inl (L₁ j)) isBlockMap_inl hΓ (by rw [himg]; exact hP) hJ' hL₁
    (fun j => isPullHerm_pullHerm _ _)
  have e2 := hAI3 I hI K ι₂ (K ⊕ K) (Sum.elim ι ι₂) Sum.inr inrV _ d G J L
    (fun j => pullHerm isBlockMap_inr (L j)) isBlockMap_inr hΓ hImg hJ hL
    (fun j => isPullHerm_pullHerm _ _)
  have e3 := hIso (K ⊕ K) (Sum.elim ι ι₂) (I (K ⊕ K) (Sum.elim ι ι₂)) (hI _ _) _ d
    (fun j => pullHerm isBlockMap_inl (L₁ j)) (fun j => pullHerm isBlockMap_inr (L j)) hΓ
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inl (isPullHerm_pullHerm _ _) (hL₁ j))
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inr (isPullHerm_pullHerm _ _) (hL j))
    (fun j => hGI K ι ι₂ P d A (L₁ j) (L j) _ _ hP hBP (ha j) (hh j) (isPullHerm_pullHerm _ _)
      (isPullHerm_pullHerm _ _))
  rw [hdeg G' J' hJ', himg] at e1
  rw [← e2, ← e3, e1]
  simp

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartRatioImageNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

theorem ChartRatioImageNull.volume_eq_zero_of_dimH_lt {e : ℕ} {S : Set (Fin e → ℂ)}
    (hS : dimH S < 2 * (e : ℝ≥0∞)) : volume S = 0 := by
  let E : ((Σ _ : Fin e, Fin 2) → ℝ) ≃L[ℝ] (Fin e → ℂ) :=
    (Pi.basis (fun _ : Fin e => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin e, Fin 2) = 2 * e := by
    simp [Fintype.card_sigma, mul_comm]
  have hT : volume (E ⁻¹' S) = 0 := by
    rw [← hausdorffMeasure_pi_real, hcard]
    have h := hausdorffMeasure_of_dimH_lt (s := E ⁻¹' S) (d := ((2 * e : ℕ) : ℝ≥0)) (by
      rw [ContinuousLinearEquiv.dimH_preimage]
      simpa using hS)
    simpa using h
  have : (Measure.map E volume).IsAddHaarMeasure := E.isAddHaarMeasure_map volume
  have hac : (volume : Measure (Fin e → ℂ)) ≪ Measure.map E volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hac
  exact (E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT

theorem ChartRatioImageNull.proof : ChartRatioImageNull.Statement := by
  intro K _ ι _ J e Ψ hdim
  classical
  set S := {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧
    (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} with hSdef
  by_cases hJ : J = ⊤
  · have hS : S = ∅ := by
      ext y
      simp only [hSdef, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨z, hz, -⟩
      have h1 := hz 1 (hJ ▸ Submodule.mem_top)
      simp at h1
    rw [hS, measure_empty]
  have : Nontrivial (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Σ k, ι k) ℂ ⧸ J)
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := by
    rcases e with _ | m
    · exact absurd (h0.trans_lt hdim) (by simp)
    · exact ⟨m, rfl⟩
  have hle : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) ≤ (m : WithBot ℕ∞) := by
    rcases hx : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) with _ | x
    · exact bot_le
    · rw [hx] at hdim
      have hx' : x < (m : ℕ∞) + 1 := by
        have h5 : ((x : WithBot ℕ∞)) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := hdim
        have h6 := WithBot.coe_lt_coe.1 h5
        exact_mod_cast h6
      exact WithBot.coe_le_coe.2 ((ENat.lt_add_one_iff (ENat.natCast_ne_top m)).1 hx')

  let eqv : (Σ k, ι k) ≃ Fin (Fintype.card (Σ k, ι k)) := Fintype.equivFin _
  let J' : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) := J.map (rename eqv)
  have hdim' : ringKrullDim (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J') ≤ (m : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv J J' (renameEquiv ℂ eqv).toRingEquiv rfl)]
    exact hle
  have hV' := GroundTheory.Heights₂.Heights.ZeroLocusDimH.full _ m J' hdim'
  let L : ((Σ k, ι k) → ℂ) ≃L[ℂ] (Fin (Fintype.card (Σ k, ι k)) → ℂ) :=
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) eqv).toContinuousLinearEquiv
  have hVsub : zeroLocus ℂ J ⊆ L ⁻¹' {x | ∀ q ∈ J', eval x q = 0} := by
    intro z hz q hq
    have hJle : J ≤ (RingHom.ker (eval (L z))).comap (rename eqv) := by
      intro p hp
      simp only [Ideal.mem_comap, RingHom.mem_ker, eval_rename]
      have h2 : (L z) ∘ eqv = z := by
        funext i; simp [L]
      rw [h2]
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz p hp
    exact Ideal.map_le_iff_le_comap.mpr hJle hq
  have hV : dimH (zeroLocus ℂ J : Set ((Σ k, ι k) → ℂ)) ≤ 2 * (m : ℝ≥0∞) :=
    (dimH_mono hVsub).trans ((L.dimH_preimage _).le.trans hV')

  let G : ((Σ k, ι k) → ℂ) → (Fin (m + 1) → ℂ) := fun z j => (Ψ (segre z) 0)⁻¹ * Ψ (segre z) j.succ
  let U := {z : (Σ k, ι k) → ℂ | Ψ (segre z) 0 ≠ 0}
  have hSsub : S ⊆ G '' (zeroLocus ℂ J ∩ U) := by
    rintro y ⟨z, hz, hz0, hy⟩
    refine ⟨z, ⟨hz, hz0⟩, ?_⟩
    funext j
    have h3 := congrFun hy j.succ
    simpa [G] using h3.symm
  have hsmooth : ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z)) := by
    have h1 : ContDiff ℂ ⊤ (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) := by
      apply contDiff_pi.2
      intro i
      exact contDiff_prod (fun k _ => contDiff_apply ℂ (fun _ => ℂ) _)
    exact (LinearMap.toContinuousLinearMap Ψ).contDiff.comp h1
  have hc : ∀ i, ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z) i) :=
    fun i => (contDiff_apply ℂ (fun _ => ℂ) i).comp hsmooth
  have hG : ∀ z ∈ U, ContDiffAt ℂ 1 G z := by
    intro z hz
    apply contDiffAt_pi.2
    intro j
    exact (((hc 0).contDiffAt.inv hz).mul (hc j.succ).contDiffAt).of_le le_top
  have hGdim : dimH (G '' (zeroLocus ℂ J ∩ U)) ≤ dimH (zeroLocus ℂ J ∩ U) := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro z hz
    obtain ⟨C, t, ht, hlip⟩ := (hG z hz.2).exists_lipschitzOnWith
    exact ⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hlip⟩
  apply ChartRatioImageNull.volume_eq_zero_of_dimH_lt
  calc dimH S ≤ dimH (G '' (zeroLocus ℂ J ∩ U)) := dimH_mono hSsub
    _ ≤ dimH (zeroLocus ℂ J ∩ U) := hGdim
    _ ≤ dimH (zeroLocus ℂ J : Set ((Σ k, ι k) → ℂ)) := dimH_mono inter_subset_left
    _ ≤ 2 * (m : ℝ≥0∞) := hV
    _ < 2 * ((m + 1 : ℕ) : ℝ≥0∞) := by
      have h4 : 2 * m < 2 * (m + 1) := by omega
      exact_mod_cast h4

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedRestrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedRestrict

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

abbrev locMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) :
    LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) g

section General

variable {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N]

theorem locMap_mk (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    locMap T g (LocalizedModule.mk m t) = LocalizedModule.mk (g m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem locMap_cellRes (g : M →ₗ[MRingOver S ι] N) (J I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon S J) M) :
    locMap (KH.cellMon S I) g (KH.cellRes S M J I x) = KH.cellRes S N J I (locMap (KH.cellMon S J) g x) := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [GenTwistGenerated.cellRes_mk h, locMap_mk, locMap_mk, GenTwistGenerated.cellRes_mk h]
  · unfold KH.cellRes
    rw [dite_eq_right h, dite_eq_right h]
    simp

end General

variable {V W : Ideal (MRingOver S ι)}

abbrev quotMap (hVW : V ≤ W) : (MRingOver S ι ⧸ V) →ₗ[MRingOver S ι] (MRingOver S ι ⧸ W) :=
  (Ideal.Quotient.factorₐ (MRingOver S ι) hVW).toLinearMap

theorem quotMap_mul (hVW : V ≤ W) (x y : MRingOver S ι ⧸ V) :
    quotMap hVW (x * y) = quotMap hVW x * quotMap hVW y := by
  simp [quotMap]

theorem quotMap_smul (hVW : V ≤ W) (s : S) (x : MRingOver S ι ⧸ V) :
    quotMap hVW (s • x) = s • quotMap hVW x :=
  LinearMap.map_smul_of_tower _ s x

theorem locMap_smul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (s : S)
    (x : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (s • x) = s • locMap T (quotMap hVW) x := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [LocalizedModule.smul'_mk, locMap_mk, locMap_mk, LocalizedModule.smul'_mk, quotMap_smul]

theorem locMap_mul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (x y : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (x * y) = locMap T (quotMap hVW) x * locMap T (quotMap hVW) y := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.mk_mul_mk, locMap_mk, locMap_mk, locMap_mk, LocalizedModule.mk_mul_mk, quotMap_mul]

theorem locMap_one (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) :
    locMap T (quotMap hVW) (1 : LocalizedModule T (MRingOver S ι ⧸ V)) = 1 := by
  have e : ∀ (P : Type) [CommRing P] [Algebra (MRingOver S ι) P],
      (1 : LocalizedModule T P) = LocalizedModule.mk 1 1 := fun _ _ _ => OreLocalization.one_def
  have h1 : quotMap hVW (1 : MRingOver S ι ⧸ V) = 1 := by simp [quotMap]
  rw [e, e, locMap_mk, h1]

theorem cechD_cechMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (n : ℕ) (f : KH.CechC S ι M n) :
    KH.cechD S ι N n (KH.cechMap S ι g n f) = KH.cechMap S ι g (n + 1) (KH.cechD S ι M n f) := by
  funext I
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [KH.cechD, KH.cechMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · exact (congrArg (fun y => KH.faceSign I.1 k i • y) (locMap_cellRes g _ I.1 (f ⟨_, h⟩))).symm.trans
      (map_zsmul (locMap (KH.cellMon S I.1) g) _ _).symm
  · simp

theorem quotMap_mem_quotPart (hVW : V ≤ W) {c : K → ℤ} {x : MRingOver S ι ⧸ V}
    (hx : x ∈ KH.quotPart S V c) : quotMap hVW x ∈ KH.quotPart S W c := by
  unfold KH.quotPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [quotMap_smul]; exact Submodule.smul_mem _ s hx

theorem locMap_mem_locPart (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) {c : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c) :
    locMap T (quotMap hVW) x ∈ KH.locPart ι (KH.quotPart S W) T c := by
  unfold KH.locPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [locMap_mk]
    exact GenTwistGenerated.mk_mem_locPart _ t a ht (quotMap_mem_quotPart hVW hm)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [locMap_smul]; exact Submodule.smul_mem _ s hx

end GeneratedRestrict


open GeneratedRestrict in
theorem GeneratedRestrict.proof : GeneratedRestrict.Statement := by
  intro S _ K _ _ ι _ _ V W a hVW hV I
  obtain ⟨r, z, u, hz, hu, h1⟩ := hV I
  refine ⟨r, fun j => KH.cechMap S ι (quotMap hVW) 0 (z j), fun j => locMap _ (quotMap hVW) (u j),
    fun j => ?_, fun j => locMap_mem_locPart hVW _ (hu j), ?_⟩
  · obtain ⟨hzc, hzd⟩ := hz j
    refine GenTwistGenerated.mem_cechZc_zero (fun J => ?_) ?_
    · exact locMap_mem_locPart hVW _ ((Submodule.mem_pi.mp hzc) J (Set.mem_univ _))
    · rw [cechD_cechMap, LinearMap.mem_ker.mp hzd, map_zero]
  · have hc : ∀ j, KH.cechMap S ι (quotMap hVW) 0 (z j) I = locMap _ (quotMap hVW) (z j I) := fun j => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, ← locMap_mul, ← map_sum, h1, locMap_one]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartPrimePowerInverse
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def ChartPrimePowerInverse.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p : ℕ, p.Prime → ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
      ∃ M : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
        (p : Ω) ^ M * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
          Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
            Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹})

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

