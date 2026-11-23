module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermPrimitivePresentation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0088
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0067
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0087

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology

noncomputable section

namespace DiscriminantSheetCover

theorem volume_zero_set {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0) :
    volume {y : Fin d → ℂ | eval y P = 0} = 0 := by
  set S := {y : Fin d → ℂ | eval y P = 0} with hSdef
  have hS : MeasurableSet S :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  have hnull : μH[((2 * d : ℕ) : ℝ)]
      (zeroSetEuc ((⊥ : Ideal (MvPolynomial (Fin d) ℂ)) ⊔ Ideal.span {P})) = 0 :=
    NullSmaller.proof d d _ (MassFinite.dim_sup_lt ⊥ Ideal.isPrime_bot (space_dim d) P
      (by simpa [Ideal.mem_bot] using hP))
  obtain ⟨c, hc⟩ := SheetAreaCompare.exists_lintegral_volume_eq d
  have h := hc (S.indicator 1)
  rw [lintegral_indicator_one hS] at h
  rw [h]
  have hae : (fun y : EuclideanSpace ℂ (Fin d) => S.indicator (1 : (Fin d → ℂ) → ENNReal) (WithLp.ofLp y))
      =ᵐ[(μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d)))] 0 := by
    refine ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)
    have hyS : WithLp.ofLp y ∈ S := by
      by_contra h'
      exact hy (by simp [Set.indicator_of_notMem h'])
    intro q hq
    rw [bot_sup_eq] at hq
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    have : eval (WithLp.ofLp y) P = 0 := hyS
    simp only [map_mul]
    rw [show (fun i => y i) = WithLp.ofLp y from rfl, this, mul_zero]
  rw [lintegral_congr_ae hae]
  simp

theorem local_sheets {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {P : MvPolynomial (Fin d) ℂ} {N : ℕ}
    (hcov : ∀ y : Fin d → ℂ, eval y P ≠ 0 →
        (fibre J A y).Finite ∧ (fibre J A y).ncard = N ∧
        ∀ x ∈ fibre J A y, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
          (g : (Fin d → ℂ) → (Fin n → ℂ)), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A.mulVec (g w) = w) ∧
            zeroSet J ∩ V = g '' U)
    (y₀ : Fin d → ℂ) (hy₀ : eval y₀ P ≠ 0) :
    ∃ W : Set (Fin d → ℂ), IsOpen W ∧ y₀ ∈ W ∧ W ⊆ {y | eval y P ≠ 0} ∧
      ∃ s : Fin N → (Fin d → ℂ) → Fin n → ℂ, (∀ j, DifferentiableOn ℂ (s j) W) ∧
        ∀ y ∈ W, fibre J A y = Set.range (fun j => s j y) ∧ Function.Injective (fun j => s j y) ∧
          ∀ j, IsSheetAt J A (s j y) (s j) := by
  obtain ⟨hfin, hcard, hloc⟩ := hcov y₀ hy₀
  have : Finite (fibre J A y₀) := hfin
  let e : fibre J A y₀ ≃ Fin N := Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hcard])
  let x : Fin N → Fin n → ℂ := fun j => (e.symm j).1
  have hx : ∀ j, x j ∈ fibre J A y₀ := fun j => (e.symm j).2
  have hxinj : Function.Injective x := fun i j h => e.symm.injective (Subtype.ext h)
  choose U V g hU hyU hV hxV hg hgy hAg hZ using fun j => hloc (x j) (hx j)
  have hcont : ∀ j, ContinuousAt (g j) y₀ := fun j =>
    (hg j).continuousOn.continuousAt ((hU j).mem_nhds (hyU j))
  have hev : ∀ᶠ w in 𝓝 y₀, (∀ j, w ∈ U j) ∧ eval w P ≠ 0 ∧ ∀ i j, i ≠ j → g i w ≠ g j w := by
    refine (eventually_all.2 fun j => (hU j).mem_nhds (hyU j)).and
      (((MvPolynomial.continuous_eval P).continuousAt.eventually_ne hy₀).and ?_)
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · have hne : g i y₀ - g j y₀ ≠ 0 := by
        rw [hgy, hgy]; exact sub_ne_zero.2 fun h => hij (hxinj h)
      filter_upwards [((hcont i).sub (hcont j)).eventually_ne hne] with w hw _
      exact sub_ne_zero.1 hw
  obtain ⟨W, hWsub, hWo, hyW⟩ := mem_nhds_iff.1 hev
  have hgZ : ∀ j, ∀ w ∈ U j, g j w ∈ zeroSet J ∩ V j := fun j w hw => (hZ j).symm ▸ ⟨w, hw, rfl⟩
  refine ⟨W, hWo, hyW, fun w hw => (hWsub hw).2.1, g,
    fun j => (hg j).mono fun w hw => (hWsub hw).1 j, fun w hw => ?_⟩
  obtain ⟨hwU, hwP, hwinj⟩ := hWsub hw
  have hinj : Function.Injective (fun j => g j w) := fun i j h => by_contra fun hij => hwinj i j hij h
  have hsub : Set.range (fun j => g j w) ⊆ fibre J A w := by
    rintro _ ⟨j, rfl⟩
    exact ⟨(hgZ j w (hwU j)).1, hAg j w (hwU j)⟩
  obtain ⟨hfinw, hcardw, -⟩ := hcov w hwP
  refine ⟨(Set.eq_of_subset_of_ncard_le hsub ?_ hfinw).symm, hinj, fun j => ?_⟩
  · rw [hcardw, Set.ncard_range_of_injective hinj, Nat.card_fin]
  · refine ⟨W, hWo, by rw [hAg j w (hwU j)]; exact hw, (hg j).mono fun v hv => (hWsub hv).1 j,
      by rw [hAg j w (hwU j)], fun v hv => ⟨hAg j v ((hWsub hv).1 j), (hgZ j v ((hWsub hv).1 j)).1⟩,
      V j, (hV j).mem_nhds (hgZ j w (hwU j)).2, fun x' hx' _ => ?_⟩
    obtain ⟨u, hu, rfl⟩ : x' ∈ g j '' U j := hZ j ▸ hx'
    rw [hAg j u hu]

end DiscriminantSheetCover

theorem DiscriminantSheetCover.proof (h₁ : ComplexSets.DiscriminantCover.Statement) :
    DiscriminantSheetCover.Statement := by
  intro n d J A hJ hdim hA
  obtain ⟨P, hP, hcov⟩ := h₁ n d J A hJ hdim hA
  have hall : ∀ y : Fin d → ℂ, ∃ W : Set (Fin d → ℂ), IsOpen W ∧ (eval y P ≠ 0 → y ∈ W) ∧
      W ⊆ {y | eval y P ≠ 0} ∧ ∃ s : Fin (projDegree J A) → (Fin d → ℂ) → Fin n → ℂ,
        (∀ j, DifferentiableOn ℂ (s j) W) ∧
        ∀ w ∈ W, fibre J A w = Set.range (fun j => s j w) ∧ Function.Injective (fun j => s j w) ∧
          ∀ j, IsSheetAt J A (s j w) (s j) := by
    intro y
    by_cases hy : eval y P = 0
    · exact ⟨∅, isOpen_empty, fun h => absurd hy h, Set.empty_subset _, fun _ _ => 0,
        fun _ => differentiableOn_empty, fun _ h => h.elim⟩
    · obtain ⟨W, hWo, hyW, hWP, s, hs, hsW⟩ := DiscriminantSheetCover.local_sheets hcov y hy
      exact ⟨W, hWo, fun _ => hyW, hWP, s, hs, hsW⟩
  choose W hWo hyW hWP s hs hsW using hall
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : {y | eval y P ≠ 0} ⊆ ⋃ k, W (e k) := by
    intro y hy
    have : y ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨y, hyW y hy⟩
    obtain ⟨i, hiT, hyi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact Set.mem_iUnion.2 ⟨k, hyi⟩
  have hcompl : (⋃ k, disjointed (fun k => W (e k)) k)ᶜ ⊆ {y | eval y P = 0} := by
    rw [iUnion_disjointed]
    intro y hy
    by_contra h
    exact hy (hcover h)
  exact ⟨P, fun k => W (e k), disjointed (fun k => W (e k)), fun _ => projDegree J A, fun k => s (e k), hP,
    fun k => ⟨hWo _, MeasurableSet.disjointed (fun i => (hWo _).measurableSet) k, disjointed_le _ k, hs _⟩,
    disjoint_disjointed _, hcompl, measure_mono_null hcompl (DiscriminantSheetCover.volume_zero_set P hP),
    fun k => hsW (e k)⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermProjectionFunctionForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter PrimeGermPrimitivePresentation

noncomputable section

namespace GermProjectionFunctionForm

variable {σ : Type} [Fintype σ]

theorem germPull_toGerm {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (u : anFun (A w)) :
    germPull A (A.analyticAt w) rfl (toGerm (A w) u) = toGerm w (compA A w u) :=
  Subtype.ext (germPull_coe A (A.analyticAt w) rfl _ u.1 rfl)

theorem coordGerm_eq_toGerm (w : σ → ℂ) (i : σ) :
    coordGerm w i = toGerm w (mkA (fun z : σ → ℂ => z i)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)) :=
  Subtype.ext rfl

theorem isGermCombination_of_mem {w : σ → ℂ} {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) (u : anFun w)
    (hu : toGerm w u ∈ holGermIdeal w p) (f : (σ → ℂ) → ℂ) (hf : ∀ z, u.1 z = f z) :
    IsGermCombination w p f := by
  obtain ⟨h, hh, e⟩ := exists_of_mem_holGermIdeal p hu
  exact ⟨h, hh, (Germ.coe_eq.1 e).mono fun z hz => by rw [← hf]; exact hz⟩

end GermProjectionFunctionForm


open GermProjectionFunctionForm in
theorem GermProjectionFunctionForm.proof : GermProjectionFunctionForm.Statement := by
  classical
  intro σ _ w k p d A hp ⟨hinj, hgen, hint⟩
  let Z : σ → anFun w := fun i => mkA (fun z : σ → ℂ => z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  have hZ : ∀ i, coordGerm w i = toGerm w (Z i) := coordGerm_eq_toGerm w
  have hpull : ∀ φ : holGerms (A w), germPull A (A.analyticAt w) rfl φ = toGerm w (compA A w (rep φ)) := by
    intro φ
    conv_lhs => rw [← toGerm_rep φ]
    exact germPull_toGerm A w (rep φ)
  refine ⟨?_, ?_, ?_⟩
  · intro h hh hcomb
    have hmem := (toGerm_mem_iff hp (compA A w (mkA h hh))).2 hcomb
    rw [← germPull_toGerm] at hmem
    have h0 := congrArg Subtype.val (hinj _ hmem)
    exact Germ.coe_eq.1 (h0.trans (Germ.coe_zero (l := 𝓝 (A w)) (M := ℂ)).symm)
  · intro i
    obtain ⟨q, hq, hqP⟩ := hint i
    refine ⟨q.natDegree, fun j => (rep (q.coeff j)).1, fun j => (rep (q.coeff j)).2, ?_⟩
    have key : q.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w i) =
        toGerm w (Z i ^ q.natDegree + ∑ j : Fin q.natDegree, compA A w (rep (q.coeff j)) * Z i ^ (j : ℕ)) := by
      conv_lhs => rw [hq.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, map_add, map_pow, map_sum, map_mul, hpull, hZ]
      rw [Fin.sum_univ_eq_sum_range (fun j => toGerm w (compA A w (rep (q.coeff j))) * toGerm w (Z i) ^ j)]
    rw [key] at hqP
    refine isGermCombination_of_mem p _ hqP _ fun z => ?_
    simp [Z, mkA, compA, Finset.sum_apply]
  · intro g hg
    obtain ⟨F, hF⟩ := hgen (toGerm w (mkA g hg))
    let e := Finsupp.equivFunOnFinite (α := σ) (M := ℕ)
    refine ⟨F.support.image e, fun m => (rep (F.coeff (e.symm m))).1, fun m _ => (rep (F.coeff (e.symm m))).2, ?_⟩
    have key : toGerm w (mkA g hg) - MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F =
        toGerm w (mkA g hg - ∑ m ∈ F.support, compA A w (rep (F.coeff m)) * ∏ i, Z i ^ m i) := by
      rw [MvPolynomial.eval₂_eq']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_mul, map_prod, map_pow, hpull, hZ]
    rw [key] at hF
    refine isGermCombination_of_mem p _ hF _ fun z => ?_
    rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
    simp [Z, mkA, compA, Finset.sum_apply, Finset.prod_apply, e]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongMassNearSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongMassNearSmall.proof (hReg : RegMassNearSmall.Statement)
    (hVar : VarMassNearSmall.Statement) : LelongMassNearSmall.Statement := by
  classical
  intro n d J I u φ f hJ hdim hu hφ _ hIdim hf hfc δ hδ
  set S := (J ⊔ Ideal.span {linForm u}).minimalPrimes with hS
  have hSfin : S.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  set M : ℝ := ∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun W _ => Nat.cast_nonneg _
  have hδ' : 0 < δ / (M + 1) := by positivity
  obtain ⟨U₀, hU₀, hIU₀, hT⟩ := hReg n d J I u φ f hJ hdim hu hφ hIdim hf.continuous hfc δ hδ
  have hW : ∀ W ∈ S, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
      ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
        |varInt W d (fun x => χ x * f x) φ| ≤ δ / (M + 1) := by
    intro W hWm
    obtain ⟨hWp, hWJ, -⟩ := mem_minimalPrimes_sup_linForm hWm
    refine hVar n d W I φ f hWp
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hJ hdim hu hWm)
      (fun i => ?_) hIdim hf.continuous hfc _ hδ'
    obtain ⟨U, hU, hSU, hC⟩ := hφ i
    exact ⟨U, hU, hWJ.trans hSU, hC⟩
  choose! UW hUW hIUW hLW using hW
  have hU : IsOpen (U₀ ∩ ⋂ W ∈ S, UW W) :=
    hU₀.inter (hSfin.isOpen_biInter fun W hW => hUW W hW)
  have hIU : zeroSet I ⊆ U₀ ∩ ⋂ W ∈ S, UW W :=
    Set.subset_inter hIU₀ (Set.subset_iInter₂ fun W hW => hIUW W hW)
  obtain ⟨χ, hχ, hχ01, hχU, V, hV, hIV, hχ1⟩ := exists_cutoff_near_zeroSet I hU hIU
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩
  refine ⟨χ, hχ, ⟨V, hV, hIV, hχ1⟩, ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact hT χ hχ.continuous hχb (hχU.trans Set.inter_subset_left) ε ⟨hε.1, hε.2.le⟩
  · rw [finsum_mem_eq_finite_toFinset_sum _ hSfin]
    calc |∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) *
            varInt W d (fun x => χ x * f x) φ|
        ≤ ∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * (δ / (M + 1)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun W hW => ?_)
          have hWS : W ∈ S := hSfin.mem_toFinset.1 hW
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hLW W hWS χ hχ.continuous hχb
            (hχU.trans (Set.inter_subset_right.trans (Set.biInter_subset_of_mem hWS))))
            (Nat.cast_nonneg _)
      _ = M * (δ / (M + 1)) := by rw [← Finset.sum_mul]
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem LocalDimDomain.proof : LocalDimDomain.Statement := by
  intro n e J hJ he q hq
  have := hJ
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hJM : J ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := M.map (Ideal.Quotient.mk J)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ J) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk J y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk J z ∉ M.map (Ideal.Quotient.mk J)
      rw [Ideal.mem_quotient_iff_mem hJM]
      exact hz
    · intro h
      change Ideal.Quotient.mk J y ∉ M.map (Ideal.Quotient.mk J) at h
      rw [Ideal.mem_quotient_iff_mem hJM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt J q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt J q),
    NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) m hm, he]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurvePointDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem NormalCurvePointDVR.proof : NormalCurvePointDVR.Statement := by
  intro σ _ I w hI hic hdim hw
  have : I.IsPrime := hI
  let m : Ideal (MvPolynomial σ ℂ) := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  let S := Localization.AtPrime m
  let T := S ⧸ I.map (algebraMap (MvPolynomial σ ℂ) S)
  let A := MvPolynomial σ ℂ ⧸ I
  have hIm : I ≤ m := fun f hf ↦ RingHom.mem_ker.2 (hw f hf)
  let P : Ideal A := m.map (Ideal.Quotient.mk I)
  have hmem : ∀ f, Ideal.Quotient.mk I f ∈ P ↔ f ∈ m := fun f ↦ Ideal.mem_quotient_iff_mem hIm
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIm)

  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 (by rw [hdim])
  have : Ring.DimensionLEOne A := ⟨fun hp0 hp ↦ hp.isMaximal_of_ne_bot hp0⟩
  have : IsDedekindRing A := { toIsIntegralClosure := hic }

  have hP0 : P ≠ ⊥ := by
    intro h0
    have hmI : m ≤ I := fun f hf ↦ by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h0]
      exact (hmem f).2 hf
    have hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun z ↦ ⟨C z, by simp⟩)
    have hfield : IsField A := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).1 (le_antisymm hIm hmI ▸ hmax)
    have := ringKrullDim_eq_zero_of_isField hfield
    rw [hdim] at this
    exact_mod_cast this

  have hsub : Algebra.algebraMapSubmonoid A m.primeCompl = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact fun h ↦ hf ((hmem f).1 h)
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨f, fun h ↦ hx ((hmem f).2 h), rfl⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid A m.primeCompl) T := inferInstance
  have hlocP : IsLocalization.AtPrime T P := by
    change IsLocalization P.primeCompl T
    rw [← hsub]
    exact hloc
  have hdom : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T (M := P.primeCompl)
    P.primeCompl_le_nonZeroDivisors
  exact ⟨hdom, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 T⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Matrix

noncomputable section

theorem PosPartIndep.proof (h : SheetOnlyNull.Statement) (hL : PosPartLocal.Statement)
    (hS : PosPartSplit.Statement) : PosPartIndep.Statement := by
  intro n d J A A' f φ hJ hd hA hA' hf hφ

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      ((∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A' (E.indicator f) φ y) := by
    intro x
    by_cases hx : (∃ s, IsSheetAt J A x s) ∧ ∃ s', IsSheetAt J A' x s'
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J A A' f φ x hf hφ hx.1 hx.2
      exact ⟨W, hW, fun _ _ => hxW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 => absurd ⟨h1, h2⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [chartPosDens, sheetSum]
  choose W hWo hxW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ W (e k) := fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2
  have hEd : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right
      Set.inter_subset_right
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') →
      ∃ k, x ∈ E k := by
    intro x hxZ h1 h2
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x h1 h2⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hxi⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  have hae : ∀ B B' : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B → IsFiniteProjection J B' →
      (∀ x ∈ zeroSet J, (∃ s, IsSheetAt J B x s) → (∃ s', IsSheetAt J B' x s') → ∃ k, x ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B B' hB hB' hc
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h n d J B B' hJ hd hB hB')] with y hy
    refine hS n d J B f φ E y hB hEd fun x hx hs => hc x hx.1 hs ?_
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩
  have hint : ∀ B : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B →
      (∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y)) →
      ∫⁻ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B hB hB2
    rw [lintegral_congr_ae hB2, lintegral_tsum fun k =>
      (IntegralIndep.measurable_chartPosDens hB (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable]
  rw [hint A hA (hae A A' hA hA' hcov),
    hint A' hA' (hae A' A hA' hA fun x hx h1 h2 => hcov x hx h2 h1)]
  exact tsum_congr fun k => hWE (e k) (E k) (hEm k) (hEW k)

end

end GroundTheory.Heights₂.Heights
end

