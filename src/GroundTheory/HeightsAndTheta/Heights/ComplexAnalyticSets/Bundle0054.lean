module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageAreaSetFrame
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

namespace SheetImageAreaSet

theorem exists_adapted_frame {n d : ℕ}
    (P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) (hP : Function.Surjective P) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m)
      (Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
      (L : EuclideanSpace ℂ (Fin d) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d))
      (π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)),
      (∀ z, ‖Q z‖ = ‖z‖) ∧
        ∀ z, Q z = WithLp.toLp 2 (fun j => Sum.elim (fun i => L (P z) i) (fun i => π z i) (e j)) := by
  classical
  set K := LinearMap.ker P with hKdef
  have h1 := K.finrank_add_finrank_orthogonal
  have h2 := LinearMap.finrank_range_add_finrank_ker P
  rw [LinearMap.range_eq_top.2 hP, finrank_top] at h2
  simp only [finrank_euclideanSpace_fin] at h1 h2
  rw [← hKdef] at h2
  have hW : finrank ℂ Kᗮ = d := by omega
  have hn : n = d + finrank ℂ K := by omega
  let bW : OrthonormalBasis (Fin d) ℂ Kᗮ := (stdOrthonormalBasis ℂ Kᗮ).reindex (finCongr hW)
  let bK := stdOrthonormalBasis ℂ K
  let e : Fin n ≃ Fin d ⊕ Fin (finrank ℂ K) := (finCongr hn).trans finSumFinEquiv.symm
  let πW : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    bW.repr.toLinearMap ∘ₗ (Kᗮ.orthogonalProjectionOnto : _ →L[ℂ] Kᗮ).toLinearMap
  let π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ K)) :=
    bK.repr.toLinearMap ∘ₗ (K.orthogonalProjectionOnto : _ →L[ℂ] K).toLinearMap
  obtain ⟨R, hR⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
  have hPR : ∀ y, P (R y) = y := fun y => LinearMap.congr_fun hR y
  have hWR : ∀ z, πW (R (P z)) = πW z := by
    intro z
    have hmem : R (P z) - z ∈ Kᗮᗮ :=
      K.le_orthogonal_orthogonal (by simp [hKdef, LinearMap.mem_ker, hPR])
    have h0 := Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hmem
    have h3 : πW (R (P z) - z) = 0 := by simp [πW, h0]
    rwa [map_sub, sub_eq_zero] at h3
  have hinj : Function.Injective (πW ∘ₗ R) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : Kᗮ.orthogonalProjectionOnto (R y) = 0 := by simpa [πW] using hy
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, K.orthogonal_orthogonal] at h0
    rw [← hPR y]
    exact h0
  let L := LinearEquiv.ofInjectiveEndo _ hinj
  let Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toFun := fun z => WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j))
      map_add' := fun z w => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp
      map_smul' := fun c z => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp }
  refine ⟨finrank ℂ K, e, Q, L, π, fun z => ?_, fun z => ?_⟩
  · refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    show ‖(WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) :
      EuclideanSpace ℂ (Fin n))‖ ^ 2 = _
    rw [GraphAreaHolomorphic.norm_sq_sumElim e (πW z) (π z), Submodule.norm_sq_eq_add_norm_sq_projection z K,
      add_comm]
    simp [πW, π]
  · show WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) = _
    simp [L, hWR]

theorem areaJacobian_eq_normDet {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) : areaJacobian M = M.normDet := by
  have h := M.normDet_sq
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [areaJacobian, ← h, Real.sqrt_sq M.normDet_nonneg]

theorem areaJacobian_comp_of_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Q : F →ₗ[ℝ] F) (hQ : ∀ v, ‖Q v‖ = ‖v‖) (M : E →ₗ[ℝ] F) :
    areaJacobian (Q ∘ₗ M) = areaJacobian M := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp,
    show (Q.domRestrict (LinearMap.range M)).normDet = 1 from
      LinearIsometry.normDet_eq_one ⟨Q.domRestrict _, fun v => hQ v⟩, one_mul]

theorem areaJacobian_comp_endo {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (T : E →ₗ[ℝ] E) :
    areaJacobian (M ∘ₗ T) = areaJacobian M * |LinearMap.det T| := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp_of_finrank_eq _ _ rfl,
    LinearMap.normDet_eq_abs_det]

end SheetImageAreaSet

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceReachesCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem SheetPieceReachesCentre.proof : SheetPieceReachesCentre.Statement := by
  intro σ _ X w B d A D δ N U V hpar hU hV hcover hdisj hne
  obtain ⟨-, hwXB, hD, hDc, hmaps, hprop, hcentre, hδ, ⟨y₁, hy₁D, hy₁⟩, -, hchart, -⟩ := hpar
  set T : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U with hTdef

  have key : ∀ y ∈ D, y ∈ closure (A '' T) → ∃ x ∈ closure T, x ∈ X ∩ B ∧ A x = y := by
    intro y hyD hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD y hyD
    have hKD : Metric.closedBall y (ε / 2) ⊆ D :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    have hP := hprop _ hKD (isCompact_closedBall y (ε / 2))
    have hQsub : closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2)) ⊆
        {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y (ε / 2)} :=
      closure_minimal (fun x hx => ⟨hx.1.1.1, hx.2⟩) hP.isClosed
    have hQ : IsCompact (closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      hP.of_isClosed_subset isClosed_closure hQsub
    have hAQ : IsClosed (A '' closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      (hQ.image A.continuous).isClosed
    have hyK : y ∈ closure (A '' (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) := by
      rw [mem_closure_iff_nhds] at hy ⊢
      intro t ht
      obtain ⟨z, ⟨hzt, hzK⟩, x, hxT, rfl⟩ :=
        hy (t ∩ Metric.closedBall y (ε / 2)) (Filter.inter_mem ht (Metric.closedBall_mem_nhds y (half_pos hε)))
      exact ⟨A x, hzt, x, ⟨hxT, hzK⟩, rfl⟩
    obtain ⟨x, hxQ, rfl⟩ := closure_minimal (Set.image_mono subset_closure) hAQ hyK
    exact ⟨x, closure_mono Set.inter_subset_left hxQ, (hQsub hxQ).1, rfl⟩

  have hopen : IsOpen (A '' T) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, ⟨⟨hxXB, hδx⟩, hxU⟩, rfl⟩
    obtain ⟨O, V', g, hO, hV', hxV', hg, hAg, hXBV⟩ := hchart x hxXB hδx
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := hXBV ▸ ⟨hxXB, hxV'⟩
    have hAx : A x = y₀ := by rw [← hgy₀, hAg y₀ hy₀O]
    subst hAx
    have h1 : g ⁻¹' (U ∩ V') ∈ 𝓝 (A x) :=
      (hg (A x) hy₀O).continuousAt.preimage_mem_nhds (by rw [hgy₀]; exact (hU.inter hV').mem_nhds ⟨hxU, hxV'⟩)
    have h2 : δ ⁻¹' {0}ᶜ ∈ 𝓝 (A x) :=
      (hδ (A x) (hmaps hxXB)).continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hδx)
    filter_upwards [h1, h2, hO.mem_nhds hy₀O] with y hy1 hy2 hy3
    have hgy : g y ∈ X ∩ B ∩ V' := hXBV ▸ ⟨y, hy3, rfl⟩
    refine ⟨g y, ⟨⟨hgy.1, ?_⟩, hy1.1⟩, hAg y hy3⟩
    rw [hAg y hy3]
    exact hy2

  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, fun _ _ => analyticAt_id, fun _ _ => rfl,
      by rw [Set.inter_self, Set.image_id]⟩
  have hE : IsPreconnected (D \ {z | δ z = 0}) :=
    ManifoldZerosComplementConnected.proof (Fin d) D δ hDc hreg hδ ⟨y₁, hy₁D, hy₁⟩
  have hEsub : D \ {z | δ z = 0} ⊆ A '' T := by
    refine hE.subset_of_closure_inter_subset hopen ?_ ?_
    · obtain ⟨x₀, hx₀S, hx₀U⟩ := hne
      exact ⟨A x₀, ⟨hmaps hx₀S.1, hx₀S.2⟩, x₀, ⟨hx₀S, hx₀U⟩, rfl⟩
    · rintro y ⟨hy, hyD, hyδ⟩
      obtain ⟨x, hxcl, hxXB, rfl⟩ := key y hyD hy
      have hxS : x ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} := ⟨hxXB, hyδ⟩
      rcases hcover hxS with hxU | hxV
      · exact ⟨x, ⟨hxS, hxU⟩, rfl⟩
      · exfalso
        obtain ⟨z, hzV, hzS, hzU⟩ := mem_closure_iff.mp hxcl V hV hxV
        have hz : z ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hzS, hzU, hzV⟩
        rw [hdisj] at hz
        exact hz

  have hwD : A w ∈ D := hmaps hwXB
  have hwE : A w ∈ closure (D \ {z | δ z = 0}) := by
    by_contra hw
    rw [mem_closure_iff_nhds] at hw
    push Not at hw
    obtain ⟨t, ht, hte⟩ := hw
    have hzero : δ =ᶠ[𝓝 (A w)] 0 := by
      filter_upwards [ht, hD.mem_nhds hwD] with y hyt hyD
      by_contra hy
      exact (Set.not_nonempty_iff_eq_empty.mpr hte) ⟨y, hyt, hyD, hy⟩
    exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hwD hzero hy₁D)
  obtain ⟨x, hxcl, hxXB, hAx⟩ := key (A w) hwD (closure_mono hEsub hwE)
  rw [← hcentre x hxXB hAx]
  exact hxcl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyProjectionMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

theorem VarietyProjectionMass.proof (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hD : ComplexSets.DiscriminantCover.Statement) (hL : LocalGraphProjectionMass.Statement) :
    VarietyProjectionMass.Statement := by
  intro n d J hJ hd U hU B hB
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  obtain ⟨W, hW, hWfin⟩ := (hG n d J hJ hd).2.2.2 1 (fun _ => 1)
  obtain ⟨b, hb⟩ := MassFinite.exists_frame W hW
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hdn)
  set A := W.submatrix (I₀.orderEmbOfFin hI₀) id
  have hAfin : ComplexSets.IsFiniteProjection J A := by
    simpa using hWfin 0 (I₀.orderEmbOfFin hI₀).toEmbedding
  obtain ⟨P, hP0, hP⟩ := hD n d J A hJ hd hAfin
  set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}
  have hPJ : ComplexSets.pullback A P ∉ J := fun hmem => hP0 <| hAfin.injective <| by
    rw [map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0 :=
    NullSmaller.proof n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)
  have hsub : zeroSetEuc J ∩ B ⊆
      zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B := by
    rintro z ⟨hz, hzB⟩
    by_cases hzP : eval (A *ᵥ WithLp.ofLp z) P = 0
    · left
      intro q hq
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hzj : eval (fun i => z i) j = 0 := hz j hj
      have hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0 := by
        rw [MassFinite.eval_pullback]
        exact hzP
      simp [hzj, hpb]
    · exact Or.inr ⟨⟨hz, hzP⟩, hzB⟩
  have hgood := hL n d b I₀ G hI₀ (MassFinite.good_localGraph J W b hb I₀ hI₀ P
    (fun y hy x hx => (hP y hy).2.2 x hx)) U hU B hB
  have hGZ : G ∩ B ⊆ zeroSetEuc J ∩ B := Set.inter_subset_inter_left _ Set.inter_subset_left
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B) :=
        measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) +
          μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := measure_union_le _ _
    _ = μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := by rw [hbad, zero_add]
    _ ≤ _ := hgood
    _ ≤ _ := by
      refine Finset.sum_le_sum fun s _ => mul_le_mul' (iSup_mono fun x => ?_)
        (measure_mono (Set.image_mono hGZ))
      exact ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨hGZ hz.1, hz.2⟩)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeierstrassDivisionAtPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

variable {τ : Type} [DecidableEq τ]

def lastToCoordinate (c : τ) : (Option {c' // c' ≠ c} → ℂ) →L[ℂ] (τ → ℂ) :=
  ContinuousLinearMap.pi fun c' =>
    if h : c' = c then ContinuousLinearMap.proj none else ContinuousLinearMap.proj (some ⟨c', h⟩)

def coordinateToLast (c : τ) : (τ → ℂ) →L[ℂ] (Option {c' // c' ≠ c} → ℂ) :=
  ContinuousLinearMap.pi fun o =>
    match o with
    | none => ContinuousLinearMap.proj c
    | some c' => ContinuousLinearMap.proj c'.1

theorem lastToCoordinate_apply (c : τ) (w : Option {c' // c' ≠ c} → ℂ) (c' : τ) :
    lastToCoordinate c w c' = if h : c' = c then w none else w (some ⟨c', h⟩) := by
  by_cases h : c' = c <;> simp [lastToCoordinate, h]

omit [DecidableEq τ] in
theorem coordinateToLast_none (c : τ) (y : τ → ℂ) : coordinateToLast c y none = y c := rfl

omit [DecidableEq τ] in
theorem coordinateToLast_some (c : τ) (y : τ → ℂ) (c' : {c' // c' ≠ c}) :
    coordinateToLast c y (some c') = y c'.1 := rfl

theorem lastToCoordinate_coordinateToLast (c : τ) (y : τ → ℂ) :
    lastToCoordinate c (coordinateToLast c y) = y := by
  funext c'
  rw [lastToCoordinate_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem lastToCoordinate_pointWithLast (c : τ) (s : ℂ) :
    lastToCoordinate c (pointWithLast 0 s) = Pi.single c s := by
  funext c'
  rw [lastToCoordinate_apply]
  split_ifs with h
  · subst h; simp [pointWithLast]
  · simp [pointWithLast, h]

theorem WeierstrassDivisionAtPoint.proof (hW : WeierstrassDivision.Statement) :
    WeierstrassDivisionAtPoint.Statement := by
  intro τ _ _ y₀ c d F g hF hg hord
  have hA : ∀ h : (τ → ℂ) → ℂ, AnalyticAt ℂ h y₀ →
      AnalyticAt ℂ (fun w => h (y₀ + lastToCoordinate c w)) 0 := by
    intro h hh
    exact AnalyticAt.fun_comp_of_eq hh (analyticAt_const.add ((lastToCoordinate c).analyticAt 0)) (by simp)
  have hord' : analyticOrderAt
      (fun t => (fun w => F (y₀ + lastToCoordinate c w)) (pointWithLast 0 t)) 0 = d := by
    simpa only [lastToCoordinate_pointWithLast] using hord
  obtain ⟨q, a, hq, ha, heq⟩ := hW {c' // c' ≠ c} d _ _ (hA F hF) (hA g hg) hord'
  refine ⟨fun y => q (coordinateToLast c (y - y₀)), fun j u => a j (fun c' => u c'.1 - y₀ c'.1), ?_, ?_, ?_⟩
  · exact AnalyticAt.fun_comp_of_eq hq
      (((coordinateToLast c).analyticAt _).comp (analyticAt_id.sub analyticAt_const)) (by simp)
  · intro j
    have hR : AnalyticAt ℂ (fun u : τ → ℂ => fun c' : {c' // c' ≠ c} => u c'.1 - y₀ c'.1) (zeroCoordinate c y₀) := by
      have hL := ((ContinuousLinearMap.pi fun c' : {c' // c' ≠ c} =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c'.1).analyticAt (zeroCoordinate c y₀)).sub
          (analyticAt_const (v := fun c' : {c' // c' ≠ c} => y₀ c'.1))
      convert hL using 1
      funext u c'
      rfl
    refine AnalyticAt.fun_comp_of_eq (ha j) hR ?_
    funext c'
    simp [zeroCoordinate_apply, c'.2]
  · have hT : Tendsto (fun y => coordinateToLast c (y - y₀)) (𝓝 y₀) (𝓝 0) := by
      have hc : Continuous fun y : τ → ℂ => coordinateToLast c (y - y₀) :=
        (coordinateToLast c).continuous.comp (continuous_id.sub continuous_const)
      simpa using hc.tendsto y₀
    filter_upwards [hT.eventually heq] with y hy
    have hy' : y₀ + lastToCoordinate c (coordinateToLast c (y - y₀)) = y := by
      rw [lastToCoordinate_coordinateToLast]; abel
    simp only [hy'] at hy
    rw [hy]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun i : {c' // c' ≠ c} => coordinateToLast c (y - y₀) (some i)) =
        fun c' => zeroCoordinate c y c'.1 - y₀ c'.1 := by
      funext c'
      rw [coordinateToLast_some, zeroCoordinate_apply, if_neg c'.2, Pi.sub_apply]
    rw [h1, coordinateToLast_none, Pi.sub_apply]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZariskiAnalyticNormality
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

theorem holGerms_isUnit_of_value_ne_zero {σ : Type} [Fintype σ] {w : σ → ℂ} (φ : holGerms w)
    (hφ : holGermValue w φ ≠ 0) : IsUnit φ := by
  rcases φ with ⟨_, f, hf, rfl⟩
  have hfw : f w ≠ 0 := hφ
  let ψ : holGerms w := ⟨((fun z => (f z)⁻¹ : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ), _, hf.inv hfw, rfl⟩
  refine IsUnit.of_mul_eq_one ψ (Subtype.ext ?_)
  change ((fun z => f z * (f z)⁻¹ : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = ((fun _ => (1 : ℂ) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
  exact Germ.coe_eq.2 ((hf.continuousAt.eventually_ne hfw).mono fun z hz => mul_inv_cancel₀ hz)

theorem holGermPointIdeal_le_jacobson {σ : Type} [Fintype σ] (w : σ → ℂ) :
    holGermPointIdeal w ≤ (⊥ : Ideal (holGerms w)).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  apply holGerms_isUnit_of_value_ne_zero
  have hx0 : holGermValue w x = 0 := RingHom.mem_ker.1 hx
  simp [map_add (f := _), map_mul, hx0]

theorem germQuotPointIdeal_le_jacobson {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    germQuotPointIdeal I w ≤ (⊥ : Ideal (holGerms w ⧸ I.map (polyGerm w))).jacobson := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have hu := Ideal.mem_jacobson_bot.1 (holGermPointIdeal_le_jacobson w hx') y'
  simpa [map_add (f := _), map_mul] using hu.map (Ideal.Quotient.mk (I.map (polyGerm w)))

theorem ZariskiAnalyticNormality.proof (hN : HolGermsNoetherian.Statement)
    (hD : CompletionNormalDescent.Statement) (hA : AffineCompletionNormal.Statement)
    (hE : GermCompletionEquiv.Statement) : ZariskiAnalyticNormality.Statement := by
  intro σ _ I w hI hIC hw
  have := hN σ w
  obtain ⟨e, -⟩ := hE σ I w
  obtain ⟨hdom, hic⟩ := hA σ I (polyPointIdeal I w) hI hIC (polyPointIdeal_isMaximal I w hw)
  have hdom' : IsDomain (AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :=
    e.toMulEquiv.isDomain
  have hic' : IsIntegrallyClosed
      (AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :=
    IsIntegrallyClosed.of_equiv e.symm
  obtain ⟨hB, hBic⟩ := hD _ (germQuotPointIdeal I w) inferInstance
    (germQuotPointIdeal_le_jacobson I w) hdom' hic'
  exact ⟨(Ideal.Quotient.isDomain_iff_prime _).1 hB, hBic⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartIntSumOffHyperplane
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def ChartIntSumOffHyperplane.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (u : Fin n → ℂ)
    (m : ℕ) (f : (Fin n → ℂ) → ℝ) (F : Fin m → (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J →
    (∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, F b x) →
    (∀ b, Integrable (chartDens J A (F b) φ)) →
      chartInt J A f φ = ∑ b, chartInt J A (F b) φ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def ChartMassCompact.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    ContinuousOn f (zeroSet J) → (∀ i, SmoothNear (zeroSet J) (ψ i)) →
    (HasCompactSupport f ∨ ∃ i, HasCompactSupport (ψ i)) →
      Integrable (chartAbsDens J A f ψ)

end

end GroundTheory.Heights₂.Heights
end

