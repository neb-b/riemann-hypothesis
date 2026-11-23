module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitalIntegralEqInvDegSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0220
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairRelevantOfPoint
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver GlobalTheory.HL
open scoped Classical

namespace GlobalTheory.RelGPoint

open GlobalTheory.HL.CoordExist

theorem exists_coord_of_point {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) (hM : M.OK) {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r)
    (hrk : Module.finrank E V = k + 2 * r + 1) (hpt : P.IsPoint) (hN : P.NormsOK) (hG : P.Gv ≠ 0) :
    ∃ S : Frames M.L r k, Nonempty (Coord P S) := by
  obtain ⟨w, hw⟩ := hpt
  obtain ⟨hTo, hT, hTo', hT', hgg⟩ := hN
  have := hM.loc
  have := nontriv M.L
  have := H.free
  have := H.fin
  let b := Module.finBasisOfFinrankEq E V hrk
  obtain ⟨ϖ, hϖ, hϖg⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    rcases h : M.split with _ | g
    · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    · exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  refine ⟨
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (b i) (b j)
      herm := hermND H b
      T := Units.mk0 _ hT
      T' := Units.mk0 _ hT'
      f := fun a => b.equivFun (P.A.f a)
      f' := fun a => b.equivFun (P.B.f a)
      es := fun a => b.equivFun (P.A.es a)
      es' := fun a => b.equivFun (P.B.es a)
      gram := fun a c => by rw [hf_basis]; exact gram_eq _ _ _
      gram' := fun a c => by rw [hf_basis]; exact gram_eq _ _ _
      dual := fun a c => by rw [hf_basis]; exact dual_eq _ _ _
      dual' := fun a c => by rw [hf_basis]; exact dual_eq _ _ _
      iso := fun a c => by rw [hf_basis]; exact P.A.h_ss _ _
      iso' := fun a c => by rw [hf_basis]; exact P.B.h_ss _ _
      w := w
      relevant := fun a c => ?_
      G_ne := ?_
      gg := M.split.isSome
      gg_ok := fun h => ?_ }, ⟨
    { e := b.equivFun
      h_eq := fun x y => hf_basis H b x y
      f_eq := fun _ => rfl
      f'_eq := fun _ => rfl
      es_eq := fun _ => rfl
      es'_eq := fun _ => rfl
      T_eq := rfl
      T'_eq := rfl
      gg_none := fun h => by simp only [h, Option.isSome_none]
      gg_some := fun g h => ⟨by simp only [h, Option.isSome_some], hϖg g h⟩ }⟩⟩
  · rw [hf_basis, ← hw, mul_right_comm, ← mul_pow]
    simp [HermSp.Zhat]
  · simp only [hf_basis]
    have h1 : H.Dl P.A.f P.B.f (r + 1) =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last (r + 1)) := by
      unfold HermSp.Dl; rw [dite_eq_left le_rfl]; rfl
    have h2 : H.Dl P.A.f P.B.f r =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last r).castSucc := by
      unfold HermSp.Dl; rw [dite_eq_left (Nat.le_succ r)]; rfl
    rw [← h1, ← h2]
    exact hG
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hgg g hg
    exact ⟨not_field M.L g, unit_of hTo u hu, unit_of hTo' v hv⟩

theorem relG_of_point : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.IsPoint → P.NormsOK → P.Gv ≠ 0 → P.RelG (theta M) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hpt hN hG
  obtain ⟨S, ⟨c⟩⟩ := exists_coord_of_point M hM H r k P hrk hpt hN hG
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨hli, -, -, hD, hDl, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  obtain ⟨-, -, -, hSt, hpsi, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hZm : S.Zh = H.Zhat P.A.f P.B.f := by
    ext a b
    show S.h (S.f' b) (S.f a) = H.h (P.B.f b) (P.A.f a)
    rw [c.f_eq, c.f'_eq, c.h_eq]
  have hDm : ∀ l (hl : l ≤ r + 1), P.Dm l = S.D ⟨l, Nat.lt_succ_of_le hl⟩ := by
    intro l hl
    unfold FPair.Dm HermSp.Dl
    rw [dite_eq_left hl]
    unfold Frames.D lead
    rw [hZm]
  have hmap : ∀ (f : Fin (r + 1) → V) (g : Fin (r + 1) → S.V), (∀ a, g a = c.e (f a)) →
      ∀ x ∈ H.Xp f, c.e x ∈ Submodule.span E (Set.range g) := by
    intro f g hg x hx
    have hgf : g = (c.e : V →ₗ[E] S.V) ∘ f := funext hg
    rw [hgf, Set.range_comp, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hx
  have hdisj := (linearIndependent_sum.1 hli).2.2
  refine ⟨?_, ?_, hG, ?_, ?_, hpt, hN⟩
  · rw [eq_bot_iff]
    intro x hx
    have h0 : c.e x = 0 :=
      (Submodule.disjoint_def.1 hdisj) _ (hmap _ _ c.f_eq x hx.1) (hmap _ _ c.f'_eq x hx.2)
    rw [Submodule.mem_bot]
    exact c.e.map_eq_zero_iff.1 h0
  · rw [hDm (r + 1) le_rfl]
    exact hD
  · intro l hl
    rw [hDm l hl]
    by_cases h : S.D ⟨l, Nat.lt_succ_of_le hl⟩ = 0
    · exact Or.inl h
    · exact Or.inr (hDl _ h)
  · intro g hg
    rw [(hpsi g).1, (hpsi g).2]
    exact GlobalTheory.HL.CharAgree.psi_eq_psi' M.L r k S _ ((hSt g).1 hg)

end GlobalTheory.RelGPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqIintLeLiminf
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerLower

section LinAlg

variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

omit [FiniteDimensional ℂ G] in
theorem hs_eq_sum (A : H →L[ℂ] G) : hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hs_adjoint [CompleteSpace H] [CompleteSpace G] (A : H →L[ℂ] G) :
    hsNormSq (ContinuousLinearMap.adjoint A) = hsNormSq A := by
  rw [hs_eq_sum, hs_eq_sum]
  have h1 : ∀ j, ‖ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ G j)‖ ^ 2 =
      ∑ i, ‖⟪stdOrthonormalBasis ℂ H i, ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ G j)⟫_ℂ‖ ^ 2 :=
    fun j => ((stdOrthonormalBasis ℂ H).sum_sq_norm_inner_right _).symm
  have h2 : ∀ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 =
      ∑ j, ‖⟪A (stdOrthonormalBasis ℂ H i), stdOrthonormalBasis ℂ G j⟫_ℂ‖ ^ 2 :=
    fun i => ((stdOrthonormalBasis ℂ G).sum_sq_norm_inner_left _).symm
  simp_rw [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]

omit [FiniteDimensional ℂ G] in
theorem hs_isom_comp (U : G →L[ℂ] G) (hU : ∀ v, ‖U v‖ = ‖v‖) (A : H →L[ℂ] G) :
    hsNormSq (U.comp A) = hsNormSq A := by
  rw [hs_eq_sum, hs_eq_sum]
  simp [hU]

theorem hs_unitary [CompleteSpace H] [CompleteSpace G] (U : G →L[ℂ] G) (hU : ∀ v, ‖U v‖ = ‖v‖)
    (V : H →L[ℂ] H) (hV : ∀ v, ‖ContinuousLinearMap.adjoint V v‖ = ‖v‖) (A : H →L[ℂ] G) :
    hsNormSq (U.comp (A.comp V)) = hsNormSq A := by
  rw [hs_isom_comp U hU, ← hs_adjoint, ContinuousLinearMap.adjoint_comp, hs_isom_comp _ hV, hs_adjoint]

omit [FiniteDimensional ℂ G] in
theorem hs_continuous : Continuous (hsNormSq : (H →L[ℂ] G) → ℝ) := by
  have : (hsNormSq : (H →L[ℂ] G) → ℝ) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 :=
    funext hs_eq_sum
  rw [this]
  fun_prop

end LinAlg

theorem exists_compact_approx {X E : Type} [PseudoMetricSpace X] [ProperSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ μ' : Measure X) [SFinite μ] [SFinite μ'] (S S' : Set X) (hS : IsClosed S) (hS' : IsClosed S')
    (h0 : μ Sᶜ = 0) (h0' : μ' S'ᶜ = 0) (F : X × X → E) (hF : Integrable F (μ.prod μ')) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C C' : Set X, IsCompact C ∧ C ⊆ S ∧ IsCompact C' ∧ C' ⊆ S' ∧
      ∀ A A' : Set X, MeasurableSet A → MeasurableSet A' → C ⊆ A → C' ⊆ A' →
        ‖∫ p, F p ∂((μ.restrict A).prod (μ'.restrict A')) - ∫ p, F p ∂(μ.prod μ')‖ < δ := by
  obtain ⟨o⟩ := ‹Nonempty X›
  let K : ℕ → Set (X × X) := fun n =>
    ((S ∩ Metric.closedBall o n) ×ˢ (S' ∩ Metric.closedBall o n))ᶜ
  have hKm : ∀ n, MeasurableSet (K n) := fun n =>
    ((hS.inter Metric.isClosed_closedBall).measurableSet.prod
      (hS'.inter Metric.isClosed_closedBall).measurableSet).compl
  have hKa : Antitone K := by
    intro m n hmn
    have hb : Metric.closedBall o (m : ℝ) ⊆ Metric.closedBall o n :=
      Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    exact Set.compl_subset_compl.2
      (Set.prod_mono (Set.inter_subset_inter_right _ hb) (Set.inter_subset_inter_right _ hb))
  have hlim := tendsto_setIntegral_of_antitone (f := fun p => ‖F p‖) (μ := μ.prod μ') hKm hKa
    ⟨0, hF.norm.integrableOn⟩
  have hnull : (μ.prod μ') (⋂ n, K n) = 0 := by
    have hsub : (⋂ n, K n) ⊆ (Sᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ S'ᶜ) := by
      intro p hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true, true_and,
        not_or, not_not] at hc
      obtain ⟨n, hn⟩ := exists_nat_ge (max (dist p.1 o) (dist p.2 o))
      exact Set.mem_iInter.1 hp n ⟨⟨hc.1, (le_max_left _ _).trans hn⟩, hc.2, (le_max_right _ _).trans hn⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_) <;> rw [Measure.prod_prod]
    · rw [h0, zero_mul]
    · rw [h0', mul_zero]
  rw [setIntegral_measure_zero _ hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  refine ⟨S ∩ Metric.closedBall o n, S' ∩ Metric.closedBall o n,
    (isCompact_closedBall o n).inter_left hS, Set.inter_subset_left,
    (isCompact_closedBall o n).inter_left hS', Set.inter_subset_left, fun A A' hA hA' hCA hCA' => ?_⟩
  rw [Measure.prod_restrict, ← integral_add_compl (hA.prod hA') hF, sub_add_cancel_left, norm_neg]
  refine (norm_integral_le_integral_norm _).trans_lt (lt_of_le_of_lt ?_ hn)
  refine setIntegral_mono_set hF.norm.integrableOn (Eventually.of_forall fun p => norm_nonneg _)
    (Eventually.of_forall fun p hp => ?_)
  exact Set.compl_subset_compl.2 (Set.prod_mono hCA hCA') hp

theorem le_liminf_of_ratio (b : ENNReal) (hb : b ≠ ⊤) (u m m' n n' : ℕ → ENNReal)
    (hn : ∀ j, 0 < n j ∧ n j < ⊤) (hn' : ∀ j, 0 < n' j ∧ n' j < ⊤)
    (h : Tendsto (fun j => m j / n j) atTop (𝓝 1)) (h' : Tendsto (fun j => m' j / n' j) atTop (𝓝 1))
    (hu : ∀ j, b * (m j * m' j) ≤ u j) : b ≤ liminf (fun j => u j / (n j * n' j)) atTop := by
  have ht : Tendsto (fun j => b * (m j / n j * (m' j / n' j))) atTop (𝓝 (b * (1 * 1))) :=
    ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul h (Or.inl one_ne_zero) h' (Or.inl one_ne_zero))
      (Or.inr hb)
  rw [mul_one, mul_one] at ht
  rw [← ht.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun j => ?_)
  have e : b * (m j / n j * (m' j / n' j)) = b * (m j * m' j) / (n j * n' j) := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (hn j).1.ne') (Or.inl (hn j).2.ne)]
    ring
  rw [e]
  exact ENNReal.div_le_div_right (hu j) _

variable {k r : ℕ}

theorem measurableSet_rmul_image {t : Mat k r} (ht : IsUnit t.det) {A : Set (Mt k r)}
    (hA : MeasurableSet A) : MeasurableSet (rmulM t '' A) := by
  have : rmulM t '' A = rmulM t⁻¹ ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : rmulM t⁻¹ (rmulM t y) = y := Matrix.mul_nonsing_inv_cancel_right t (Matrix.of y) ht
      rw [Set.mem_preimage, this]; exact hy
    · intro hx
      exact ⟨_, hx, Matrix.nonsing_inv_mul_cancel_right t (Matrix.of x) ht⟩
  rw [this]
  exact (continuous_rmulM _).measurable hA

theorem subset_rmul_image {t : Mt k r} (ht : IsUnit (Matrix.of t : Mat k r).det) {C Oc Om : Set (Mt k r)}
    (h : ∀ c ∈ C, ∀ x ∈ Oc, lmulM (Matrix.of c) x ∈ Om) (hO : invM t ∈ Oc) :
    C ⊆ rmulM (Matrix.of t) '' Om := fun c hc =>
  ⟨_, h c hc _ hO, Matrix.nonsing_inv_mul_cancel_right (Matrix.of t) (Matrix.of c) ht⟩

theorem hsNormSq_Iint_le_liminf : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ Om Om' : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → IsFolner (Sset k r z') μS' Om' → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∀ γ ∈ Greg k r z z', ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' γ)) ≤ Filter.liminf (fun j => (∫⁻ p, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of (act2 γ p)))) ∂(μS.prod μS')) / (μS (Om j) * μS' (Om' j))) Filter.atTop := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' Om Om' hF hF'
    x hx y hy ξ ξ' γ hγ
  have hint := (_root_.GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' y hy x hx ξ ξ' γ hγ).1
  have hcl := (_root_.GlobalTheory.SgInf.closedSub_groups k r z hS.1 hS.2.1).2.2.2.1
  have hcl' := (_root_.GlobalTheory.SgInf.closedSub_groups k r z' hS'.1 hS'.2.1).2.2.2.1
  have hP := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hS.1 hS.2.1 hS.2.2.1
  have hP' := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z' c' π' hS'.1 hS'.2.1 hS'.2.2.1
  have hinv := ((_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z hS.1 hS.2.1 μS).1 hS.2.2.2.1).2
  have hinv' := ((_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z' hS'.1 hS'.2.1 μS').1 hS'.2.2.2.1).2
  haveI := hS.2.2.2.1.1
  haveI := hS'.2.2.2.1.1
  have h0 := hS.2.2.2.1.2.2.1
  have h0' := hS'.2.2.2.1.2.2.1
  refine ENNReal.le_of_forall_nnreal_lt fun b hb => ?_
  have hb' : (b : ℝ) < hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' γ) := by
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg b.coe_nonneg] at hb
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    ((hs_continuous (H := Wq) (G := Wp)).continuousAt.eventually (lt_mem_nhds hb'))
  obtain ⟨C, C', hC, hCS, hC', hCS', happ⟩ := exists_compact_approx μS μS'
    {x | Matrix.of x ∈ Sset k r z} {x | Matrix.of x ∈ Sset k r z'} hcl.2.1 hcl'.2.1 h0 h0' _ hint hδ
  obtain ⟨Oc, hOc, hlim⟩ := hF.2 C hC hCS
  obtain ⟨Oc', hOc', hlim'⟩ := hF'.2 C' hC' hCS'
  refine le_liminf_of_ratio b ENNReal.coe_ne_top _ _ _ _ _ (fun j => (hF.1 j).2.2.2)
    (fun j => (hF'.1 j).2.2.2) hlim hlim' fun j => ?_
  have e1 : μS (Oc j) = μS (invM ⁻¹' Oc j) := by
    rw [← Measure.map_apply measurable_invM (hOc j).1, hinv]
  have e2 : μS' (Oc' j) = μS' (invM ⁻¹' Oc' j) := by
    rw [← Measure.map_apply measurable_invM (hOc' j).1, hinv']
  rw [e1, e2, ← Measure.prod_prod, ← lintegral_indicator_const
    ((measurable_invM (hOc j).1).prod (measurable_invM (hOc' j).1))]
  have hae : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.1 ∈ Sset k r z ∧ Matrix.of p.2 ∈ Sset k r z' :=
    (Measure.quasiMeasurePreserving_fst.ae (p := fun x => Matrix.of x ∈ Sset k r z) h0).and
      (Measure.quasiMeasurePreserving_snd.ae (p := fun x => Matrix.of x ∈ Sset k r z') h0')
  refine lintegral_mono_ae (hae.mono fun p hp => ?_)
  by_cases hm : p ∈ (invM ⁻¹' Oc j) ×ˢ (invM ⁻¹' Oc' j)
  swap
  · rw [Set.indicator_of_notMem hm]; exact zero_le
  rw [Set.indicator_of_mem hm, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hu : IsUnit (Matrix.of p.1 : Mat k r).det := WeylGroupFacts.isUnit_of_uh (hcl.1 hp.1)
  have hu' : IsUnit (Matrix.of p.2 : Mat k r).det := WeylGroupFacts.isUnit_of_uh (hcl'.1 hp.2)
  have heq := _root_.GlobalTheory.SgInf.Equivar.Iint_equivariant k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' x y ξ ξ' (Om j) (Om' j)
    (hF.1 j).1 (hF'.1 j).1 γ hγ.1 _ hp.1 _ hp.2
  have ha : (Matrix.of (act2 γ p) : Mat k r) = Matrix.of p.1 * γ * (Matrix.of p.2)⁻¹ := rfl
  rw [ha, heq, hs_unitary _ (hP.2.1.2.1 _ hp.1)]
  · refine (hball ?_).le
    rw [dist_eq_norm]
    exact happ _ _ (measurableSet_rmul_image hu (hF.1 j).1) (measurableSet_rmul_image hu' (hF'.1 j).1)
      (subset_rmul_image hu (hOc j).2.2 hm.1) (subset_rmul_image hu' (hOc' j).2.2 hm.2)
  · rw [← (hP'.2.2.1 _ hp.2).2, ContinuousLinearMap.adjoint_adjoint]
    exact hP'.2.1.2.1 _ hp.2

end GlobalTheory.SgInf.FolnerLower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IintEqEll
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.EllName

theorem rankOneInnerOperator_smul_smul_eq_mul_conj_smul {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (α β : ℂ) (a : Wp) (b : Wq) :
    rk1 (α • a) (β • b) = (α * (starRingEnd ℂ) β) • rk1 a b := by
  ext η
  rw [ContinuousLinearMap.smul_apply, rankOneInnerOperator_apply, rankOneInnerOperator_apply, inner_smul_left, smul_smul, smul_smul]
  congr 1
  ring

private theorem Afun_eq_inner_smul_of_isEll {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {μS : Measure (Mt k r)}
    {σ : Mat k r → (H →L[ℂ] H)} {w : H} {l : H → Wp} (hl : IsEll z ψ π μS σ (DD σ w) l)
    {w₀ : H} (hw₀ : w₀ ∈ DD σ w) (ξ : Wp) {x : Mat k r} (hx : x ∈ GG k r) :
    Afun ψ π μS σ w w₀ ξ x = ⟪l w₀, ξ⟫_ℂ • l (σ x w) := by
  unfold Afun
  rw [hl.2.2 _ (mem_DD σ w hx) _ hw₀, rankOneInnerOperator_apply]

theorem iint_eq_ell : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∀ γ ∈ Greg k r z z', Integrable (fun x : Mt k r => rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w))) μG ∧ ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ w₀' w₀ ξ ξ' γ = (⟪l w₀, ξ⟫_ℂ * ⟪ξ', l' w₀'⟫_ℂ * (d : ℂ)) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) γ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' l l' hl hl' γ hγ
  have hHaar := hStd.2.2.2.2.1
  have hd : (0 : ℝ) < d := hStd.2.2.2.2.2.1.1
  have h0 : μG {x | Matrix.of x ∉ GG k r} = 0 := by
    first
    | exact hHaar.1
    | exact hHaar.2.2.1
  have hGG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := ae_iff.2 h0
  have hU : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ (Hpk k r) hU
  have hγG : γ ∈ GG k r := Greg_subset z z' hγ
  have hγi : γ⁻¹ ∈ GG k r := (hgrp.2.2 γ hγG).2
  have hae : ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq),
      (fun x : Mt k r => rk1 (Afun (psiGen k r z c) π μS σ w w₀ ξ (Matrix.of x))
        (Afun (psiGen k r z' c') π' μS' σ w w₀' ξ' (γ⁻¹ * Matrix.of x))) =ᵐ[μG]
      fun x => (⟪l w₀, ξ⟫_ℂ * (starRingEnd ℂ) ⟪l' w₀', ξ'⟫_ℂ) •
        rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w)) := by
    intro w₀ hw₀ w₀' hw₀' ξ ξ'
    filter_upwards [hGG] with x hx
    rw [Afun_eq_inner_smul_of_isEll hl hw₀ ξ hx, Afun_eq_inner_smul_of_isEll hl' hw₀' ξ' (hgrp.2.1 _ hγi _ hx), rankOneInnerOperator_smul_smul_eq_mul_conj_smul]
  obtain ⟨u, hu, hlu⟩ := hl.2.1
  obtain ⟨u', hu', hlu'⟩ := hl'.2.1
  have hint : Integrable
      (fun x : Mt k r => rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w))) μG := by
    obtain ⟨-, hI, -⟩ := _root_.GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' u hu u' hu'
      (l u) (l' u') γ hγ
    have hc : (⟪l u, l u⟫_ℂ * (starRingEnd ℂ) ⟪l' u', l' u'⟫_ℂ) ≠ 0 :=
      mul_ne_zero (inner_self_ne_zero.2 hlu) ((map_ne_zero _).2 (inner_self_ne_zero.2 hlu'))
    refine (hI.smul (⟪l u, l u⟫_ℂ * (starRingEnd ℂ) ⟪l' u', l' u'⟫_ℂ)⁻¹).congr ?_
    filter_upwards [hae u hu u' hu' (l u) (l' u')] with x hx
    rw [Pi.smul_apply, hx, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨hint, ?_⟩
  intro w₀ hw₀ w₀' hw₀' ξ ξ'
  obtain ⟨-, -, hO⟩ := _root_.GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' w₀ hw₀ w₀' hw₀'
    ξ ξ' γ hγ
  have hO2 : OO μG (Afun (psiGen k r z c) π μS σ w w₀ ξ) (Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') γ =
      (⟪l w₀, ξ⟫_ℂ * (starRingEnd ℂ) ⟪l' w₀', ξ'⟫_ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) γ := by
    unfold OO
    rw [integral_congr_ae (hae w₀ hw₀ w₀' hw₀' ξ ξ'), integral_smul]
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hO2, eq_inv_smul_iff₀ hdne] at hO
  rw [← hO, smul_smul, inner_conj_symm]
  congr 1
  ring

end GlobalTheory.SgInf.EllName
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultipliableOfRealReOfComplexStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multipliable_ofReal_re_of_nonneg_real : ∀ (ι : Type) (c : ι → ℂ), Multipliable c → (∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) → Multipliable (fun i => ENNReal.ofReal (c i).re) ∧ ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re := by
  first | exact @GlobalTheory.multipliable_ofReal_re_of_complex' | exact GlobalTheory.multipliable_ofReal_re_of_complex' | (intros; apply GlobalTheory.multipliable_ofReal_re_of_complex' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodular
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.StabMeas
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RootMeas

theorem normR_facts : ∀ (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → NormR k r γ s μR → IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ NormR k r γ⁻¹ s (μR.map (conjM γ)) := by
  rintro k r γ s μR hs ⟨n₁, h₁, n₂, h₂, g₀, β, hg, rfl, rfl⟩
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  obtain ⟨-, -, b1, b2, a3, c1⟩ := _root_.GlobalTheory.Amp.StabNormal.stabiliser_normal k r g₀ β hg
  have hγ : n₁ * g₀ * n₂ ∈ GG k r :=
    isClosedSub_GG.2.2.2.1 _ (isClosedSub_GG.2.2.2.1 _ (n1 h₁) _ hg.1) _ (n1 h₂)
  have hinv : (n₁ * g₀ * n₂)⁻¹ = n₂⁻¹ * g₀⁻¹ * n₁⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  obtain ⟨d1, d2⟩ := haar_smul b1 b2 hs
  obtain ⟨e1, e2⟩ := haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ h₂))) (conj_mem_Rset h₁ h₂ g₀) d1 d2
  refine ⟨isClosedSub_Rset hγ, e1, e2, n₂⁻¹, n5 _ h₂, n₁⁻¹, n5 _ h₁, g₀⁻¹, β, a3, hinv, ?_⟩
  rw [map_conj_conj, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_of_mem_GG (n1 h₂)), ← map_conj_conj,
    Measure.map_smul, c1, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 h₁))]
  exact (meas_conj g₀).aemeasurable

end GlobalTheory.Amp.RootMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormStabilizerMeasureEqAnyNormalForm
section
open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.Amp.StabHaar

theorem normalFormStabilizerMeasure_eq_any_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (n₁ n₂ g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ) (μR : Measure (Mt k r)), n₁ ∈ Nset k r → n₂ ∈ Nset k r → IsNormal0 k r hj β c z z' g₀ → IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 μR → μR = (lebR0 k r j β).map (conjM n₂⁻¹) ∧ SigmaFinite (lebR0 k r j β) := by
  intro k r j hj z z' n₁ n₂ g₀ β c μR hn₁ hn₂ hg₀ hR
  obtain ⟨hz, hz', hT, -⟩ := id hR

  have hN : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 ((lebR0 k r j β).map (conjM n₂⁻¹)) := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by rw [ENNReal.ofReal_one, one_smul]⟩
  obtain ⟨-, hcl, hHaar, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 _ one_pos hN
  obtain ⟨-, -, hHaarR, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 μR one_pos hR

  obtain ⟨huniq, -, -⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos (2 * r + k + 1)
    (Rset k r (n₁ * g₀ * n₂)) ((lebR0 k r j β).map (conjM n₂⁻¹)) (matGroup hcl) hHaar
  obtain ⟨t, -, htop, ht⟩ := huniq μR hHaarR

  have hNt : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) t.toReal μR := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by
      rw [ht, ENNReal.ofReal_toReal htop.ne, Measure.map_smul]
      exact (conj_cont n₂⁻¹).measurable.aemeasurable⟩
  have h1 := normalFormStabilizerMeasure_scalar_le hj z z' _ 1 t.toReal μR hR hNt
  have h2 := normalFormStabilizerMeasure_scalar_le hj z z' _ t.toReal 1 μR hNt hR
  rw [ENNReal.ofReal_one, ENNReal.ofReal_toReal htop.ne] at h1 h2
  have ht1 : t = 1 := le_antisymm h2 h1
  obtain ⟨hH, -⟩ := _root_.GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer k r j hj z z' g₀ β c hz hz' hT hg₀
  obtain ⟨hσ, -⟩ := hH
  exact ⟨by rw [ht, ht1, one_smul], hσ⟩

end GlobalTheory.Amp.StabHaar
end

