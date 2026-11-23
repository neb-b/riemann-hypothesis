module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0063
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreSectionsCovering
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

theorem FibreSectionsCovering.proof : FibreSectionsCovering.Statement := by
  intro n e N A Ω X hX hfib hsec
  let f : X → Ω := Set.MapsTo.restrict _ X Ω hX
  show IsCoveringMap f
  have hAc : Continuous (fun x : Fin n → ℂ => A *ᵥ x) :=
    (Matrix.mulVecLin A).continuous_of_finiteDimensional
  choose O V' g hO hAO hV' hxV' hg hgx hAg hXV' using hsec

  have key : ∀ x₀ (h₀ : x₀ ∈ X) x, x ∈ X → x ∈ V' x₀ h₀ → g x₀ h₀ (A *ᵥ x) = x := by
    intro x₀ h₀ x hx hxv
    have hx' : x ∈ g x₀ h₀ '' O x₀ h₀ := hXV' x₀ h₀ ▸ ⟨hx, hxv⟩
    obtain ⟨o, ho, rfl⟩ := hx'
    rw [hAg x₀ h₀ o ho]

  have inX : ∀ x₀ (h₀ : x₀ ∈ X) w, w ∈ O x₀ h₀ → g x₀ h₀ w ∈ X ∧ g x₀ h₀ w ∈ V' x₀ h₀ := by
    intro x₀ h₀ w hw
    have h : g x₀ h₀ w ∈ X ∩ V' x₀ h₀ := hXV' x₀ h₀ ▸ ⟨w, hw, rfl⟩
    exact h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have : IsEmpty X := by
      refine ⟨fun x => ?_⟩
      have h := hfib _ (hX x.2)
      rw [hN, Nat.cast_zero, Set.encard_eq_zero] at h
      have hm : (x : Fin n → ℂ) ∈ {x' | x' ∈ X ∧ A *ᵥ x' = A *ᵥ (x : Fin n → ℂ)} := ⟨x.2, rfl⟩
      rw [h] at hm
      exact hm
    exact IsCoveringMap.of_isEmpty _
  intro y

  have hFenc : {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)}.encard = N := hfib y y.2
  have hFfin := Set.finite_of_encard_eq_coe hFenc
  have := hFfin.to_subtype
  have hFcard : Nat.card {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)} = N := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hFenc]
    rfl
  let eq := (Finite.equivFinOfCardEq hFcard).symm
  let pt : Fin N → Fin n → ℂ := fun i => (eq i : Fin n → ℂ)
  have pt_mem : ∀ i, pt i ∈ X ∧ A *ᵥ pt i = y := fun i => (eq i).2
  have pt_inj : Function.Injective pt := fun i j h => eq.injective (Subtype.ext h)
  let G : Fin N → (Fin (e + 1) → ℂ) → Fin n → ℂ := fun i => g (pt i) (pt_mem i).1
  let OO : Fin N → Set (Fin (e + 1) → ℂ) := fun i => O (pt i) (pt_mem i).1
  let VV : Fin N → Set (Fin n → ℂ) := fun i => V' (pt i) (pt_mem i).1
  have hGy : ∀ i, G i y = pt i := fun i => by
    rw [← (pt_mem i).2]
    exact hgx (pt i) (pt_mem i).1
  have hOy : ∀ i, OO i ∈ 𝓝 (y : Fin (e + 1) → ℂ) := fun i =>
    (hO _ _).mem_nhds (by have h : A *ᵥ pt i ∈ OO i := hAO _ _; rwa [(pt_mem i).2] at h)
  have hGc : ∀ i, ∀ w ∈ OO i, ContinuousAt (G i) w := fun i w hw =>
    (hg _ _).continuousOn.continuousAt ((hO _ _).mem_nhds hw)
  have hS : ∀ᶠ w in 𝓝 (y : Fin (e + 1) → ℂ), (∀ i, w ∈ OO i) ∧ ∀ i j, i ≠ j → G i w ≠ G j w := by
    refine (Filter.eventually_all.2 hOy).and
      (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_)
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · have hne : G i y ≠ G j y := by
        rw [hGy, hGy]
        exact fun h => hij (pt_inj h)
      exact (((hGc i y (mem_of_mem_nhds (hOy i))).ne_iff_eventually_ne
        (hGc j y (mem_of_mem_nhds (hOy j)))).1 hne).mono fun _ hw _ => hw
  obtain ⟨W, hWS, hWo, hyW⟩ := mem_nhds_iff.1 hS
  have hWO : ∀ i, ∀ w ∈ W, w ∈ OO i := fun i w hw => (hWS hw).1 i
  have hWd : ∀ w ∈ W, ∀ i j, i ≠ j → G i w ≠ G j w := fun w hw => (hWS hw).2
  have hGX : ∀ i, ∀ w ∈ W, G i w ∈ X := fun i w hw => (inX _ _ w (hWO i w hw)).1
  have hGV : ∀ i, ∀ w ∈ W, G i w ∈ VV i := fun i w hw => (inX _ _ w (hWO i w hw)).2
  have hAG : ∀ i, ∀ w ∈ W, A *ᵥ G i w = w := fun i w hw => hAg _ _ w (hWO i w hw)
  have hfc : Continuous f := (hAc.comp continuous_subtype_val).subtype_mk fun x => hX x.2
  have hres : ∀ i (q : Ω) (hq : (q : Fin (e + 1) → ℂ) ∈ W),
      f ⟨G i q, hGX i q hq⟩ = q := fun i q hq =>
    Subtype.ext (hAG i q hq)
  let V : Set Ω := {p | (p : Fin (e + 1) → ℂ) ∈ W}
  let U : Fin N → Set X := fun i => {x | (x : Fin n → ℂ) ∈ VV i ∧ A *ᵥ (x : Fin n → ℂ) ∈ W}
  have hVo : IsOpen V := continuous_subtype_val.isOpen_preimage _ hWo
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    continuous_subtype_val.isOpen_preimage _ ((hV' _ _).inter (hWo.preimage hAc))

  have hUG : ∀ i (x : X), x ∈ U i → G i (A *ᵥ (x : Fin n → ℂ)) = x := fun i x hx =>
    key _ _ _ x.2 hx.1
  have open_iff : ∀ i {W' : Set Ω}, W' ⊆ V → (IsOpen W' ↔ IsOpen (f ⁻¹' W' ∩ U i)) := by
    intro i W' hW'V
    refine ⟨fun h => (hfc.isOpen_preimage _ h).inter (hUo i), fun h => ?_⟩
    obtain ⟨T', hT'o, hT'eq⟩ := isOpen_induced_iff.1 h
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpW : (p : Fin (e + 1) → ℂ) ∈ W := hW'V hp
    have hGp : G i p ∈ T' := by
      have hm : (⟨G i p, hGX i p hpW⟩ : X) ∈ f ⁻¹' W' ∩ U i := by
        refine ⟨?_, hGV i p hpW, ?_⟩
        · show f ⟨G i p, hGX i p hpW⟩ ∈ W'
          rw [hres i p hpW]
          exact hp
        · show A *ᵥ G i p ∈ W
          rw [hAG i p hpW]
          exact hpW
      rw [← hT'eq] at hm
      exact hm
    rw [mem_nhds_subtype]
    refine ⟨W ∩ G i ⁻¹' T', Filter.inter_mem (hWo.mem_nhds hpW)
      ((hGc i p (hWO i p hpW)).preimage_mem_nhds (hT'o.mem_nhds hGp)), ?_⟩
    rintro q ⟨hqW, hqT⟩
    have hm : (⟨G i q, hGX i q hqW⟩ : X) ∈ Subtype.val ⁻¹' T' := hqT
    rw [hT'eq] at hm
    have h1 := hm.1
    rw [Set.mem_preimage, hres i q hqW] at h1
    exact h1
  have inj : ∀ i, (U i).InjOn f := by
    intro i x hx x' hx' hxx'
    have h : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (x' : Fin n → ℂ) := congrArg Subtype.val hxx'
    apply Subtype.ext
    rw [← hUG i x hx, ← hUG i x' hx', h]
  have surj : ∀ i, (U i).SurjOn f V := by
    intro i p hp
    refine ⟨⟨G i p, hGX i p hp⟩, ⟨hGV i p hp, ?_⟩, hres i p hp⟩
    show A *ᵥ G i p ∈ W
    rw [hAG i p hp]
    exact hp
  have disj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj => ?_
    exact hWd _ hxi.2 i j hij ((hUG i x hxi).trans (hUG j x hxj).symm)
  have exh : f ⁻¹' V ⊆ ⋃ i, U i := by
    intro x hx
    have hxW : A *ᵥ (x : Fin n → ℂ) ∈ W := hx
    set w := A *ᵥ (x : Fin n → ℂ) with hw
    have hwΩ : w ∈ Ω := hX x.2
    have hFw := hfib w hwΩ
    have hsub : Set.range (fun i => G i w) ⊆ {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      rintro _ ⟨i, rfl⟩
      exact ⟨hGX i w hxW, hAG i w hxW⟩
    have hinj : Function.Injective (fun i => G i w) := by
      intro i j h
      by_contra hij
      exact hWd w hxW i j hij h
    have heq : Set.range (fun i => G i w) = {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      refine ((Set.finite_of_encard_eq_coe hFw).subset hsub).eq_of_subset_of_encard_le hsub ?_
      rw [hFw]
      rw [hinj.encard_range]
      simp
    have hxmem : (x : Fin n → ℂ) ∈ Set.range (fun i => G i w) := by
      rw [heq]
      exact ⟨x.2, rfl⟩
    obtain ⟨i, hi⟩ := hxmem
    refine Set.mem_iUnion.2 ⟨i, ?_, hxW⟩
    show (x : Fin n → ℂ) ∈ VV i
    rw [← hi]
    exact hGV i w hxW
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Ω → X) := ⟨fun _ => ⟨pt ⟨0, hN⟩, (pt_mem _).1⟩⟩
  let T := IsOpen.trivializationDiscrete (f := f) U V hVo open_iff inj surj disj exh
  have hyT : y ∈ T.baseSet := hyW
  exact (IsEvenlyCovered.of_trivialization hyT).to_isEvenlyCovered_preimage

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem varInt_eq_zero_of_vanish {n k : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) (hf : ∀ x ∈ zeroSet W, f x = 0) :
    varInt W k f φ = 0 := by
  classical
  unfold varInt
  split_ifs with h
  · have h0 : chartDens W h.choose f φ = fun _ => 0 := by
      funext y
      unfold chartDens sheetSum
      refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
      rw [finsum_eq_dif]
      by_cases hx : x ∈ fibre W h.choose y
      · rw [dite_eq_left hx]
        split_ifs
        · show f x * _ = 0
          rw [hf x hx.1, zero_mul]
        · rfl
      · rw [dite_eq_right hx]
    simp [chartInt, h0]
  · rfl

theorem LelongLimit.proof (hOff : LelongLimitOffZero.Statement) (hOn : LelongLimitOnZero.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimit.Statement := by
  classical
  intro n d J u f φ hJ hdim hu hf hfc hφ
  set S := (J ⊔ Ideal.span {linForm u}).minimalPrimes with hS
  have hW : ∀ W ∈ S, W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0 := by
    intro W hWm
    have hle : J ⊔ Ideal.span {linForm u} ≤ W := hWm.1.2
    refine ⟨hWm.1.1,
      fun x hx q hq => hx q (hle (Ideal.mem_sup_left hq)), fun x hx => ?_⟩
    have := hx _ (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))
    simpa [linForm, linEval] using this
  have hφW : ∀ W ∈ S, ∀ i, SmoothNear (zeroSet W) (φ i) := fun W hWm i => by
    obtain ⟨U, hU, hSU, hC⟩ := hφ i
    exact ⟨U, hU, (hW W hWm).2.1.trans hSU, hC⟩
  have hclosed : IsClosed (zeroSet J ∩ {x | linEval u x = 0}) := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
    · exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  refine tendsto_of_forall_local (fun ε g => varInt J (d + 1) g (vecCons (logReg u ε) φ))
    (fun g => ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S),
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) ?_ ?_ ?_ f hf hfc
  · intro g₁ g₂ h1 h1c h2 h2c
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine hAdd n (d + 1) J g₁ g₂ _ hJ h1.continuous h1c h2.continuous h2c fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
    · simpa using hφ j
  · intro g₁ g₂ h1 h1c h2 h2c
    rw [← finsum_mem_add_distrib (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)]
    refine finsum_mem_congr rfl fun W hWm => ?_
    rw [hAdd n d W g₁ g₂ φ (hW W hWm).1 h1.continuous h1c h2.continuous h2c (hφW W hWm), mul_add]
  · intro p
    by_cases hp : p ∈ zeroSet J ∩ {x | linEval u x = 0}
    · exact hOn n d J u φ p hJ hdim hu hφ hp.1 hp.2
    · refine ⟨_, hclosed.isOpen_compl.mem_nhds hp, fun g hg hgc hgN => ?_⟩
      have h0 : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) = 0 := by
        refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
        rw [finsum_eq_dif]
        by_cases hWm : W ∈ S
        · rw [dite_eq_left hWm, varInt_eq_zero_of_vanish W g φ fun x hx =>
            image_eq_zero_of_notMem_tsupport fun hxs =>
              hgN hxs ⟨(hW W hWm).2.1 hx, (hW W hWm).2.2 x hx⟩, mul_zero]
        · rw [dite_eq_right hWm]
      simp only [h0]
      exact hOff n d J u g φ hJ hdim hu hg hgc hφ (Set.disjoint_left.2 fun x hx hx' => hgN hx hx')

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHess
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem tubeWeight_nonneg {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : 0 ≤ tubeWeight Q y := by
  unfold tubeWeight
  split_ifs <;> positivity

theorem LogLogCutHess.proof (hC : HessCCompPluri.Statement) : LogLogCutHess.Statement := by
  obtain ⟨K, hK0, hK⟩ := logLogStep_deriv2_bound
  refine ⟨K, hK0, fun m Q k y => ?_⟩
  have hc : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hnn : 0 ≤ K / ((k : ℝ) + 1) * tubeWeight Q y :=
    mul_nonneg (div_nonneg hK0 (by linarith)) (tubeWeight_nonneg Q y)
  have hconst : ∀ c : ℝ, logLogCut Q k =ᶠ[𝓝 y] (fun _ => c) → ∃ a b : ℝ,
      |a| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ |b| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧
      hessC (logLogCut Q k) y = (a : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y ∧
      hessC (fun z => logLogCut Q k z ^ 2 / 2) y = (b : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y := by
    intro c hev
    obtain ⟨e1, e2⟩ := hessC_of_eventually_const hev
    exact ⟨0, 0, by simpa using hnn, by simpa using hnn, by simp [e1], by simp [e2]⟩
  by_cases h1 : ‖eval y Q‖ ^ 2 < cutLevel k
  · exact hconst 0 (logLogCut_eventually_zero Q k h1)
  by_cases h2 : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2
  · exact hconst 1 (logLogCut_eventually_one Q k h2)
  have hw0 : 0 < ‖eval y Q‖ ^ 2 := lt_of_lt_of_le (cutLevel_mem k).1 (not_lt.1 h1)
  have hw1 : ‖eval y Q‖ ^ 2 < 1 :=
    lt_of_le_of_lt (not_lt.1 h2) (Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _)))
  have hLy : logAbsSq Q y ≤ -1 := by
    have e1 : logAbsSq Q y ≤ -Real.exp (((k : ℝ) + 1) / 2) := (Real.log_le_iff_le_exp hw0).2 (not_lt.1 h2)
    have e2 : 1 ≤ Real.exp (((k : ℝ) + 1) / 2) := Real.one_le_exp (by positivity)
    linarith
  have htw : tubeWeight Q y = (logAbsSq Q y ^ 2)⁻¹ := if_pos hLy
  have hg : AnalyticAt ℂ (fun z => eval z Q) y := AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)
  have hgy : eval y Q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw0
    norm_num at hw0
  have hLcd : ContDiffAt ℝ 2 (logAbsSq Q) y :=
    (((contDiff_norm_sq ℝ).contDiffAt).comp y (hg.contDiffAt.restrict_scalars ℝ)).log hw0.ne'
  have hlcd : ContDiffAt ℝ 2 (fun z => Real.log ‖eval z Q‖) y :=
    ((contDiffAt_norm ℝ hgy).comp y (hg.contDiffAt.restrict_scalars ℝ)).log (norm_ne_zero_iff.2 hgy)
  have hLpl : hessC (logAbsSq Q) y = 0 := by
    have e : logAbsSq Q = fun z => Real.log ‖eval z Q‖ + Real.log ‖eval z Q‖ := by
      funext z
      rw [logAbsSq, Real.log_pow]
      push_cast
      ring
    rw [e]
    exact (hessC_add_log_norm _ (fun z => eval z Q) y hlcd hg hgy).trans (hessC_log_norm _ y hg hgy)
  obtain ⟨hFcd, hHcd, hF2, hH2⟩ := hK ((k : ℝ) + 1) hc (logAbsSq Q y) (by linarith)
  have hev := logLogCut_eventually_step Q k hw0 hw1
  have hevsq : (fun z => logLogCut Q k z ^ 2 / 2) =ᶠ[𝓝 y]
      fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) ^ 2 / 2 := by
    filter_upwards [hev] with z hz
    rw [hz]
  have eF := hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1))) (logAbsSq Q) y hFcd hLcd hLpl
  have eH := hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1)) ^ 2 / 2) (logAbsSq Q) y hHcd hLcd hLpl
  rw [← hessC_congr' hev] at eF
  rw [← hessC_congr' hevsq] at eH
  refine ⟨_, _, ?_, ?_, eF, eH⟩
  · rw [htw, ← div_eq_mul_inv, div_div]; exact hF2
  · rw [htw, ← div_eq_mul_inv, div_div]; exact hH2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLeibniz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace MaDensLeibniz

variable {D : ℕ}

theorem exists_open_contDiffOn (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ z ∈ U ∧ ContDiffOn ℝ 2 f U ∧ ContDiffOn ℝ 2 g U := by
  obtain ⟨U, hP, hU, hzU⟩ :=
    eventually_nhds_iff.mp ((hf.eventually (by simp)).and (hg.eventually (by simp)))
  exact ⟨U, hU, hzU, fun y hy => (hP y hy).1.contDiffWithinAt,
    fun y hy => (hP y hy).2.contDiffWithinAt⟩

theorem contDiffAt_cplx {f : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ContDiffAt ℝ 2 (cplx f) z := by
  have h : cplx f = fun y => Complex.ofRealCLM (f y) := by funext y; simp [cplx]
  rw [h]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hf

theorem dzb_cplx_mul (k : Fin D) (f g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx fun x => f x * g x) y = cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
  rw [dzb_cplx_eq_star, dz_cplx_mul k f g y hf hg, dzb_cplx_eq_star, dzb_cplx_eq_star]
  simp [cplx, star_add]

theorem dzb_cplx_sq_half (k : Fin D) (f : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) :
    dzb k (cplx fun x => f x ^ 2 / 2) y = cplx f y * dzb k (cplx f) y := by
  rw [dzb_cplx, dzb_cplx, fderiv_sq_half f y hf]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, cplx]
  push_cast
  ring

theorem hessC_mul (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (fun y => f y * g y) z =
      (f z : ℂ) • hessC g z + (g z : ℂ) • hessC f z + gradMat f g z + gradMat g f z := by
  obtain ⟨U, hU, hzU, hfU, hgU⟩ := exists_open_contDiffOn f g z hf hg
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hfU.mul hgU) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k,
    hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx fun y => f y * g y) =ᶠ[𝓝 z]
      fun y => cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_mul k f g y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hG := (contDiffAt_cplx hg).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  have hG' := differentiableAt_dzb (j := k) (contDiffAt_cplx hg)
  rw [dz_congr hev, dz_add (hF.fun_mul hG') (hG.fun_mul hF'), dz_mul hF hG', dz_mul hG hF']
  simp only [gradMat, cplx]
  ring

theorem hessC_sq_half (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z) :
    hessC (fun y => f y ^ 2 / 2) z = (f z : ℂ) • hessC f z + gradMat f f z := by
  obtain ⟨U, hU, hzU, hfU, -⟩ := exists_open_contDiffOn f f z hf hf
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU ((hfU.pow 2).div_const 2) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k]
  have hev : dzb k (cplx fun y => f y ^ 2 / 2) =ᶠ[𝓝 z] fun y => cplx f y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_sq_half k f y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  rw [dz_congr hev, dz_mul hF hF']
  simp only [gradMat, cplx]
  ring

theorem mdisc_cons_add {n : ℕ} (A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (A + A') B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
        mdisc (Fin.cons A' B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  simpa using mdisc_cons_smul_add 1 1 A A' B

theorem proof : MaDensLeibniz.Statement := by
  intro D φ f g z hf hg
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, maDens_cons_eq, hessC_mul f g z hf hg]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_add, mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_sq_half f z hf]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_smul_fst]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring

end MaDensLeibniz

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeEuclMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

theorem TubeEuclMass.proof (hC : TubeCollarMass.Statement) (hD : TubeDeepMass.Statement) :
    TubeEuclMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hS : {y : Fin (d + 1) → ℂ | logAbsSq P y < -Real.exp 1} =
      {y | -Real.exp 1 ≤ logAbsSq P y}ᶜ := by
    ext y
    simp [not_le]
  have h := (hC n d J A P R hJ hdim hA hP).add (hD n d J A P R hJ hdim hA hP)
  rw [hS, Set.indicator_self_add_compl] at h
  exact h

end

end GroundTheory.Heights₂.Heights
end

