module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace SheetSumMeasurable

variable {n d : ℕ}

theorem measurable_maDens {D : ℕ} (ψ : Fin D → (Fin D → ℂ) → ℝ) :
    Measurable (ReciprocityTheory.AnForm.maDens ψ) := by
  set_option synthInstance.maxHeartbeats 200000 in
  set M : ((Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) → Matrix (Fin D) (Fin D) ℂ := fun H i j =>
    ((H (Pi.single i 1) (Pi.single j 1) +
        H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
      Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1) -
        H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4 with hMdef
  have hM : Continuous M := continuous_pi fun i => continuous_pi fun j => by
    simp only [hMdef]
    fun_prop
  have hdisc : Continuous fun B : Fin D → Matrix (Fin D) (Fin D) ℂ =>
      (ReciprocityTheory.AnForm.mdisc B).re := by
    unfold ReciprocityTheory.AnForm.mdisc
    exact Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun S _ =>
      continuous_const.mul (Continuous.matrix_det (continuous_finsetSum _ fun k _ =>
        continuous_apply k))))
  have heq : ReciprocityTheory.AnForm.maDens ψ = fun z => (D.factorial : ℝ) * (2 / Real.pi) ^ D *
      (ReciprocityTheory.AnForm.mdisc fun k => M (fderiv ℝ (fderiv ℝ (ψ k)) z)).re := rfl
  rw [heq]
  exact measurable_const.mul ((hdisc.comp (continuous_pi fun k => hM.comp (continuous_apply k))).measurable.comp
    (Measurable.of_eval fun k => measurable_fderiv ℝ _))

theorem sheet_eventuallyEq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s s' : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (hs' : IsSheetAt J A x s') : s' =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨U, hU, hxU, -, -, -, V, hV, hVs⟩ := hs
  obtain ⟨U', hU', hxU', hsd', hsx', hsec', -⟩ := hs'
  have hcont : ContinuousAt s' (A *ᵥ x) := hsd'.continuousOn.continuousAt (hU'.mem_nhds hxU')
  have h1 : ∀ᶠ w in 𝓝 (A *ᵥ x), s' w ∈ V := hcont.preimage_mem_nhds (by rw [hsx']; exact hV)
  filter_upwards [h1, hU.mem_nhds hxU, hU'.mem_nhds hxU'] with w hwV hwU hwU'
  have h := hVs (s' w) ⟨(hsec' w hwU').2, hwV⟩ (by rw [(hsec' w hwU').1]; exact hwU)
  rw [(hsec' w hwU').1] at h
  exact h

theorem term_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) {x : Fin n → ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (h : ∃ s, IsSheetAt J A x s) :
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) =
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ x)) := by
  rw [IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k =>
    ((sheet_eventuallyEq hs h.choose_spec).fun_comp (φ k))]

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ ContinuousOn s U ∧ (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by
  by_cases hx : ∃ s, IsSheetAt J A x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    refine ⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU,
      isOpen_interior.inter (hU.preimage hAc), hsd.continuousOn, hsec, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'U⟩
    have hx's : s (A *ᵥ x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, continuousOn_empty _, by simp,
      by simp, fun h => absurd h hx⟩

theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by
    ext x
    simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const


open Classical in
theorem measurable_sheetSum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) (Φ : ℝ → ℝ → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    {g : (Fin n → ℂ) → ℝ} (hg : Measurable g) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    Measurable fun y => sheetSum J A
      (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y := by
  choose σ U W hU hW hσc hσsec hWsh hxW using
    fun x : Fin n → ℂ => exists_sheet_nhds (J := J) (A := A) x

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ W (e k) := by
    intro x hx
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hx⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact ⟨k, hxi⟩

  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hW (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ zeroSet J ∩ W (e k) := fun k x hx =>
    ⟨hx.1, disjointed_subset (fun k => W (e k)) k hx.2⟩
  have hEdisj : ∀ k k' x, x ∈ E k → x ∈ E k' → k = k' := by
    intro k k' x hk hk'
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_disjointed (fun k => W (e k)) hne) hk.2 hk'.2
  have hEcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ E k := by
    intro x hx
    obtain ⟨m, hm⟩ := hcover x hx
    have hxZ : x ∈ zeroSet J := by
      obtain ⟨s, U₀, -, hxU₀, -, hsx, hsec, -⟩ := hx
      rw [← hsx]
      exact (hsec _ hxU₀).2
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  set t : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, IsSheetAt J A x s then
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) else 0 with ht
  have htdef : ∀ x, t x = if h : ∃ s, IsSheetAt J A x s then
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) else 0 := fun x => rfl
  have htE : ∀ k x, x ∈ E k →
      t x = Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k' => φ k' ∘ σ (e k)) (A *ᵥ x)) := by
    intro k x hx
    have hsh := (hWsh (e k) x (hEW k hx)).2
    rw [htdef, dite_eq_left ⟨_, hsh⟩]
    exact term_eq Φ g φ hsh _
  have htS : ∀ x, t x ≠ 0 → ∃ s, IsSheetAt J A x s := by
    intro x hx
    by_contra h
    exact hx (by rw [htdef, dite_eq_right h])

  set σ' : ℕ → (Fin d → ℂ) → Fin n → ℂ := fun k => (U (e k)).piecewise (σ (e k)) fun _ => 0
    with hσ'
  set f : ℕ → (Fin d → ℂ) → ℝ := fun k => (U (e k) ∩ σ' k ⁻¹' E k).indicator
    (fun y => Φ (g (σ' k y)) (ReciprocityTheory.AnForm.maDens (fun k' => φ k' ∘ σ (e k)) y)) with hf
  have hσ'm : ∀ k, Measurable (σ' k) := fun k =>
    (hσc (e k)).measurable_piecewise continuousOn_const (hU (e k)).measurableSet
  have hfm : ∀ k, Measurable (f k) := fun k =>
    (hΦ.comp ((hg.comp (hσ'm k)).prodMk (measurable_maDens _))).indicator
      ((hU (e k)).measurableSet.inter (hσ'm k (hEm k)))

  have hpiece : ∀ (k : ℕ) (y : Fin d → ℂ) (F : Finset (Fin n → ℂ)),
      (∀ x, x ∈ F ↔ x ∈ fibre J A y) → ∑ x ∈ F, (E k).indicator t x = f k y := by
    intro k y F hF
    by_cases hy : y ∈ U (e k) ∧ σ (e k) y ∈ E k
    · have hσ'y : σ' k y = σ (e k) y := by simp [hσ', Set.piecewise_eq_of_mem _ _ _ hy.1]
      have hx0 : σ (e k) y ∈ F :=
        (hF _).2 ⟨(hEW k hy.2).1, (hσsec (e k) y hy.1).1⟩
      rw [Finset.sum_eq_single_of_mem _ hx0, Set.indicator_of_mem hy.2, htE k _ hy.2,
        (hσsec (e k) y hy.1).1, hf]
      · simp only
        rw [Set.indicator_of_mem (show y ∈ U (e k) ∩ σ' k ⁻¹' E k from
          ⟨hy.1, by simp only [Set.mem_preimage, hσ'y]; exact hy.2⟩), hσ'y]
      · intro x hxF hne
        refine Set.indicator_of_notMem (fun hxE => hne ?_) _
        obtain ⟨-, hAx⟩ := (hF x).1 hxF
        obtain ⟨-, hsh⟩ := hWsh (e k) x (hEW k hxE)
        obtain ⟨-, -, -, -, hsx, -⟩ := hsh
        rw [← hsx, hAx]
    · have hfy : f k y = 0 := by
        rw [hf]
        refine Set.indicator_of_notMem (fun (hmem : y ∈ U (e k) ∩ σ' k ⁻¹' E k) => hy ⟨hmem.1, ?_⟩) _
        have hσ'y : σ' k y = σ (e k) y := by simp [hσ', Set.piecewise_eq_of_mem _ _ _ hmem.1]
        have := hmem.2
        simp only [Set.mem_preimage, hσ'y] at this
        exact this
      rw [hfy]
      refine Finset.sum_eq_zero fun x hxF => Set.indicator_of_notMem (fun hxE => hy ?_) _
      obtain ⟨-, hAx⟩ := (hF x).1 hxF
      obtain ⟨hAU, hsh⟩ := hWsh (e k) x (hEW k hxE)
      obtain ⟨-, -, -, -, hsx, -⟩ := hsh
      rw [hAx] at hAU hsx
      exact ⟨hAU, hsx ▸ hxE⟩

  refine measurable_of_tendsto_metrizable (f := fun N y => ∑ k ∈ Finset.range N, f k y)
    (fun N => Finset.measurable_sum _ fun k _ => hfm k) (tendsto_pi_nhds.2 fun y => ?_)
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  have hsum : sheetSum J A (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y =
      ∑ x ∈ hfin.toFinset, t x := by
    unfold sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    rw [htdef, hx.2]
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ x ∈ hfin.toFinset, ∀ᶠ N in atTop,
      t x = ∑ k ∈ Finset.range N, (E k).indicator t x := by
    intro x _
    by_cases hx : ∃ s, IsSheetAt J A x s
    · obtain ⟨k0, hk0⟩ := hEcover x hx
      filter_upwards [eventually_gt_atTop k0] with N hN
      rw [Finset.sum_eq_single_of_mem k0 (Finset.mem_range.2 hN), Set.indicator_of_mem hk0]
      intro k _ hk
      exact Set.indicator_of_notMem (fun hxk => hk (hEdisj k k0 x hxk hk0)) _
    · have htx : t x = 0 := by rw [htdef, dite_eq_right hx]
      refine Eventually.of_forall fun N => ?_
      rw [htx]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      by_cases hxk : x ∈ E k
      · rw [Set.indicator_of_mem hxk]; exact htx
      · exact Set.indicator_of_notMem hxk _
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => hpiece k y _ fun x => Set.Finite.mem_toFinset hfin

end SheetSumMeasurable

theorem SheetSumMeasurable.proof : SheetSumMeasurable.Statement := by
  intro n d J A g φ _ _ hA hg _
  refine ⟨SheetSumMeasurable.measurable_sheetSum hA (fun a b => a * b)
    (continuous_fst.mul continuous_snd).measurable hg φ,
    SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
      (continuous_fst.mul continuous_snd).abs.measurable hg φ⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeierstrassPolynomialDivision
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

namespace WeierstrassPolynomialDivision

theorem circleIntegral_finset_sum {ι : Type} (u : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ i ∈ u, ContinuousOn (f i) (sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ u, f i z) = ∑ i ∈ u, ∮ z in C(c, R), f i z := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a u ha ih =>
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add ((hf a (by simp)).circleIntegrable hR)
      ((continuousOn_finsetSum u fun i hi => hf i (by simp [hi])).circleIntegrable hR),
      ih fun i hi => hf i (by simp [hi])]

theorem pointWithLast_eta {σ : Type} (x : Option σ → ℂ) : pointWithLast (fun i => x (some i)) (x none) = x := by
  funext o
  cases o <;> rfl

theorem differentiable_pointWithLast {σ : Type} [Fintype σ] :
    Differentiable ℂ (fun p : (σ → ℂ) × ℂ => pointWithLast p.1 p.2) := by
  rw [differentiable_pi]
  intro o
  cases o with
  | none => exact differentiable_snd
  | some i =>
    show Differentiable ℂ fun p : (σ → ℂ) × ℂ => p.1 i
    fun_prop

theorem norm_pointWithLast_lt {σ : Type} [Fintype σ] {z : σ → ℂ} {s : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : ‖z‖ < ε)
    (hs : ‖s‖ < ε) : ‖pointWithLast z s‖ < ε := by
  rw [pi_norm_lt_iff hε]
  intro o
  cases o with
  | none => exact hs
  | some i => exact (norm_le_pi_norm z i).trans_lt hz

end WeierstrassPolynomialDivision


open WeierstrassPolynomialDivision in
theorem WeierstrassPolynomialDivision.proof (hC : ParametricCircleIntegralAnalytic.Statement) :
    WeierstrassPolynomialDivision.Statement := by
  intro σ _ d c g hc hc0 hg
  obtain ⟨εg, hεg, hgan⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨εc, hεc, hcan⟩ := Metric.eventually_nhds_iff_ball.1
    (Filter.eventually_all.2 fun j => (hc j).eventually_analyticAt)
  set ε := min εg εc with hε_def
  have hε : 0 < ε := lt_min hεg hεc
  set r := ε / 2 with hr_def
  have hr : 0 < r := half_pos hε
  have hrε : r < ε := half_lt_self hε

  let G : (σ → ℂ) × ℂ → ℂ := fun p => g (pointWithLast p.1 p.2)
  let F : (σ → ℂ) × ℂ → ℂ := fun p => weierstrassPolynomial c (pointWithLast p.1 p.2)
  let A : Set ((σ → ℂ) × ℂ) := ball 0 ε ×ˢ ball 0 ε
  have hcd : ∀ z ∈ ball (0 : σ → ℂ) ε, ∀ j, DifferentiableAt ℂ (c j) z := fun z hz j =>
    (hcan z (mem_ball_zero_iff.2 ((mem_ball_zero_iff.1 hz).trans_le (min_le_right _ _))) j).differentiableAt
  have hGd : ∀ p ∈ A, DifferentiableAt ℂ G p := by
    intro p hp
    have hp' : pointWithLast p.1 p.2 ∈ ball (0 : Option σ → ℂ) εg := mem_ball_zero_iff.2
      (norm_pointWithLast_lt hεg ((mem_ball_zero_iff.1 hp.1).trans_le (min_le_left _ _))
        ((mem_ball_zero_iff.1 hp.2).trans_le (min_le_left _ _)))
    exact (hgan _ hp').differentiableAt.comp p (differentiable_pointWithLast p)
  have hFd : ∀ p ∈ A, DifferentiableAt ℂ F p := by
    intro p hp
    show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ d + ∑ j : Fin d, c j p.1 * p.2 ^ (j : ℕ)) p
    exact (differentiableAt_snd.pow d).add (DifferentiableAt.fun_sum fun j _ =>
      ((hcd p.1 hp.1 j).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))

  have hFne : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ∀ s ∈ sphere (0 : ℂ) r, F (z, s) ≠ 0 := by
    refine (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun s hs => ?_
    have hsn : ‖s‖ = r := mem_sphere_zero_iff_norm.1 hs
    have hA : ((0 : σ → ℂ), s) ∈ A := ⟨mem_ball_self hε, mem_ball_zero_iff.2 (hsn ▸ hrε)⟩
    have h0 : F (0, s) ≠ 0 := by
      show weierstrassPolynomial c (pointWithLast 0 s) ≠ 0
      rw [weierstrassPolynomial_pointWithLast_zero c hc0]
      exact pow_ne_zero _ (norm_ne_zero_iff.1 (hsn ▸ hr.ne'))
    exact (hFd _ hA).continuousAt.eventually_ne h0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff_ball.1 (hFne.and (ball_mem_nhds (0 : σ → ℂ) hε))

  let O₀ : Set ((σ → ℂ) × ℂ) := A ∩ F ⁻¹' {0}ᶜ
  have hO₀ : IsOpen O₀ := ContinuousOn.isOpen_inter_preimage
    (fun p hp => (hFd p hp).continuousAt.continuousWithinAt) (isOpen_ball.prod isOpen_ball) isOpen_compl_singleton
  have hmem₀ : ∀ z ∈ ball (0 : σ → ℂ) δ, ∀ s ∈ sphere (0 : ℂ) r, (z, s) ∈ O₀ := fun z hz s hs =>
    ⟨⟨(hδF z hz).2, mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hs).trans_lt hrε)⟩, (hδF z hz).1 s hs⟩

  let μ : (Option σ → ℂ) × ℂ → (σ → ℂ) × ℂ := fun p => ((fun i => p.1 (some i)), p.2)
  have hμ : Differentiable ℂ μ :=
    (differentiable_pi.2 fun i => by fun_prop).prodMk differentiable_snd
  let Φq : (Option σ → ℂ) × ℂ → ℂ := fun p => G (μ p) / (F (μ p) * (p.2 - p.1 none))
  let Oq : Set ((Option σ → ℂ) × ℂ) := μ ⁻¹' O₀ ∩ {p | p.2 - p.1 none ≠ 0}
  have hOq : IsOpen Oq := (hO₀.preimage hμ.continuous).inter (isOpen_ne_fun (by fun_prop) continuous_const)
  let Uq : Set (Option σ → ℂ) :=
    (fun x : Option σ → ℂ => fun i => x (some i)) ⁻¹' ball (0 : σ → ℂ) δ ∩ (fun x : Option σ → ℂ => x none) ⁻¹' ball (0 : ℂ) r
  have hUq : IsOpen Uq :=
    (isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage (continuous_apply none))
  have hΦq : DifferentiableOn ℂ Φq Oq := by
    rintro p ⟨⟨hA, hF⟩, hne⟩
    have hden : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => F (μ p) * (p.2 - p.1 none)) p :=
      ((hFd _ hA).comp p (hμ p)).mul (differentiableAt_snd.sub
        (by fun_prop : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => p.1 none) p))
    rw [show Φq = fun p => G (μ p) * (F (μ p) * (p.2 - p.1 none))⁻¹ from funext fun _ => div_eq_mul_inv _ _]
    exact (((hGd _ hA).comp p (hμ p)).mul (hden.inv (mul_ne_zero hF hne))).differentiableWithinAt
  have hmemq : ∀ x ∈ Uq, ∀ s ∈ sphere (0 : ℂ) r, (x, s) ∈ Oq := by
    intro x hx s hs
    refine ⟨hmem₀ _ hx.1 s hs, ?_⟩
    show s - x none ≠ 0
    intro h
    have h1 := mem_sphere_zero_iff_norm.1 hs
    have h2 := mem_ball_zero_iff.1 hx.2
    rw [sub_eq_zero.1 h] at h1
    linarith
  have h0q : (0 : Option σ → ℂ) ∈ Uq := ⟨by exact Set.mem_preimage.mpr (mem_ball_self hδ), by exact Set.mem_preimage.mpr (mem_ball_self hr)⟩
  have hqan := hC (Option σ) Φq Oq Uq 0 r hr.le hOq hUq hΦq hmemq

  let Φa : Fin d → (σ → ℂ) × ℂ → ℂ := fun j p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j / F p
  have hΦa : ∀ j, DifferentiableOn ℂ (Φa j) O₀ := by
    intro j p hp
    have hP : DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => monicDifferenceCoeff (fun k => c k p.1) p.2 j) p := by
      show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ (d - 1 - (j : ℕ)) +
        ∑ k ∈ Finset.univ.filter (fun k : Fin d => (j : ℕ) < k), c k p.1 * p.2 ^ ((k : ℕ) - 1 - j)) p
      exact (differentiableAt_snd.pow _).add (DifferentiableAt.fun_sum fun k _ =>
        ((hcd p.1 hp.1.1 k).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))
    rw [show Φa j = fun p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j * (F p)⁻¹ from
      funext fun _ => div_eq_mul_inv _ _]
    exact (((hGd p hp.1).mul hP).mul ((hFd p hp.1).inv hp.2)).differentiableWithinAt
  have haan := fun j => hC σ (Φa j) O₀ (ball 0 δ) 0 r hr.le hO₀ isOpen_ball (hΦa j) hmem₀
  refine ⟨fun x => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φq (x, s),
    fun j z => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φa j (z, s),
    analyticAt_const.mul (hqan 0 h0q), fun j => analyticAt_const.mul (haan j 0 (mem_ball_self hδ)), ?_⟩
  filter_upwards [hUq.mem_nhds h0q] with x hx
  set z : σ → ℂ := fun i => x (some i) with hz
  set t : ℂ := x none with ht
  have hgx : g x = G (z, t) := congrArg g (pointWithLast_eta x).symm

  have hcau : (2 * π * I)⁻¹ • (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) = G (z, t) := by
    refine DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (f := fun s => G (z, s)) ?_ hx.2
    refine DifferentiableOn.diffContOnCl_ball (U := ball 0 ε) (fun s hs => ?_) (closedBall_subset_ball hrε)
    exact ((hGd (z, s) ⟨(hδF z hx.1).2, hs⟩).comp s
      ((differentiableAt_const z).prodMk differentiableAt_id)).differentiableWithinAt

  have hpt : Set.EqOn (fun s => (s - t)⁻¹ • G (z, s))
      (fun s => weierstrassPolynomial c x * Φq (x, s) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s))
      (sphere (0 : ℂ) r) := by
    intro s hs
    have hFs : F (z, s) ≠ 0 := (hδF z hx.1).1 s hs
    have hst : s - t ≠ 0 := (hmemq x hx s hs).2
    have key : F (z, s) - weierstrassPolynomial c x =
        (s - t) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) :=
      monic_sub_eq_mul_sum (fun k => c k z) s t
    have hsum : ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s) =
        G (z, s) / F (z, s) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show t ^ (j : ℕ) * (G (z, s) * monicDifferenceCoeff (fun k => c k z) s j / F (z, s)) = _
      ring
    have hP : ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) =
        (F (z, s) - weierstrassPolynomial c x) / (s - t) := by
      rw [key]
      field_simp
    show (s - t)⁻¹ • G (z, s) =
      weierstrassPolynomial c x * (G (z, s) / (F (z, s) * (s - t))) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)
    rw [hsum, hP, smul_eq_mul]
    field_simp
    ring
  have hcq : ContinuousOn (fun s => Φq (x, s)) (sphere (0 : ℂ) r) :=
    hΦq.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmemq x hx s hs
  have hca : ∀ j ∈ (Finset.univ : Finset (Fin d)), ContinuousOn (fun s => t ^ (j : ℕ) * Φa j (z, s))
      (sphere (0 : ℂ) r) := fun j _ => continuousOn_const.mul
    ((hΦa j).continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmem₀ z hx.1 s hs)
  have hint : (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) =
      weierstrassPolynomial c x * (∮ s in C(0, r), Φq (x, s)) +
        ∑ j : Fin d, t ^ (j : ℕ) * ∮ s in C(0, r), Φa j (z, s) := by
    have hi1 : CircleIntegrable (fun s => weierstrassPolynomial c x * Φq (x, s)) 0 r :=
      (continuousOn_const.mul hcq).circleIntegrable hr.le
    have hi2 : CircleIntegrable (fun s => ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)) 0 r :=
      (continuousOn_finsetSum _ hca).circleIntegrable hr.le
    rw [circleIntegral.integral_congr hr.le hpt, circleIntegral.integral_add hi1 hi2,
      circleIntegral.integral_const_mul, circleIntegral_finset_sum _ _ hr.le hca]
    congr 1
    exact Finset.sum_congr rfl fun j _ => circleIntegral.integral_const_mul _ _ _ _
  rw [hgx, ← hcau, smul_eq_mul, hint, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveMinimalPrimeQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def CurveMinimalPrimeQuotient.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (p : Ideal (curveLocalRing I q)),
    p ∈ minimalPrimes (curveLocalRing I q) →
      ∃ J : Ideal (MvPolynomial (Fin n) ℂ), J ∈ I.minimalPrimes ∧ J ≤ RingHom.ker (eval q) ∧
        ∃ φ : curveLocalRing I q →+* curveLocalRing J q, Function.Surjective φ ∧ RingHom.ker φ = p ∧
          ∀ f : MvPolynomial (Fin n) ℂ, φ (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) =
            algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveProperClosedFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveProperClosedFinite.Statement : Prop :=
  ∀ (n : ℕ) (W K : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 → ¬ K ≤ W →
      (zeroSet W ∩ zeroSet K).Finite

end

end GroundTheory.Heights₂.Heights
end

