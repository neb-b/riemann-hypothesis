module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnbranchedProperCountLocallyConstant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set

theorem UnbranchedProperCountLocallyConstant.proof : UnbranchedProperCountLocallyConstant.Statement := by
  intro σ _ Y d A D δ hD _ hprop hchart y hyD hδy
  choose! O V g hO hV hxV hg hsec hYV using hchart

  have key : ∀ x ∈ Y, δ (A x) ≠ 0 → ∀ z ∈ Y, z ∈ V x → A z ∈ O x ∧ g x (A z) = z := by
    intro x hx hδ z hz hzV
    obtain ⟨w, hw, rfl⟩ : z ∈ g x '' O x := hYV x hx hδ ▸ ⟨hz, hzV⟩
    rw [hsec x hx hδ w hw]; exact ⟨hw, rfl⟩
  set F := {x | x ∈ Y ∧ A x = y} with hFdef
  have hFδ : ∀ x ∈ F, δ (A x) ≠ 0 := fun x hx => hx.2 ▸ hδy
  have hyO : ∀ x ∈ F, y ∈ O x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).1
  have hgy : ∀ x ∈ F, g x y = x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).2

  have hFc : IsCompact F := by
    simpa [hFdef] using hprop {y} (singleton_subset_iff.2 hyD) isCompact_singleton
  have hFfin : F.Finite := by
    obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover V
      (fun x hx => (hV x hx.1 (hFδ x hx)).mem_nhds (hxV x hx.1 (hFδ x hx)))
    refine t.finite_toSet.subset fun z hz => ?_
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov hz)
    have hx := htF x hxt
    have := (key x hx.1 (hFδ x hx) z hz.1 hzx).2
    rw [hz.2, hgy x hx] at this
    exact this ▸ hxt
  refine ⟨hFfin, ?_⟩

  have hev1 : ∀ᶠ y' in 𝓝 y, ∀ x ∈ F, y' ∈ O x :=
    (eventually_all_finite hFfin).2 fun x hx => (hO x hx.1 (hFδ x hx)).mem_nhds (hyO x hx)

  have hev2 : ∀ᶠ y' in 𝓝 y, ∀ p ∈ F ×ˢ F, p.1 ≠ p.2 → g p.1 y' ≠ g p.2 y' := by
    refine (eventually_all_finite (hFfin.prod hFfin)).2 fun p hp => ?_
    by_cases hne : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hne h
    have c1 := ((hg p.1 hp.1.1 (hFδ _ hp.1)).continuousAt ((hO _ hp.1.1 (hFδ _ hp.1)).mem_nhds (hyO _ hp.1)))
    have c2 := ((hg p.2 hp.2.1 (hFδ _ hp.2)).continuousAt ((hO _ hp.2.1 (hFδ _ hp.2)).mem_nhds (hyO _ hp.2)))
    have hne' : g p.1 y ≠ g p.2 y := by rwa [hgy _ hp.1, hgy _ hp.2]
    exact ((c1.tendsto.prodMk_nhds c2.tendsto).eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds hne')).mono fun _ h _ => h

  have hev3 : ∀ᶠ y' in 𝓝 y, ∀ z ∈ Y, A z = y' → ∃ x ∈ F, z ∈ V x := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD y hyD
    set K := Metric.closedBall y (ε / 2)
    have hKD : K ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
    set W := ⋃ x ∈ F, V x
    have hW : IsOpen W := isOpen_biUnion fun x hx => hV x hx.1 (hFδ x hx)
    have hC : IsCompact ({z | z ∈ Y ∧ A z ∈ K} \ W) :=
      (hprop K hKD (isCompact_closedBall y _)).diff hW
    have hyn : y ∉ A '' ({z | z ∈ Y ∧ A z ∈ K} \ W) := by
      rintro ⟨z, ⟨⟨hzY, -⟩, hzW⟩, hzy⟩
      exact hzW (mem_iUnion₂.2 ⟨z, ⟨hzY, hzy⟩, hxV z hzY (hzy ▸ hδy)⟩)
    filter_upwards [Metric.closedBall_mem_nhds y (half_pos hε),
      (hC.image A.continuous).isClosed.isOpen_compl.mem_nhds hyn] with y' hy'K hy'C z hzY hzy
    by_contra hno
    exact hy'C ⟨z, ⟨⟨hzY, hzy ▸ hy'K⟩, fun h => hno (by simpa [W] using h)⟩, hzy⟩
  filter_upwards [hev1, hev2, hev3] with y' h1 h2 h3
  have himg : {x | x ∈ Y ∧ A x = y'} = (fun x => g x y') '' F := by
    ext z
    constructor
    · rintro ⟨hzY, hzy⟩
      obtain ⟨x, hx, hzx⟩ := h3 z hzY hzy
      exact ⟨x, hx, by simpa [hzy] using (key x hx.1 (hFδ x hx) z hzY hzx).2⟩
    · rintro ⟨x, hx, rfl⟩
      have hm : g x y' ∈ Y ∩ V x := hYV x hx.1 (hFδ x hx) ▸ mem_image_of_mem _ (h1 x hx)
      exact ⟨hm.1, hsec x hx.1 (hFδ x hx) y' (h1 x hx)⟩
  rw [himg]
  refine InjOn.encard_image fun a ha b hb hab => ?_
  by_contra hne
  exact h2 (a, b) ⟨ha, hb⟩ hne hab

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnitaryZariskiDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Matrix Complex

noncomputable section

namespace UnitaryZariskiDense

theorem eval_aeval_subst {σ τ : Type*} (F : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ)
    (x : τ → ℂ) : eval x (aeval F p) = eval (fun i => eval x (F i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

theorem polyEval_aeval_subst {σ : Type*} (F : σ → Polynomial ℂ) (p : MvPolynomial σ ℂ) (z : ℂ) :
    (aeval F p).eval z = eval (fun i => (F i).eval z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem unit_circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  intro hfin
  have hsub : Polynomial.nthRootsFinset (hfin.toFinset.card + 1) (1 : ℂ) ⊆ hfin.toFinset := by
    intro z hz
    rw [Polynomial.mem_nthRootsFinset (Nat.succ_pos _)] at hz
    rw [Set.Finite.mem_toFinset]
    exact Complex.norm_eq_one_of_pow_eq_one hz (Nat.succ_ne_zero _)
  have hc := Finset.card_le_card hsub
  rw [(Complex.isPrimitiveRoot_exp (hfin.toFinset.card + 1) (Nat.succ_ne_zero _)).card_nthRootsFinset]
    at hc
  omega

theorem conj_diagonal_mem {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ)
    {d : Fin n → ℂ} (hd : ∀ k, ‖d k‖ = 1) : V * diagonal d * star V ∈ unitaryGroup (Fin n) ℂ := by
  have hD : diagonal d ∈ unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext k
    simpa [Complex.mul_conj', hd k]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hV hD) (Unitary.star_mem hV)

end UnitaryZariskiDense


open UnitaryZariskiDense in
theorem UnitaryZariskiDense.proof : UnitaryZariskiDense.Statement := by
  intro n p hp
  by_contra hall
  push Not at hall
  apply hp

  have herm : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian →
      eval (fun ij : Fin n × Fin n => H ij.1 ij.2) p = 0 := by
    intro H hH
    have hspec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    set V : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hVdef
    have hV : V ∈ unitaryGroup (Fin n) ℂ := hH.eigenvectorUnitary.2
    have hentry : ∀ d : Fin n → ℂ,
        eval d (aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p) =
          eval (fun ij : Fin n × Fin n => (V * diagonal d * star V) ij.1 ij.2) p := by
      intro d
      rw [eval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      rw [Matrix.mul_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, eval_C, eval_X, Matrix.mul_diagonal]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hr : aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p = 0 :=
      funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unit_circle_infinite) fun d hd => by
        rw [hentry, map_zero]
        exact hall _ (conj_diagonal_mem hV fun k => hd k trivial)
    have h0 := hentry (RCLike.ofReal ∘ hH.eigenvalues)
    rw [hr, map_zero] at h0
    rw [h0]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    exact congrFun (congrFun hspec ij.1) ij.2

  have all : ∀ A : Matrix (Fin n) (Fin n) ℂ, eval (fun ij : Fin n × Fin n => A ij.1 ij.2) p = 0 := by
    intro A
    set g : Polynomial ℂ := aeval (fun ij : Fin n × Fin n =>
      Polynomial.C (A ij.1 ij.2) * (Polynomial.C (1 / 2) - Polynomial.C (I / 2) * Polynomial.X) +
        Polynomial.C (Aᴴ ij.1 ij.2) * (Polynomial.C (1 / 2) + Polynomial.C (I / 2) * Polynomial.X)) p
      with hgdef
    have hg : ∀ z : ℂ, g.eval z = eval (fun ij : Fin n × Fin n =>
        A ij.1 ij.2 * (1 / 2 - I / 2 * z) + Aᴴ ij.1 ij.2 * (1 / 2 + I / 2 * z)) p := by
      intro z
      rw [hgdef, polyEval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      simp
    have g0 : g = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
      rintro _ ⟨t, rfl⟩
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hg]
      have hstar : star (1 / 2 - I / 2 * (t : ℂ)) = 1 / 2 + I / 2 * (t : ℂ) := by
        apply Complex.ext <;> (simp; try ring)
      have hM : ((1 / 2 - I / 2 * (t : ℂ)) • A + (1 / 2 + I / 2 * (t : ℂ)) • Aᴴ).IsHermitian := by
        unfold IsHermitian
        rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_conjTranspose,
          hstar, ← hstar, star_star, add_comm]
      have h := herm _ hM
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
      rw [← h]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      ring
    have h := hg I
    rw [g0, Polynomial.eval_zero] at h
    rw [h]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    have h1 : (1 / 2 - I / 2 * I : ℂ) = 1 := by
      ring_nf
      rw [I_sq]
      norm_num
    have h2 : (1 / 2 + I / 2 * I : ℂ) = 0 := by
      ring_nf
      rw [I_sq]
      norm_num
    rw [h1, h2]
    ring

  exact MvPolynomial.funext fun x => by
    simpa using all (Matrix.of fun i j => x (i, j))

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeightedAreaFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set Filter Function Topology

open scoped ENNReal NNReal

noncomputable section

theorem WeightedAreaFormula.proof : WeightedAreaFormula.Statement := by
  intro E _ _ _ _ _ μ _ A f H hA hf hfin hint
  classical
  have hder : ∀ x ∈ A, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf x hx).differentiableAt (hA.mem_nhds hx)).hasFDerivAt
  set B : Set E := {x ∈ A | (fderiv ℝ f x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hBm : MeasurableSet B := by
    have hm : Measurable fun x => (fderiv ℝ f x).det :=
      ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ f)
    exact hA.measurableSet.inter (hm (measurableSet_singleton 0).compl)

  have hZ : μ (f '' {x ∈ A | (fderiv ℝ f x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hder x hx.1).hasFDerivWithinAt) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f)
      (fun x hx => (hder x hx.1).hasFDerivWithinAt) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, MeasurableSet (P n) := fun n => hBm.inter (htm n)
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (fderiv ℝ f x) (P n) x := fun n x hx =>
    (hder x (hPA n hx)).hasFDerivWithinAt
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (fderiv ℝ f y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, MeasurableSet (f '' P n) := fun n =>
    measurable_image_of_fderivWithin (hPm n) (hderP n) (hinj n)

  let g : ℕ → E → ℝ := fun n y => H (invFunOn f (P n) y)
  have hgP : ∀ n, ∀ x ∈ P n, g n (f x) = H x := fun n x hx =>
    congrArg H (hinj n (invFunOn_mem ⟨x, hx, rfl⟩) hx (invFunOn_eq ⟨x, hx, rfl⟩))
  let F : ℕ → E → ℝ := fun n => (f '' P n).indicator (g n)
  have hFint : ∀ n, Integrable (F n) μ := fun n =>
    (integrable_indicator_iff (himg n)).2
      ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ (hPm n) (hderP n) (hinj n)
        (g n)).2 ((hint.mono_set (hPA n)).congr_fun
          (fun x hx => by simp only [smul_eq_mul, hgP n x hx]) (hPm n)))
  have hFint_eq : ∀ n, ∫ y, F n y ∂μ = ∫ x in P n, |(fderiv ℝ f x).det| * H x ∂μ := fun n => by
    calc ∫ y, F n y ∂μ = ∫ y in f '' P n, g n y ∂μ := integral_indicator (himg n)
      _ = ∫ x in P n, |(fderiv ℝ f x).det| • g n (f x) ∂μ :=
        integral_image_eq_integral_abs_det_fderiv_smul μ (hPm n) (hderP n) (hinj n) (g n)
      _ = ∫ x in P n, |(fderiv ℝ f x).det| * H x ∂μ :=
        setIntegral_congr_fun (hPm n) fun x hx => by simp only [smul_eq_mul, hgP n x hx]
  have hFlint : ∀ n, ∫⁻ y, ‖F n y‖ₑ ∂μ = ∫⁻ x in P n, ‖|(fderiv ℝ f x).det| * H x‖ₑ ∂μ :=
    fun n => by
    calc ∫⁻ y, ‖F n y‖ₑ ∂μ = ∫⁻ y, (f '' P n).indicator (fun z => ‖g n z‖ₑ) y ∂μ :=
          lintegral_congr fun y => enorm_indicator_eq_indicator_enorm (g n) y
      _ = ∫⁻ y in f '' P n, ‖g n y‖ₑ ∂μ := lintegral_indicator (himg n) _
      _ = ∫⁻ x in P n, ENNReal.ofReal |(fderiv ℝ f x).det| * ‖g n (f x)‖ₑ ∂μ :=
        lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hPm n) (hderP n) (hinj n)
          (fun z => ‖g n z‖ₑ)
      _ = ∫⁻ x in P n, ‖|(fderiv ℝ f x).det| * H x‖ₑ ∂μ := by
        refine setLIntegral_congr_fun (hPm n) fun x hx => ?_
        simp only [hgP n x hx, enorm_mul, Real.enorm_eq_ofReal_abs, abs_abs]
  have hsumlint : ∑' n, ∫⁻ y, ‖F n y‖ₑ ∂μ ≠ ∞ := by
    simp_rw [hFlint]
    rw [← lintegral_iUnion hPm hPd, ← hBU]
    exact (lt_of_le_of_lt (lintegral_mono_set hBA) (hasFiniteIntegral_iff_enorm.1 hint.2)).ne

  have hinjT : ∀ y, InjOn (fun n => invFunOn f (P n) y) {n | y ∈ f '' P n} := by
    intro y m hm n hn hmn
    by_contra hne
    refine Set.disjoint_left.1 (hPd hne) (invFunOn_mem hm) ?_
    simp only at hmn
    rw [hmn]; exact invFunOn_mem hn
  have hT : ∀ y, {n | y ∈ f '' P n}.Finite := by
    intro y
    refine Set.Finite.of_finite_image ((hfin y).subset ?_) (hinjT y)
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨hPA n (invFunOn_mem hn), invFunOn_eq hn⟩
  have hsum : ∀ y, HasSum (fun n => F n y) (∑ n ∈ (hT y).toFinset, F n y) := fun y =>
    hasSum_sum_of_ne_finset_zero fun n hn =>
      show (f '' P n).indicator (g n) y = 0 from
        indicator_of_notMem (s := f '' P n) (fun h => hn ((hT y).mem_toFinset.2 h)) (g n)

  have hae : ∀ᵐ y ∂μ, ∑' n, F n y = ∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
    have hbij : BijOn (fun n => invFunOn f (P n) y) {n | y ∈ f '' P n}
        {x | x ∈ A ∧ f x = y} := by
      refine ⟨fun n hn => ⟨hPA n (invFunOn_mem hn), invFunOn_eq hn⟩, hinjT y, ?_⟩
      rintro x ⟨hxA, hxy⟩
      have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
      have hxP : x ∈ P n := ⟨hxB, hn⟩
      have hyn : y ∈ f '' P n := ⟨x, hxP, hxy⟩
      exact ⟨n, hyn, hinj n (invFunOn_mem hyn) hxP ((invFunOn_eq hyn).trans hxy.symm)⟩
    rw [(hsum y).tsum_eq]
    change _ = ∑ᶠ (x : E) (_ : x ∈ {x | x ∈ A ∧ f x = y}), H x
    rw [← finsum_mem_eq_of_bijOn _ hbij
      (f := fun n => H (invFunOn f (P n) y)) (fun n _ => rfl),
      finsum_mem_eq_finite_toFinset_sum _ (hT y)]
    exact Finset.sum_congr rfl fun n hn =>
      indicator_of_mem (s := f '' P n) ((hT y).mem_toFinset.1 hn) (g n)

  have hGm : AEStronglyMeasurable (fun y => ∑' n, F n y) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (integrable_finsetSum (Finset.range N) fun n _ => hFint n).1)
      (ae_of_all _ fun y => (hsum y).summable.hasSum.tendsto_sum_nat)
  have hGfin : HasFiniteIntegral (fun y => ∑' n, F n y) μ := by
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ y, ‖∑' n, F n y‖ₑ ∂μ ≤ ∫⁻ y, ∑' n, ‖F n y‖ₑ ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [(hsum y).tsum_eq]
          exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
      _ = ∑' n, ∫⁻ y, ‖F n y‖ₑ ∂μ := lintegral_tsum fun n => (hFint n).1.enorm
      _ < ∞ := hsumlint.lt_top

  have hIA : ∫ x in A, |(fderiv ℝ f x).det| * H x ∂μ =
      ∫ x in B, |(fderiv ℝ f x).det| * H x ∂μ :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA.measurableSet hBA fun x hx => by
      have h0 : (fderiv ℝ f x).det = 0 := by
        by_contra h; exact hx.2 ⟨hx.1, h⟩
      simp [h0]
  have hBint : IntegrableOn (fun x => |(fderiv ℝ f x).det| * H x) (⋃ n, P n) μ := by
    rw [← hBU]; exact hint.mono_set hBA
  refine ⟨Integrable.congr (⟨hGm, hGfin⟩ : Integrable (fun y => ∑' n, F n y) μ) hae, ?_⟩
  rw [← integral_congr_ae hae, integral_tsum (fun n => (hFint n).1) hsumlint, hIA, hBU]
  simp_rw [hFint_eq]
  exact (hasSum_integral_iUnion hPm hPd hBint).tsum_eq

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RegularLocus
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsRegularPointOf {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (x : σ → ℂ) : Prop :=
  x ∈ Y ∧ ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
    (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧
      (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O

def regLocus {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) : Set (σ → ℂ) :=
  {x | IsRegularPointOf Y x}

theorem regLocus_subset {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) : regLocus Y ⊆ Y :=
  fun _ hx => hx.1

theorem isRegularPointOf_regLocus {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {x : σ → ℂ}
    (hx : x ∈ regLocus Y) : IsRegularPointOf (regLocus Y) x := by
  have hx' : IsRegularPointOf Y x := hx
  obtain ⟨hxY, d, A, O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hx'
  refine ⟨hx, d, A, O, V, g, hO, hV, hxV, hg, hAg, ?_⟩
  rw [← hYV]
  ext z
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨regLocus_subset Y hz, hzV⟩
  · rintro ⟨hzY, hzV⟩
    exact ⟨⟨hzY, d, A, O, V, g, hO, hV, hzV, hg, hAg, hYV⟩, hzV⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscrAdjoin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def DiscrAdjoin.Statement : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (ℓ : L), IsIntegral R ℓ →
    IntermediateField.adjoin K {ℓ} = ⊤ →
      (minpoly R ℓ).natDegree = Module.finrank K L ∧ (minpoly R ℓ).discr ≠ 0 ∧
      ∀ z : L, IsIntegral R z → (minpoly R ℓ).discr • z ∈ Algebra.adjoin R {ℓ}

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDominantFibreBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def DominantFibreBound.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ),
    P.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ) →
    Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)) →
    ∃ (e : ℕ) (Δ : MvPolynomial (Fin d) ℂ), Δ ≠ 0 ∧ ∀ w : Fin d → ℂ, eval w Δ ≠ 0 →
      {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i}.encard ≤ e

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def NormalModelExists.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime → Nonempty (NormalModel J)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

