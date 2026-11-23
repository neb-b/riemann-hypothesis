module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianPhaseCriticalValueBlocksGeneral
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

private lemma dot_transpose_mulVec' {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) (u : n → ℂ) (v : m → ℂ) : u ⬝ᵥ Xᵀ *ᵥ v = v ⬝ᵥ X *ᵥ u := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

theorem gaussian_phase_critical_value_blocks_general {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (C : Matrix n m ℂ) (B : Matrix m n ℂ)
    (a c : m → ℂ) (b d : n → ℂ) (hN : IsUnit (1 - C * B).det) :
    (let S : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 Cᵀ C 0
     let T : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 B Bᵀ 0
     let w : m ⊕ n → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b)
     let u : m ⊕ n → ℂ := Sum.elim a b + S *ᵥ w
     1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u)
       = a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
         + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c) := by
  intro S T w u
  have hM : IsUnit (1 - B * C).det := by rwa [det_one_sub_mul_comm]
  set M := (1 - B * C)⁻¹ with hMdef
  set N := (1 - C * B)⁻¹ with hNdef
  have hM1 : M * (1 - B * C) = 1 := nonsing_inv_mul _ hM
  have hM2 : (1 - B * C) * M = 1 := mul_nonsing_inv _ hM
  have hN1 : N * (1 - C * B) = 1 := nonsing_inv_mul _ hN
  have hN2 : (1 - C * B) * N = 1 := mul_nonsing_inv _ hN
  have hMB : B * N = M * B := by
    have h : B * (1 - C * B) = (1 - B * C) * B := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    calc B * N = M * ((1 - B * C) * B) * N := by
          rw [← Matrix.mul_assoc, hM1, Matrix.one_mul]
      _ = M * B := by
          rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, hN2, Matrix.mul_one]
  have hCM : C * M = N * C := by
    have h : C * (1 - B * C) = (1 - C * B) * C := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    calc C * M = N * ((1 - C * B) * C) * M := by
          rw [← Matrix.mul_assoc, hN1, Matrix.one_mul]
      _ = N * C := by
          rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, hM2, Matrix.mul_one]
  have hMBC : B * (N * C) = M - 1 := by
    rw [← Matrix.mul_assoc, hMB, ← hM1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hNCB : N * C * B = N - 1 := by
    rw [← hN1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hinv : (1 - T * S)⁻¹ = fromBlocks M 0 0 Nᵀ := by
    apply inv_eq_left_inv
    have h1 : (1 - T * S) = fromBlocks (1 - B * C) 0 0 (1 - C * B)ᵀ := by
      simp only [T, S, fromBlocks_multiply, ← fromBlocks_one]
      ext (i | i) (j | j) <;> simp [transpose_mul, Matrix.one_apply, eq_comm]
    rw [h1, fromBlocks_multiply, ← transpose_mul, hM1, hN2]
    simp
  have hw : w = Sum.elim (M *ᵥ (c + B *ᵥ b)) (Nᵀ *ᵥ (d + Bᵀ *ᵥ a)) := by
    have h : Sum.elim c d + T *ᵥ Sum.elim a b = Sum.elim (c + B *ᵥ b) (d + Bᵀ *ᵥ a) := by
      simp only [T, fromBlocks_mulVec]
      ext (i | i) <;> simp
    simp only [w]
    rw [hinv, h, fromBlocks_mulVec]
    simp
  have hu : u = Sum.elim (a + (N * C)ᵀ *ᵥ (d + Bᵀ *ᵥ a)) (b + (N * C) *ᵥ (c + B *ᵥ b)) := by
    simp only [u, S]
    rw [hw, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr,
      mulVec_mulVec, ← transpose_mul, hCM]
    ext (i | i) <;> simp
  rw [hu, hw, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
  simp only [dotProduct_add, mulVec_add, mulVec_mulVec, ← transpose_mul, dot_transpose_mulVec',
    hMB, hMBC, hNCB, sub_mulVec, one_mulVec, dotProduct_sub]
  rw [dotProduct_comm c a]
  ring

theorem gaussian_phase_critical_value_blocks :
    ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (a c : Fin P → ℂ) (b d : Fin Q → ℂ),
      IsUnit (1 - Aᴴ * B).det →
      (let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 Aᴴᵀ Aᴴ 0
       let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0
       let w : Fin P ⊕ Fin Q → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b)
       let u : Fin P ⊕ Fin Q → ℂ := Sum.elim a b + S *ᵥ w
       1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u)
         = a ⬝ᵥ (1 - B * Aᴴ)⁻¹ *ᵥ c + d ⬝ᵥ (1 - Aᴴ * B)⁻¹ *ᵥ b
           + a ⬝ᵥ ((1 - B * Aᴴ)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - Aᴴ * B)⁻¹ * Aᴴ) *ᵥ c) :=
  fun _ _ A B a c b d h => gaussian_phase_critical_value_blocks_general Aᴴ B a c b d h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GermSectionsHalfPlaneGlobalSection
section
open Filter Topology

namespace GlobalTheory

theorem germSections_glue {Y ι : Type} (G : ℂ → (ℂ → Y) → Prop)
    (h1 : ∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s') (i₀ : ι)
    (U : ι → Set ℂ) (s : ι → ℂ → Y) (hU : ∀ i, IsOpen (U i))
    (hs : ∀ i, ∀ z ∈ U i, G z (s i))
    (hag : ∀ i j, Set.EqOn (s i) (s j) (U i ∩ U j)) :
    ∃ t : ℂ → Y, ∀ i, ∀ z ∈ U i, G z t := by
  classical
  refine ⟨fun z => if h : ∃ i, z ∈ U i then s h.choose z else s i₀ z, fun i z hz => ?_⟩
  refine h1 z (s i) _ ?_ (hs i z hz)
  filter_upwards [(hU i).mem_nhds hz] with w hw
  have h : ∃ i, w ∈ U i := ⟨i, hw⟩
  rw [dite_eq_left h]
  exact hag i _ ⟨hw, h.choose_spec⟩

theorem germSections_halfPlane_global (Y : Type) (G : ℂ → (ℂ → Y) → Prop) (T : ℝ)
    (h1 : ∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s')
    (h2 : ∀ w : ℂ, T < w.im → ∃ s, ∀ᶠ z in 𝓝 w, G z s)
    (h3 : ∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) →
      (∀ z ∈ U, G z s) → (∀ z ∈ U, G z s') → ∀ w ∈ U, s w = s' w → Set.EqOn s s' U)
    (h4 : ∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) →
      (∀ z ∈ U, G z s) → ∀ w ∈ U, G w s' → ∃ s'' : ℂ → Y, (∀ z ∈ U, G z s'') ∧ s'' w = s' w) :
    ∃ s : ℂ → Y, ∀ w : ℂ, T < w.im → G w s := by
  have hH : IsOpen {z : ℂ | T < z.im} := isOpen_lt continuous_const Complex.continuous_im

  have glue : ∀ {ι : Type} (_ : ι) (U : ι → Set ℂ) (p : ℂ), (∀ i, IsOpen (U i)) →
      (∀ i, Convex ℝ (U i)) → (∀ i, ∀ z ∈ U i, T < z.im) → (∀ i, p ∈ U i) →
      (∀ i, ∃ s, ∀ z ∈ U i, G z s) → ∃ t : ℂ → Y, ∀ i, ∀ z ∈ U i, G z t := by
    intro ι i₀ U p ho hc hT hp hs
    obtain ⟨s₀, hs₀⟩ := hs i₀
    have : ∀ i, ∃ s : ℂ → Y, (∀ z ∈ U i, G z s) ∧ s p = s₀ p := fun i => by
      obtain ⟨s, hs⟩ := hs i
      exact h4 (U i) s s₀ (ho i) (hc i) (hT i) hs p (hp i) (hs₀ p (hp i₀))
    choose s hs hsp using this
    refine germSections_glue G h1 i₀ U s ho hs fun i j => ?_
    exact h3 (U i ∩ U j) (s i) (s j) ((ho i).inter (ho j)) ((hc i).inter (hc j))
      (fun z hz => hT i z hz.1) (fun z hz => hs i z hz.1) (fun z hz => hs j z hz.2) p
      ⟨hp i, hp j⟩ ((hsp i).trans (hsp j).symm)
  have loc : ∀ w : ℂ, T < w.im → ∃ D : Set ℂ, IsOpen D ∧ Convex ℝ D ∧ (∀ z ∈ D, T < z.im) ∧
      w ∈ D ∧ ∃ s, ∀ z ∈ D, G z s := by
    intro w hw
    obtain ⟨s, hs⟩ := h2 w hw
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hs.and (hH.mem_nhds hw))
    exact ⟨Metric.ball w ε, Metric.isOpen_ball, convex_ball w ε, fun z hz => (hb z hz).2,
      Metric.mem_ball_self hε, s, fun z hz => (hb z hz).1⟩
  set p : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hpdef
  have hp : T < p.im := by simp [hpdef]
  let good : ℂ → Prop := fun w => ∃ U : Set ℂ, IsOpen U ∧ Convex ℝ U ∧ (∀ z ∈ U, T < z.im) ∧
      p ∈ U ∧ w ∈ U ∧ ∃ s, ∀ z ∈ U, G z s
  have hgood : ∀ w : ℂ, T < w.im → good w := by
    intro w hw
    let γ : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap p w
    have hγc : Continuous γ := AffineMap.lineMap_continuous
    have hγ0 : γ 0 = p := AffineMap.lineMap_apply_zero p w
    have hγ1 : γ 1 = w := AffineMap.lineMap_apply_one p w
    have hγH : ∀ t ∈ Set.Icc (0 : ℝ) 1, T < (γ t).im := by
      intro t ht
      have hc := ((convex_halfSpace_im_gt T).affine_preimage γ).ordConnected
      exact hc.out (x := 0) (y := 1) (by simpa [hγ0] using hp) (by simpa [hγ1] using hw) ht
    have step : ∀ D : Set ℂ, IsOpen D → Convex ℝ D → (∀ z ∈ D, T < z.im) →
        (∃ s, ∀ z ∈ D, G z s) → ∀ a b : ℝ, 0 ≤ b → γ a ∈ D → γ b ∈ D →
        good (γ a) → good (γ b) := by
      rintro D hDo hDc hDT hDs a b hb ha hbD ⟨U, hUo, hUc, hUT, hpU, haU, hUs⟩
      obtain ⟨t, ht⟩ := glue true (fun i : Bool => cond i U D) (γ a)
        (by rintro (_ | _) <;> assumption) (by rintro (_ | _) <;> assumption)
        (by rintro (_ | _) <;> assumption) (by rintro (_ | _) <;> assumption)
        (by rintro (_ | _) <;> assumption)
      have hK : IsCompact (γ '' Set.Icc 0 b) := isCompact_Icc.image hγc
      have hKc : Convex ℝ (γ '' Set.Icc 0 b) := (convex_Icc 0 b).affine_image γ
      have hsub : γ '' Set.Icc 0 b ⊆ U ∪ D := by
        rintro _ ⟨r, hr, rfl⟩
        rcases le_total r a with h | h
        · left
          exact (hUc.affine_preimage γ).ordConnected.out (x := 0) (y := a)
            (by simpa [hγ0] using hpU) haU ⟨hr.1, h⟩
        · right
          exact (hDc.affine_preimage γ).ordConnected.out (x := a) (y := b) ha hbD ⟨h, hr.2⟩
      obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open (hUo.union hDo) hsub
      refine ⟨Metric.thickening δ (γ '' Set.Icc 0 b), Metric.isOpen_thickening,
        hKc.thickening δ, fun z hz => ?_, ?_, ?_, t, fun z hz => ?_⟩
      · rcases hth hz with h | h
        · exact hUT z h
        · exact hDT z h
      · exact Metric.self_subset_thickening hδ _ ⟨0, ⟨le_rfl, hb⟩, hγ0⟩
      · exact Metric.self_subset_thickening hδ _ ⟨b, ⟨hb, le_rfl⟩, rfl⟩
      · rcases hth hz with h | h
        · exact ht true z h
        · exact ht false z h
    have key := (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).induction₂'
      (fun a b => good (γ a) → good (γ b)) (by
        intro x hx
        obtain ⟨D, hDo, hDc, hDT, hxD, hDs⟩ := loc (γ x) (hγH x hx)
        have : ∀ᶠ y in 𝓝 x, γ y ∈ D := hγc.continuousAt.eventually (hDo.mem_nhds hxD)
        filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with y hy hyI
        exact ⟨step D hDo hDc hDT hDs x y hyI.1 hxD hy, step D hDo hDc hDT hDs y x hx.1 hy hxD⟩)
      (fun _ _ _ _ _ _ h h' hh => h' (h hh)) (x := 0) (y := 1) (by simp) (by simp)
    rw [hγ0, hγ1] at key
    apply key
    obtain ⟨D, hDo, hDc, hDT, hxD, hDs⟩ := loc p hp
    exact ⟨D, hDo, hDc, hDT, hxD, hxD, hDs⟩
  choose U hUo hUc hUT hpU hwU hUs using hgood
  obtain ⟨t, ht⟩ := glue (ι := {w : ℂ // T < w.im}) ⟨p, hp⟩ (fun w => U w.1 w.2) p
    (fun w => hUo w.1 w.2) (fun w => hUc w.1 w.2) (fun w => hUT w.1 w.2) (fun w => hpU w.1 w.2)
    (fun w => hUs w.1 w.2)
  exact ⟨t, fun w hw => ht ⟨w, hw⟩ w (hwU w hw)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasFDerivAtSetIntegral
section
open MeasureTheory Metric Set
open scoped ContDiff

namespace GlobalTheory.SetIntegralSmoothness

theorem hasFDerivAt_setIntegral {X P E : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {a : X → E} (ha : Continuous a) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p₀ : P) :
    HasFDerivAt (fun p : P => ∫ x in K, Ψ (p, a x) ∂μ)
      (∫ x in K, (fderiv ℝ Ψ (p₀, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ) p₀ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by exact_mod_cast le_top)
  have hdΨ : Continuous (fderiv ℝ Ψ) := hΨ1.continuous_fderiv one_ne_zero
  have hS : IsCompact (closedBall p₀ 1 ×ˢ (a '' K)) := (isCompact_closedBall p₀ 1).prod (hK.image ha)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hdΨ.continuousOn
  have hcont : ∀ p : P, Continuous fun x : X => Ψ (p, a x) :=
    fun p => hΨ.continuous.comp (continuous_const.prodMk ha)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ.restrict K) (x₀ := p₀)
    (F := fun p x => Ψ (p, a x)) (F' := fun p x => (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E))
    (bound := fun _ => C * ‖ContinuousLinearMap.inl ℝ P E‖)
    (closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun p =>
      (hcont p).continuousOn.aestronglyMeasurable_of_isCompact hK hKm
  · exact (hcont p₀).continuousOn.integrableOn_compact hK
  · exact ((hdΨ.comp (continuous_const.prodMk ha)).clm_comp continuous_const).continuousOn.aestronglyMeasurable_of_isCompact hK hKm
  · refine (ae_restrict_iff' hKm).mpr (Filter.Eventually.of_forall fun x hx p hp => ?_)
    calc ‖(fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E)‖
        ≤ ‖fderiv ℝ Ψ (p, a x)‖ * ‖ContinuousLinearMap.inl ℝ P E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ‖ContinuousLinearMap.inl ℝ P E‖ :=
        mul_le_mul_of_nonneg_right (hC _ ⟨hp, mem_image_of_mem a hx⟩) (norm_nonneg _)
  · exact integrableOn_const hK.measure_ne_top
  · exact Filter.Eventually.of_forall fun x p _ =>
      ((hΨ1.differentiable one_ne_zero) (p, a x)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p (a x))

theorem contDiff_setIntegral {X P E : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {a : X → E} (ha : Continuous a) (m : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun p : P => ∫ x in K, Ψ (p, a x) ∂μ) := by
  induction m generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun p₀ =>
      (hasFDerivAt_setIntegral μ hK ha Ψ hΨ p₀).continuousAt
  | succ m IH =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun p => ∫ x in K, (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ, ?_,
      fun p₀ => hasFDerivAt_setIntegral μ hK ha Ψ hΨ p₀⟩
    have hΨ' : ContDiff ℝ ∞ fun q : P × E => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ P E) :=
      (hΨ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
    exact IH (fun q : P × E => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ P E)) hΨ'

end GlobalTheory.SetIntegralSmoothness
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IInfMapLeMapIInfOfFlat
section
open scoped TensorProduct

namespace GlobalTheory.FlatIdealInf

open TensorProduct

theorem range_lTensor_iInf_le {B R M : Type} [CommRing B] [AddCommGroup R] [Module B R]
    [Module.Flat B R] [AddCommGroup M] [Module B M] {ι : Type} [Finite ι]
    (K : ι → Submodule B M) :
    ⨅ i, LinearMap.range (LinearMap.lTensor R (K i).subtype) ≤
      LinearMap.range (LinearMap.lTensor R (⨅ i, K i).subtype) := by
  classical
  cases nonempty_fintype ι
  intro t ht
  rw [Submodule.mem_iInf] at ht
  let φ : M →ₗ[B] (∀ i, M ⧸ K i) := LinearMap.pi (fun i => (K i).mkQ)
  have hexB : Function.Exact (⨅ i, K i).subtype φ := by
    rw [LinearMap.exact_iff, LinearMap.ker_pi, Submodule.range_subtype]
    simp only [Submodule.ker_mkQ]
  have hex := Module.Flat.lTensor_exact R hexB
  have hcomp : ∀ i (u : R ⊗[B] M), TensorProduct.piRight B B R (fun i => M ⧸ K i) (LinearMap.lTensor R φ u) i =
      LinearMap.lTensor R (K i).mkQ u := by
    intro i u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [φ]
    | add x y hx hy => simp_all
  have h0 : LinearMap.lTensor R φ t = 0 := by
    apply (TensorProduct.piRight B B R (fun i => M ⧸ K i)).injective
    rw [map_zero]
    funext i
    rw [hcomp i t, Pi.zero_apply]
    obtain ⟨s, hs⟩ := ht i
    rw [← hs]
    exact (lTensor_exact R (LinearMap.exact_subtype_mkQ (K i)) (Submodule.mkQ_surjective _) _).mpr
      ⟨s, rfl⟩
  obtain ⟨s, hs⟩ := (hex t).mp h0
  exact ⟨s, hs⟩

theorem mem_map_algebraMap_iff {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (I : Ideal B) (x : R) :
    x ∈ I.map (algebraMap B R) ↔
      x ⊗ₜ[B] (1 : B) ∈ LinearMap.range (LinearMap.lTensor R (Submodule.subtype (I.restrictScalars B))) := by
  rw [← Ideal.map_includeRight_eq (R := B) (A := R) I, Submodule.restrictScalars_mem]
  let e := (Algebra.TensorProduct.rid B R R).toRingEquiv
  have he : (e : R ⊗[B] B →+* R).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[B] R ⊗[B] B) : B →+* R ⊗[B] B) = algebraMap B R := by
    ext b
    simp [e, Algebra.algebraMap_eq_smul_one]
  rw [← he, ← Ideal.map_map, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl

theorem iInf_map_le_map_iInf : ∀ {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    [Module.Flat B R] {ι : Type} [Finite ι] (K : ι → Ideal B),
    ⨅ i, (K i).map (algebraMap B R) ≤ (⨅ i, K i).map (algebraMap B R) := by
  intro B R _ _ _ _ ι _ K x hx
  rw [mem_map_algebraMap_iff]
  have h := range_lTensor_iInf_le (R := R) (fun i => (K i).restrictScalars B)
  have hK : (⨅ i, (K i).restrictScalars B) = (⨅ i, K i).restrictScalars B := by
    ext y; simp
  rw [hK] at h
  apply h
  rw [Submodule.mem_iInf]
  intro i
  exact (mem_map_algebraMap_iff (K i) x).mp ((Submodule.mem_iInf _).mp hx i)

end GlobalTheory.FlatIdealInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsAlt
section
namespace GlobalTheory.KeyLemmaTwo

lemma key {z : ℂ} (h : ∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    set w := z ^ (2 ^ k) with hw
    have hw2 : z ^ (2 ^ (k + 1)) = w ^ 2 := by rw [hw, ← pow_mul, pow_succ]
    have hlt : ‖w - 1‖ < 1 / 2 := h _
    have hplus : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
      have e : w + 1 = (2 : ℂ) + (w - 1) := by ring
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      have := norm_sub_norm_le (2 : ℂ) (-(w - 1))
      rw [e]
      have h3 : ‖(2 : ℂ) - -(w - 1)‖ = ‖(2 : ℂ) + (w - 1)‖ := by rw [sub_neg_eq_add]
      rw [norm_neg, h2, h3] at this
      linarith
    have fac : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [hw2, fac, norm_mul, pow_succ]
    have hn : 0 ≤ ‖w - 1‖ := norm_nonneg _
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖w - 1‖ * (3 / 2) := by gcongr
      _ ≤ ‖w - 1‖ * ‖w + 1‖ := by gcongr

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key h k
  have h2 := h (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.KeyLemmaTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsExtra
section
namespace GlobalTheory.IsolatedTheoremFive

theorem main {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n d : ℕ}
    (E : Matrix (Fin n) (Fin d) K) (h : Function.Injective (Matrix.mulVec E)) :
    Function.Injective (Matrix.mulVec (Matrix.map E (⇑φ : K → K'))) := by
  have hl : LinearMap.ker (Matrix.mulVecLin E) = ⊥ := LinearMap.ker_eq_bot.mpr h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin E) hl
  have hB : LinearMap.toMatrix' g * E = 1 := by
    have e : Matrix.mulVecLin E = Matrix.toLin' E := rfl
    have : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin E) = LinearMap.toMatrix' g * E := by
      rw [LinearMap.toMatrix'_comp, e, LinearMap.toMatrix'_toLin']
    rw [← this, hg, LinearMap.toMatrix'_id]
  have hB' : (LinearMap.toMatrix' g).map φ * E.map φ = 1 := by
    rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero φ) (map_one φ)]
  intro x y hxy
  have := congrArg (Matrix.mulVec ((LinearMap.toMatrix' g).map φ)) hxy
  simpa [Matrix.mulVec_mulVec, hB'] using this

theorem target : ∀ {K K' : Type} [inst : Field K] [inst_1 : Field K'] (φ : K →+* K') {n d : ℕ} (E : Matrix (Fin n) (Fin d) K), Function.Injective (Matrix.mulVec E) → Function.Injective (Matrix.mulVec (Matrix.map E (⇑φ : K → K'))) := by
  intro K K' _ _ φ n d E h
  exact main φ E h

end GlobalTheory.IsolatedTheoremFive
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsFurther
section
namespace GlobalTheory.IsolatedTheoremFour

open IsDedekindDomain

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {l : ℕ}, Nat.Prime l → ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), (↑l : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  intro K _ _ l hl
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers K)) ≤ Ideal.span {(l : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective_int (algebraMap ℤ (NumberField.RingOfIntegers K)))]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker
  have hlQ : ((l : ℕ) : NumberField.RingOfIntegers K) ∈ Q := by
    have h1 : (l : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.subset_span rfl
    simpa using h1
  have hl0 : ((l : ℕ) : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast hl.ne_zero
  exact ⟨⟨Q, hQ.isPrime, fun h => hl0 (Ideal.mem_bot.mp (h ▸ hlQ))⟩, hlQ⟩

end GlobalTheory.IsolatedTheoremFour
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsMore
section
namespace GlobalTheory.IsolatedTheoremThree

theorem main : (let d1 : (R : Type) → {A : Type} → [inst : CommRing R] → [inst_1 : CommRing A] → [inst_2 : Algebra R A] → (ℕ → A) → ℕ → Submodule R A := @(fun (R : Type) {A : Type} [CommRing R] [CommRing A] [Algebra R A] (γ : ℕ → A) (N : ℕ) ↦ Submodule.span R (γ '' {m : ℕ | m < N})); ∀ {R A : Type} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A], (∀ (n : ℕ), IsUnit (↑(Nat.factorial n) : A)) → ∀ (ξ : R) (γ : ℕ → A), (∀ (n : ℕ), (↑(Nat.factorial n) : A) * γ n = (Algebra.algebraMap R A : R → A) ξ ^ n) → ∀ (N : ℕ), ∀ w ∈ Submodule.span R (Set.range γ), ∃ w₁ ∈ d1 R γ N, (Algebra.algebraMap R A : R → A) ξ ^ N ∣ w - w₁) := by
  intro d1 R A _ _ _ hfac ξ γ hγ N w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, rfl⟩ := hw
    by_cases hn : n < N
    · exact ⟨γ n, Submodule.subset_span ⟨n, hn, rfl⟩, by simp⟩
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [sub_zero]
      obtain ⟨u, hu⟩ := hfac n
      have hg : γ n = ↑u⁻¹ * algebraMap R A ξ ^ n := by
        rw [← hγ n, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
      have hp : algebraMap R A ξ ^ n = algebraMap R A ξ ^ N * algebraMap R A ξ ^ (n - N) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hg, hp]
      exact Dvd.intro (↑u⁻¹ * algebraMap R A ξ ^ (n - N)) (by ring)
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hda⟩ := hx
    obtain ⟨b, hb, hdb⟩ := hy
    refine ⟨a + b, Submodule.add_mem _ ha hb, ?_⟩
    rw [show x + y - (a + b) = (x - a) + (y - b) by ring]
    exact dvd_add hda hdb
  | smul r x _ hx =>
    obtain ⟨a, ha, hda⟩ := hx
    refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
    rw [← smul_sub, Algebra.smul_def]
    exact Dvd.dvd.mul_left hda _

end GlobalTheory.IsolatedTheoremThree
end

