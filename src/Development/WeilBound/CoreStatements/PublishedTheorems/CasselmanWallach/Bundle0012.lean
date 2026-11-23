module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SlopeLimitConstant
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum Filter Topology

namespace PositivityTheory.CW

namespace ExistsNormingFunctional

theorem exists_norming {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) (x₀ : E) :
    ∃ φ : Module.Dual ℂ E, ‖φ x₀‖ = q x₀ ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have H : ∀ c : ℂ, c • x₀ = 0 → (RingHom.id ℂ) c • ((q x₀ : ℝ) : ℂ) = 0 := by
    intro c hc
    have h0 : ‖c‖ * q x₀ = 0 := by rw [← map_smul_eq_mul q, hc, map_zero]
    rcases mul_eq_zero.1 h0 with h | h
    · simp [norm_eq_zero.1 h]
    · simp [h]
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) :=
    (LinearPMap.mkSpanSingleton' x₀ ((q x₀ : ℝ) : ℂ) H).toFun
  have hf : ∀ (c : ℂ) (h : c • x₀ ∈ Submodule.span ℂ {x₀}), f ⟨c • x₀, h⟩ = c * (q x₀ : ℂ) := by
    intro c h
    exact (LinearPMap.mkSpanSingleton'_apply x₀ ((q x₀ : ℝ) : ℂ) H c h).trans (by simp)
  have h1 : f ⟨x₀, Submodule.mem_span_singleton_self x₀⟩ = (q x₀ : ℂ) :=
    LinearPMap.mkSpanSingleton'_apply_self x₀ ((q x₀ : ℝ) : ℂ) H _
  obtain ⟨g, hg, hgq⟩ := Module.Dual.exists_extension_of_le_seminorm
    (Submodule.span ℂ {x₀}) f (p := q) (by
      rintro ⟨z, hz⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      exact le_of_eq (map_smul_eq_mul q c x₀).symm)
  refine ⟨g, ?_, hgq⟩
  have h2 := hg ⟨x₀, Submodule.mem_span_singleton_self x₀⟩
  rw [h1] at h2
  rw [show g x₀ = (q x₀ : ℂ) from h2, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]

end ExistsNormingFunctional

private theorem exp_smul_mem_UJset_of_mem_lieSet {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X ∈ lieSet ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε := by
  set J := ReciprocityTheory.ChartRestriction.DS.Jm ε with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef, ReciprocityTheory.ChartRestriction.DS.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨J, J, hJJ, hJJ⟩
  have hX' : Xᴴ * J + J * X = 0 := hX
  set Y : Matrix (Fin n) (Fin n) ℂ := t • X with hYdef
  have hYJ : Yᴴ * J = -(J * Y) := by
    rw [hYdef, Matrix.conjTranspose_smul, star_trivial, smul_mul_assoc, Matrix.mul_smul,
      eq_neg_of_add_eq_zero_left hX', smul_neg]
  have hY : Yᴴ = J * (-Y) * J := by
    calc Yᴴ = Yᴴ * J * J := by rw [mul_assoc, hJJ, mul_one]
      _ = J * (-Y) * J := by rw [hYJ, mul_neg, neg_mul]
  have hexp : NormedSpace.exp Yᴴ = J * NormedSpace.exp (-Y) * J := by
    have h := Matrix.exp_units_conj u (-Y)
    rw [hY]
    exact h
  have hdet : IsUnit (NormedSpace.exp Y).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  show (NormedSpace.exp Y)ᴴ * J * NormedSpace.exp Y = J
  rw [← Matrix.exp_conjTranspose, hexp, Matrix.exp_neg]
  simp only [mul_assoc]
  rw [← mul_assoc J J, hJJ, one_mul, Matrix.nonsing_inv_mul _ hdet, mul_one]

theorem d1b : D1 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hCore T₀ hT i
  obtain ⟨q, N, hq, hgrow⟩ := hπ.growth i
  obtain ⟨S, C, I₀, hS, hC, hI₀, hmain⟩ := hCore N
  refine ⟨S, C * ∑ e ∈ I₀, q (T₀ e), hS, ?_⟩
  intro w hw
  obtain ⟨φ, hφ1, hφ2⟩ := ExistsNormingFunctional.exists_norming (p i) (T₀ w)
  have hφc : Continuous φ :=
    hπ.withSeminorms.continuous_normedSpace_rng ℂ φ ⟨{i}, 1, by
      intro x
      simpa using hφ2 x⟩
  let F : H →ₗ[ℂ] Mx n → ℂ :=
    LinearMap.pi (fun g => φ ∘ₗ (π g).toLinearMap ∘ₗ T₀)
  have hF : ∀ v g, F v g = φ (π g (T₀ v)) := fun _ _ => rfl
  have hpos : ∀ g : Mx n, 0 ≤ (1 + hs g) ^ N := by
    intro g
    apply pow_nonneg
    have : 0 ≤ hs g := by
      unfold hs
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hB : 0 ≤ ∑ e ∈ I₀, q (T₀ e) := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  have key := hmain F
    (fun v _ => by
      show ContinuousOn (fun g => φ (π g (T₀ v))) (UJset ε)
      exact hφc.comp_continuousOn (hπ.continuousOn (T₀ v)))
    (fun X hX v hv g hg => by
      rw [hF, hT.2 X hX v hv, hasDerivAt_iff_tendsto_slope]
      have hΛ : Continuous fun z : E => φ (π g z) := hφc.comp (π g).continuous
      have heq : slope (fun t : ℝ => F v (g * NormedSpace.exp (t • X))) 0 =
          fun t : ℝ => φ (π g (((t : ℂ))⁻¹ • ((π (NormedSpace.exp (t • X))) (T₀ v) - T₀ v))) := by
        funext t
        rw [slope_def_module]
        simp only [hF, sub_zero, zero_smul, NormedSpace.exp_zero, mul_one,
          hπ.map_mul g hg _ (exp_smul_mem_UJset_of_mem_lieSet ε X hX t), ContinuousLinearMap.comp_apply, map_smul, map_sub,
          smul_eq_mul, Complex.real_smul, Complex.ofReal_inv]
      rw [heq]
      exact (hΛ.tendsto _).comp (hπ.hasDRep X hX (T₀ v)))
    (fun v _ => ⟨q (T₀ v), fun g hg => by
      rw [hF]
      calc ‖φ (π g (T₀ v))‖ ≤ p i (π g (T₀ v)) := hφ2 _
        _ ≤ (1 + hs g) ^ N * q (T₀ v) := hgrow g hg (T₀ v)
        _ = q (T₀ v) * (1 + hs g) ^ N := mul_comm _ _⟩)
    (∑ e ∈ I₀, q (T₀ e)) hB
    (fun e he g hg => by
      rw [hF]
      calc ‖φ (π g (T₀ e))‖ ≤ p i (π g (T₀ e)) := hφ2 _
        _ ≤ (1 + hs g) ^ N * q (T₀ e) := hgrow g hg (T₀ e)
        _ ≤ (1 + hs g) ^ N * ∑ e ∈ I₀, q (T₀ e) :=
          mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun e => q (T₀ e)) (fun _ _ => apply_nonneg _ _) he)
            (hpos g)
        _ = (∑ e ∈ I₀, q (T₀ e)) * (1 + hs g) ^ N := mul_comm _ _)
    w hw
  rw [hF, hπ.map_one, ContinuousLinearMap.one_apply] at key
  rw [← hφ1]
  exact key

end PositivityTheory.CW
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.TendstoPiZero
section
noncomputable section

open Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped Topology

namespace PositivityTheory.CW

namespace SlopeLimitConstant

variable {n : ℕ}

theorem const_of_slope {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
    {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) (f : ℝ → E)
    (hf : ∀ t, Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • (f (t + h) - f t)) (𝓝[≠] 0) (𝓝 0)) : f 1 = f 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := hp.separating_of_T1 (f 1 - f 0) (sub_ne_zero.2 hne)
  set g : ℝ → ℝ := fun t => p i (f t - f 0) with hg
  have hd : ∀ t, HasDerivAt g 0 t := by
    intro t
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h1 : Tendsto (fun h : ℝ => p i (((h : ℂ)⁻¹) • (f (t + h) - f t))) (𝓝[≠] 0) (𝓝 0) := by
      have := ((hp.continuous_seminorm i).tendsto 0).comp (hf t)
      rw [map_zero] at this
      exact this
    refine squeeze_zero_norm (fun h => ?_) h1
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, map_smul_eq_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := abs_sub_map_le_sub (p i) (f (t + h) - f 0) (f t - f 0)
    simpa [hg] using this
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  apply hi
  have : g 1 = 0 := by rw [hc]; simp [hg]
  simpa [hg] using this

theorem tendsto_pi_zero {ε : Fin n → Bool} {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] {p : ℕ → Seminorm ℂ E} {π dπ : Mx n → (E →L[ℂ] E)} (hπ : IsSmoothModRep ε p π dπ)
    {ι : Type} {l : Filter ι} {v : ι → E} (hv : Tendsto v l (𝓝 0)) {g : ι → Mx n} {g₀ : Mx n}
    (hg : ∀ x, g x ∈ UJset ε) (hg₀ : Tendsto g l (𝓝 g₀)) : Tendsto (fun x => π (g x) (v x)) l (𝓝 0) := by
  rw [hπ.withSeminorms.tendsto_nhds _ 0]
  intro i δ hδ
  obtain ⟨q, N, hq, hb⟩ := hπ.growth i
  have h1 : Tendsto (fun x => (1 + hs (g x)) ^ N * q (v x)) l (𝓝 ((1 + hs g₀) ^ N * 0)) := by
    refine Tendsto.mul ?_ ?_
    · exact ((tendsto_const_nhds.add ((continuous_hs).tendsto g₀ |>.comp hg₀)).pow N)
    · have := (hq.tendsto 0).comp hv
      rw [map_zero] at this
      exact this
  rw [mul_zero] at h1
  filter_upwards [(tendsto_order.1 h1).2 δ hδ] with x hx
  rw [sub_zero]
  exact lt_of_le_of_lt (hb (g x) (hg x) (v x)) hx

theorem Dw_sub {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H}
    (hx : Sm ε σ x) (hy : Sm ε σ y) : Dw σ l (x - y) = Dw σ l x - Dw σ l y := by
  have hy' : Sm ε σ ((-1 : ℂ) • y) := by
    rw [sm_iff] at hy ⊢
    exact Submodule.smul_mem _ _ hy
  rw [sub_eq_add_neg, ← neg_one_smul ℂ y, Dw_add hσ hl hx hy', Dw_smul hσ hl _ hy, neg_one_smul, ← sub_eq_add_neg]

theorem tendsto_rem {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) (hSD : SobDiff ε σ) {T : H →ₗ[ℂ] E}
    (hT : SobBdOn ε σ (Sm ε σ) p T) {X : Mx n} (hX : X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w))
      (𝓝[≠] 0) (𝓝 0) := by
  have hwX : Sm ε σ (dRep σ X w) := by
    have := hw.word hσ (l := [X]) (by simpa using hX)
    simpa [Dw] using this
  have hsm : ∀ h : ℝ, Sm ε σ (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w) := by
    intro h
    have h1 := hw.translate hσ (exp_mem_UJ hX h)
    rw [sm_iff] at h1 hw hwX ⊢
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 hw) (Submodule.smul_mem _ _ hwX)
  rw [hp.tendsto_nhds _ 0]
  intro j δ hδ
  obtain ⟨S, C, hS, hb⟩ := hT j
  have hl : ∀ l ∈ S, Tendsto (fun h : ℝ =>
      ‖((h : ℂ)⁻¹) • Dw σ l (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)‖) (𝓝[≠] 0) (𝓝 0) := by
    intro l hlS
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := hS l hlS
    have hd := hSD l hl' w hw X hX
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    have e0 : Dw σ l (σ (NormedSpace.exp ((0 : ℝ) • X)) w) = Dw σ l w := by
      rw [zero_smul, NormedSpace.exp_zero, sigma_one hσ]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hd
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have htr := hw.translate hσ (exp_mem_UJ hX h)
    have hsw : Sm ε σ ((h : ℂ) • dRep σ X w) := by
      rw [sm_iff] at hwX ⊢
      exact Submodule.smul_mem _ _ hwX
    have hdiff : Sm ε σ (σ (NormedSpace.exp (h • X)) w - w) := by
      rw [sm_iff] at htr hw ⊢
      exact Submodule.sub_mem _ htr hw
    rw [Dw_sub hσ hl' hdiff hsw, Dw_sub hσ hl' htr hw, Dw_smul hσ hl' _ hwX, zero_add, e0,
      ← Complex.coe_smul, Complex.ofReal_inv, smul_sub, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hh', one_smul]
  have hsum : Tendsto (fun h : ℝ => C * (S.map fun l =>
      ‖((h : ℂ)⁻¹) • Dw σ l (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)‖).sum) (𝓝[≠] 0) (𝓝 0) := by
    have := (tendsto_list_sum (l := S) hl).const_mul C
    simpa using this
  have hle : ∀ h : ℝ, p j (((h : ℂ)⁻¹) • T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w) - 0) ≤
      C * (S.map fun l =>
        ‖((h : ℂ)⁻¹) • Dw σ l (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)‖).sum := by
    intro h
    rw [sub_zero, map_smul_eq_mul]
    calc ‖((h : ℂ)⁻¹)‖ * p j (T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w))
        ≤ ‖((h : ℂ)⁻¹)‖ * (C * sobNorm σ S (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)) :=
          mul_le_mul_of_nonneg_left (hb _ (hsm h)) (norm_nonneg _)
      _ = _ := by
          rw [sobNorm, mul_left_comm, ← List.sum_map_mul_left]
          congr 2
          exact List.map_congr_left fun l _ => (norm_smul _ _).symm
  filter_upwards [(tendsto_order.1 hsum).2 δ hδ] with h hh
  exact lt_of_le_of_lt (hle h) hh

theorem tendsto_key {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] {p : ℕ → Seminorm ℂ E} {π dπ : Mx n → (E →L[ℂ] E)} (hπ : IsSmoothModRep ε p π dπ)
    (hSD : SobDiff ε σ) {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) {X : Mx n} (hX : X ∈ lieSet ε)
    (hc : ∀ w, Sm ε σ w → T (dRep σ X w) = dπ X (T w)) {w : H} (hw : Sm ε σ w) :
    Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) •
      (π (NormedSpace.exp ((-h) • X)) (T (σ (NormedSpace.exp (h • X)) w)) - T w)) (𝓝[≠] 0) (𝓝 0) := by
  set a := T w
  set b := dπ X a
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => neg_ne_zero.2 hx⟩
    have := ((continuous_neg (G := ℝ)).tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    simpa using this
  have hg : Tendsto (fun h : ℝ => NormedSpace.exp ((-h) • X)) (𝓝[≠] 0) (𝓝 1) := by
    have := ((continuous_exp_smul X).tendsto 0).comp (tendsto_nhdsWithin_iff.1 hneg).1
    simpa [Function.comp_def] using this
  have hgU : ∀ h : ℝ, NormedSpace.exp ((-h) • X) ∈ UJset ε := fun h => exp_mem_UJ hX (-h)
  have hgW : Tendsto (fun h : ℝ => NormedSpace.exp ((-h) • X)) (𝓝[≠] 0) (𝓝[UJset ε] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hg, Eventually.of_forall hgU⟩

  have t1 := tendsto_pi_zero hπ (tendsto_rem hσ hπ.withSeminorms hSD hT hX hw) hgU hg
  have t2 : Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • (π (NormedSpace.exp ((-h) • X)) a - a)) (𝓝[≠] 0) (𝓝 (-b)) := by
    have := ((hπ.hasDRep X hX a).comp hneg).neg
    refine this.congr' (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply, Complex.ofReal_neg, inv_neg, neg_smul, neg_neg]
  have t3 : Tendsto (fun h : ℝ => π (NormedSpace.exp ((-h) • X)) b) (𝓝[≠] 0) (𝓝 b) := by
    have := ((hπ.continuousOn b) 1 (one_mem_UJ ε)).tendsto.comp hgW
    rw [hπ.map_one] at this
    exact this
  have hsum := (t1.add t2).add t3
  rw [zero_add, neg_add_cancel] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hTu : T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w) =
      T (σ (NormedSpace.exp (h • X)) w) - a - (h : ℂ) • b := by
    rw [map_sub, map_sub, map_smul, hc w hw]
  rw [hTu, (π (NormedSpace.exp ((-h) • X))).map_smul, map_sub, map_sub, (π (NormedSpace.exp ((-h) • X))).map_smul]
  rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hh', one_smul]
  abel

end SlopeLimitConstant

open SlopeLimitConstant in
theorem d4b : D4 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hSD T hT X hX hc w hw
  set f : ℝ → E := fun t => π (NormedSpace.exp ((-t) • X)) (T (σ (NormedSpace.exp (t • X)) w)) with hf
  have hmulπ : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ y, π a (π b y) = π (a * b) y := by
    intro a ha b hb y
    rw [hπ.map_mul a ha b hb]; rfl
  have hslope : ∀ t, Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • (f (t + h) - f t)) (𝓝[≠] 0) (𝓝 0) := by
    intro t
    have hwt := hw.translate hU (exp_mem_UJ hX t)
    have hk := tendsto_key hU hπ hSD hT hX hc hwt
    have := ((π (NormedSpace.exp ((-t) • X))).continuous.tendsto 0).comp hk
    rw [map_zero] at this
    refine this.congr' (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply, hf, map_smul, map_sub]
    congr 2
    · rw [hmulπ _ (exp_mem_UJ hX _) _ (exp_mem_UJ hX _), ← exp_add_smul, ← sigma_mul hU (exp_mem_UJ hX _)
        (exp_mem_UJ hX _), ← exp_add_smul, neg_add, add_comm h t]
  have h10 := const_of_slope hπ.withSeminorms f hslope
  simp only [hf, neg_zero, zero_smul, NormedSpace.exp_zero, sigma_one hU, hπ.map_one] at h10
  have h11 := congrArg (π (NormedSpace.exp ((1 : ℝ) • X))) h10
  rw [hmulπ _ (exp_mem_UJ hX _) _ (exp_mem_UJ hX _), ← exp_add_smul, add_neg_cancel, zero_smul,
    NormedSpace.exp_zero, hπ.map_one, one_smul] at h11
  simpa using h11

end PositivityTheory.CW
end
end

