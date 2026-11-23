module

public import Mathlib
public import ReciprocityTheory.SemistableReduction.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRapidFourierSeriesOfIntPeriodic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOfFiniteOfClosedFibres
section
open Filter Metric Set
open scoped Topology

namespace GlobalTheory.ThetaFamily

theorem exists_quotient_closure {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] {W : Set (V × V')}
    {f θ : V × V' → ℂ} (hW : IsOpen W) (hf : DifferentiableOn ℂ f W) (hθ : DifferentiableOn ℂ θ W) {S : Set V}
    (hS : ∀ b ∈ S, ∃ F : V' → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W} ∧ ∀ z, (b, z) ∈ W → F z * θ (b, z) = f (b, z))
    {w : V × V'} (hw : w ∈ W) (hfr : ∃ᶠ z in 𝓝 w.2, θ (w.1, z) ≠ 0) :
    ∃ (U : Set (V × V')) (G : V × V' → ℂ), IsOpen U ∧ w ∈ U ∧ U ⊆ W ∧ DifferentiableOn ℂ G U ∧
      ∀ y ∈ U, y.1 ∈ closure S → G y * θ y = f y := by
  obtain ⟨v, r, hr, hin, hne⟩ := exists_circle_ne_zero_of_frequently_ne_zero
    (S := {z | (w.1, z) ∈ W}) (g := fun z => θ (w.1, z)) (z₀ := w.2)
    ((hW.preimage (f := fun z => (w.1, z)) (by fun_prop)).mem_nhds hw)
    (hθ.comp (f := fun z => (w.1, z)) (by fun_prop) fun z hz => hz) hfr
  let p : V × V' → ℂ → V × V' := fun y t => (y.1, y.2 + t • v)
  have hp : Continuous fun q : (V × V') × ℂ => p q.1 q.2 := by fun_prop
  have h1 : ∀ᶠ y in 𝓝 w, ∀ t ∈ closedBall (0 : ℂ) r, p y t ∈ W :=
    (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht =>
      hp.continuousAt.eventually (hW.mem_nhds (hin t ht))
  have h2 : ∀ᶠ y in 𝓝 w, ∀ t ∈ sphere (0 : ℂ) r, θ (p y t) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => by
      have hc : ContinuousAt θ (p w t) :=
        (hθ.differentiableAt (hW.mem_nhds (hin t (sphere_subset_closedBall ht)))).continuousAt
      exact (ContinuousAt.comp (g := θ) (f := fun q : (V × V') × ℂ => p q.1 q.2) (x := (w, t))
        hc hp.continuousAt).eventually_ne (hne t ht)
  obtain ⟨U, hU, hUo, hwU⟩ := _root_.eventually_nhds_iff.1 (h1.and h2)
  have hp0 : ∀ y, p y 0 = y := fun y => by simp [p]
  have hUW : U ⊆ W := fun y hy => hp0 y ▸ (hU y hy).1 0 (mem_closedBall_self hr.le)
  have hcm : ∀ s : ℝ, circleMap 0 r s ∈ sphere (0 : ℂ) r := fun s =>
    circleMap_mem_sphere 0 hr.le s
  have hG := (differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (s : ℝ) (y : V × V') => f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)))
    (a := 0) (b := 2 * Real.pi) hUo ?_ ?_).1
  · obtain ⟨G, hGd, hEq⟩ : ∃ G : V × V' → ℂ, DifferentiableOn ℂ G U ∧ ∀ y ∈ U, y.1 ∈ S → G y * θ y = f y := by
      refine ⟨fun y => ((2 * Real.pi)⁻¹ : ℝ) • ∫ s in (0 : ℝ)..2 * Real.pi,
        f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)), hG.const_smul ((2 * Real.pi)⁻¹ : ℝ), fun y hy hyS => ?_⟩
      obtain ⟨F, hFd, hF⟩ := hS _ hyS
      have hd : DifferentiableOn ℂ (fun t : ℂ => F (y.2 + t • v)) (closedBall 0 r) :=
        hFd.comp (f := fun t : ℂ => y.2 + t • v) (by fun_prop) fun t ht => (hU y hy).1 t ht
      have hdc : DiffContOnCl ℂ (fun t : ℂ => F (y.2 + t • v)) (ball 0 |r|) := by
        apply DifferentiableOn.diffContOnCl
        rwa [abs_of_pos hr, closure_ball _ hr.ne']
      have hav := hdc.circleAverage
      rw [Real.circleAverage_def, zero_smul, add_zero] at hav
      rw [← hF y.2 (hUW hy), ← hav]
      beta_reduce
      congr 2
      refine intervalIntegral.integral_congr fun s _ => ?_
      have hs := hcm s
      show _ / _ = _
      rw [div_eq_iff ((hU y hy).2 _ hs)]
      exact (hF _ ((hU y hy).1 _ (sphere_subset_closedBall hs))).symm
    refine ⟨U, G, hUo, hwU, hUW, hGd, fun y hy hyS => ?_⟩
    have hc : Continuous fun b : V => (b, y.2) := by fun_prop
    have c1 : ContinuousAt (fun b : V => G (b, y.2) * θ (b, y.2)) y.1 :=
      ContinuousAt.comp (g := fun q => G q * θ q) (f := fun b : V => (b, y.2)) (x := y.1)
        ((hGd.mul (hθ.mono hUW)).differentiableAt (hUo.mem_nhds hy)).continuousAt hc.continuousAt
    have c2 : ContinuousAt (fun b : V => f (b, y.2)) y.1 :=
      ContinuousAt.comp (g := f) (f := fun b : V => (b, y.2)) (x := y.1)
        (hf.differentiableAt (hW.mem_nhds (hUW hy))).continuousAt hc.continuousAt
    have hev : ∀ᶠ b in 𝓝 y.1, (b, y.2) ∈ U := hc.continuousAt.eventually (hUo.mem_nhds hy)
    exact tendsto_nhds_unique_of_frequently_eq c1 c2
      (((mem_closure_iff_frequently.1 hyS).and_eventually hev).mono fun b hb => hEq _ hb.2 hb.1)
  · have hq : Continuous fun q : ℝ × (V × V') => p q.2 (circleMap 0 r q.1) :=
      hp.comp (f := fun q : ℝ × (V × V') => (q.2, circleMap 0 r q.1)) (by fun_prop)
    have hm : ∀ q : ℝ × (V × V'), q ∈ uIcc 0 (2 * Real.pi) ×ˢ U →
        p q.2 (circleMap 0 r q.1) ∈ W := fun q hq =>
      (hU _ hq.2).1 _ (sphere_subset_closedBall (hcm _))
    exact (hf.continuousOn.comp hq.continuousOn hm).div
      (hθ.continuousOn.comp hq.continuousOn hm) fun q hq => (hU _ hq.2).2 _ (hcm _)
  · intro s _
    have hq : Differentiable ℂ fun y : V × V' => p y (circleMap 0 r s) := by fun_prop
    have hm : ∀ y ∈ U, p y (circleMap 0 r s) ∈ W := fun y hy =>
      (hU _ hy).1 _ (sphere_subset_closedBall (hcm _))
    simp only [div_eq_mul_inv]
    exact (hf.comp hq.differentiableOn hm).mul
      ((hθ.comp hq.differentiableOn hm).inv fun y hy => (hU _ hy).2 _ (hcm _))

theorem exists_entire_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {θ θ' : E → ℂ}
    (hfr : ∀ z, ∃ᶠ w in 𝓝 z, θ' w ≠ 0)
    (h : ∀ z, ∃ ρ : E → ℂ, ρ z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ' w = θ w) :
    ∃ ρ : E → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ z, ρ z * θ' z = θ z := by
  choose ρ h0 h using h
  refine ⟨fun z => ρ z z, fun z => ?_, h0, fun z => (h z).self_of_nhds.2⟩
  refine (h z).self_of_nhds.1.congr_of_eventuallyEq ?_
  filter_upwards [(h z).eventually_nhds] with w hw
  refine tendsto_nhds_unique_of_frequently_eq (h w).self_of_nhds.1.continuousAt hw.self_of_nhds.1.continuousAt ?_
  exact (((hfr w).and_eventually (h w)).and_eventually hw).mono fun u hu =>
    mul_right_cancel₀ hu.1.1 (hu.1.2.2.trans hu.2.2.symm)

theorem eq_of_finite_of_closed_fibres {X Y : Type*} [TopologicalSpace X] {B : Set X} (hB : IsPreconnected B)
    {C : Set Y} (hC : C.Finite) (c : X → Y) (hc : ∀ b ∈ B, c b ∈ C)
    (h : ∀ k ∈ C, ∀ b ∈ B, b ∈ closure {b' ∈ B | c b' = k} → c b = k) : ∀ b ∈ B, ∀ b' ∈ B, c b = c b' := by
  have : PreconnectedSpace B := Subtype.preconnectedSpace hB
  have hl : IsLocallyConstant fun b : B => c b := fun s => by
    have e : ((fun b : B => c b) ⁻¹' s)ᶜ = ⋃ k ∈ C \ s, (Subtype.val ⁻¹' closure {b' ∈ B | c b' = k} : Set B) := by
      ext b
      simp only [mem_compl_iff, mem_preimage, mem_iUnion, mem_diff, exists_prop]
      exact ⟨fun hb => ⟨c b, ⟨hc b b.2, hb⟩, subset_closure ⟨b.2, rfl⟩⟩,
        fun ⟨k, hk, hb⟩ => (h k hk.1 b b.2 hb).symm ▸ hk.2⟩
    rw [← isClosed_compl_iff, e]
    exact (hC.subset diff_subset).isClosed_biUnion fun k _ => isClosed_closure.preimage continuous_subtype_val
  exact fun b hb b' hb' => hl.apply_eq_of_preconnectedSpace ⟨b, hb⟩ ⟨b', hb'⟩

theorem frequently_ne_zero_of_entire {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {θ : E → ℂ} (hd : Differentiable ℂ θ) (h0 : θ ≠ 0) (z : E) : ∃ᶠ w in 𝓝 z, θ w ≠ 0 := by
  intro h
  refine h0 (funext fun w => ?_)
  exact (SCV.analyticOnNhd_of_differentiable hd univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ z) (h.mono fun _ hu => not_not.1 hu) (mem_univ w)

theorem differentiableOn_left_inverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : Type} [Fintype n]
    [DecidableEq n] {B : Set V} {M h : V → Matrix n n ℂ} (hM : ∀ i j, DifferentiableOn ℂ (fun b => M b i j) B)
    (hh : ∀ b ∈ B, h b * M b = 1) (i j : n) : DifferentiableOn ℂ (fun b => h b i j) B := by
  have hdet : ∀ {N : V → Matrix n n ℂ}, (∀ i j, DifferentiableOn ℂ (fun b => N b i j) B) →
      DifferentiableOn ℂ (fun b => (N b).det) B := fun {N} hN => by
    exact ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of (F := fun i j b => N b i j) hN
  have hne : ∀ b ∈ B, (M b).det ≠ 0 := fun b hb => (Matrix.isUnit_det_of_left_inverse (hh b hb)).ne_zero
  refine (((hdet hM).inv hne).mul (hdet (N := fun b => (M b).updateRow j (Pi.single i 1)) fun k l => ?_)).congr
    fun b hb => ?_
  · by_cases hk : k = j
    · simp only [hk, Matrix.updateRow_self]; exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hk]; exact hM k l
  · rw [← Matrix.inv_eq_left_inv (hh b hb), Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply,
      Ring.inverse_eq_inv', smul_eq_mul]
    rfl

end GlobalTheory.ThetaFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorusEllipticSystemSolvable
section
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory
namespace TorusElliptic

def Rapid {n : ℕ} (c : (Fin n → ℤ) → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C

noncomputable def ch {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) : ℂ :=
  cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))

lemma norm_ch {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) : ‖ch ν x‖ = 1 := by
  have : (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = ((2 * π * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [ch, this, Complex.norm_exp_ofReal_mul_I]

lemma ch_periodic {n : ℕ} (ν μ : Fin n → ℤ) (x : Fin n → ℝ) :
    ch ν (x + fun k => (μ k : ℝ)) = ch ν x := by
  have : (2 * π * I * ∑ k, (ν k : ℂ) * (((x + fun k => (μ k : ℝ)) k : ℝ) : ℂ))
      = (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) + ((∑ k, ν k * μ k : ℤ) : ℂ) * (2 * π * I) := by
    simp only [Pi.add_apply]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rw [ch, this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ch]

lemma summable_int_weight : Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have h : Summable (fun j : ℕ => 1 / (1 + (j : ℝ)) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    refine this.congr fun j => ?_
    push_cast; rw [add_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h

lemma summable_pi_weight (n : ℕ) :
    Summable (fun ν : Fin n → ℤ => ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2) := by
  classical
  refine summable_of_sum_le (c := ∏ _k : Fin n, ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2)
    (fun ν => by positivity) fun s => ?_
  calc ∑ ν ∈ s, ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2
      ≤ ∑ ν ∈ Fintype.piFinset (fun k => (s.image (fun ν => ν k) : Finset ℤ)),
          ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun ν hν => ?_) (fun _ _ _ => by positivity)
        exact Fintype.mem_piFinset.2 fun k => Finset.mem_image_of_mem _ hν
    _ = ∏ k, ∑ j ∈ (s.image (fun ν => ν k) : Finset ℤ), 1 / (1 + |(j : ℝ)|) ^ 2 := by
        exact (Finset.prod_univ_sum (fun k => (s.image (fun ν => ν k) : Finset ℤ))
          (fun _ j => 1 / (1 + |(j : ℝ)|) ^ 2)).symm
    _ ≤ _ := by
        refine Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
        exact summable_int_weight.sum_le_tsum _ (fun _ _ => by positivity)

lemma Rapid.summable {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) :
    Summable (fun ν => ‖c ν‖) := by
  obtain ⟨C, hC⟩ := h (2 * n)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ν => ?_)
    ((summable_pi_weight n).mul_left C)
  have h1 : ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by
    calc ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ ∏ _k : Fin n, (1 + ∑ k, |(ν k : ℝ)|) ^ 2 := by
          refine Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
          gcongr
          exact Finset.single_le_sum (f := fun k => |(ν k : ℝ)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ k)
      _ = _ := by simp [pow_mul]
  rw [Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div, le_div_iff₀ (by positivity)]
  exact le_trans (by gcongr) (hC ν)

lemma Rapid.mul {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (z : ℂ) (j : Fin n) :
    Rapid (fun ν => z * (ν j : ℂ) * c ν) := by
  intro N
  obtain ⟨C, hC⟩ := h (N + 1)
  refine ⟨‖z‖ * C, fun ν => ?_⟩
  have h1 : ‖(ν j : ℂ)‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := by
    have := Finset.single_le_sum (f := fun k => |(ν k : ℝ)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
    rw [Complex.norm_intCast]
    linarith
  calc ‖z * (ν j : ℂ) * c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N
      = ‖z‖ * (‖c ν‖ * ((1 + ∑ k, |(ν k : ℝ)|) ^ N * ‖(ν j : ℂ)‖)) := by
        simp only [norm_mul]; ring
    _ ≤ ‖z‖ * (‖c ν‖ * ((1 + ∑ k, |(ν k : ℝ)|) ^ N * (1 + ∑ k, |(ν k : ℝ)|))) := by gcongr
    _ ≤ ‖z‖ * C := by rw [← pow_succ]; gcongr; exact hC ν

lemma summable_ch {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Summable (fun ν => ‖c ν‖))
    (x : Fin n → ℝ) : Summable (fun ν => c ν * ch ν x) := by
  refine Summable.of_norm ?_
  simpa [norm_ch] using h

lemma summable_symb {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) :
    Summable (fun ν : Fin n → ℤ => ‖2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν‖) := by
  have : Summable (fun ν : Fin n → ℤ => ∑ k, (q k * (2 * π * I)) * (ν k : ℂ) * c ν) :=
    summable_sum fun k _ => (h.mul _ k).summable.of_norm
  refine (summable_norm_iff.2 this).congr fun ν => ?_
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma sum_fderiv {n : ℕ} {c : (Fin n → ℤ) → ℂ} (h : Rapid c) (q : Fin n → ℂ) (x : Fin n → ℝ) :
    ∑ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1)
      = ∑' ν, 2 * π * I * (∑ k, q k * (ν k : ℂ)) * c ν * ch ν x := by
  have h1 : ∀ k, q k * fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * ch ν x) x (Pi.single k 1)
      = ∑' ν : Fin n → ℤ, (q k * (2 * π * I)) * (ν k : ℂ) * c ν * ch ν x := by
    intro k
    have := (GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n c h).2 x k
    unfold ch
    rw [this, ← tsum_mul_left]
    exact tsum_congr fun ν => by ring
  simp_rw [h1]
  rw [← Summable.tsum_finsetSum fun k _ => summable_ch (h.mul _ k).summable x]
  refine tsum_congr fun ν => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma symbol_lower {n m : ℕ} (p : Fin m → Fin n → ℂ)
    (hp : ∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Fin n → ℤ, ν ≠ 0 → ∃ a, ε ≤ ‖∑ k, p a k * (ν k : ℂ)‖ := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    { toFun := fun ξ a => ∑ k, p a k * (ξ k : ℂ)
      map_add' := fun ξ η => by
        funext a; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r ξ => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        push_cast
        exact Finset.sum_congr rfl fun k _ => by ring }
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ξ hξ
    exact hp ξ fun a => congrFun hξ a
  obtain ⟨K, hK, hA⟩ := L.exists_antilipschitzWith hL
  have hK' : (0 : ℝ) < K := hK
  refine ⟨1 / K, by positivity, fun ν hν => ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 : ‖L (fun k => (ν k : ℝ))‖ < 1 / K := by
    rw [pi_norm_lt_iff (by positivity)]
    intro a
    simpa [L] using hcon a
  have h2 := hA.le_mul_dist (fun k => (ν k : ℝ)) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h2
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hν
  have h3 : (1 : ℝ) ≤ ‖(fun k => (ν k : ℝ))‖ := by
    refine le_trans ?_ (norm_le_pi_norm (fun k => (ν k : ℝ)) k)
    rw [Real.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hk
  rw [lt_div_iff₀ hK'] at h1
  linarith

end TorusElliptic


open TorusElliptic in
theorem torus_elliptic_system_solvable : ∀ (n m : ℕ) (p : Fin m → Fin n → ℂ), (∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) → ∀ w : Fin m → (Fin n → ℝ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ (∀ (ν : Fin n → ℤ) x, w a (x + fun k => (ν k : ℝ)) = w a x)) → (∀ a b x, ∑ k, p a k * fderiv ℝ (w b) x (Pi.single k 1) = ∑ k, p b k * fderiv ℝ (w a) x (Pi.single k 1)) → ∃ (t : Fin m → ℂ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (ν : Fin n → ℤ) x, f (x + fun k => (ν k : ℝ)) = f x) ∧ ∀ a x, ∑ k, p a k * fderiv ℝ f x (Pi.single k 1) = w a x - t a := by
  classical
  intro n m p hp w hw hcomp
  choose c hc hwc using fun a => GlobalTheory.exists_rapid_fourierSeries_of_int_periodic n (w a) (hw a).1 (hw a).2
  have hc' : ∀ a, Rapid (c a) := hc
  have hwf : ∀ a, w a = fun x => ∑' ν, c a ν * ch ν x := fun a => funext (hwc a)
  have h2pi : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hsym : ∀ a b ν, (∑ k, p a k * (ν k : ℂ)) * c b ν = (∑ k, p b k * (ν k : ℂ)) * c a ν := by
    intro a b ν
    have hs1 := summable_symb (hc' b) (p a)
    have hs2 := summable_symb (hc' a) (p b)
    have := GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin n (fun ν => 2 * π * I * (∑ k, p a k * (ν k : ℂ)) * c b ν
      - 2 * π * I * (∑ k, p b k * (ν k : ℂ)) * c a ν)
      (summable_norm_iff.2 (hs1.of_norm.sub hs2.of_norm)) (fun x => by
        have h := hcomp a b x
        rw [hwf a, hwf b, sum_fderiv (hc' b), sum_fderiv (hc' a)] at h
        have h' := (summable_ch hs1 x).tsum_sub (summable_ch hs2 x)
        rw [h, sub_self] at h'
        rw [← h']
        exact tsum_congr fun ν => by unfold ch; ring) ν
    apply mul_left_cancel₀ h2pi
    linear_combination this
  obtain ⟨ε, hε, hlow⟩ := symbol_lower p hp
  choose α hα using hlow
  let d : (Fin n → ℤ) → ℂ := fun ν =>
    if h : ν = 0 then 0 else c (α ν h) ν / (2 * π * I * ∑ k, p (α ν h) k * (ν k : ℂ))
  have hd : Rapid d := by
    intro N
    choose C hC using fun a => hc' a N
    have hC0 : ∀ a, 0 ≤ C a := fun a => le_trans (by positivity) (hC a 0)
    refine ⟨(∑ a, C a) / (‖(2 * π * I : ℂ)‖ * ε), fun ν => ?_⟩
    have hn : 0 < ‖(2 * π * I : ℂ)‖ := norm_pos_iff.2 h2pi
    have hS : 0 ≤ ∑ a, C a := Finset.sum_nonneg fun a _ => hC0 a
    by_cases h : ν = 0
    · simp only [d, dif_pos h, norm_zero, zero_mul]
      positivity
    · simp only [d, dif_neg h]
      rw [norm_div, norm_mul (2 * π * I : ℂ), div_mul_eq_mul_div]
      have h1 := Finset.single_le_sum (f := C) (fun a _ => hC0 a) (Finset.mem_univ (α ν h))
      have h2 := hα ν h
      have h3 := hC (α ν h) ν
      gcongr
      linarith
  refine ⟨fun a => c a 0, fun x => ∑' ν, d ν * ch ν x, (GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n d hd).1, ?_, ?_⟩
  · intro μ x
    simp only [ch_periodic]
  · intro a x
    rw [sum_fderiv hd, hwf a]
    have hs := summable_ch (hc' a).summable x
    have h0 := hs.tsum_eq_add_tsum_ite 0
    have hch : ch (0 : Fin n → ℤ) x = 1 := by simp [ch]
    rw [hch, mul_one] at h0
    simp only []
    rw [h0, add_sub_cancel_left]
    refine tsum_congr fun ν => ?_
    by_cases h : ν = 0
    · simp only [d, dif_pos h, if_pos h, mul_zero, zero_mul]
    · simp only [d, dif_neg h, if_neg h]
      have h2 : (∑ k, p (α ν h) k * (ν k : ℂ)) ≠ 0 := by
        intro h0
        have := hα ν h
        rw [h0, norm_zero] at this
        linarith
      have h3 := hsym a (α ν h) ν
      congr 1
      rw [mul_div_assoc', div_eq_iff (mul_ne_zero h2pi h2)]
      linear_combination (2 * π * I) * h3

end GlobalTheory
end

