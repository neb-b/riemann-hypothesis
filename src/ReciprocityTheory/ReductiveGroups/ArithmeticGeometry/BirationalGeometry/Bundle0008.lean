module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter Topology

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def bsmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => c p.1 * z p

theorem eval_bsmul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (bsmul c z) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∈ s.support := support_map_subset _ _ hm
  have hblk := hs m hm'
  simp only [bsmul, mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
    rw [← hblk k, Finset.prod_pow_eq_pow_sum]
  rw [hc]
  ring

theorem logNorm_bsmul (A : HermLine ι) {s : MRing ι} {a : K → ℕ} (hA : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNorm A s (bsmul c z) = logNorm A s z := by
  unfold logNorm
  rw [eval_bsmul_of_isMultiHomog hs]
  have hh : A.h (bsmul c z) = (∏ k, ‖c k‖ ^ (a k)) * A.h z := by
    rw [show bsmul c z = fun p => c p.1 * z p from rfl, A.smul c z hc]
    simp [hA, zpow_natCast]
  rw [hh, norm_mul, norm_prod]
  simp only [norm_pow]
  rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))]

theorem prod_update_eq [DecidableEq K] (z : (Σ k, ι k) → ℂ) (i0 : (k : K) → ι k) (k : K) (i : ι k) :
    ∏ k', z ⟨k', Function.update i0 k i k'⟩ = z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k' hk' => ?_
    simp [Finset.ne_of_mem_erase hk']

theorem eq_bsmul_of_segre_eq {z z' : (Σ k, ι k) → ℂ} (i0 : (k : K) → ι k)
    (h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0) (hs : segre z = segre z') :
    (∀ k, z' ⟨k, i0 k⟩ ≠ 0) ∧ z' = bsmul (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z := by
  classical
  have hseg : ∀ i : (k : K) → ι k, ∏ k, z ⟨k, i k⟩ = ∏ k, z' ⟨k, i k⟩ := fun i => congrFun hs i
  have hP0 : ∏ k, z ⟨k, i0 k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => h0 k
  have h0' : ∀ k, z' ⟨k, i0 k⟩ ≠ 0 := by
    intro k
    have h1 : ∏ k, z' ⟨k, i0 k⟩ ≠ 0 := by rw [← hseg i0]; exact hP0
    exact Finset.prod_ne_zero_iff.1 h1 k (Finset.mem_univ _)
  refine ⟨h0', ?_⟩
  funext ⟨k, i⟩
  simp only [bsmul]
  have hA' : z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k i, ← prod_update_eq z' i0 k i]
    exact hseg _
  have hB' : z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k (i0 k), ← prod_update_eq z' i0 k (i0 k)]
    exact hseg _
  have hP' : ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => h0' k'
  rw [div_mul_eq_mul_div, eq_div_iff (h0 k)]
  apply mul_right_cancel₀ hP'
  linear_combination (-(z ⟨k, i0 k⟩)) * hA' + z ⟨k, i⟩ * hB'

end Alg

section Hess

variable {e : ℕ}

theorem fderiv_re_apply {h : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hh : DifferentiableAt ℂ h y)
    (v : Fin e → ℂ) : fderiv ℝ (fun y' => (h y').re) y v = (fderiv ℂ h y v).re := by
  have hd : HasFDerivAt (fun y' => (h y').re)
      (Complex.reCLM.comp ((fderiv ℂ h y).restrictScalars ℝ)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hh.hasFDerivAt.restrictScalars ℝ)
  rw [hd.fderiv]
  rfl

theorem hess_re {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hG : AnalyticAt ℂ G y) (v w : Fin e → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y v w = (fderiv ℂ (fderiv ℂ G) y v w).re := by
  let Φ : ((Fin e → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin e → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin e → ℂ) ℂ ℝ ℝ)
  have hΦ : ∀ L : (Fin e → ℂ) →L[ℂ] ℂ, ∀ u, Φ L u = (L u).re := fun L u => rfl
  have heq : fderiv ℝ (fun y' => (G y').re) =ᶠ[𝓝 y] fun y' => Φ (fderiv ℂ G y') := by
    filter_upwards [hG.eventually_analyticAt] with y' hy'
    ext u
    rw [fderiv_re_apply hy'.differentiableAt u, hΦ]
  have hD : HasFDerivAt (fderiv ℂ G) (fderiv ℂ (fderiv ℂ G) y) y :=
    hG.fderiv.differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun y' => Φ (fderiv ℂ G y'))
      (Φ.comp ((fderiv ℂ (fderiv ℂ G) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hD.restrictScalars ℝ)
  rw [heq.fderiv_eq, h2.fderiv]
  rfl

theorem cxHessian_add_re {φ : (Fin e → ℂ) → ℝ} {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (C : ℝ)
    (hφ : ContDiffAt ℝ 2 φ y) (hG : AnalyticAt ℂ G y) :
    cxHessian (fun y' => φ y' + (G y').re + C) y = cxHessian φ y := by
  have hre2 : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hG.contDiffAt.restrict_scalars ℝ)
  have hφev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ φ y' :=
    (hφ.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have hreev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ (fun y' => (G y').re) y' :=
    (hre2.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => φ y' + (G y').re + C) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ φ y' + fderiv ℝ (fun y' => (G y').re) y' := by
    filter_upwards [hφev, hreev] with y' h1 h2
    rw [fderiv_add_const]
    exact (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdre : DifferentiableAt ℝ (fderiv ℝ (fun y' => (G y').re)) y :=
    (hre2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsum : fderiv ℝ (fderiv ℝ (fun y' => φ y' + (G y').re + C)) y =
      fderiv ℝ (fderiv ℝ φ) y + fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y := by
    rw [heq.fderiv_eq]
    exact (hdφ.hasFDerivAt.add hdre.hasFDerivAt).fderiv
  have hH := hess_re hG
  have k1 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) (Complex.I • v) =
      - fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u v := by
    intro u v
    rw [hH, hH]
    simp [map_smul, ← mul_assoc]
  have k2 : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y u (Complex.I • v) =
      fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y (Complex.I • u) v := by
    intro u v
    rw [hH, hH]
    simp [map_smul]
  ext i j
  simp only [cxHessian, hsum, ContinuousLinearMap.add_apply, k1, k2]
  push_cast
  ring

theorem cxHessian_congr {f g : (Fin e → ℂ) → ℝ} {y : Fin e → ℂ} (h : f =ᶠ[𝓝 y] g) :
    cxHessian f y = cxHessian g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := h.fderiv.fderiv_eq
  unfold cxHessian
  rw [h2]

end Hess

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

def secSet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (B : Set (Fin e → ℂ)) : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) :=
  {G | (∀ y ∉ B, G y = 0) ∧ DifferentiableOn ℂ G B ∧ ∀ y ∈ B, G y ∈ fibre P Ψ y}

theorem coincide_null (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {c : Fin e → ℂ} {r : ℝ}
    {G G' : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} (hG : G ∈ secSet P Ψ (ball c r))
    (hG' : G' ∈ secSet P Ψ (ball c r)) (hne : G ≠ G') :
    volume {y | y ∈ ball c r ∧ G y = G' y} = 0 := by
  obtain ⟨y0, hy0⟩ : ∃ y0, G y0 ≠ G' y0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  have hy0b : y0 ∈ ball c r := by
    by_contra hb
    exact hy0 (by rw [hG.1 y0 hb, hG'.1 y0 hb])
  obtain ⟨i, hi⟩ : ∃ i, G y0 i ≠ G' y0 i := by
    by_contra hcon
    push_neg at hcon
    exact hy0 (funext hcon)
  set f : (Fin e → ℂ) → ℂ := fun y => G y i - G' y i with hf
  have hdiff : DifferentiableOn ℂ f (ball c r) := by
    have h1 : DifferentiableOn ℂ (fun y => G y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG.2.1 y hy)) i
    have h2 : DifferentiableOn ℂ (fun y => G' y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG'.2.1 y hy)) i
    exact h1.sub h2
  have han : AnalyticOnNhd ℂ f (ball c r) := hA e (ball c r) f isOpen_ball hdiff
  have hnull := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball (convex_ball c r).isPreconnected han
    ⟨y0, hy0b, sub_ne_zero.2 hi⟩
  refine measure_mono_null ?_ hnull
  intro y hy
  exact ⟨hy.1, by simp [f, hy.2]⟩

theorem secSet_finite (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite)
    (c : Fin e → ℂ) {r : ℝ} (hr : 0 < r) : (secSet P Ψ (ball c r)).Finite := by
  by_contra hinf
  have hS : (secSet P Ψ (ball c r)).Infinite := hinf
  have key : ∀ m : ℕ, volume {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} = 0 := by
    intro m
    obtain ⟨F, hFS, hFc⟩ := hS.exists_subset_card_eq m
    have hnull : volume (⋃ G ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)), ⋃ G' ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)),
        {y | G ≠ G' ∧ y ∈ ball c r ∧ G y = G' y}) = 0 := by
      refine (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G hG =>
        (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA (hFS hG) (hFS hG') h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    refine measure_mono_null (fun y hy => ?_) hnull
    obtain ⟨hyb, hlt⟩ := hy
    by_contra hnot
    have hinj : Set.InjOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) := fun G hG G' hG' heq => by
      by_contra hne
      exact hnot (Set.mem_iUnion₂.2 ⟨G, hG, Set.mem_iUnion₂.2 ⟨G', hG', ⟨hne, hyb, heq⟩⟩⟩)
    have hmaps : Set.MapsTo (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) (fibre P Ψ y) := fun G hG => (hFS hG).2.2 y hyb
    have hle := Set.ncard_le_ncard_of_injOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) hmaps hinj (hfin y)
    rw [Set.ncard_coe_finset, hFc] at hle
    omega
  have hcover : ball c r ⊆ ⋃ m : ℕ, {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} := fun y hy =>
    Set.mem_iUnion.2 ⟨(fibre P Ψ y).ncard + 1, hy, Nat.lt_succ_self _⟩
  have h0 : volume (ball c r) = 0 := measure_mono_null hcover (measure_iUnion_null key)
  exact (Metric.measure_ball_pos volume c hr).ne' h0

def badSet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set (Fin e → ℂ) :=
  {y | ∃ w γ γ', IsSheet P Ψ y w γ ∧ IsSheet P Ψ y w γ' ∧
    ¬ ((fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y'))}

theorem segre_differentiableAt {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : DifferentiableAt ℂ γ y) : DifferentiableAt ℂ (fun y' => segre (γ y')) y := by
  rw [differentiableAt_pi]
  intro i
  simp only [segre]
  classical
  have key : ∀ s : Finset K, DifferentiableAt ℂ (fun x => ∏ k ∈ s, γ x ⟨k, i k⟩) y := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact ((differentiableAt_pi.1 hγ) ⟨a, i a⟩).mul ih
  exact key Finset.univ

theorem mem_secSet_of_sheet {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {B : Set (Fin e → ℂ)}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : ∀ y' ∈ B, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y') :
    B.indicator (fun y' => segre (γ y')) ∈ secSet P Ψ B := by
  refine ⟨fun y hy => Set.indicator_of_notMem hy _, ?_, fun y hy => ?_⟩
  · have hd : DifferentiableOn ℂ (fun y' => segre (γ y')) B := fun y' hy' =>
      (segre_differentiableAt (h y' hy').1).differentiableWithinAt
    exact hd.congr (fun y' hy' => Set.indicator_of_mem hy' _)
  · rw [Set.indicator_of_mem hy]
    exact ⟨γ y, (h y hy).2.1, rfl, (h y hy).2.2⟩

theorem badSet_null (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite) :
    volume (badSet P Ψ) = 0 := by
  obtain ⟨Dc, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  let S : (Fin e → ℂ) → ℚ → Set (Fin e → ℂ) := fun d q =>
    ⋃ G ∈ secSet P Ψ (ball d q), ⋃ G' ∈ secSet P Ψ (ball d q), {y | G ≠ G' ∧ y ∈ ball d (q : ℝ) ∧ G y = G' y}
  have hS : ∀ d q, volume (S d q) = 0 := by
    intro d q
    by_cases hq : (0 : ℝ) < q
    · have hfinS := secSet_finite hA hfin d hq
      refine (measure_biUnion_null_iff hfinS.countable).2 fun G hG =>
        (measure_biUnion_null_iff hfinS.countable).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA hG hG' h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    · have hempty : ball d (q : ℝ) = ∅ := Metric.ball_eq_empty.2 (not_lt.1 hq)
      refine measure_mono_null ?_ measure_empty
      intro y hy
      simp only [S, Set.mem_iUnion] at hy
      obtain ⟨G, _, G', _, _, hyb, _⟩ := hy
      rw [hempty] at hyb
      exact hyb
  have hcount : volume (⋃ d ∈ Dc, ⋃ q : ℚ, S d q) = 0 :=
    (measure_biUnion_null_iff hDc).2 fun d _ => measure_iUnion_null fun q => hS d q
  refine measure_mono_null ?_ hcount
  intro y hy
  obtain ⟨w, γ, γ', ⟨hγw, hγev⟩, ⟨hγ'w, hγ'ev⟩, hne⟩ := hy
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hγev.and hγ'ev)
  obtain ⟨q, hq0, hqε⟩ : ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < ε / 2 := by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (half_pos hε)
    exact ⟨q, h1, h2⟩
  obtain ⟨d, hdD, hd⟩ := hDd.exists_mem_open isOpen_ball ⟨y, mem_ball_self hq0⟩
  have hdy : dist y d < q := by
    rw [dist_comm]
    exact hd
  have hyB : y ∈ ball d (q : ℝ) := by
    rw [mem_ball]
    exact hdy
  have hBsub : ball d (q : ℝ) ⊆ ball y ε := by
    intro y' hy'
    rw [mem_ball] at hy' ⊢
    calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
      _ < q + q := by
        rw [dist_comm d y]
        exact add_lt_add hy' hdy
      _ < ε := by linarith
  have hG : (ball d (q : ℝ)).indicator (fun y' => segre (γ y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).1)
  have hG' : (ball d (q : ℝ)).indicator (fun y' => segre (γ' y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).2)
  refine Set.mem_iUnion₂.2 ⟨d, hdD, Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨_, hG,
    Set.mem_iUnion₂.2 ⟨_, hG', ?_, hyB, ?_⟩⟩⟩⟩
  · intro heq
    apply hne
    filter_upwards [isOpen_ball.mem_nhds hyB] with y' hy'
    have h1 := congrFun heq y'
    simpa [Set.indicator_of_mem hy'] using h1
  · simp [Set.indicator_of_mem hyB, hγw, hγ'w]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

