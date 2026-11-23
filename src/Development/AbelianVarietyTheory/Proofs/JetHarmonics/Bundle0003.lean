module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeasurePreservingSnocMeasurableEquiv
section
open MeasureTheory Filter Topology

namespace GlobalTheory

noncomputable def snocMeasurableEquiv (n : ℕ) : ((Fin n → ℂ) × ℂ) ≃ᵐ (Fin (n + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n)).symm

lemma snocMeasurableEquiv_apply (n : ℕ) (p : (Fin n → ℂ) × ℂ) :
    snocMeasurableEquiv n p = Fin.snoc (α := fun _ => ℂ) p.1 p.2 := by
  simp [snocMeasurableEquiv, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
    Fin.insertNthEquiv, Fin.insertNth_last']

lemma measurePreserving_snocMeasurableEquiv (n : ℕ) :
    MeasurePreserving (snocMeasurableEquiv n)
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) volume := by
  have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.prodComm : ((Fin n → ℂ) × ℂ) ≃ᵐ (ℂ × (Fin n → ℂ)))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    Measure.measurePreserving_swap
  exact h2.trans h1

lemma ae_coords_ne_zero (n : ℕ) : ∀ᵐ c : Fin n → ℂ, ∀ i, c i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  exact Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℂ)) i 0

theorem iterated_integral_eq_integral_pi :
    ∀ (n : ℕ) (W : ℕ → ℂ → ℝ) (R : (j : ℕ) → (Fin j → ℂ) → ℝ), (∀ j t, 0 ≤ W j t) → (∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) → 0 ≤ R n c) → AEMeasurable (fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c) → (∀ j, j < n → ∀ c : Fin j → ℂ, (∀ i, c i ≠ 0) → Integrable (fun t : ℂ => W (j + 1) t * R (j + 1) (Fin.snoc c t)) ∧ R j c = ∫ t : ℂ, W (j + 1) t * R (j + 1) (Fin.snoc c t)) → Integrable (fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c) ∧ R 0 (fun i => i.elim0) = ∫ c : Fin n → ℂ, (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by
  intro n W R hW
  induction n with
  | zero =>
    intro _ _ _
    refine ⟨Integrable.of_finite, ?_⟩
    rw [integral_unique]
    have : (volume : Measure (Fin 0 → ℂ)).real Set.univ = 1 := by
      simp [Measure.real, volume_pi, Measure.pi_univ]
    rw [this]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, smul_eq_mul]
    exact congrArg _ (Subsingleton.elim _ _)
  | succ n ih =>
    intro hR hm hstep
    have hmp := measurePreserving_snocMeasurableEquiv n
    set T : (Fin (n + 1) → ℂ) → ℝ :=
      fun c => (∏ i : Fin (n + 1), W ((i : ℕ) + 1) (c i)) * R (n + 1) c with hT
    set F : (Fin n → ℂ) × ℂ → ℝ := fun p => T (snocMeasurableEquiv n p) with hF
    have hFm : AEStronglyMeasurable F
        ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) :=
      (hm.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving).aestronglyMeasurable
    have hFeq : ∀ (c : Fin n → ℂ) (t : ℂ), F (c, t) =
        (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) *
          (W (n + 1) t * R (n + 1) (Fin.snoc (α := fun _ => ℂ) c t)) := by
      intro c t
      simp only [hF, hT, snocMeasurableEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, Fin.val_castSucc, Fin.val_last, mul_assoc]
    have hpos : ∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) → ∀ᵐ t : ℂ,
        0 ≤ W (n + 1) t * R (n + 1) (Fin.snoc (α := fun _ => ℂ) c t) := by
      intro c hc
      have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
        simp [ae_iff]
      filter_upwards [h0] with t ht
      refine mul_nonneg (hW _ _) (hR _ ?_)
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using ht
      · simpa using hc i
    have hslice : ∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) →
        ∫ t, F (c, t) = (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by
      intro c hc
      simp only [hFeq]
      rw [integral_const_mul, (hstep n (Nat.lt_succ_self n) c hc).2]
    have hae : (fun c => ∫ t, F (c, t)) =ᵐ[volume]
        fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by
      filter_upwards [ae_coords_ne_zero n] with c hc using hslice c hc
    obtain ⟨hint, heq⟩ := ih
      (fun c hc => by
        rw [(hstep n (Nat.lt_succ_self n) c hc).2]
        exact integral_nonneg_of_ae (hpos c hc))
      (hFm.integral_prod_right'.aemeasurable.congr hae)
      (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    have hFi : Integrable F ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [integrable_prod_iff hFm]
      constructor
      · filter_upwards [ae_coords_ne_zero n] with c hc
        simp only [hFeq]
        exact (hstep n (Nat.lt_succ_self n) c hc).1.const_mul _
      · refine hint.congr ?_
        filter_upwards [ae_coords_ne_zero n] with c hc
        rw [← hslice c hc]
        refine integral_congr_ae ?_
        filter_upwards [hpos c hc] with t ht
        rw [Real.norm_of_nonneg]
        rw [hFeq]
        exact mul_nonneg (Finset.prod_nonneg fun i _ => hW _ _) ht
    refine ⟨?_, ?_⟩
    · exact (hmp.integrable_comp_emb (snocMeasurableEquiv n).measurableEmbedding).1 hFi
    · rw [heq, ← hmp.integral_comp' T, ← integral_congr_ae hae]
      exact (integral_prod F hFi).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemLpAndTendstoIntegralInnerOfEventuallyEq
section
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem memLp_and_tendsto_integral_inner_of_eventually_eq : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ℝ → X → E) (u : X → E) (h : X → ℝ), Integrable h μ → (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (a ε) μ) → (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ, ‖a ε x‖ ^ 2 ≤ h x) → (∀ᵐ x ∂μ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ε x = u x) → MemLp u 2 μ ∧ Tendsto (fun ε : ℝ => ∫ x, inner ℂ (a ε x) (u x) ∂μ) (𝓝[>] 0) (𝓝 (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ))) := by
  intro X _ μ E _ _ a u h hh hm hb he

  obtain ⟨s, hs⟩ := (𝓝[>] (0 : ℝ)).exists_seq_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.eventually (hm.and hb))
  have hs' : Tendsto (fun n => s (n + N)) atTop (𝓝[>] (0 : ℝ)) :=
    hs.comp (tendsto_add_atTop_nat N)
  have hev : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, a (s (n + N)) x = u x := by
    filter_upwards [he] with x hx
    exact hs'.eventually hx
  have hu : AEStronglyMeasurable u μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => a (s (n + N)))
      (fun n => (hN (n + N) (Nat.le_add_left _ _)).1) ?_
    filter_upwards [hev] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun n hn => hn.symm)
  have hub : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ h x := by
    have h1 : ∀ᵐ x ∂μ, ∀ n, ‖a (s (n + N)) x‖ ^ 2 ≤ h x :=
      ae_all_iff.2 fun n => (hN (n + N) (Nat.le_add_left _ _)).2
    filter_upwards [hev, h1] with x hx h1x
    obtain ⟨n, hn⟩ := hx.exists
    rw [← hn]; exact h1x n
  refine ⟨?_, ?_⟩
  · rw [memLp_two_iff_integrable_sq_norm hu]
    refine hh.mono' (hu.norm.pow 2) ?_
    filter_upwards [hub] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hx
  · have key : (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ)) = ∫ x, inner ℂ (u x) (u x) ∂μ := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [key]
    refine tendsto_integral_filter_of_dominated_convergence h ?_ ?_ hh ?_
    · filter_upwards [hm] with ε hε
      exact hε.inner hu
    · filter_upwards [hb] with ε hε
      filter_upwards [hε, hub] with x h1 h2
      have := norm_inner_le_norm (𝕜 := ℂ) (a ε x) (u x)
      nlinarith [sq_nonneg (‖a ε x‖ - ‖u x‖)]
    · filter_upwards [he] with x hx
      exact tendsto_const_nhds.congr' (hx.mono fun ε hε => by simp only [hε])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemLpTwoAndTendstoOfCauchyOfAeTendsto
section
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem eLpNorm_two_le_ofReal_sqrt_of_integral_le {X : Type} [MeasurableSpace X] {μ : Measure X} {E : Type}
    [NormedAddCommGroup E] {f : X → E} (hf : MemLp f 2 μ) {c : ℝ}
    (h : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ c) : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt c) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  rw [h2]
  have h3 : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    simp only [Real.rpow_two]
  rw [h3, Real.sqrt_eq_rpow, one_div]
  exact Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h (by norm_num)

theorem memLp_two_and_tendsto_of_cauchy_of_ae_tendsto :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] (v : ℕ → X → E) (u : X → E) (K : ℝ), (∀ n, MemLp (v n) 2 μ) → (∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (u x))) → (∀ n m : ℕ, n ≤ m → ∫ x, ‖v n x - v m x‖ ^ 2 ∂μ ≤ K / ((n : ℝ) + 1)) → MemLp u 2 μ ∧ Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) := by
  intro X _ μ E _ v u K hv hlim hC
  have hu : AEStronglyMeasurable u μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hv n).aestronglyMeasurable) hlim
  have hb : ∀ n, eLpNorm (v n - u) 2 μ ≤ ENNReal.ofReal (Real.sqrt (K / ((n : ℝ) + 1))) := by
    intro n
    have hF := Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := μ) (p := 2) (f := fun m => v n - v m)
      (fun m => ((hv n).sub (hv m)).aestronglyMeasurable) (v n - u)
      ((hv n).aestronglyMeasurable.sub hu)
      (by
        filter_upwards [hlim] with x hx
        exact tendsto_const_nhds.sub hx)
    refine hF.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    filter_upwards [eventually_ge_atTop n] with m hm
    exact eLpNorm_two_le_ofReal_sqrt_of_integral_le ((hv n).sub (hv m)) (hC n m hm)
  refine ⟨?_, ?_⟩
  · have h0 : MemLp (v 0 - u) 2 μ :=
      memLp_iff.mpr ((hb 0).trans_lt ENNReal.ofReal_lt_top)
    have := (hv 0).sub h0
    simpa using this
  · have h1 : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (K / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (h1.sqrt)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun _ => bot_le) hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MonicEqProd
section
namespace GlobalTheory.MonicSeparableProduct

open Polynomial

theorem monic_eq_prod {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) :
    ∀ (n : ℕ) (f : W[X]), f.Monic → f.natDegree = n →
      ∃ M : Multiset W, f = (M.map (fun r => X - C r)).prod := by
  intro n
  induction n with
  | zero =>
    intro f hf h0
    exact ⟨0, by simpa using (hf.natDegree_eq_zero).1 h0⟩
  | succ n ih =>
    intro f hf hn
    have hinj : Function.Injective (algebraMap W F) := Subtype.val_injective
    have hdeg : f.degree ≠ 0 := by
      rw [degree_eq_natDegree hf.ne_zero, hn]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective (algebraMap W F) hinj f hdeg
    have hint : IsIntegral W x := ⟨f, hf, hx⟩
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hroot : f.IsRoot r := by
      apply hinj
      rw [map_zero, ← hx, ← hr, eval₂_at_apply]
    have hfac := mul_divByMonic_eq_iff_isRoot.2 hroot
    have hq : (f /ₘ (X - C r)).Monic := by
      apply Monic.of_mul_monic_left (monic_X_sub_C r)
      rw [hfac]; exact hf
    have hqd : (f /ₘ (X - C r)).natDegree = n := by
      rw [natDegree_divByMonic f (monic_X_sub_C r), hn, natDegree_X_sub_C]
      simp
    obtain ⟨M, hM⟩ := ih _ hq hqd
    refine ⟨r ::ₘ M, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hM, hfac]

theorem exists_sep {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W)
    (hp : ∀ a : W, ¬IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p})
    (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W)
    (t : A) (ht : aug t = 0) :
    ∃ s b : A, IsUnit (aug s) ∧ s = b * s ^ 2 ∧
      ∀ P : Ideal A, P.IsPrime → algebraMap W A p ∈ P → s ∉ P → t ∈ P := by
  classical
  obtain ⟨f, hf, hft⟩ : IsIntegral W t := Algebra.IsIntegral.isIntegral t
  obtain ⟨M, hM⟩ := monic_eq_prod W _ f hf rfl
  have h0 : (M.map (fun r => t - algebraMap W A r)).prod = 0 := by
    have : aeval t f = 0 := hft
    rw [hM, map_multiset_prod, Multiset.map_map] at this
    simpa using this
  set s : A := ((M.filter (fun r => IsUnit r)).map (fun r => t - algebraMap W A r)).prod with hs
  set g : A := ((M.filter (fun r => ¬ IsUnit r)).map (fun r => t - algebraMap W A r)).prod with hg
  have hsg : s * g = 0 := by
    rw [hs, hg, ← Multiset.prod_add, ← Multiset.map_add (f := _), Multiset.filter_add_not, h0]
  have hcop : IsCoprime s g := by
    rw [hs]
    refine Multiset.prod_induction (fun x => IsCoprime x g) _
      (fun a b ha hb => ha.mul_left hb) isCoprime_one_left ?_
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have hru : IsUnit r := (Multiset.mem_filter.1 hr).2
    rw [hg]
    refine Multiset.prod_induction (fun y => IsCoprime (t - algebraMap W A r) y) _
      (fun a b ha hb => ha.mul_right hb) isCoprime_one_right ?_
    intro y hy
    obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.1 hy
    have hru' : ¬ IsUnit r' := (Multiset.mem_filter.1 hr').2
    have hd : IsUnit (r - r') := by
      by_contra hnu
      have h1 : r - r' ∈ IsLocalRing.maximalIdeal W := hnu
      have h2 : r' ∈ IsLocalRing.maximalIdeal W := hru'
      have h3 : r ∈ IsLocalRing.maximalIdeal W := by
        simpa using add_mem h1 h2
      exact h3 hru
    obtain ⟨u, hu⟩ := hd.exists_left_inv
    refine ⟨-algebraMap W A u, algebraMap W A u, ?_⟩
    have := congrArg (algebraMap W A) hu
    rw [map_mul, map_sub, map_one] at this
    linear_combination this
  obtain ⟨b, a, hab⟩ := hcop
  refine ⟨s, b, ?_, ?_, ?_⟩
  · rw [hs, map_multiset_prod]
    refine Multiset.prod_induction IsUnit _ (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro x hx
    rw [Multiset.map_map] at hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have hru : IsUnit r := (Multiset.mem_filter.1 hr).2
    have : aug (t - algebraMap W A r) = -r := by
      rw [map_sub, ht, AlgHom.commutes]; simp
    show IsUnit (aug (t - algebraMap W A r))
    rw [this]; exact hru.neg
  · linear_combination (-s) * hab + a * hsg
  · intro P hP hpP hsP
    have hgP : g ∈ P := by
      have : s * g ∈ P := by rw [hsg]; exact P.zero_mem
      exact (hP.mem_or_mem this).resolve_left hsP
    rw [hg] at hgP
    obtain ⟨y, hy, hyP⟩ := (hP.multiset_prod_mem_iff_exists_mem _).1 hgP
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨n, hn⟩ := hp r (Multiset.mem_filter.1 hr).2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    have : algebraMap W A r ^ n ∈ P := by
      rw [← map_pow, ← hc, map_mul]
      exact P.mul_mem_left _ hpP
    have h2 := hP.mem_of_pow_mem n this
    simpa using add_mem hyP h2

theorem main : ∀ (F : Type) [inst : Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : ↥W), (∀ (a : ↥W), ¬IsUnit a → ∃ (n : ℕ), a ^ n ∈ Ideal.span {p}) → ∀ (A : Type) [inst_2 : CommRing A] [inst_3 : Algebra (↥W) A] [Module.Finite (↥W) A] (aug : A →ₐ[↥W] ↥W), ∃ (s : A), Function.Surjective (⇑(Algebra.algebraMap A (Localization.Away s)) : A → Localization.Away s) ∧ (∃ (m : ℕ), Ideal.map (Algebra.algebraMap A (Localization.Away s)) (RingHom.ker aug) ^ m ≤ Ideal.span {(Algebra.algebraMap (↥W) (Localization.Away s) : ↥W → Localization.Away s) p}) ∧ ∀ (R : Type) [inst_5 : CommRing R] [inst_6 : Algebra (↥W) R] (w : A →ₐ[↥W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent ((w : A → R) t)) → IsUnit ((w : A → R) s) := by
  intro F _ _ W p hp A _ _ _ aug
  classical
  obtain ⟨S, hS⟩ : (⊤ : Submodule W A).FG := Module.Finite.fg_top
  let τ : A → A := fun a => a - algebraMap W A (aug a)
  have hτ : ∀ a, aug (τ a) = 0 := by
    intro a
    simp only [τ]
    rw [map_sub, AlgHom.commutes]; simp
  choose σ β h1 h2 h3 using fun a => exists_sep W p hp A aug (τ a) (hτ a)
  have hker : RingHom.ker aug = Ideal.span ((S.image τ : Finset A) : Set A) := by
    apply le_antisymm
    · intro x hx
      have key : ∀ y ∈ Submodule.span W (S : Set A),
          τ y ∈ Ideal.span ((S.image τ : Finset A) : Set A) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          apply Ideal.subset_span
          simp only [Finset.coe_image]
          exact ⟨y, hy, rfl⟩
        | zero => simp [τ]
        | add y z _ _ hy hz =>
          have : τ (y + z) = τ y + τ z := by simp only [τ, map_add (f := _)]; ring
          rw [this]; exact add_mem hy hz
        | smul c y _ hy =>
          have : τ (c • y) = algebraMap W A c * τ y := by
            simp only [τ]
            rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]; ring
          rw [this]; exact Ideal.mul_mem_left _ _ hy
      have := key x (by rw [hS]; trivial)
      have hx0 : aug x = 0 := hx
      simpa [τ, hx0] using this
    · rw [Ideal.span_le]
      intro x hx
      simp only [Finset.coe_image] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact hτ y
  set s : A := ∏ a ∈ S, σ a with hs
  have hsu : IsUnit (aug s) := by
    rw [hs, map_prod]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun a _ => h1 a)
  have hsb : s = (∏ a ∈ S, β a) * s ^ 2 := by
    rw [hs, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun a _ => h2 a)
  set b : A := ∏ a ∈ S, β a with hb
  have hLu : IsUnit (algebraMap A (Localization.Away s) s) := IsLocalization.Away.algebraMap_isUnit s
  refine ⟨s, ?_, ?_, ?_⟩
  · have hinv : algebraMap A (Localization.Away s) s * algebraMap A (Localization.Away s) b = 1 := by
      apply hLu.mul_left_cancel
      have := congrArg (algebraMap A (Localization.Away s)) hsb
      rw [map_mul, map_pow] at this
      linear_combination -this
    intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s z
    refine ⟨a * b ^ n, ?_⟩
    rw [map_mul, map_pow, ← ha, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
  · apply Ideal.exists_pow_le_of_le_radical_of_fg
    · rw [hker, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Finset.coe_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Ideal.radical_eq_sInf]
      refine Ideal.mem_sInf.2 ?_
      rintro P ⟨hle, hP⟩
      refine h3 y (P.comap (algebraMap A (Localization.Away s))) inferInstance ?_ ?_
      · rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
        exact hle (Ideal.mem_span_singleton_self _)
      · intro hmem
        have hsm : s ∈ P.comap (algebraMap A (Localization.Away s)) :=
          Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem σ hy) hmem
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hsm hLu)
    · apply Ideal.FG.map
      rw [hker]
      exact ⟨_, rfl⟩
  · intro R _ _ w hw
    have hn := hw (τ s) (hτ s)
    have hu : IsUnit (algebraMap W R (aug s)) := hsu.map _
    have : w s = algebraMap W R (aug s) + w (τ s) := by
      simp only [τ]
      rw [map_sub, AlgHom.commutes]; ring
    rw [this]
    exact hn.isUnit_add_left_of_commute hu (Commute.all _ _)

end GlobalTheory.MonicSeparableProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormEigenLePowMulNormSum
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem norm_eigen_le_pow_mul_norm_sum {H κ : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [DecidableEq κ] (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (lam : κ → ℂ) (s : κ) (Bd : ℝ)
    (hBd : 0 ≤ Bd) (E : Finset κ) :
    (∀ j ∈ E, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ E, ∀ x ∈ VV, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) →
    ∀ v : κ → H, (∀ i, v i ∈ VV ∧ T (v i) = lam i • v i) →
      ‖v s‖ ≤ Bd ^ E.card * ‖v s + ∑ i ∈ E, v i‖ := by
  induction E using Finset.induction_on with
  | empty => intro _ _ v _; simp
  | insert j E hj ih =>
    intro h1 h2 v hv
    have hw : ∀ i, (lam i - lam j) • v i ∈ VV ∧
        T ((lam i - lam j) • v i) = lam i • (lam i - lam j) • v i := fun i =>
      ⟨VV.smul_mem _ (hv i).1, by rw [map_smul, (hv i).2, smul_comm]⟩
    have hih := ih (fun k hk => h1 k (mem_insert_of_mem hk))
      (fun k hk => h2 k (mem_insert_of_mem hk)) (fun i => (lam i - lam j) • v i) hw
    have hy : v s + ∑ i ∈ insert j E, v i ∈ VV :=
      VV.add_mem (hv s).1 (VV.sum_mem fun i _ => (hv i).1)
    have hT := h2 j (mem_insert_self j E) _ hy
    have heq : T (v s + ∑ i ∈ insert j E, v i) - lam j • (v s + ∑ i ∈ insert j E, v i)
        = (lam s - lam j) • v s + ∑ i ∈ E, (lam i - lam j) • v i := by
      rw [sum_insert hj]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, (hv _).2, smul_add, smul_sum, sub_smul, sum_sub_distrib]
      abel
    rw [heq] at hT
    have hs : ‖v s‖ ≤ ‖(lam s - lam j) • v s‖ := by
      rw [norm_smul]
      exact le_mul_of_one_le_left (norm_nonneg _) (h1 j (mem_insert_self j E))
    rw [card_insert_of_notMem hj, pow_succ, mul_assoc]
    exact hs.trans (hih.trans (mul_le_mul_of_nonneg_left hT (pow_nonneg hBd _)))

theorem norm_node_projector_le :
    ∀ (H κ : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [Fintype κ] [DecidableEq κ] (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (Nd : Finset κ) (s : κ) (Bd Cn : ℝ), s ∈ Nd → 0 ≤ Bd → (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = lam i • p i x) → (∀ x ∈ VV, T x ∈ VV) → (∀ j ∈ Nd.erase s, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ Nd.erase s, ∀ x ∈ VV, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) → (∀ x ∈ VV, ‖∑ i ∈ Nd, p i x‖ ≤ Cn * ‖x‖) → ∀ x ∈ VV, ‖p s x‖ ≤ Cn * Bd ^ (Nd.erase s).card * ‖x‖ := by
  intro H κ _ _ _ _ VV T p lam Nd s Bd Cn hs hBd hp _ h1 h2 hC x hx
  have h := norm_eigen_le_pow_mul_norm_sum VV T lam s Bd hBd (Nd.erase s) h1 h2
    (fun i => p i x) (fun i => hp i x hx)
  have hsum : p s x + ∑ i ∈ Nd.erase s, p i x = ∑ i ∈ Nd, p i x :=
    add_sum_erase Nd (fun i => p i x) hs
  rw [hsum] at h
  calc ‖p s x‖ ≤ Bd ^ (Nd.erase s).card * ‖∑ i ∈ Nd, p i x‖ := h
    _ ≤ Bd ^ (Nd.erase s).card * (Cn * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hC x hx) (pow_nonneg hBd _)
    _ = Cn * Bd ^ (Nd.erase s).card * ‖x‖ := by ring

end GlobalTheory
end

