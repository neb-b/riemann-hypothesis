module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtZeroEqSumIntegralKernelIteratedDeriv
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory

theorem value_at_zero_eq_sum_integral_kernel_iteratedDeriv :
    ∀ ε : ℝ, 0 < ε → ∃ κ : Fin 3 → ℝ → ℂ,
      (∀ n, Continuous (κ n) ∧ tsupport (κ n) ⊆ Set.Icc (-ε) ε) ∧
      ∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → u 0 = ∑ n : Fin 3, ∫ t, κ n t * iteratedDeriv n u t := by
  intro ε hε
  set e : ℂ := (ε : ℂ) with he_def
  have he : e ≠ 0 := by
    rw [he_def]; exact_mod_cast hε.ne'
  let s : ℝ → ℝ := fun t => max 0 (min t ε)
  have hs_cont : Continuous s := by fun_prop
  have hs_eq : ∀ t ∈ Set.Icc 0 ε, s t = t := by
    intro t ht; simp only [s]; rw [min_eq_left ht.2, max_eq_right ht.1]
  let P : Fin 3 → ℂ → ℂ := ![fun x => x * (6 / e ^ 2 * (1 - x / e)),
    fun x => x * (2 * (-3 / e * (1 - x / e) ^ 2)), fun x => x * (1 - x / e) ^ 3]
  have hP_cont : ∀ n, Continuous (P n) := by
    intro n; fin_cases n <;> simp [P] <;> fun_prop
  have hP0 : ∀ n, P n 0 = 0 := by
    intro n; fin_cases n <;> simp [P]
  have hPe : ∀ n, P n e = 0 := by
    intro n; fin_cases n <;> simp [P, div_self he]
  have hzero : ∀ n t, t ∉ Set.Ioc 0 ε → P n (s t : ℂ) = 0 := by
    intro n t ht
    rcases le_or_gt t 0 with h | h
    · have : s t = 0 := by simp only [s]; exact max_eq_left (min_le_of_left_le h)
      rw [this, Complex.ofReal_zero, hP0]
    · have h' : ε < t := by
        by_contra h''; exact ht ⟨h, not_lt.mp h''⟩
      have : s t = ε := by simp only [s]; rw [min_eq_right h'.le, max_eq_right hε.le]
      rw [this, ← he_def, hPe]
  refine ⟨fun n t => P n (s t : ℂ), ?_, ?_⟩
  · intro n
    refine ⟨(hP_cont n).comp (Complex.continuous_ofReal.comp hs_cont), ?_⟩
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    by_contra h
    apply ht
    apply hzero n t
    intro h2; exact h ⟨by linarith [h2.1], h2.2⟩
  · intro u hu
    have h1 := contDiff_infty_iff_deriv.mp hu
    have h2 := contDiff_infty_iff_deriv.mp h1.2
    have hu1 : ∀ x, HasDerivAt u (deriv u x) x := fun x => (h1.1 x).hasDerivAt
    have hu2 : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x => (h2.1 x).hasDerivAt
    have hc0 : Continuous u := h1.1.continuous
    have hc1 : Continuous (deriv u) := h2.1.continuous
    have hc2 : Continuous (deriv (deriv u)) := h2.2.continuous
    have hd2 : iteratedDeriv 2 u = deriv (deriv u) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hI : ∀ (g : ℝ → ℂ) (n : Fin 3),
        ∫ t, P n (s t : ℂ) * g t = ∫ t in (0:ℝ)..ε, P n (s t : ℂ) * g t := by
      intro g n
      rw [intervalIntegral.integral_of_le hε.le, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro t ht; rw [hzero n t ht, zero_mul]
    have hK : ∀ n, Continuous (fun t => P n (s t : ℂ)) := fun n =>
      (hP_cont n).comp (Complex.continuous_ofReal.comp hs_cont)
    rw [Fin.sum_univ_three]
    have e0 : iteratedDeriv ((0 : Fin 3) : ℕ) u = u := iteratedDeriv_zero
    have e1 : iteratedDeriv ((1 : Fin 3) : ℕ) u = deriv u := iteratedDeriv_one
    have e2 : iteratedDeriv ((2 : Fin 3) : ℕ) u = deriv (deriv u) := hd2
    rw [e0, e1, e2]
    rw [hI, hI, hI, ← intervalIntegral.integral_add, ← intervalIntegral.integral_add]
    all_goals try (apply Continuous.intervalIntegrable; have := hK 0; have := hK 1; have := hK 2; fun_prop)
    let F : ℝ → ℂ := fun t => (t : ℂ) * (-3 / e * (1 - (t : ℂ) / e) ^ 2 * u t
      + (1 - (t : ℂ) / e) ^ 3 * deriv u t) - (1 - (t : ℂ) / e) ^ 3 * u t
    have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (a := 0) (b := ε)
      (f' := fun t => P 0 (s t : ℂ) * u t + P 1 (s t : ℂ) * deriv u t
        + P 2 (s t : ℂ) * deriv (deriv u) t) ?_
      (by apply Continuous.intervalIntegrable; have := hK 0; have := hK 1; have := hK 2; fun_prop)
    · rw [key]
      simp only [F, Complex.ofReal_zero, zero_div, sub_zero, one_pow, one_mul, zero_mul,
        zero_sub, ← he_def, div_self he, sub_self]
      ring
    · intro x hx
      rw [Set.uIcc_of_le hε.le] at hx
      simp only [hs_eq x hx]
      have hx' : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      have hL : HasDerivAt (fun t : ℝ => (1 : ℂ) - (t : ℂ) / e) (-(1 / e)) x := by
        convert (hx'.div_const e).const_sub 1 using 1
      have hφ : HasDerivAt (fun t : ℝ => (1 - (t : ℂ) / e) ^ 3) (-3 / e * (1 - (x : ℂ) / e) ^ 2) x := by
        exact (hL.pow 3).congr_deriv (by norm_num <;> ring)
      have hφ' : HasDerivAt (fun t : ℝ => -3 / e * (1 - (t : ℂ) / e) ^ 2)
          (6 / e ^ 2 * (1 - (x : ℂ) / e)) x := by
        exact ((hL.pow 2).const_mul (-3 / e)).congr_deriv (by norm_num <;> ring)
      have hF := (hx'.mul ((hφ'.mul (hu1 x)).add (hφ.mul (hu2 x)))).sub (hφ.mul (hu1 x))
      refine hF.congr_deriv ?_
      simp only [Pi.mul_apply, Pi.add_apply, P, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOfProjectionSupport
section
open MeasureTheory Filter Topology

namespace GlobalTheory.FiberPointwise

lemma lintegral_indicator_translate {X : Type} [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd X]
    (μ : Measure X) [μ.IsAddRightInvariant] (P : X →+ X)
    (h : X → ENNReal) (hinv : ∀ x z, P z = z → h (x + z) = h x) (S : Set X) (z : X) (hz : P z = z) :
    ∫⁻ x, Set.indicator {x | P x - z ∈ S} h x ∂μ = ∫⁻ x, Set.indicator {x | P x ∈ S} h x ∂μ := by
  rw [← lintegral_add_right_eq_self (μ := μ) _ z]
  congr 1
  funext x
  show Set.indicator {x | P x - z ∈ S} h (x + z) = Set.indicator {x | P x ∈ S} h x
  have hx : (P (x + z) - z ∈ S) ↔ (P x ∈ S) := by rw [map_add (f := _), hz, add_sub_cancel_right]
  by_cases hxs : P x ∈ S
  · rw [Set.indicator_of_mem (show x + z ∈ {x | P x - z ∈ S} from hx.mpr hxs),
      Set.indicator_of_mem (show x ∈ {x | P x ∈ S} from hxs), hinv x z hz]
  · rw [Set.indicator_of_notMem (show x + z ∉ {x | P x - z ∈ S} from fun h' => hxs (hx.mp h')),
      Set.indicator_of_notMem (show x ∉ {x | P x ∈ S} from hxs)]

theorem vanish_at_point : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := by
  intro X _ _ _ _ _ _ μ _ P hPc hPP Φ Ψ hΦ hΨ K hK hΦK y hΦy hyp
  by_contra hne
  set δ : NNReal := ‖Ψ y‖₊ / 2 with hδ
  have hΨpos : 0 < ‖Ψ y‖₊ := nnnorm_pos.mpr hne
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ‖Ψ y‖₊ := NNReal.half_lt_self hΨpos.ne'
  let V : Set X := {x | δ < ‖Ψ x‖₊}
  have hVo : IsOpen V := isOpen_lt continuous_const hΨ.nnnorm
  have hyV : y ∈ V := hδlt
  have hsum : P y + (y - P y) = y := by abel
  have hpre : (fun p : X × X => p.1 + p.2) ⁻¹' V ∈ 𝓝 (P y, y - P y) := by
    apply continuous_add.continuousAt.preimage_mem_nhds
    simp only [hsum]
    exact hVo.mem_nhds hyV
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨s1, hs1, hs1u, hs1c⟩ := local_compact_nhds hu
  obtain ⟨s2, hs2, hs2v, hs2c⟩ := local_compact_nhds hv
  set U1 := interior s1 with hU1
  set O2 := interior s2 with hO2
  have hU1o : IsOpen U1 := isOpen_interior
  have hO2o : IsOpen O2 := isOpen_interior
  have hPyU1 : P y ∈ U1 := mem_interior_iff_mem_nhds.mpr hs1
  have hQyO2 : y - P y ∈ O2 := mem_interior_iff_mem_nhds.mpr hs2
  have hUV : ∀ a ∈ U1, ∀ b ∈ O2, a + b ∈ V := fun a ha b hb =>
    huv (Set.mk_mem_prod (hs1u (interior_subset ha)) (hs2v (interior_subset hb)))
  set PK := P '' K with hPK
  have hPKc : IsCompact PK := hK.image hPc
  have hPKfix : ∀ a ∈ PK, P a = a := by rintro _ ⟨k, -, rfl⟩; exact hPP k
  obtain ⟨t, htPK, hcover⟩ := hPKc.elim_nhds_subcover (fun a => {w | w - (a - P y) ∈ U1}) (by
    intro a _
    apply (hU1o.preimage (continuous_id.sub continuous_const)).mem_nhds
    show a - (a - P y) ∈ U1
    rwa [sub_sub_cancel])
  set N := t.card with hN
  set ε : NNReal := δ / (N + 1) with hεdef
  have hεpos : 0 < ε := div_pos hδpos (by positivity)
  have hε : ε ^ 2 * N < δ ^ 2 := by
    rw [hεdef, ← NNReal.coe_lt_coe]; push_cast
    have hδr : (0:ℝ) < δ := hδpos
    have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg _
    rw [div_pow, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos hδr 2, mul_nonneg (pow_pos hδr 2).le (sq_nonneg (N:ℝ)), mul_nonneg (pow_pos hδr 2).le hNr]
  have htube : ∀ᶠ b in 𝓝 (y - P y), ∀ a ∈ PK, ‖Φ (a + b)‖₊ < ε := by
    apply hPKc.eventually_forall_of_forall_eventually
    intro a ha
    have h0 : Φ (a + (y - P y)) = 0 := by
      have := hΦy (a - P y) (by rw [map_sub, hPKfix a ha, hPP])
      rwa [show y + (a - P y) = a + (y - P y) by abel] at this
    have hcont : Continuous fun p : X × X => ‖Φ (p.2 + p.1)‖₊ :=
      (hΦ.comp (continuous_snd.add continuous_fst)).nnnorm
    have hmem : {p : X × X | ‖Φ (p.2 + p.1)‖₊ < ε} ∈ 𝓝 (y - P y, a) :=
      (isOpen_lt hcont continuous_const).mem_nhds (by simp [h0, hεpos])
    exact hmem
  obtain ⟨O3, hO3sub, hO3o, hQyO3⟩ := eventually_nhds_iff.mp htube
  let O : Set X := {w | w - P y ∈ O2 ∩ O3}
  have hOo : IsOpen O := (hO2o.inter hO3o).preimage (continuous_id.sub continuous_const)
  have hyO : y ∈ O := ⟨hQyO2, hQyO3⟩
  obtain ⟨h, hhm, hh1, hinv, hsupp, ⟨O', hO'o, hyO', hO'⟩, heq⟩ := hyp O hOo hyO
  have hsupp' : ∀ x, h x ≠ 0 → x - P x ∈ O2 ∧ x - P x ∈ O3 := by
    intro x hx
    have := hsupp x hx
    simp only [O, Set.mem_setOf_eq] at this
    rwa [show x + (P y - P x) - P y = x - P x by abel] at this
  have hdec : ∀ x : X, P x + (x - P x) = x := fun x => by abel
  set A : Set X := {x | P x ∈ U1} with hA
  set I := ∫⁻ x, A.indicator h x ∂μ with hI
  have hlow : (δ:ENNReal) ^ 2 * I ≤ ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ := by
    rw [hI, ← lintegral_const_mul' _ _ (by simp)]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      by_cases hx0 : h x = 0
      · simp [hx0]
      · have hxV : x ∈ V := by
          have := hUV (P x) hxA (x - P x) (hsupp' x hx0).1
          rwa [hdec] at this
        rw [mul_comm]
        gcongr
        rw [enorm_eq_nnnorm]
        exact ENNReal.coe_le_coe.mpr hxV.le
    · simp [hxA]
  have hup : ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ ≤ (ε:ENNReal) ^ 2 * (N * I) := by
    have hpt : ∀ x, h x * ‖Φ x‖ₑ ^ 2 ≤
        (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
      intro x
      by_cases hx0 : h x = 0
      · simp [hx0]
      by_cases hΦ0 : Φ x = 0
      · simp [hΦ0]
      have hPx : P x ∈ PK := ⟨P x, hΦK x hΦ0, hPP x⟩
      obtain ⟨a, hat, hxa⟩ : ∃ a ∈ t, P x - (a - P y) ∈ U1 := by
        have := hcover hPx
        simp only [Set.mem_iUnion] at this
        obtain ⟨a, ha, h'⟩ := this
        exact ⟨a, ha, h'⟩
      have hsmall : ‖Φ x‖₊ < ε := by
        have := hO3sub _ (hsupp' x hx0).2 (P x) hPx
        rwa [hdec] at this
      calc h x * ‖Φ x‖ₑ ^ 2 ≤ h x * (ε:ENNReal) ^ 2 := by
            gcongr
            rw [enorm_eq_nnnorm]
            exact ENNReal.coe_le_coe.mpr hsmall.le
        _ = (ε:ENNReal) ^ 2 * Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
            rw [Set.indicator_of_mem (show x ∈ {x | P x - (a - P y) ∈ U1} from hxa), mul_comm]
        _ ≤ (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
            gcongr
            exact Finset.single_le_sum (f := fun a => Set.indicator {x | P x - (a - P y) ∈ U1} h x)
              (fun _ _ => bot_le) hat
    calc _ ≤ ∫⁻ x, (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x ∂μ :=
          lintegral_mono hpt
      _ = (ε:ENNReal) ^ 2 * ∑ a ∈ t, ∫⁻ x, Set.indicator {x | P x - (a - P y) ∈ U1} h x ∂μ := by
          rw [lintegral_const_mul' _ _ (by simp), MeasureTheory.lintegral_finsetSum]
          intro a _
          exact hhm.indicator ((hU1o.preimage (hPc.sub continuous_const)).measurableSet)
      _ = (ε:ENNReal) ^ 2 * (N * I) := by
          congr 1
          rw [Finset.sum_congr rfl (fun a ha => lintegral_indicator_translate μ P h hinv U1 (a - P y)
            (by rw [map_sub, hPKfix a (htPK a ha), hPP])), Finset.sum_const, nsmul_eq_mul]
  have hIpos : I ≠ 0 := by
    let W := O' ∩ {x | Ψ x ≠ 0} ∩ A
    have hWo : IsOpen W := (hO'o.inter (isOpen_ne_fun hΨ continuous_const)).inter (hU1o.preimage hPc)
    have hyW : y ∈ W := ⟨⟨hyO', hne⟩, hPyU1⟩
    have hWpos : 0 < μ W := hWo.measure_pos μ ⟨y, hyW⟩
    have hle : (1/2 : ENNReal) * μ W ≤ I := by
      rw [← lintegral_indicator_const hWo.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hxW : x ∈ W
      · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem hxW.2]
        exact hO' x hxW.1.1 hxW.1.2
      · simp [hxW]
    intro h0
    rw [h0] at hle
    exact (mul_ne_zero (by simp) hWpos.ne') (le_zero_iff.mp hle)
  have hIfin : I ≠ ⊤ := by
    have hC : IsCompact ((fun p : X × X => p.1 + p.2) '' (s1 ×ˢ s2)) :=
      (hs1c.prod hs2c).image continuous_add
    obtain ⟨U, hCU, hUo, hUfin⟩ := hC.exists_open_superset_measure_lt_top μ
    have hle : I ≤ μ U := by
      rw [← lintegral_indicator_one hUo.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA]
        by_cases hx0 : h x = 0
        · simp [hx0]
        · have hxU : x ∈ U := hCU ⟨(P x, x - P x),
            ⟨interior_subset hxA, interior_subset (hsupp' x hx0).1⟩, hdec x⟩
          rw [Set.indicator_of_mem hxU]
          simpa using hh1 x
      · simp [hxA]
    exact ne_top_of_le_ne_top hUfin.ne hle
  have hchain : (δ:ENNReal) ^ 2 * I ≤ ((ε:ENNReal) ^ 2 * N) * I := by
    calc _ ≤ _ := hlow
      _ = _ := heq
      _ ≤ _ := hup
      _ = _ := by ring
  have h2 := (ENNReal.mul_le_mul_iff_left hIpos hIfin).mp hchain
  have h3 : ((δ ^ 2 : NNReal) : ENNReal) ≤ ((ε ^ 2 * N : NNReal) : ENNReal) := by
    push_cast; exact h2
  exact absurd (ENNReal.coe_le_coe.mp h3) (not_le.mpr hε)

end GlobalTheory.FiberPointwise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceIffIdempotentFixed
section
open scoped TensorProduct
universe u

namespace GlobalTheory

theorem weightSpace_iff_idempotent_fixed : ∀ (k : Type) [Field k] (C : Type) [CommRing C] (M : Type u) [AddCommGroup M] [Module k M] [Module (k ⊗[ℤ] C) M] [IsScalarTower k (k ⊗[ℤ] C) M] [FiniteDimensional k M] (χ : C →+* k) (e : k ⊗[ℤ] C), IsIdempotentElem e → (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) e = 1 → (∀ a, (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) a = 0 → IsNilpotent (e * a)) → ∀ m : M, m ∈ (⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c)) ↔ e • m = m := by
  intro k _ C _ M _ _ _ _ _ χ e he he1 hnil m
  set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) with hφ
  have hφt : ∀ (x : k) (c : C), φ (x ⊗ₜ[ℤ] c) = x * χ c := by
    intro x c
    simp [hφ]
  let ρ : k ⊗[ℤ] C →ₐ[k] Module.End k M := Algebra.lsmul k k M
  let T : C → k ⊗[ℤ] C := fun c => (1 : k) ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (χ c)
  have hφT : ∀ c, φ (T c) = 0 := by
    intro c
    simp [T, hφt, AlgHom.commutes]
  have hρT : ∀ c, ρ (T c) = DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c) - χ c • (1 : Module.End k M) := by
    intro c
    simp only [T]
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    rfl
  constructor
  · intro hm
    set X := ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c) with hX
    have hstab : ∀ (a : k ⊗[ℤ] C) (x : M), x ∈ X → a • x ∈ X := by
      intro a x hx
      rw [hX, Submodule.mem_iInf] at hx ⊢
      intro c
      have hc : Commute (ρ ((1 : k) ⊗ₜ[ℤ] c)) (ρ a) := (Commute.all _ _).map ρ
      exact Module.End.mapsTo_maxGenEigenspace_of_comm hc (χ c) (hx c)
    let X' : Submodule (k ⊗[ℤ] C) M :=
      { carrier := X
        add_mem' := fun ha hb => X.add_mem ha hb
        zero_mem' := X.zero_mem
        smul_mem' := fun a x hx => hstab a x hx }
    let ρX : k ⊗[ℤ] C →ₐ[k] Module.End k X' := Algebra.lsmul k k X'
    have hT : ∀ c, IsNilpotent (ρX (T c)) := by
      intro c
      refine ⟨Module.End.maxGenEigenspaceIndex (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c), ?_⟩
      ext ⟨x, hx⟩
      have hx' : x ∈ Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
        (Submodule.mem_iInf _).1 hx c
      rw [Module.End.maxGenEigenspace_eq, Module.End.mem_genEigenspace_nat] at hx'
      rw [← hρT, ← map_pow] at hx'
      rw [LinearMap.mem_ker] at hx'
      rw [← map_pow, LinearMap.zero_apply]
      exact hx'
    have hall : ∀ a, IsNilpotent (ρX (a - algebraMap k (k ⊗[ℤ] C) (φ a))) := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        have : x ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (φ (x ⊗ₜ[ℤ] c)) = x • T c := by
          simp only [T, hφt, smul_sub, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul]
          rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
          simp
        rw [this, map_smul]
        exact (hT c).smul x
      | add a b ha hb =>
        have : a + b - algebraMap k (k ⊗[ℤ] C) (φ (a + b)) =
            (a - algebraMap k (k ⊗[ℤ] C) (φ a)) + (b - algebraMap k (k ⊗[ℤ] C) (φ b)) := by
          rw [map_add (f := _), map_add (f := _)]; abel
        rw [this, map_add (f := _)]
        exact Commute.isNilpotent_add ((Commute.all _ _).map ρX) ha hb
    have h1e : IsNilpotent (ρX (1 - e)) := by
      have := hall (1 - e)
      rwa [show φ (1 - e) = 0 by rw [map_sub, map_one, he1, sub_self], map_zero, sub_zero] at this
    have hid : IsIdempotentElem (ρX (1 - e)) := he.one_sub.map ρX
    have h0 := hid.eq_zero_of_isNilpotent h1e
    have := congrArg (fun f => (f ⟨m, hm⟩ : X')) h0
    simp only [LinearMap.zero_apply] at this
    have := congrArg Subtype.val this
    change (1 - e) • m = 0 at this
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · intro hm
    rw [Submodule.mem_iInf]
    intro c
    rw [Module.End.mem_maxGenEigenspace]
    obtain ⟨n, hn⟩ := hnil (T c) (hφT c)
    refine ⟨n, ?_⟩
    have hen : ∀ j : ℕ, e ^ j • m = m := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, mul_smul, hm, ih]
    rw [← hρT, ← map_pow]
    change T c ^ n • m = 0
    rw [← hen n, smul_smul, mul_comm, ← mul_pow, hn, zero_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceTensorRingHomFinrankPos
section
open scoped TensorProduct

namespace GlobalTheory

theorem weightSpace_tensor_ringHom_pos : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (χ : C →+* k), 0 < Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ χ
  let φ : k ⊗[ℤ] C →ₐ[k] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)
  have hφs : Function.Surjective φ := fun a => ⟨algebraMap k (k ⊗[ℤ] C) a, by rw [φ.commutes]; rfl⟩
  let m : Ideal (k ⊗[ℤ] C) := RingHom.ker φ
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφs
  haveI : IsArtinianRing (k ⊗[ℤ] C) := IsArtinianRing.of_finite k (k ⊗[ℤ] C)
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (m ^ j), fun a b h => Ideal.pow_le_pow_right h⟩ :
      ℕ →o (Ideal (k ⊗[ℤ] C))ᵒᵈ)
  have hst : ∀ j, N ≤ j → m ^ N = m ^ j := fun j hj => hN j hj
  have hJJ : IsIdempotentElem (m ^ (N + 1)) := by
    show m ^ (N + 1) * m ^ (N + 1) = m ^ (N + 1)
    rw [← pow_add, ← hst (N + 1 + (N + 1)) (by omega), hst (N + 1) (by omega)]
  obtain ⟨e, he, hJe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian (m ^ (N + 1)))).mp hJJ
  have hJe' : m ^ (N + 1) = Ideal.span {e} := hJe
  have hv : (1 - e : k ⊗[ℤ] C) ≠ 0 := by
    intro h
    have h1 : e = 1 := (sub_eq_zero.mp h).symm
    have : m ^ (N + 1) = ⊤ := by rw [hJe', h1, Ideal.span_singleton_one]
    exact hm.ne_top (top_le_iff.mp (this ▸ Ideal.pow_le_self (by omega)))
  have key : ∀ x ∈ m, x ^ (N + 1) * (1 - e) = 0 := by
    intro x hx
    have hx' : x ^ (N + 1) ∈ Ideal.span {e} := hJe' ▸ Ideal.pow_mem_pow hx (N + 1)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
    rw [← ha, mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]
  refine lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 ?_)
  rw [Submodule.ne_bot_iff]
  refine ⟨1 - e, ?_, hv⟩
  rw [Submodule.mem_iInf]
  intro c
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨N + 1, ?_⟩
  let x : k ⊗[ℤ] C := (1 : k) ⊗ₜ c - algebraMap k (k ⊗[ℤ] C) (χ c)
  have hxm : x ∈ m := by
    simp [m, x, φ, RingHom.mem_ker]
  have hf : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c) - χ c • (1 : Module.End k (k ⊗[ℤ] C))
      = Algebra.lmul k (k ⊗[ℤ] C) x := by
    ext y
    simp [x, sub_mul, Algebra.smul_def]
  rw [hf, ← map_pow]
  simpa using key x hxm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftLeftIsPullbackSnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem whiskerLeft_left_isPullback_snd (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T) :
    IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  have hw : (U ◁ f).left ≫ (snd U T).left = (snd U T').left ≫ f.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  refine IsPullback.of_right (h₁₂ := (fst U T).left) (h₂₂ := T.hom) (v₁₃ := U.hom) ?_ hw ?_
  · have h1 : (U ◁ f).left ≫ (fst U T).left = (fst U T').left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    have h2 : f.left ≫ T.hom = T'.hom := Over.w f
    rw [h1, h2, Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T'.hom
  · rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T.hom

end GlobalTheory
end

