module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistOkAll
section
open IsDedekindDomain Polynomial

namespace GlobalTheory

theorem hensel_norm_lift_of_involution :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (τ : A →+* A), (∀ a, τ (τ a) = a) → IsUnit (2 : A) → (∀ a ∈ I, τ a ∈ I) → ∀ a t₀ : A, IsUnit a → τ a = a → IsUnit t₀ → t₀ * τ t₀ - a ∈ I → ∃ t : A, IsUnit t ∧ t * τ t = a := by
  intro A _ I _ τ hτ h2 hI a t₀ ha hτa ht₀ hclose
  set c := t₀ * τ t₀ with hc_def
  have hc : IsUnit c := ht₀.mul (ht₀.map τ)
  have hτc : τ c = c := by
    simp only [hc_def, map_mul, hτ]; ring
  obtain ⟨w, hw⟩ := hc.exists_right_inv
  have hτw : τ w = w := by
    apply hc.mul_left_cancel
    rw [hw, ← hτc, ← map_mul, hw, map_one]
  set b := a * w with hb_def
  have hτb : τ b = b := by simp only [hb_def, map_mul, hτa, hτw]
  have hb1 : 1 - b ∈ I := by
    have : 1 - b = w * (c - a) := by
      rw [hb_def]; linear_combination (-1 : A) * hw
    rw [this]; exact I.mul_mem_left w hclose
  obtain ⟨s, hs, hs1⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - C b)
    (monic_X_pow_sub_C b (by norm_num)) 1 (by simpa using hb1)
    (by
      have : (derivative (X ^ 2 - C b)).eval (1 : A) = 2 := by simp [one_add_one_eq_two]
      rw [this]; exact h2.map _)
  have hs2 : s ^ 2 = b := by
    have := hs.eq_zero; simp at this; linear_combination this
  have hτs2 : τ s ^ 2 = b := by rw [← map_pow, hs2, hτb]
  have hτs1 : τ s - 1 ∈ I := by
    have := hI _ hs1; simpa using this
  have hsum : IsUnit (s + τ s) := by
    have hj : (s - 1) + (τ s - 1) ∈ Ideal.jacobson (⊥ : Ideal A) :=
      by simpa only [Ideal.jacobson_bot] using HenselianRing.jac (Ideal.add_mem I hs1 hτs1)
    obtain ⟨v, hv⟩ := h2.exists_right_inv
    have hu := (Ideal.mem_jacobson_bot.1 hj) v
    have : s + τ s = (((s - 1) + (τ s - 1)) * v + 1) * 2 := by
      linear_combination (-(s - 1 + (τ s - 1))) * hv
    rw [this]; exact hu.mul h2
  have hfix : τ s = s := by
    have h0 : (s - τ s) * (s + τ s) = 0 := by linear_combination hs2 - hτs2
    have := (hsum.mul_left_eq_zero).1 h0
    linear_combination -this
  have hbu : IsUnit b := ha.mul (IsUnit.of_mul_eq_one_right c hw)
  have hsu : IsUnit s := by
    rw [← hs2, pow_two] at hbu; exact isUnit_of_mul_isUnit_left hbu
  refine ⟨t₀ * s, ht₀.mul hsu, ?_⟩
  rw [map_mul, hfix]
  have : t₀ * s * (τ t₀ * s) = c * s ^ 2 := by rw [hc_def]; ring
  rw [this, hs2, hb_def]
  linear_combination a * hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem mulVec_eq_zero_of_det_nonZeroDivisor {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n R) (hA : A.det ∈ nonZeroDivisors R) (v : n → R)
    (hv : A *ᵥ v = 0) : v = 0 := by
  have h : A.det • v = 0 := by
    have := congrArg (fun w => A.adjugate *ᵥ w) hv
    simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec] using this
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hA).1 hi

theorem twistedTrace_equivariant_and_injective_of_groupDet :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R] (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (u : R), (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R → (∀ (F : R) (g : H), st g (∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) = ((χ g : Kˣ) : K) • ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) ∧ (∀ f : R, (∀ h, ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g (f * st h u) = 0) → f = 0) ∧ (∀ F : H → R, (∀ h g, st g (F h) = ((χ g : Kˣ) : K) • F h) → ∑ h, F h * st h u = 0 → F = 0) := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet
  refine ⟨?_, ?_, ?_⟩
  · intro F g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    rw [map_smul, ← hmul, Equiv.coe_mulRight, smul_smul, ← Units.val_mul]
    congr 2
    rw [map_mul, mul_inv_rev, mul_inv_cancel_left]
  · intro f hf
    have h := mulVec_eq_zero_of_det_nonZeroDivisor _ hdet
      (fun g => (((χ g)⁻¹ : Kˣ) : K) • st g f) (by
        funext h
        rw [Pi.zero_apply, ← hf h]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, ← hmul, mul_smul_comm, mul_comm])
    simpa [h1] using congrFun h 1
  · intro F hF h0
    refine mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.of fun h g : H => st (h * g) u)ᵀ
      (by rwa [Matrix.det_transpose]) F ?_
    funext g
    have h2 := congrArg (st g) h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    have h3 : ((χ g : Kˣ) : K) • ∑ h, st (h * g) u * F h = 0 := by
      rw [← h2, Finset.smul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_mul, hF, ← hmul, smul_mul_assoc, mul_comm]
    have h4 := congrArg (fun x => (((χ g)⁻¹ : Kˣ) : K) • x) h3
    simp only [smul_smul, Units.inv_mul, one_smul, smul_zero] at h4
    simpa [Matrix.mulVec, dotProduct] using h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourier
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.PoincareUnfold

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

open MeasureTheory in
open scoped Pointwise in
private lemma setIntegral_exp_linear_fundamentalDomain_eq_zero {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V)
    [VAddInvariantMeasure L V μ] [Countable L] {D : Set V} (hD : IsAddFundamentalDomain L D μ)
    (hDm : MeasurableSet D) (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (hint : ∀ y ∈ L, ∃ z : ℤ, φ y = z) :
    ∫ v in D, Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) ∂μ = 0 := by
  set f : V → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) with hf
  have hper : ∀ (g : L) (v : V), f (g +ᵥ v) = f v := by
    intro g v
    obtain ⟨z, hz⟩ := hint g g.2
    have hgv : (g +ᵥ v : V) = (g : V) + v := rfl
    simp only [hf, hgv, map_add (f := _), hz]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I z]; ring_nf
    rw [this, one_mul]
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (LinearMap.ext h)
  set w : V := (1 / (2 * φ u)) • u with hw
  have hφw : φ w = 1 / 2 := by
    rw [hw, map_smul, smul_eq_mul]; field_simp
  have hshift : ∀ v, f (w + v) = -f v := by
    intro v
    simp only [hf, map_add (f := _), hφw]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℂ)) = -1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring]
      exact Complex.exp_pi_mul_I
    rw [this, neg_one_mul]
  have hD' : IsAddFundamentalDomain L (w +ᵥ D) μ := hD.vadd_of_comm w
  have h1 : ∫ v in D, f v ∂μ = ∫ v in w +ᵥ D, f v ∂μ := hD.setIntegral_eq hD' hper
  have h2 : ∫ v in w +ᵥ D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := by
    rw [← integral_indicator (hDm.const_vadd w), ← integral_indicator hDm]
    · rw [← integral_add_left_eq_self (μ := μ) _ w]
      congr 1
      ext v
      by_cases hv : v ∈ D
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show w + v ∈ w +ᵥ D from Set.vadd_mem_vadd_set hv)]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem]
        rwa [← vadd_eq_add, Set.vadd_mem_vadd_set_iff]

  have h3 : ∫ v in D, f v ∂μ = -∫ v in D, f v ∂μ := by
    calc ∫ v in D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := h1.trans h2
      _ = ∫ v in D, -f v ∂μ := setIntegral_congr_fun hDm fun v _ => hshift v
      _ = -∫ v in D, f v ∂μ := integral_neg _
  have h4 : (2 : ℂ) * ∫ v in D, f v ∂μ = 0 := by
    rw [two_mul]; nth_rewrite 2 [h3]; ring
  simpa using h4


open MeasureTheory in
open scoped Pointwise in
theorem _root_.GlobalTheory.PoincareUnfold.unfold_poincare_fourier : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ,
    (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ →
    ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) →
    (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) →
    ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) →
    l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) →
    (∀ v, ∑' x, Q x * F (j x + v) =
      ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) →
    ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  intro V _ _ _ _ _ μ _ Γ _ j hj C hfin hspan n t Q hQsupp ht hQper F hF a l ha hl0 hl hint H
  classical
  set L : Submodule ℤ V := (C.map j).toIntSubmodule with hLdef
  have hmemL : ∀ y, y ∈ L ↔ ∃ c ∈ C, j c = y := fun y => by
    exact AddSubgroup.mem_map
  have hLset : (L : Set V) = j '' (C : Set Γ) := by
    ext y; simp only [SetLike.mem_coe, hmemL, Set.mem_image]
  have hj0 : ∀ c, j c = 0 ↔ c = 0 := fun c => ⟨fun h => hj (by rw [h, map_zero]), fun h => by
    rw [h, map_zero]⟩
  haveI : DiscreteTopology L := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    set T : Finset ℝ := insert 1 (((hfin 1).toFinset.filter (· ≠ 0)).image fun c => ‖j c‖)
    have hTne : T.Nonempty := Finset.insert_nonempty _ _
    refine ⟨T.min' hTne, ?_, ?_⟩
    · show 0 < T.min' hTne
      rw [Finset.lt_min'_iff]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_image] at hy
      rcases hy with rfl | ⟨c, hc, rfl⟩
      · exact one_pos
      · rw [Finset.mem_filter] at hc
        exact norm_pos_iff.2 fun h => hc.2 ((hj0 c).1 h)
    · rintro ⟨y, hy⟩ hdist
      obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
      have hlt : ‖j c‖ < T.min' hTne := by simpa [dist_eq_norm] using hdist
      have hle1 : T.min' hTne ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
      by_cases hc0 : c = 0
      · ext; simp [hc0]
      · exfalso
        have hmem : ‖j c‖ ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.2
          ⟨c, Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨hc, by linarith⟩, hc0⟩, rfl⟩)
        exact absurd (Finset.min'_le _ _ hmem) (not_le.2 hlt)
  haveI : IsZLattice ℝ L := ⟨by rw [hLset]; exact hspan⟩
  haveI : VAddInvariantMeasure L V μ := ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩
  set ψ : C → L := fun c => ⟨j c, (hmemL _).2 ⟨c, c.2, rfl⟩⟩ with hψ
  have hψinj : Function.Injective ψ := fun c c' h => Subtype.ext (hj (congrArg Subtype.val h))
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨c, hc, hcy⟩ := (hmemL y).1 y.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  haveI : Countable L := (Module.Free.chooseBasis ℤ L).repr.injective.countable
  haveI : Countable C := hψinj.countable
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) with hDdef
  have hD : IsAddFundamentalDomain L D μ := ZLattice.isAddFundamentalDomain _ μ
  have hDfin : μ D < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  refine ⟨ZLattice.covolume L μ, ZLattice.covolume_pos L μ, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hD]
  have hR : ∫ v in D, (∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) ∂μ =
      ((μ.real D : ℝ) : ℂ) * a 0 := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set E : Γ → V → ℂ := fun x v => Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ)) with hE
    have hEnorm : ∀ x v, ‖E x v‖ₑ = 1 := by
      intro x v
      rw [← ofReal_norm_eq_enorm]
      simp only [hE]
      rw [show (2 * Real.pi * Complex.I * ((l x v : ℝ) : ℂ)) = ((2 * Real.pi * l x v : ℝ) : ℂ) *
        Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
    have hEcont : ∀ x, Continuous (E x) := fun x => by
      simp only [hE]
      fun_prop
    set s := Function.support a with hs
    have hscount : s.Countable := ha.of_norm.countable_support
    haveI : Countable s := hscount.to_subtype
    have hsub : ∀ v, ∑' x, a x * E x v = ∑' x : s, a x * E x v := fun v =>
      (tsum_subtype_eq_of_support_subset fun x hx => by
        simp only [Function.mem_support] at hx ⊢
        intro h; exact hx (by rw [h, zero_mul])).symm
    have hchar : ∀ x, ∫ v in D, a x * E x v ∂μ =
        if x = 0 then ((μ.real D : ℝ) : ℂ) * a 0 else 0 := by
      intro x
      rw [integral_const_mul]
      split_ifs with hx
      · subst hx
        simp only [hE, hl0, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
          setIntegral_const, Complex.real_smul, mul_one]
        ring
      · by_cases hax : a x = 0
        · rw [hax, zero_mul]
        · rw [setIntegral_exp_linear_fundamentalDomain_eq_zero μ L hD hDm (l x) (hl x hx)
            (fun y hy => by
              obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
              exact hint x hax c hc), mul_zero]
    show ∫ v in D, (∑' x, a x * E x v) ∂μ = _
    simp_rw [hsub]
    rw [integral_tsum]
    · rw [tsum_subtype_eq_of_support_subset (f := fun x => ∫ v in D, a x * E x v ∂μ)]
      · simp_rw [hchar]
        exact tsum_ite_eq 0 _
      · intro x hx
        rw [Function.mem_support, hchar] at hx
        split_ifs at hx with h0
        · subst h0
          intro h; exact hx (by rw [h, mul_zero])
        · exact absurd rfl hx
    · intro x
      exact ((hEcont x).const_mul (a x) |>.aestronglyMeasurable)
    · simp_rw [enorm_mul, hEnorm, mul_one, lintegral_const, Measure.restrict_apply_univ]
      rw [ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ hDfin.ne
      simp_rw [enorm_eq_nnnorm]
      refine ENNReal.tsum_coe_ne_top_iff_summable.2 ?_
      rw [← NNReal.summable_coe]
      exact ha.subtype (· ∈ s)
  have hLHS : ∫ v in D, (∑' x, Q x * F (j x + v)) ∂μ = (∑ k, Q (t k)) * ∫ v, F v ∂μ := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set e : Fin n × C → Γ := fun p => t p.1 + p.2 with he
    have heinj : Function.Injective e := by
      rintro ⟨k, c⟩ ⟨k', c'⟩ h
      simp only [he] at h
      have hk : k = k' := ht k k' (by
        rw [show t k - t k' = c' - c by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]]
        exact C.sub_mem c'.2 c.2)
      subst hk
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h))
    have hsupp : ∀ v, Function.support (fun x => Q x * F (j x + v)) ⊆ Set.range e := by
      intro v x hx
      have hQx : Q x ≠ 0 := fun h => hx (by simp [h])
      obtain ⟨k, hk⟩ := hQsupp x hQx
      exact ⟨(k, ⟨x - t k, hk⟩), by simp [he]⟩
    set g : Fin n × C → V → ℂ := fun p v => Q (t p.1) * F (j (t p.1) + (j p.2 + v)) with hg
    have hrw : ∀ v, ∑' x, Q x * F (j x + v) = ∑' p, g p v := by
      intro v
      rw [← heinj.tsum_eq (hsupp v)]
      refine tsum_congr fun p => ?_
      simp only [he, hg, map_add (f := _), hQper _ _ p.2.2, add_assoc]
    have hunf : ∀ G : V → ℂ, Integrable G μ → ∫ v, G v ∂μ = ∑' c : C, ∫ v in D, G (j c + v) ∂μ := by
      intro G hG
      rw [hD.integral_eq_tsum' G hG,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hunfl : ∀ G : V → ENNReal, ∫⁻ v, G v ∂μ = ∑' c : C, ∫⁻ v in D, G (j c + v) ∂μ := by
      intro G
      rw [hD.lintegral_eq_tsum' G,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hfinite : ∑' p, ∫⁻ v in D, ‖g p v‖ₑ ∂μ ≠ ⊤ := by
      simp_rw [hg, enorm_mul]
      simp_rw [lintegral_const_mul' _ _ enorm_ne_top]
      rw [ENNReal.tsum_prod (f := fun k (c : C) =>
        ‖Q (t k)‖ₑ * ∫⁻ v in D, ‖F (j (t k) + (j c + v))‖ₑ ∂μ), tsum_fintype]
      refine (ENNReal.sum_lt_top.2 fun k _ => ?_).ne
      rw [ENNReal.tsum_mul_left, ← hunfl (fun v => ‖F (j (t k) + v)‖ₑ)]
      exact ENNReal.mul_lt_top enorm_lt_top (hF.comp_add_left (j (t k))).hasFiniteIntegral
    have hmeas : ∀ p, AEStronglyMeasurable (g p) (μ.restrict D) := fun p =>
      (((hF.comp_add_left (j (t p.1))).comp_add_left (j p.2)).aestronglyMeasurable.const_mul
        _).restrict
    have hsumm : Summable (fun p => ∫ v in D, g p v ∂μ) := by
      refine Summable.of_norm_bounded (ENNReal.summable_toReal hfinite) fun p => ?_
      refine (norm_integral_le_lintegral_norm _).trans_eq ?_
      simp_rw [ofReal_norm_eq_enorm]
    simp_rw [hrw]
    rw [integral_tsum hmeas hfinite, hsumm.tsum_prod, tsum_fintype, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hg, integral_const_mul]
    rw [tsum_mul_left, ← hunf _ (hF.comp_add_left (j (t k))), integral_add_left_eq_self]
  rw [← hLHS, ← hR]
  exact setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) fun v _ => H v

end GlobalTheory.PoincareUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldSumInvariantLeviConj
section
namespace GlobalTheory

theorem unfold_sum_conj_invariant : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → ∀ k ∈ KM, ∀ y : P, (∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * ((s k)⁻¹ * y * s k) * u (Quotient.out x))) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK hL F hF k hk y
  set c := s k with hc_def
  have hc : c ∈ KP := hsK k hk
  have hπu : ∀ X, π (u X) = 1 := fun X => (hker _).2 ⟨X, rfl⟩
  have hex : ∀ (d : P), ∀ X, ∃ Y, u Y = d * u X * d⁻¹ := by
    intro d X
    exact (hker _).1 (by simp [map_mul, map_inv, hπu])
  choose φ hφ using hex c
  choose ψ hψ using hex c⁻¹
  have h1 : ∀ X, φ (ψ X) = X := fun X => hu (by rw [hφ, hψ]; group)
  have h2 : ∀ X, ψ (φ X) = X := fun X => hu (by rw [hψ, hφ]; group)
  have hconj : ∀ z, c * z * c⁻¹ ∈ KP ↔ z ∈ KP := by
    intro z
    constructor
    · intro h
      have := KP.mul_mem (KP.mul_mem (KP.inv_mem hc) h) hc
      simpa [mul_assoc] using this
    · intro h
      exact KP.mul_mem (KP.mul_mem hc h) (KP.inv_mem hc)
  let eN : N ≃ N := ⟨φ, ψ, h2, h1⟩
  let e : N ⧸ L ≃ N ⧸ L := Quotient.congr eN (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← hL, ← hL]
    simp only [eN, Equiv.coe_fn_mk, map_mul, map_inv, hφ]
    rw [← hconj]
    constructor <;> intro h <;> convert h using 1 <;> group)
  conv_rhs => rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro x
  set X := Quotient.out x with hX
  have hex' : e x = (QuotientGroup.mk (φ X) : N ⧸ L) := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  set Z := Quotient.out (e x) with hZ
  have hZL : Z⁻¹ * φ X ∈ L := by
    apply QuotientGroup.eq.mp
    rw [← hex']
    exact Quotient.out_eq _
  have hw : u (Z⁻¹ * φ X) ∈ KP := (hL _).2 hZL
  calc F ((u X)⁻¹ * (c⁻¹ * y * c) * u X) = F (c⁻¹ * ((u (φ X))⁻¹ * y * u (φ X)) * c) := by
        congr 1; rw [hφ]; group
    _ = F ((u (φ X))⁻¹ * y * u (φ X)) := hF c hc _
    _ = F ((u Z * u (Z⁻¹ * φ X))⁻¹ * y * (u Z * u (Z⁻¹ * φ X))) := by
        rw [← map_mul, mul_inv_cancel_left]
    _ = F ((u (Z⁻¹ * φ X))⁻¹ * ((u Z)⁻¹ * y * u Z) * u (Z⁻¹ * φ X)) := by
        congr 1; group
    _ = F ((u Z)⁻¹ * y * u Z) := hF _ hw _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralCl
section
open IsLocalRing

namespace GlobalTheory

theorem pi_eq_pow_ramificationIdx_mul_unit
    (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D]
    (P : Ideal (integralClosure S L)) [P.IsMaximal] :
    Irreducible π → algebraMap S (integralClosure S L) π ∈ P →
      ∃ ϖ : Localization.AtPrime P, Irreducible ϖ ∧ ∃ u : (Localization.AtPrime P)ˣ,
        algebraMap S (Localization.AtPrime P) π = ϖ ^ P.ramificationIdx S * (u : Localization.AtPrime P) := by
  intro hπ hπP
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hO0 : algebraMap S (integralClosure S L) π ≠ 0 := by
    intro h
    have h2 : algebraMap (integralClosure S L) L (algebraMap S (integralClosure S L) π) = 0 := by rw [h, map_zero]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S K L] at h2
    rw [map_eq_zero_iff _ (algebraMap K L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective S K)] at h2
    exact hπ0 h2
  have hPbot : P ≠ ⊥ := fun h => hO0 (by rw [h] at hπP; simpa using hπP)
  haveI hA : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure S L) hPbot (Localization.AtPrime P)
  have hinj : Function.Injective (algebraMap (integralClosure S L) (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have hx0 : algebraMap S (Localization.AtPrime P) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply S (integralClosure S L) (Localization.AtPrime P)]
    exact fun h => hO0 (hinj (by rw [h, map_zero]))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ

  have hunder : P.under S = Ideal.span {π} := by
    have hmem : π ∈ P.under S := by simpa [Ideal.under] using hπP
    have hne : P.under S ≠ ⊥ := fun h => hπ0 (by rw [h] at hmem; simpa using hmem)
    have hmax : (P.under S).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
    rw [IsLocalRing.eq_maximalIdeal hmax, hπ.maximalIdeal_eq]
  have hram : P.ramificationIdx S = n := by
    rw [Ideal.ramificationIdx_def, hunder, Ideal.map_span, Set.image_singleton, hn,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
      ENat.toNat_natCast]
  refine ⟨ϖ, hϖ, u, ?_⟩
  rw [hram, hn, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
section
noncomputable section

open Matrix

namespace GlobalTheory.HeisLatVac


open Classical in
def vacFn {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K) : (κ → K) → ℂ := by
  classical
  exact fun x => if h : ∃ u ∈ Λ, x = x₀ + u.1 then
    χ h.choose * ψ₀ (-(x₀ ⬝ᵥ h.choose.2) - ⅟(2 : K) * (h.choose.1 ⬝ᵥ h.choose.2)) else 0

end GlobalTheory.HeisLatVac
end
end

