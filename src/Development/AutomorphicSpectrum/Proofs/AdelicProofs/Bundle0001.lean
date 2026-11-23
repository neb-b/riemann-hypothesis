module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.EqOneOfPowEqLeExponent
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem eq_one_of_pow_eq_le_exponent {a n m : ℕ} (ha : a ≠ 0) (h : a ^ n = m) (hm : m ≤ n) : a = 1 := by
  by_contra h1
  have h2 : 1 < a := by omega
  have := Nat.lt_pow_self (n := n) h2
  omega

theorem ratUnit_eq_one_of_divisible :
    ∀ x : ℚˣ, (∀ n : ℕ, 0 < n → ∃ y : ℚˣ, y ^ n = x) → x = 1 := by
  intro x h
  obtain ⟨y, hy⟩ := h (2 * ((x : ℚ).num.natAbs + (x : ℚ).den + 1)) (by omega)
  set n := 2 * ((x : ℚ).num.natAbs + (x : ℚ).den + 1) with hn
  have hq : (y : ℚ) ^ n = (x : ℚ) := by rw [← hy]; simp
  have hnum : (y : ℚ).num ^ n = (x : ℚ).num := by rw [← hq, Rat.num_pow]
  have hden : (y : ℚ).den ^ n = (x : ℚ).den := by rw [← hq, Rat.den_pow]
  have h1 : (y : ℚ).den = 1 := eq_one_of_pow_eq_le_exponent (y : ℚ).den_nz hden (by omega)
  have h2 : (y : ℚ).num.natAbs = 1 :=
    eq_one_of_pow_eq_le_exponent (n := n) (m := (x : ℚ).num.natAbs)
      (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 y.ne_zero))
      (by rw [← hnum, Int.natAbs_pow]) (by omega)
  have h3 : (y : ℚ).num ^ 2 = 1 := by
    rcases Int.natAbs_eq_iff.1 h2 with h | h <;> rw [h] <;> simp
  have h4 : (x : ℚ).num = 1 := by rw [← hnum, hn, pow_mul, h3, one_pow]
  have h5 : (x : ℚ).den = 1 := by rw [← hden, h1, one_pow]
  apply Units.ext
  rw [Units.val_one, ← Rat.num_div_den (x : ℚ), h4, h5]
  simp

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.MapMulRightEqOfMemCompactSubgroup
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.Xa1

theorem map_mul_right_eq_of_mem_compact_subgroup :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsMulLeftInvariant → IsFiniteMeasureOnCompacts μ → ∀ K : Subgroup G, IsCompact (K : Set G) → ∀ k ∈ K, μ.map (fun x => x * k) = μ := by
  intro G _ _ _ _ _ _ _ _ μ hinv hfin K hK k hk
  let ν : Measure G := Measure.haar
  have hmeas : Measurable (fun x : G => x * k) := measurable_mul_const k
  have key : ν.map (fun x => x * k) = ν := by
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
    have hS : IsCompact (C * (K : Set G)) := hC.mul hK
    have hsub : C ⊆ C * (K : Set G) := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
    have hpos : ν (C * (K : Set G)) ≠ 0 :=
      ((Measure.measure_pos_of_mem_nhds ν hC1).trans_le (measure_mono hsub)).ne'
    have htop : ν (C * (K : Set G)) ≠ ⊤ := hS.measure_lt_top.ne
    have hpre : (fun x : G => x * k) ⁻¹' (C * (K : Set G)) = C * (K : Set G) := by
      ext x
      constructor
      · rintro ⟨c, hc, l, hl, h⟩
        refine ⟨c, hc, l * k⁻¹, K.mul_mem hl (K.inv_mem hk), ?_⟩
        simp only at h ⊢
        rw [← mul_assoc, h, mul_inv_cancel_right]
      · rintro ⟨c, hc, l, hl, rfl⟩
        exact ⟨c, hc, l * k, K.mul_mem hl hk, (mul_assoc _ _ _).symm⟩
    haveI : IsFiniteMeasureOnCompacts (ν.map (fun x => x * k)) :=
      ⟨fun L hL => by
        rw [Measure.map_apply hmeas hL.measurableSet]
        exact ((Homeomorph.mulRight k).isCompact_preimage.2 hL).measure_lt_top⟩
    have h1 := Measure.isMulLeftInvariant_eq_smul (ν.map (fun x => x * k)) ν
    set c := Measure.haarScalarFactor (ν.map (fun x => x * k)) ν with hc
    have h2 : (ν.map (fun x => x * k)) (C * (K : Set G)) = ν (C * (K : Set G)) := by
      rw [Measure.map_apply hmeas hS.measurableSet, hpre]
    rw [h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    have h3 : (c : ℝ≥0∞) = 1 := by
      have := (ENNReal.mul_left_inj hpos htop).1 (h2.trans (one_mul _).symm)
      exact this
    have h4 : c = 1 := by exact_mod_cast h3
    rw [h1, h4, one_smul]
  have h := Measure.isMulLeftInvariant_eq_smul μ ν
  rw [h, Measure.map_smul, key]
  exact hmeas.aemeasurable

end GlobalTheory.CompanionTheory.Xa1
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.RelIndexInfEqOfMemMul
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem relIndex_inf_eq_of_mem_mul : ∀ (G : Type) [Group G] (Γ K₁ K₂ : Subgroup G),
    (∀ k ∈ K₂, ∃ γ ∈ Γ, ∃ k' ∈ K₁ ⊓ K₂, k = γ * k') →
      (K₁ ⊓ Γ).relIndex (K₂ ⊓ Γ) = K₁.relIndex K₂ := by
  intro G _ Γ K₁ K₂ h
  unfold Subgroup.relIndex Subgroup.index
  let i : ↥(K₂ ⊓ Γ) → ↥K₂ := fun x => ⟨x.1, x.2.1⟩
  have key : ∀ a b : ↥(K₂ ⊓ Γ),
      (QuotientGroup.leftRel ((K₁ ⊓ Γ).subgroupOf (K₂ ⊓ Γ))) a b ↔
      (QuotientGroup.leftRel (K₁.subgroupOf K₂)) (i a) (i b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro H
      exact H.1
    · intro H
      exact ⟨H, (a⁻¹ * b).2.2⟩
  let f : ↥(K₂ ⊓ Γ) ⧸ (K₁ ⊓ Γ).subgroupOf (K₂ ⊓ Γ) → ↥K₂ ⧸ K₁.subgroupOf K₂ :=
    Quotient.map' i (fun a b H => (key a b).1 H)
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro x y
    induction x using Quotient.inductionOn' with | h a => ?_
    induction y using Quotient.inductionOn' with | h b => ?_
    intro H
    exact Quotient.sound' ((key a b).2 (Quotient.exact' H))
  · intro y
    induction y using Quotient.inductionOn' with | h k => ?_
    obtain ⟨γ, hγ, k', hk', e⟩ := h k.1 k.2
    have hγ2 : γ ∈ K₂ := by
      have : γ = k.1 * k'⁻¹ := by rw [e]; simp
      rw [this]
      exact K₂.mul_mem k.2 (K₂.inv_mem hk'.2)
    refine ⟨Quotient.mk'' ⟨γ, hγ2, hγ⟩, Quotient.sound' ?_⟩
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have : ((((i ⟨γ, hγ2, hγ⟩)⁻¹ * k : ↥K₂)) : G) = k' := by
      simp [i, e]
    rw [this]
    exact hk'.1

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.RelIndexNeZeroOfIsCompactOfRelOpen
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem relIndex_ne_zero_of_isCompact_of_relOpen :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S K K' : Subgroup G),
      K' ≤ S → IsCompact (K' : Set G) →
      (∃ O : Set G, IsOpen O ∧ O ∩ (S : Set G) = (K : Set G)) → K.relIndex K' ≠ 0 := by
  intro G _ _ _ S K K' hK'S hK' ⟨O, hO, hOS⟩
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
  have hopen : IsOpen ((K.subgroupOf K' : Subgroup K') : Set K') := by
    have hset : ((K.subgroupOf K' : Subgroup K') : Set K') = Subtype.val ⁻¹' O := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
      constructor
      · intro hx
        have : (x : G) ∈ O ∩ (S : Set G) := by rw [hOS]; exact hx
        exact this.1
      · intro hx
        have : (x : G) ∈ O ∩ (S : Set G) := ⟨hx, hK'S x.2⟩
        rw [hOS] at this
        exact this
    rw [hset]
    exact hO.preimage continuous_subtype_val
  have := (K.subgroupOf K').quotient_finite_of_isOpen hopen
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.RelIndexRatioCocycle
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem relIndex_ratio_cocycle : ∀ (G : Type) [Group G] (A B C : Subgroup G), A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → B.relIndex C ≠ 0 → C.relIndex B ≠ 0 → A.relIndex C ≠ 0 ∧ C.relIndex A ≠ 0 ∧ B.relIndex A * C.relIndex B * A.relIndex C = A.relIndex B * B.relIndex C * C.relIndex A := by
  intro G _ A B C hAB hBA hBC hCB
  have hAC : A.relIndex C ≠ 0 := Subgroup.relIndex_ne_zero_trans hAB hBC
  have hCA : C.relIndex A ≠ 0 := Subgroup.relIndex_ne_zero_trans hCB hBA
  refine ⟨hAC, hCA, ?_⟩
  set T : Subgroup G := A ⊓ B ⊓ C with hT
  have hTAB : T ≤ A ⊓ B := inf_le_left
  have hTBC : T ≤ B ⊓ C := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hTAC : T ≤ A ⊓ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have h1 := Subgroup.relIndex_mul_relIndex T (A ⊓ B) A hTAB inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex T (A ⊓ B) B hTAB inf_le_right
  have h3 := Subgroup.relIndex_mul_relIndex T (B ⊓ C) B hTBC inf_le_left
  have h4 := Subgroup.relIndex_mul_relIndex T (B ⊓ C) C hTBC inf_le_right
  have h5 := Subgroup.relIndex_mul_relIndex T (A ⊓ C) A hTAC inf_le_left
  have h6 := Subgroup.relIndex_mul_relIndex T (A ⊓ C) C hTAC inf_le_right
  rw [Subgroup.inf_relIndex_left A B] at h1
  rw [Subgroup.inf_relIndex_left] at h3 h5
  rw [Subgroup.inf_relIndex_right] at h2 h4 h6
  have hTC : T.relIndex C ≠ 0 := by
    rw [hT, Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_inf_ne_zero hAC hBC
  have hTB : T.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hTC hCB
  have hx : T.relIndex (A ⊓ B) ≠ 0 := left_ne_zero_of_mul (h2 ▸ hTB)
  have hy : T.relIndex (B ⊓ C) ≠ 0 := left_ne_zero_of_mul (h4 ▸ hTC)
  have hz : T.relIndex (A ⊓ C) ≠ 0 := left_ne_zero_of_mul (h6 ▸ hTC)
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hx hy) hz)
  calc T.relIndex (A ⊓ B) * T.relIndex (B ⊓ C) * T.relIndex (A ⊓ C) *
        (B.relIndex A * C.relIndex B * A.relIndex C)
      = (T.relIndex (A ⊓ B) * B.relIndex A) * (T.relIndex (B ⊓ C) * C.relIndex B) *
        (T.relIndex (A ⊓ C) * A.relIndex C) := by ring
    _ = (T.relIndex (A ⊓ C) * C.relIndex A) * (T.relIndex (A ⊓ B) * A.relIndex B) *
        (T.relIndex (B ⊓ C) * B.relIndex C) := by rw [h1, h2, h3, h4, h5, h6]
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstant
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv


open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem const_of_orthogonal_log_units : ∀ (F : Type) [Field F] [NumberField F] (m : (F →+* ℂ) → ℝ),
    (∀ sg, m (ComplexEmbedding.conjugate sg) = m sg) →
    (∀ θ : (𝓞 F)ˣ, ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = 0) →
    ∀ sg sg', m sg = m sg' := by
  open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem in
  intro F _ _ m hconj horth
  classical

  have hdesc : ∀ sg sg' : F →+* ℂ, InfinitePlace.mk sg = InfinitePlace.mk sg' → m sg = m sg' := by
    intro sg sg' h
    rcases InfinitePlace.mk_eq_iff.mp h with h | h
    · rw [h]
    · rw [← h, hconj]
  set mw : InfinitePlace F → ℝ := fun w => m w.embedding with hmw
  have hmk : ∀ sg : F →+* ℂ, m sg = mw (InfinitePlace.mk sg) := by
    intro sg
    exact hdesc _ _ (by simp [InfinitePlace.mk_embedding])

  have hplace : ∀ θ : (𝓞 F)ˣ,
      ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) * mw w = 0 := by
    intro θ
    rw [← horth θ, ← Finset.sum_fiberwise Finset.univ (fun sg : F →+* ℂ => InfinitePlace.mk sg)]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hfib : ∀ sg ∈ Finset.univ.filter (fun sg : F →+* ℂ => InfinitePlace.mk sg = w),
        Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = Real.log (w ((θ : 𝓞 F) : F)) * mw w := by
      intro sg hsg
      have hsg' : InfinitePlace.mk sg = w := (Finset.mem_filter.mp hsg).2
      rw [hmk sg, hsg', ← hsg', InfinitePlace.apply]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul,
      mul_assoc]

  let L : logSpace F →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ w, x w * (mw w.1 - mw w₀)
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum, mul_assoc] }
  have hLunit : ∀ θ : (𝓞 F)ˣ, L (logEmbedding F (Additive.ofMul θ)) = 0 := by
    intro θ
    have h1 : ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) = 0 := by
      exact_mod_cast sum_mult_mul_log θ
    have h2 : ∑ w : InfinitePlace F,
        (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) * (mw w - mw w₀) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hplace θ, ← Finset.sum_mul, h1]
      simp
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace F)] at h2
    simpa [L, logEmbedding_component] using h2
  have hL : L = 0 := by
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ Submodule.span ℝ (unitLattice F : Set (logSpace F)) := by
      rw [unitLattice_span_eq_top]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      exact hLunit (Additive.toMul a)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  have hconst : ∀ w : InfinitePlace F, mw w = mw w₀ := by
    intro w
    by_cases hw : w = w₀
    · rw [hw]
    · have := LinearMap.congr_fun hL (Pi.single ⟨w, hw⟩ 1)
      have h3 : mw w - mw w₀ = 0 := by
        simpa [L, Pi.single_apply, Finset.sum_ite_eq] using this
      linarith
  intro sg sg'
  rw [hmk sg, hmk sg', hconst (InfinitePlace.mk sg), hconst (InfinitePlace.mk sg')]

end GlobalTheory.CompanionTheory.Ar.Giv
end

