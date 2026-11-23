module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0031
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0019
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountExtP
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem absNorm_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  induction 𝔭 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp [extP]
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.mp hx]
    simp only [extP]
    simp only [Ideal.map_top, Ideal.absNorm_top, one_pow]
  | h₃ a p ha hp ih =>
    have hpm : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hq := idealPowerSpanBounds.absNorm_extP_eq_sq hK hF hpm
    simp only [extP] at ih hq ⊢
    rw [Ideal.map_mul, map_mul, map_mul, ih, hq, mul_pow]

theorem map_comap_eq_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [conjIdeal_eq_comap] at hc
  exact SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ

theorem extP_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hP' := conjIdeal_isMaximal hK hP
  have h1 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P := Ideal.map_comap_le
  have h2 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    have : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).comap (algebraMap (𝓞 F) (𝓞 K)) =
        P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [conjIdeal_eq_comap]
      exact SplitPrimeIdeals.comap_ι_comap (conjO_eq_iff_mem_range hF) P
    rw [← this]
    exact Ideal.map_comap_le
  have hcop : IsCoprime P (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) :=
    (Ideal.isCoprime_iff_sup_eq).2 (hP.coprime_of_ne hP' (Ne.symm hc))
  have h3 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact le_inf h1 h2
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 h3
  have hN := absNorm_extP hK hF (P.comap (algebraMap (𝓞 F) (𝓞 K)))
  rw [hC, map_mul, map_mul, absNorm_conjIdeal hK, absNorm_comap_split hK hF hP hc, sq] at hN
  have hpos : 0 < Ideal.absNorm P * Ideal.absNorm P := by
    have : 0 < Ideal.absNorm P := by
      have := IdealNormInequalities.one_lt_absNorm hP
      exact_mod_cast zero_lt_one.trans this
    positivity
  have hC1 : Ideal.absNorm C = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [hN, mul_one])
  rw [hC, Ideal.absNorm_eq_one_iff.1 hC1, Ideal.mul_top]

theorem alphaStd_one (𝔭 : Ideal (𝓞 F)) :
    alphaStd K 𝔭 1 = 1 - etaF K F 𝔭 * (Ideal.absNorm 𝔭 : ℝ)⁻¹ := by
  simp [alphaStd]

theorem normRepCount_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {j : ℕ} (hj : 1 ≤ j) :
    (normRepCount K (extP K 𝔭 ^ j) 1 1 : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ j * alphaStd K 𝔭 1 := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have h1 : (1 : 𝓞 K) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hd := localDensity K hK P hP 1 j le_rfl hj 1 (map_one _) h1
  rw [alphaStd_one, etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [map_comap_eq_of_inert hK hF hP hc, hd.1 hc, if_pos hc, ← absNorm_comap_inert hK hF hP hc]
    push_cast
    rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    simp
  · rw [extP_split hK hF hP hc, hd.2 hc, if_neg hc, absNorm_comap_split hK hF hP hc]
    simp

end Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN
section
open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace MeanC

theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)

theorem finite_quot_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Finite (𝓞 F ⧸ 𝔭 ^ k) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero k (ne_bot_of_isMaximal h𝔭))

theorem one_lt_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 1 < Ideal.absNorm 𝔭 := by
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h => ne_bot_of_isMaximal h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem card_quot_pow (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Nat.card (𝓞 F ⧸ 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ k := by
  rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem vF_lt_of_notMem {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {j : ℕ} (h : n ∉ 𝔭 ^ j) : vF 𝔭 n < j := by
  have hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := ⟨j, fun e he => by
    by_contra hlt
    push_neg at hlt
    exact h (Ideal.pow_le_pow_right hlt.le he)⟩
  have hne : ({e : ℕ | n ∈ 𝔭 ^ e}).Nonempty := ⟨0, by simp⟩
  have hm : n ∈ 𝔭 ^ sSup {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem hne hb
  unfold vF
  by_contra hle
  push_neg at hle
  exact h (Ideal.pow_le_pow_right hle hm)

theorem card_out_mem (𝔭 : Ideal (𝓞 F)) {j k : ℕ} (hjk : j ≤ k) :
    Nat.card {n' : 𝓞 F ⧸ 𝔭 ^ k // Quotient.out n' ∈ 𝔭 ^ j} * Ideal.absNorm 𝔭 ^ j =
      Ideal.absNorm 𝔭 ^ k := by
  have hle : 𝔭 ^ k ≤ 𝔭 ^ j := Ideal.pow_le_pow_right hjk
  let f : (𝓞 F ⧸ 𝔭 ^ k) →+* (𝓞 F ⧸ 𝔭 ^ j) := Ideal.Quotient.factor hle
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  have hset : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k,
      Quotient.out n' ∈ 𝔭 ^ j ↔ n' ∈ f.toAddMonoidHom.ker := by
    intro n'
    rw [AddMonoidHom.mem_ker]
    conv_rhs => rw [← Ideal.Quotient.mk_out n']
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, f,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  have e1 : Nat.card {n' : 𝓞 F ⧸ 𝔭 ^ k // Quotient.out n' ∈ 𝔭 ^ j} =
      Nat.card f.toAddMonoidHom.ker := Nat.card_congr (Equiv.subtypeEquivRight hset)
  have h2 : (f.toAddMonoidHom.ker).index = Nat.card (𝓞 F ⧸ 𝔭 ^ j) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hf).toEquiv
  have h1 := AddSubgroup.card_mul_index (f.toAddMonoidHom.ker)
  rw [h2, card_quot_pow, card_quot_pow] at h1
  rw [e1, h1]

end MeanC

theorem sum_nkCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, nkCount h L 𝔭 k (Quotient.out n') =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V * k) := by
  classical
  haveI := MeanC.finite_quot_pow h𝔭 k
  have hN := MeanC.one_lt_absNorm h𝔭
  haveI : Finite (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :=
    Nat.finite_of_card_ne_zero (by
      rw [MeanB.card_quot_extP hK hF hL h𝔭 k]; exact pow_ne_zero _ (by omega))
  let nv : ↥L → 𝓞 F := fun y => (MeanB.exists_val hF hs hLi y).choose
  have hnv : ∀ y : ↥L, h (y : V) (y : V) = algebraMap F K (nv y : F) :=
    fun y => (MeanB.exists_val hF hs hLi y).choose_spec
  let rep : (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) → ↥L :=
    fun x => (Submodule.Quotient.mk_surjective _ x).choose
  have hrep : ∀ x, Submodule.Quotient.mk (rep x) = x :=
    fun x => (Submodule.Quotient.mk_surjective _ x).choose_spec
  let φ : (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) → 𝓞 F ⧸ 𝔭 ^ k :=
    fun x => Ideal.Quotient.mk _ (nv (rep x))
  have hfib : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k,
      nkCount h L 𝔭 k (Quotient.out n') = Nat.card {x // φ x = n'} := by
    intro n'
    unfold nkCount
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · rintro ⟨y, hy, hc⟩
      rw [hnv y, MeanB.congrP_algebraMap_iff_sub_mem h𝔭] at hc
      have hyx : rep x - y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
        (Submodule.Quotient.eq _).mp ((hrep x).trans hy.symm)
      have h2 := MeanB.val_congr hF hs hLi 𝔭 k hyx (hnv _) (hnv y)
      show Ideal.Quotient.mk _ (nv (rep x)) = n'
      conv_rhs => rw [← Ideal.Quotient.mk_out n']
      rw [Ideal.Quotient.eq]
      have := Ideal.add_mem _ h2 hc
      simpa using this
    · intro hx
      refine ⟨rep x, hrep x, ?_⟩
      rw [hnv, MeanB.congrP_algebraMap_iff_sub_mem h𝔭]
      rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
      exact hx
  letI := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ k)
  rw [finsum_eq_sum_of_fintype]
  simp_rw [hfib]
  rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv φ),
    MeanB.card_quot_extP hK hF hL h𝔭 k]

theorem alphaN_eq_of_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {n : 𝓞 F} (hn : n ≠ 0) {k : ℕ} (hk : 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k) :
    alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  exact firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hn) (by omega)

theorem tendsto_mean_alphaN (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Tendsto (fun k : ℕ => (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n')) atTop (𝓝 1) := by
  classical
  obtain ⟨C0, hC0⟩ := nkCount_le hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm h𝔭
  have hN1 := MeanC.one_lt_absNorm h𝔭
  have hNpos : (0:ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  have hCnn : (0:ℝ) ≤ max C0 0 := le_max_right _ _
  have hratio : ∀ (k : ℕ) (n : 𝓞 F), (nkCount h L 𝔭 k n : ℝ) /
      (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) ≤ max C0 0 := fun k n => by
    rw [div_le_iff₀ (pow_pos hNpos _)]
    exact (hC0 k n).trans (by gcongr; exact le_max_left _ _)
  have hratio0 : ∀ (k : ℕ) (n : 𝓞 F), 0 ≤ (nkCount h L 𝔭 k n : ℝ) /
      (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := fun k n => by positivity
  have hα : ∀ n : 𝓞 F, n ≠ 0 → |alphaN h L 𝔭 n| ≤ max C0 0 := by
    intro n hn
    rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn (k := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) le_rfl,
      abs_of_nonneg (hratio0 _ _)]
    exact hratio _ _
  let j : ℕ → ℕ := fun k => (k - 2 * vd h L 𝔭) / 2
  have hjk : ∀ k, j k ≤ k := fun k => by
    show (k - 2 * vd h L 𝔭) / 2 ≤ k
    omega
  have hgood : ∀ (k : ℕ) (n : 𝓞 F), n ∉ 𝔭 ^ j k →
      n ≠ 0 ∧ 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k := by
    intro k n hn
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hn (Ideal.zero_mem _)
    · have : vF 𝔭 n < (k - 2 * vd h L 𝔭) / 2 := MeanC.vF_lt_of_notMem hn
      omega
  have key : ∀ k : ℕ, |(Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n') - 1| ≤
        (2 * max C0 0 + |alphaN h L 𝔭 0|) * ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ (j k) := by
    intro k
    haveI := MeanC.finite_quot_pow h𝔭 k
    letI := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ k)
    have hsumr : ∑ n' : 𝓞 F ⧸ 𝔭 ^ k, (nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
        (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) = (Ideal.absNorm 𝔭 : ℝ) ^ k := by
      have hS := sum_nkCount hK hF hs hd hL hLi h𝔭 k
      rw [finsum_eq_sum_of_fintype] at hS
      rw [← Finset.sum_div, ← Nat.cast_sum, hS]
      push_cast
      rw [div_eq_iff (pow_ne_zero _ hNpos.ne'), ← pow_add]
      congr 1
      have h2f : 2 * finrank K V - 1 + 1 = 2 * finrank K V := by omega
      nth_rewrite 1 [← h2f]
      ring
    rw [finsum_eq_sum_of_fintype]
    have hdiff : (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) *
        ∑ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n') - 1 =
        (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * ∑ n' : 𝓞 F ⧸ 𝔭 ^ k,
          (alphaN h L 𝔭 (Quotient.out n') - (nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
            (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))) := by
      rw [Finset.sum_sub_distrib, hsumr, mul_sub, zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ hNpos.ne')]
    rw [hdiff]
    have hterm : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k, |alphaN h L 𝔭 (Quotient.out n') -
        (nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
          (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))| ≤
        if Quotient.out n' ∈ 𝔭 ^ j k then 2 * max C0 0 + |alphaN h L 𝔭 0| else 0 := by
      intro n'
      split_ifs with hin
      · have h1 : |alphaN h L 𝔭 (Quotient.out n')| ≤ max C0 0 + |alphaN h L 𝔭 0| := by
          by_cases h0 : Quotient.out n' = 0
          · rw [h0]
            linarith
          · linarith [hα _ h0, abs_nonneg (alphaN h L 𝔭 0)]
        have h2 := hratio k (Quotient.out n')
        have h3 := hratio0 k (Quotient.out n')
        calc _ ≤ |alphaN h L 𝔭 (Quotient.out n')| + |(nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
              (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))| := abs_sub _ _
          _ ≤ _ := by
            rw [abs_of_nonneg h3]
            linarith
      · obtain ⟨hn0, hk⟩ := hgood k _ hin
        rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn0 hk, sub_self, abs_zero]
    have hcount : ((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k =>
        Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) * (Ideal.absNorm 𝔭 : ℝ) ^ (j k) =
          (Ideal.absNorm 𝔭 : ℝ) ^ k := by
      have h1 := MeanC.card_out_mem 𝔭 (hjk k)
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
      exact_mod_cast h1
    rw [abs_mul, abs_of_pos (zpow_pos hNpos _)]
    calc _ ≤ (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * ∑ n' : 𝓞 F ⧸ 𝔭 ^ k,
          (if Quotient.out n' ∈ 𝔭 ^ j k then 2 * max C0 0 + |alphaN h L 𝔭 0| else 0) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' _ => hterm n')
      _ = (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * (((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k =>
          Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) * (2 * max C0 0 + |alphaN h L 𝔭 0|)) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ = _ := by
          rw [zpow_neg, zpow_natCast, ← hcount, inv_pow]
          have hc0 : ((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k =>
              Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) ≠ 0 := by
            intro h0
            rw [h0, zero_mul] at hcount
            exact (pow_pos hNpos k).ne' hcount.symm
          field_simp
  have hj : Tendsto j atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b + 2 * vd h L 𝔭, fun k hk => ?_⟩
    show b ≤ (k - 2 * vd h L 𝔭) / 2
    omega
  have hlim : Tendsto (fun k => (2 * max C0 0 + |alphaN h L 𝔭 0|) *
      ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ (j k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast hN1))
    simpa using (h1.comp hj).const_mul (2 * max C0 0 + |alphaN h L 𝔭 0|)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact key k) hlim

end Formalism.HermitianLattices.Ext.L3
end
end

