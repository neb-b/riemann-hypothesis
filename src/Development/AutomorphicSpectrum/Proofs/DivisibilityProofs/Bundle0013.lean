module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerIdentityAtCutoff
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem abs_apply_le_of_monomial_bound {σ : Type} (G : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (F : MvPolynomial σ ℝ) {d : ℕ}
    (hF : F.IsHomogeneous d) {e : ℝ} (he : ∀ m : σ →₀ ℕ, m.degree = d → |G (monomial m 1)| ≤ e) :
    |G F| ≤ (∑ m ∈ F.support, |F.coeff m|) * e := by
  have h1 : G F = ∑ m ∈ F.support, F.coeff m * G (monomial m 1) := by
    conv_lhs => rw [F.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : monomial m (F.coeff m) = F.coeff m • monomial m (1 : ℝ) := by
      rw [smul_monomial]; simp
    rw [this, map_smul, smul_eq_mul]
  rw [h1, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left (he m ?_) (abs_nonneg _)
  by_contra hne
  exact (mem_support_iff.mp hm) (hF.coeff_eq_zero hne)

theorem tendsto_coeffs_of_tests {a b R₁ R₂ E₁ E₂ : ℕ → ℝ} {v H₁ H₂ L₁ L₂ r₁ r₂ s₁ n s₂ t₂ : ℝ}
    (hv : v ≠ 0) (hn : n ≠ 0) (hs₂ : s₂ ≠ 0) (ht₂ : t₂ = 0)
    (hR₁ : Tendsto R₁ atTop (𝓝 r₁)) (hR₂ : Tendsto R₂ atTop (𝓝 r₂))
    (hE₁ : Tendsto E₁ atTop (𝓝 0)) (hE₂ : Tendsto E₂ atTop (𝓝 0))
    (h₁ : ∀ᶠ B in atTop, L₁ = v * (H₁ - a B * s₁ - b B * n + R₁ B) + E₁ B)
    (h₂ : ∀ᶠ B in atTop, L₂ = v * (H₂ - a B * s₂ - b B * t₂ + R₂ B) + E₂ B) :
    ∃ A b₀ : ℝ, Tendsto a atTop (𝓝 A) ∧ Tendsto b atTop (𝓝 b₀) := by
  subst ht₂
  have ha : Tendsto a atTop (𝓝 ((H₂ + r₂ + 0 / v - L₂ / v) / s₂)) := by
    have h := (((hR₂.const_add H₂).add (hE₂.div_const v)).sub_const (L₂ / v)).div_const s₂
    refine h.congr' ?_
    filter_upwards [h₂] with B hB
    rw [hB]
    field_simp
    ring
  have hb : Tendsto b atTop (𝓝 ((H₁ - (H₂ + r₂ + 0 / v - L₂ / v) / s₂ * s₁ + r₁ + 0 / v - L₁ / v) / n)) := by
    have h := (((((ha.mul_const s₁).const_sub H₁).add hR₁).add (hE₁.div_const v)).sub_const (L₁ / v)).div_const n
    refine h.congr' ?_
    filter_upwards [h₁] with B hB
    rw [hB]
    field_simp
    ring
  exact ⟨_, _, ha, hb⟩

theorem eq_of_tendsto_coeffs {a b R E : ℕ → ℝ} {v H L s t A b₀ r : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 b₀)) (hR : Tendsto R atTop (𝓝 r))
    (hE : Tendsto E atTop (𝓝 0))
    (h : ∀ᶠ B in atTop, L = v * (H - a B * s - b B * t + R B) + E B) :
    L = v * (H - A * s - b₀ * t + r) := by
  have h1 : Tendsto (fun B => v * (H - a B * s - b B * t + R B) + E B) atTop
      (𝓝 (v * (H - A * s - b₀ * t + r) + 0)) :=
    ((((((ha.mul_const s).const_sub H).sub (hb.mul_const t)).add hR).const_mul v)).add hE
  have h2 : Tendsto (fun B => v * (H - a B * s - b B * t + R B) + E B) atTop (𝓝 L) :=
    tendsto_const_nhds.congr' (h.mono fun B hB => hB)
  simpa using tendsto_nhds_unique h2 h1

theorem tendsto_const_mul_log_div (c C : ℝ) :
    Tendsto (fun B : ℕ => c * (C * Real.log B / B)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have h2 := (h.const_mul C).const_mul c
  simp only [mul_zero] at h2
  refine h2.congr fun B => ?_
  simp [mul_div_assoc]

section

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem pk_mul_isHomogeneous (hN : 2 ≤ N) (τ : Ψ) {k : ℕ} (hk : k ≤ N) {Q : RP Ψ N}
    (hQ : Q.IsHomogeneous (dimFl Ψ N + 1 - k)) : (pk τ k * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
  have hpk : (pk τ k : RP Ψ N).IsHomogeneous k :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
  have h1 : N - 1 ≤ N * (N - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num), mul_comm N]
    exact Nat.mul_le_mul_left _ hN
  have h2 : N * (N - 1) / 2 ≤ dimFl Ψ N :=
    Nat.le_mul_of_pos_left _ (Fintype.card_pos_iff.mpr ⟨τ⟩)
  have h3 : k + (dimFl Ψ N + 1 - k) = dimFl Ψ N + 1 := by omega
  simpa [h3] using hpk.mul hQ

theorem exists_finite_identity (II : IntersectionSystem) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ)
    (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (hshape : FrobShape frob) (h6 : T.Prop6 II frob) (hBA : T.ThmBA II hh)
    (B₀ : ℕ) (hB₀ : 2 ≤ B₀) :
    ∃ a b : ℕ → ℝ, ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) →
      ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
        T.PPt II B₀ (pk τ k * Q) = T.volT * (hh (pk τ k * Q) - a B * ∑ σ, Sh T.j σ (pk τ k * Q) -
          b B * ∑ σ, Tot σ (pk τ k * Q) +
          ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad), restTerm T.j p (frob p τ) k Q) + E B := by
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.deltaTerm_eq Ψ N T.j frob T.j_lt.le (by omega) hshape
  obtain ⟨-, hSh, hTot, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.degFl_Sh_Tot_linear Ψ N
  choose ΦS hΦS using hSh
  choose ΦT hΦT using hTot
  obtain ⟨C, B₁, hC⟩ := hBA
  choose! α β hαβ using hC
  let PL : ℕ → (RP Ψ N →ₗ[ℝ] ℝ) := fun B => ∑ c, ((T.M B c).PP II).comp (rename some).toLinearMap
  have hPL : ∀ B F, PL B F = T.PPt II B F := by
    intro B F
    simp [PL, RootTower.PPt, RootTower.PPc, toA, LinearMap.sum_apply]
  let G : ℕ → (RP Ψ N →ₗ[ℝ] ℝ) := fun B =>
    PL B - T.volT • (hh - (α B - β B) • (∑ σ, ΦS T.j σ) - β B • (∑ σ, ΦT σ))
  have hG : ∀ B F, G B F = T.PPt II B F - T.volT * (hh F - (α B - β B) * ∑ σ, Sh T.j σ F -
      β B * ∑ σ, Tot σ F) := by
    intro B F
    simp [G, hPL, LinearMap.sum_apply, hΦS, hΦT]
  let S : ℕ → Finset ℕ := fun B => (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad)
  refine ⟨fun B => α B - β B + ∑ p ∈ S B, Real.log p / ((p : ℝ) - 1), fun B => β B - ∑ p ∈ S B, κ p,
    fun τ k hk1 hkN Q hQ => ?_⟩
  have hF := pk_mul_isHomogeneous hN τ hkN hQ
  refine ⟨fun B => G B (pk τ k * Q), ?_, ?_⟩
  · refine squeeze_zero_norm' ?_ (tendsto_const_mul_log_div (∑ m ∈ (pk τ k * Q : RP Ψ N).support,
      |(pk τ k * Q : RP Ψ N).coeff m|) C)
    filter_upwards [eventually_ge_atTop B₁] with B hB
    rw [Real.norm_eq_abs]
    refine abs_apply_le_of_monomial_bound (G B) _ hF fun m hm => ?_
    rw [hG]
    exact hαβ B hB m hm
  · filter_upwards [eventually_ge_atTop B₀] with B hB
    have hsum : T.PPt II B₀ (pk τ k * Q) = T.PPt II B (pk τ k * Q) +
        T.volT * ∑ p ∈ S B, deltaTerm T.j p τ (frob p τ) k Q := by
      simp only [RootTower.PPt, RootTower.volT, Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => h6 B₀ B hB₀ hB c τ k hk1 hkN Q hQ
    have hdelta : ∑ p ∈ S B, deltaTerm T.j p τ (frob p τ) k Q =
        -(∑ p ∈ S B, Real.log p / ((p : ℝ) - 1)) * ∑ σ, Sh T.j σ (pk τ k * Q) +
          (∑ p ∈ S B, κ p) * ∑ σ, Tot σ (pk τ k * Q) + ∑ p ∈ S B, restTerm T.j p (frob p τ) k Q := by
      rw [Finset.sum_congr rfl fun p hp => hκ p τ k Q
        (Finset.mem_filter.mp hp).2.1.two_le hk1]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        Finset.sum_neg_distrib]
    show T.PPt II B₀ (pk τ k * Q) = _
    rw [hG, hsum, hdelta]
    ring

end

end GlobalTheory.CompanionTheory.Ar.Top

theorem GlobalTheory.CompanionTheory.Ar.Top.exists_identAt : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), T.Proportional → FrobShape frob →
    T.Prop6 II frob → T.ThmBA II hh → ∀ B₀ : ℕ, 2 ≤ B₀ → ∃ A₀ b₀ : ℝ, T.IdentAt II hh frob B₀ A₀ b₀ := by
  intro II Ψ _ _ N T hh frob hprop hshape h6 hBA B₀ hB₀
  have hvol : 0 < T.volT := Finset.sum_pos (fun c _ => hprop.1 c) Finset.univ_nonempty
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  obtain ⟨a, b, hid⟩ := exists_finite_identity II T hh frob hshape h6 hBA B₀ hB₀
  have hrest : ∀ (τ : Ψ) (k : ℕ) (Q : RP Ψ N), _ := fun τ k Q =>
    (_root_.GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto Ψ N T.j T.bad frob τ k Q).2 B₀
  by_cases hΨ : Nonempty Ψ
  · obtain ⟨τ₀⟩ := hΨ
    obtain ⟨⟨Q₁, hQ₁, hd₁⟩, Q₂, hQ₂, hd₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.testForms_sh_tot Ψ N T.j τ₀ T.j_pos T.j_lt
    have hQ₁' : Q₁.IsHomogeneous (dimFl Ψ N + 1 - 1) := by simpa using hQ₁
    have hQ₂' : Q₂.IsHomogeneous (dimFl Ψ N + 1 - 2) := by
      have : dimFl Ψ N + 1 - 2 = dimFl Ψ N - 1 := by omega
      rwa [this]
    obtain ⟨E₁, hE₁, h₁⟩ := hid τ₀ 1 le_rfl (by omega) Q₁ hQ₁'
    obtain ⟨E₂, hE₂, h₂⟩ := hid τ₀ 2 (by omega) hN Q₂ hQ₂'
    have hn : ∑ σ, Tot σ (pk τ₀ 1 * Q₁) ≠ 0 := by
      have h5 := fun σ => (_root_.GlobalTheory.CompanionTheory.Ar.Top.sh_tot_pk_mul Ψ N T.j τ₀ σ 1 Q₁ le_rfl).2
      simp only [h5, hd₁]
      simp
      omega
    have hs₂ : ∑ σ, Sh T.j σ (pk τ₀ 2 * Q₂) ≠ 0 := by
      have h5 := fun σ => (_root_.GlobalTheory.CompanionTheory.Ar.Top.sh_tot_pk_mul Ψ N T.j τ₀ σ 2 Q₂ (by omega)).1
      simp only [h5]
      simp [hd₂]
    have ht₂ : ∑ σ, Tot σ (pk τ₀ 2 * Q₂) = 0 := by
      have h5 := fun σ => (_root_.GlobalTheory.CompanionTheory.Ar.Top.sh_tot_pk_mul Ψ N T.j τ₀ σ 2 Q₂ (by omega)).2
      simp [h5]
    obtain ⟨A₀, b₀, ha, hb⟩ := tendsto_coeffs_of_tests hvol.ne' hn hs₂ ht₂
      (hrest τ₀ 1 Q₁) (hrest τ₀ 2 Q₂) hE₁ hE₂ h₁ h₂
    refine ⟨A₀, b₀, fun τ k hk1 hkN Q hQ => ?_⟩
    obtain ⟨E, hE, h⟩ := hid τ k hk1 hkN Q hQ
    exact eq_of_tendsto_coeffs ha hb (hrest τ k Q) hE h
  · exact ⟨0, 0, fun τ => (hΨ ⟨τ⟩).elim⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberZeroOfHorizontal
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem relDim_lt_of_dim_lt {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} (I : Ideal (MRing ι F)) (n : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) < ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim I < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  unfold GroundTheory.Heights₂.Heights.FieldNumbers.relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) < ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      exact not_top_lt h'
    | coe m =>
      have h' : ((m : ℕ) : ℕ∞) < ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      have h'' : m < n + Fintype.card K := by exact_mod_cast h'
      have hlt : (m : ℤ) - Fintype.card K < n := by omega
      change (((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) <
        (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact_mod_cast hlt

theorem dim_lt_of_two_drops {a b : WithBot ℕ∞} {n : ℕ} (h₁ : a + 1 ≤ b)
    (h₂ : b + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) : a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp at h₁
    | coe b =>
      have h₁' : a + 1 ≤ b := by exact_mod_cast h₁
      have h₂' : b + 1 ≤ ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast h₂
      have h₃ : b ≤ (n : ℕ∞) := by
        have : b + 1 ≤ (n : ℕ∞) + 1 := by exact_mod_cast h₂'
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 this
      have h₄ : a < (n : ℕ∞) := by
        refine lt_of_lt_of_le ?_ h₃
        refine lt_of_lt_of_le ?_ h₁'
        refine ENat.lt_add_one_iff ?_ |>.2 le_rfl
        rintro rfl
        simp at h₁'
        subst h₁'
        simp at h₃
      exact_mod_cast h₄

theorem specialIdeal_dim_add_one_le {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι O)) [W.IsPrime]
    (hW : (C ϖ : MRing ι O) ∉ W) :
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) + 1 ≤
      ringKrullDim (MRing ι O ⧸ W) := by
  have hres : IsLocalRing.residue O ϖ = 0 :=
    (IsLocalRing.residue_eq_zero_iff ϖ).2
      ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
  have hsp : specialIdeal (W ⊔ Ideal.span {(C ϖ : MRing ι O)}) = specialIdeal W := by
    unfold specialIdeal
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, MvPolynomial.map_C, hres, map_zero]
    simp
  have hdim := SpecialQuotDim.full O ϖ hϖ K ι (W ⊔ Ideal.span {(C ϖ : MRing ι O)})
    (Ideal.mem_sup_right (Ideal.subset_span rfl))
  rw [hsp] at hdim
  rw [hdim]
  have hne : Ideal.Quotient.mk W (C ϖ) ≠ 0 := fun h => hW (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have he : ringKrullDim ((MRing ι O ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W (C ϖ : MRing ι O)}) =
      ringKrullDim (MRing ι O ⧸ (W ⊔ Ideal.span {(C ϖ : MRing ι O)})) := by
    refine ringKrullDim_eq_of_ringEquiv ?_
    have hm : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk W) =
        Ideal.span {Ideal.Quotient.mk W (C ϖ : MRing ι O)} := by
      rw [Ideal.map_span, Set.image_singleton]
    exact (Ideal.quotEquivOfEq hm.symm).trans (DoubleQuot.quotQuotEquivQuotSup _ _)
  rwa [he] at h1

theorem horizontal_vNumL_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ W, divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∉ W → ∀ l : List (K → ℤ), l.length = d → vNumL W l = 0 := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a f hf hfP W hW hϖW l hl
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold divCycle at hW
  split_ifs at hW with hW'
  swap
  · exact absurd rfl hW
  have hWmin := hW'.1
  have hWp : W.IsPrime := hWmin.1.1
  have hWm : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.full O K ι _ W
      (SupSpanMultiHomog.full O K ι P f a hP.multiProj.multiHomog hf) hWmin
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hlt : P < W := lt_of_le_of_ne hPW (fun e => hfP (e ▸ hfW))
  have hdrop := DimStrictDrop.full (MRing ι O) P W hlt
  rw [hP.dim] at hdrop
  have hdrop' : ringKrullDim (MRing ι O ⧸ W) + 1 ≤ ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    have e : d + 1 + Fintype.card K = d + Fintype.card K + 1 := by omega
    rwa [e] at hdrop
  have hdim := dim_lt_of_two_drops (specialIdeal_dim_add_one_le hϖ W hϖW) hdrop'
  subst hl
  exact (GroundTheory.Heights₂.Heights.FieldNumbers.IntNumZeroSlot.full _ K ι (specialIdeal W)).2
    (SpecialIdealMultiHomog.full O K ι W hWm) _ _ (relDim_lt_of_dim_lt _ _ hdim)

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalPairPowerSumVanish
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem classList_length_of_mem_support {K σ : Type} (cls : σ → K → ℤ) {m : ℕ}
    {G : MvPolynomial σ ℝ} (hG : G.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ G.support) :
    (classList cls μ).length = m := by
  have h := hG (mem_support_iff.mp hμ)
  have hw : Finsupp.weight (1 : σ → ℕ) μ = μ.sum fun _ => id := by
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hw] at h
  simpa [classList, Multiset.length_toList, Finsupp.card_toMultiset] using h

theorem sum_X_inr_pow_eq {σ : Type} {r : ℕ} (e : Fin r → σ) (k : ℕ) :
    (∑ a, X (Sum.inr (e a)) ^ k : MvPolynomial (σ ⊕ σ) ℝ) =
      rename (Sum.inr ∘ e) (MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin r) ℤ k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [psum, map_sum, map_pow, rename_X]

theorem val_psum_mul_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (σ : Type) [Fintype σ] (T : LocPair ι O σ), T.IsVert P ϖ → ∀ (r : ℕ) (e : Fin r → σ), PowerSumsVanish P d (T.x' ∘ e) → ∀ k m : ℕ, 1 ≤ k → k + m = d → ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ, (∀ i, (Gs i).IsHomogeneous m) → T.val P (fun i => (∑ a, X (Sum.inr (e a)) ^ k) * Gs i) = 0 := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP σ _ T hT r e hv k m hk hkm Gs hGs
  have hfib := (_root_.GlobalTheory.CompanionTheory.Ar.Num.FibreComp.fibre_comp O ϖ hϖ K ι P d hP).2.2
  unfold LocPair.val
  refine Finset.sum_eq_zero fun i _ => ?_
  have hZc : ∀ W, ratDiv P (T.f i) (T.g i) W ≠ 0 → IsFibreComp P W := hfib _ _ _ (hT i)
  have hfin : (Function.support (ratDiv P (T.f i) (T.g i))).Finite := by
    refine (Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι O)
      (P ⊔ (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O))).subset ?_
    intro W hW
    exact (hZc W hW).1
  rw [_root_.GlobalTheory.CompanionTheory.Ar.Num.cycNum_mul O K ι (σ ⊕ σ) (ratDiv P (T.f i) (T.g i)) (Sum.elim T.x T.x') _ (Gs i) []]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hlen : ((classList (Sum.elim T.x T.x') μ ++ []).length) + k = d := by
    rw [List.append_nil, classList_length_of_mem_support _ (hGs i) hμ]
    omega
  have hcomp : Sum.elim T.x T.x' ∘ (Sum.inr ∘ e) = T.x' ∘ e := by
    funext a
    simp
  rw [sum_X_inr_pow_eq, (_root_.GlobalTheory.CompanionTheory.Ar.Num.numbers_rename).1 O K ι (Fin r) (σ ⊕ σ) (Sum.inr ∘ e), hcomp,
    (cycNum_int_and_comb O K ι (Fin r) (T.x' ∘ e) (classList (Sum.elim T.x T.x') μ ++ [])).1
      (ratDiv P (T.f i) (T.g i)) hfin (psum (Fin r) ℤ k)]
  have hzero : cycEval (fun W => classNum (T.x' ∘ e) (psum (Fin r) ℤ k)
      (classList (Sum.elim T.x T.x') μ ++ []) W) (ratDiv P (T.f i) (T.g i)) = 0 := by
    unfold cycEval
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    by_cases hW : ratDiv P (T.f i) (T.g i) W = 0
    · simp [hW]
    · beta_reduce
      rw [hv W (hZc W hW) k hk _ hlen, mul_zero]
  rw [hzero]
  simp

end GlobalTheory.CompanionTheory.Ar.Num
end

