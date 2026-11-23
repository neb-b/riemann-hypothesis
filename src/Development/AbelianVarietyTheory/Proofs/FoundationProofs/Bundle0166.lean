module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0159

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeSumGcdFactorOut
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.GcdOut

abbrev CopVec (L : ℕ) : Type := {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}

def scl (L : ℕ) (p : ℕ+ × CopVec L) : ℤ × ℤ := (((p.1 : ℕ) : ℤ) * p.2.1.1, ((p.1 : ℕ) : ℤ) * p.2.1.2)

lemma scl_injective (L : ℕ) : Function.Injective (scl L) := by
  rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩ ⟨δ', ⟨⟨a', b'⟩, hab', ha'⟩⟩ h
  simp only [scl, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have g1 : Int.gcd a b = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab
  have g2 : Int.gcd a' b' = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab'
  have hd : (δ : ℕ) = (δ' : ℕ) := by
    have e1 := Int.gcd_mul_left ((δ : ℕ) : ℤ) a b
    have e2 := Int.gcd_mul_left ((δ' : ℕ) : ℤ) a' b'
    rw [h1, h2, e2, g1, g2] at e1
    simpa using e1.symm
  have hδ : δ = δ' := PNat.coe_injective hd
  subst hδ
  have hne : ((δ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast δ.ne_zero
  have := mul_left_cancel₀ hne h1
  have := mul_left_cancel₀ hne h2
  subst_vars
  rfl

lemma trm_zero (j : ℕ) (s : ℝ) (hj : 2 ≤ j) : trm j s 0 = 0 := by
  simp [trm, zero_pow (by omega : j ≠ 0)]

lemma trm_smul (j : ℕ) (s : ℝ) (δ : ℕ) (z : ℂ) :
    trm j s ((δ : ℂ) * z) = (((δ : ℂ) ^ j)⁻¹ * ((((δ : ℝ) ^ (2 * s))⁻¹ : ℝ) : ℂ)) * trm j s z := by
  unfold trm
  rw [norm_mul, Complex.norm_natCast, Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _), neg_mul,
    Real.rpow_neg (Nat.cast_nonneg _), ← neg_mul, mul_pow, mul_inv]
  push_cast
  ring

lemma cpow_split (j : ℕ) (s : ℝ) (δ : ℕ) (hδ : 0 < δ) :
    (δ : ℂ) ^ ((j : ℂ) + 2 * (s : ℂ)) = (δ : ℂ) ^ j * ((((δ : ℝ) ^ (2 * s)) : ℝ) : ℂ) := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hδ.ne'), Complex.cpow_natCast,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.EisM.GcdOut

open GlobalTheory.EisM.GcdOut in
theorem GlobalTheory.EisM.lattice_sum_gcd_out (j L : ℕ) (s : ℝ) (φ : DirichletCharacter ℂ L) (τ : ℍ)
    (hj : 2 ≤ j) (hs : 0 < s) (hL : 0 < L) :
    ∑' x : ℤ × ℤ, latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2) =
      LSeries (fun n => φ n) (j + 2 * s) *
        ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1},
          φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2) := by
  let F : ℤ × ℤ → ℂ := fun x => latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2)
  let f : ℕ+ → ℂ := fun δ => LSeries.term (fun n => φ n) ((j : ℂ) + 2 * (s : ℂ)) (δ : ℕ)
  let g : CopVec L → ℂ := fun x => φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2)
  change ∑' x, F x = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) * ∑' x, g x
  have hsumT := (_root_.GlobalTheory.EisM.lat_eq_tsum_of_kills j L s 0 0 τ hj hs hL ⟨0, by simp⟩ (fun x => by simp [Kills])).1
  have hgs : Summable fun x => ‖g x‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
      (hsumT.comp_injective Subtype.val_injective)
    simp only [g, Function.comp, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hLS : LSeriesSummable (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    rw [DirichletCharacter.LSeriesSummable_iff hL.ne']
    have : (2:ℝ) ≤ j := by exact_mod_cast hj
    simp
    linarith
  have hfs : Summable fun δ => ‖f δ‖ :=
    (summable_norm_iff.2 hLS).comp_injective PNat.coe_injective
  have hterm : ∀ p : ℕ+ × CopVec L, F (scl L p) = f p.1 * g p.2 := by
    rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩
    have hδ : 0 < (δ : ℕ) := δ.pos
    simp only [F, f, g, scl, latF]
    rw [if_pos (dvd_mul_of_dvd_right ha _), LSeries.term_of_ne_zero hδ.ne', cpow_split j s _ hδ]
    have e : ((((δ : ℕ) : ℤ) * a : ℤ) : ℂ) * (τ : ℂ) + ((((δ : ℕ) : ℤ) * b : ℤ) : ℂ)
        = ((δ : ℕ) : ℂ) * ((a : ℂ) * τ + b) := by push_cast; ring
    rw [e, trm_smul]
    have e2 : (((((δ : ℕ) : ℤ) * b : ℤ)) : ZMod L) = ((δ : ℕ) : ZMod L) * (b : ZMod L) := by push_cast; ring
    rw [e2, map_mul]
    have h1 : ((δ:ℕ) : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hδ.ne')
    have h2 : ((((δ : ℕ) : ℝ) ^ (2 * s) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hδ) _).ne'
    push_cast
    field_simp
  have hsupp : Function.support F ⊆ Set.range (scl L) := by
    rintro ⟨x1, x2⟩ hx
    simp only [Function.mem_support, F, latF] at hx
    by_cases hL1 : (L : ℤ) ∣ x1
    swap
    · simp [hL1] at hx
    rw [if_pos hL1, one_mul] at hx
    have hφ : φ (x2 : ZMod L) ≠ 0 := left_ne_zero_of_mul hx
    have ht : trm j s ((x1 : ℂ) * τ + x2) ≠ 0 := right_ne_zero_of_mul hx
    have hgpos : 0 < Int.gcd x1 x2 := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [trm_zero j s hj] at ht
    obtain ⟨a, b, hab, h1, h2⟩ := Int.exists_gcd_one hgpos
    generalize Int.gcd x1 x2 = d at h1 h2 hgpos
    have hunit : IsUnit (x2 : ZMod L) := by
      by_contra h
      exact hφ (MulChar.map_nonunit φ h)
    have hdu : IsUnit ((d : ℕ) : ZMod L) := by
      rw [h2] at hunit
      push_cast at hunit
      exact isUnit_of_mul_isUnit_right hunit
    have hcop : Nat.Coprime d L := (ZMod.isUnit_iff_coprime d L).1 hdu
    have hLa : (L : ℤ) ∣ a := by
      have hc : IsCoprime (L : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
      rw [h1] at hL1
      exact hc.dvd_of_dvd_mul_right hL1
    refine ⟨(⟨d, hgpos⟩, ⟨(a, b), Int.isCoprime_iff_gcd_eq_one.2 hab, hLa⟩), ?_⟩
    simp only [scl, PNat.mk_coe]
    rw [h1, h2, mul_comm a, mul_comm b]
  have hLser : ∑' δ : ℕ+, f δ = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    unfold LSeries
    refine (PNat.coe_injective.tsum_eq (f := LSeries.term (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ))) ?_)
    intro n hn
    have : n ≠ 0 := by
      rintro rfl
      exact hn (LSeries.term_zero _ _)
    exact ⟨⟨n, Nat.pos_of_ne_zero this⟩, rfl⟩
  calc ∑' x, F x = ∑' p, F (scl L p) := ((scl_injective L).tsum_eq hsupp).symm
    _ = ∑' p : ℕ+ × CopVec L, f p.1 * g p.2 := tsum_congr hterm
    _ = (∑' δ, f δ) * ∑' x, g x := (tsum_mul_tsum_of_summable_norm hfs hgs).symm
    _ = _ := by rw [hLser]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGamma1OfIsCuspFormCoeffSeq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma norm_petersson_self (k : ℕ) (h : ℍ → ℂ) (z : ℍ) :
    ‖petersson (k : ℤ) h h z‖ = ‖h z‖ ^ 2 * z.im ^ k := by
  simp only [petersson, norm_mul, Complex.norm_conj, zpow_natCast, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos z.im_pos]
  ring

lemma isZeroAtImInfty_of_bound (k : ℕ) (hk : 1 ≤ k) (h : ℍ → ℂ) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖h τ‖ ^ 2 * τ.im ^ k ≤ C) : IsZeroAtImInfty h := by
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero]
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hsq : Tendsto (fun τ : ℍ => ‖h τ‖ ^ 2) atImInfty (𝓝 0) := by
    have hlim : Tendsto (fun τ : ℍ => max C 0 * (τ.im)⁻¹) atImInfty (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp him).const_mul (max C 0)
    refine squeeze_zero' (Eventually.of_forall fun τ => by positivity) ?_ hlim
    filter_upwards [him.eventually_ge_atTop 1] with τ hτ
    have hpos : 0 < τ.im := τ.im_pos
    have hpow : τ.im ≤ τ.im ^ k := by
      calc τ.im = τ.im ^ 1 := (pow_one _).symm
        _ ≤ τ.im ^ k := pow_le_pow_right₀ hτ hk
    rw [le_mul_inv_iff₀ hpos]
    calc ‖h τ‖ ^ 2 * τ.im ≤ ‖h τ‖ ^ 2 * τ.im ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ C := hC τ
      _ ≤ max C 0 := le_max_left _ _
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

end GlobalTheory.EisM

theorem GlobalTheory.EisM.cuspForm_of_CF : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) a → ∃ f : CuspForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  intro k L N ε a hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.EisM.modularForm_gammaOne_of_MF k L N ε a hL hNL hcf.1
  obtain ⟨C, hC⟩ := hcf.2
  have hall : ∀ γ : SL(2, ℤ), IsZeroAtImInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] γ) := by
    intro γ
    refine isZeroAtImInfty_of_bound k hk _ C fun τ => ?_
    have h1 := congrArg norm (petersson_slash_SL (k : ℤ) (f : ℍ → ℂ) f γ τ)
    rw [norm_petersson_self, norm_petersson_self, hf] at h1
    rw [hf, h1]
    exact hC _
  refine ⟨⟨f.toSlashInvariantForm, f.holo', ?_⟩, hf⟩
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  exact hall γ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

open Asymptotics Function

theorem isBigO_qParam_pow_of_qExpansion_coeff_zero {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ) (h : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
    intro i hi
    have := h i hi
    rw [qExpansion_coeff] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt ha).mp h1
  have ht := qParam_tendsto_atImInfty (h := 1) one_pos
  have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp ht).isBigO_one ℂ
  have h3 := (isBigO_refl (fun τ : ℍ => Periodic.qParam 1 τ ^ m) atImInfty).mul h2
  simp only [mul_one] at h3
  refine h3.congr' ?_ EventuallyEq.rfl
  filter_upwards [ht.eventually hfg] with τ hτ
  rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
  rw [hτ]; simp

theorem qExpansion_coeff_zero_of_isBigO_qParam_pow {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hlt.ne_top
    rw [← hj] at hlt
    have hjm : j < m := by exact_mod_cast hlt
    obtain ⟨g, hg, hg0, hfg⟩ := ha.analyticOrderAt_eq_natCast.mp hj.symm
    have ht := qParam_tendsto_atImInfty (h := 1) one_pos
    have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty]
        fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j) := by
      have h3 := (isBigO_refl (fun τ : ℍ => (Periodic.qParam 1 τ ^ j)⁻¹) atImInfty).mul h
      refine h3.congr' ?_ ?_
      · filter_upwards [ht.eventually hfg] with τ hτ
        rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        rw [hτ, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
      · refine Eventually.of_forall fun τ => ?_
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        simp only
        rw [pow_sub₀ _ hq hjm.le, mul_comm]
    have h4 : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)) atImInfty (𝓝 0) := by
      have := ht.pow (m - j)
      rwa [zero_pow (by omega)] at this
    exact hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.comp ht) (h2.trans_tendsto h4))
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha] at h1
  intro n hn
  rw [qExpansion_coeff, h1 n hn, mul_zero]

theorem modularFormNorm_isBigO_self_atImInfty {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))
  have hb : ∀ q : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ),
      SlashInvariantForm.quotientFunc (k := k) f q =O[atImInfty] fun _ => (1 : ℂ) := by
    refine Quotient.forall.mpr fun ⟨r, hr⟩ => ?_
    have hc : IsCusp OnePoint.infty 𝒮ℒ := Fact.out
    have := (ModularForm.translate f r⁻¹).bdd_at_cusps' (c := OnePoint.infty)
      (by simpa using hc.of_isFiniteRelIndex_conj hr)
    rw [OnePoint.isBoundedAt_infty_iff] at this
    have h2 : (ModularForm.translate f r⁻¹ : ℍ → ℂ) =O[atImInfty] (1 : ℍ → ℝ) := this
    refine IsBigO.trans h2 ?_
    exact IsBigO.of_bound 1 (by simp)
  have h1 : (∏ q ∈ Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)),
      SlashInvariantForm.quotientFunc (k := k) f q) =O[atImInfty] fun _ => (1 : ℂ) := by
    have := IsBigO.finsetProd (s := Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))) (fun q _ => hb q)
    simpa [Finset.prod_fn] using this
  have h2 := (isBigO_refl (f : ℍ → ℂ) atImInfty).mul h1
  simp only [mul_one] at h2
  refine h2.congr_left fun τ => ?_
  have h3 := congr_fun (Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (k := k) f q)
    (Finset.mem_univ (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)))) τ
  rw [ModularForm.coe_norm]
  have h4 : SlashInvariantForm.quotientFunc (k := k) f (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)) = f := by simp
  rw [h4, Pi.mul_apply] at h3
  convert h3

theorem exists_sturmBound_modularForm_arithmetic {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : ModularForm Γ k, (∀ n < m, (qExpansion 1 f).coeff n = 0) → f = 0 := by
  refine ⟨(k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1, fun f hf => ?_⟩
  have h1 := qExpansion_coeff_zero_of_isBigO_qParam_pow one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) _
    ((modularFormNorm_isBigO_self_atImInfty f).trans (isBigO_qParam_pow_of_qExpansion_coeff_zero hΓ f _ hf))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

theorem sturm_coef_zero : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N), 0 < L → N ∣ L →
    ∃ B : ℕ, ∀ a, MF k L (ch ε) a → (∀ n < B, a n = 0) → a = 0 := by
  intro k L N ε hL hN
  have hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨m, hm⟩ := exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)
  refine ⟨m, fun a ha hz => ?_⟩
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.EisM.modularForm_gammaOne_of_MF k L N ε a hL hN ha
  have hc : ∀ n, (qExpansion 1 f).coeff n = a n := by
    intro n
    have := _root_.GlobalTheory.EisM.coef_qs a ha.1 n
    unfold coef at this
    rw [← this, hf]
  have h0 : f = 0 := hm f fun n hn => by rw [hc n]; exact hz n hn
  funext n
  rw [← hc n, h0]
  simp [qExpansion_zero]

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTopologicalGeneratorTauTower
section
open GlobalTheory.K5 Polynomial IntermediateField

noncomputable section

namespace GlobalTheory.K5.TauGen

theorem not_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := _root_.GlobalTheory.K5.NotPow.q_not_pow

def geoF (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x})

theorem isOpen_setOf_apply {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    (x : Ω) (P : Ω → Prop) : IsOpen {σ : Ω ≃ₐ[F] Ω | P (σ x)} := by
  haveI : FiniteDimensional F F⟮x⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  have hU : IsOpen (((F⟮x⟯).fixingSubgroup : Subgroup (Ω ≃ₐ[F] Ω)) : Set (Ω ≃ₐ[F] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hV : IsOpen ((fun τ : Ω ≃ₐ[F] Ω => σ⁻¹ * τ) ⁻¹' ((F⟮x⟯).fixingSubgroup : Set (Ω ≃ₐ[F] Ω))) :=
    hU.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (hV.mem_nhds ?_) ?_
  · show σ⁻¹ * σ ∈ (F⟮x⟯).fixingSubgroup
    rw [inv_mul_cancel]; exact one_mem _
  · intro τ hτ
    have h1 := (mem_fixingSubgroup_iff _ _).1 hτ x (mem_adjoin_simple_self F x)
    have h2 : τ x = σ x := by
      have : σ⁻¹ (τ x) = x := h1
      calc τ x = σ (σ⁻¹ (τ x)) := by simp
        _ = σ x := by rw [this]
    show P (τ x)
    rw [h2]; exact hσ

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ T : Tower p Ω, ∃ τ ∈ Ggeo (p := p) Ω, ∀ n, τ (T.qq n) = T.ζ n * T.qq n := by
  intro p hp hp2 Ω _ _ hΩ T
  haveI := hΩ.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo hΩ
  have hO : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ geoF p Ω := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hA : ∀ x : Ω, IsAlgZp (p := p) x → x ∈ geoF p Ω := fun x hx => Subfield.subset_closure (Or.inr hx)
  let F := geoF p Ω
  let φ : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  have hφ : Function.Injective φ := fun a b h => hΩ.inj (congrArg Subtype.val h)
  have hcomp : (algebraMap F Ω).comp φ = algebraMap (O0 p) Ω := by ext a; rfl
  haveI hal : Algebra.IsAlgebraic F Ω := by
    constructor
    intro x
    obtain ⟨P, hP, hx⟩ := hΩ.alg.isAlgebraic x
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφ).2 hP, ?_⟩
    rw [aeval_def, eval₂_map, hcomp, ← aeval_def, hx]
  haveI : IsAlgClosure F Ω := ⟨inferInstance, hal⟩
  haveI : IsGalois F Ω := {}
  haveI : CompactSpace (Ω ≃ₐ[F] Ω) := inferInstance
  let q' : F := ⟨algebraMap (O0 p) Ω (qO p), hO _⟩
  have hirr : ∀ n, Irreducible (X ^ (p ^ n) - C q') := fun n =>
    irreducible_X_pow_sub_C_of_prime_pow_of_ne_two hp.out hp2 n (fun b hb =>
      not_pow p Ω hΩ (b : Ω) b.2 (by rw [← SubmonoidClass.coe_pow, hb]))
  have hmin : ∀ n (y : Ω), y ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) → minpoly F y = X ^ (p ^ n) - C q' := by
    intro n y hy
    refine (minpoly.eq_of_irreducible_of_monic (hirr n) ?_ (monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero))).symm
    simp only [map_sub, map_pow, aeval_X, aeval_C, hy]
    exact sub_self _
  let S : ℕ → Set (Ω ≃ₐ[F] Ω) := fun n => {σ | σ (T.qq n) = T.ζ n * T.qq n}
  have hne : ∀ n, (S n).Nonempty := by
    intro n
    have h1 := hmin n (T.qq n) (Basic.qq_pow T n)
    have h2 := hmin n (T.ζ n * T.qq n) (by rw [mul_pow, (T.prim n).pow_eq_one, one_mul, Basic.qq_pow T n])
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) Ω).1 (h2.trans h1.symm)
    exact ⟨σ, hσ⟩
  have hdec : ∀ n, S (n + 1) ⊆ S n := by
    intro n σ hσ
    show σ (T.qq n) = T.ζ n * T.qq n
    have hσ' : σ (T.qq (n + 1)) = T.ζ (n + 1) * T.qq (n + 1) := hσ
    rw [← T.qpow n, map_pow, hσ', mul_pow, T.ζpow, T.qpow]
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    rw [← isOpen_compl_iff]
    exact isOpen_setOf_apply (F := F) (T.qq n) (fun y => ¬ y = T.ζ n * T.qq n)
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  let τ : Gal p Ω :=
    { σ.toRingEquiv with
      commutes' := fun a => σ.commutes (⟨algebraMap (O0 p) Ω a, hO a⟩ : F) }
  refine ⟨τ, fun x hx => σ.commutes (⟨x, hA x hx⟩ : F), fun n => hσ n⟩

end GlobalTheory.K5.TauGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCoboundaryTwistCochain
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB.TwistCochain

theorem pow_mod_of_pow_eq_one' {Ω : Type} [Field Ω] {N : ℕ} {ζ : Ω} (hN : ζ ^ N = 1) (n : ℕ) :
    ζ ^ (n % N) = ζ ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n N, pow_add, pow_mul, hN, one_pow, one_mul]

theorem twist_cochain : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∀ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w → (∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h)) →
  ∃ v : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant v ∧
    ∀ g h, (v g : Ω) * g (v h) = ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val * v (g * h) := by
  intro K Ω _ _ _ _ N ζ hN hζ hζfix a b α β ha hb hα hβ w hw hcoc
  haveI : NeZero N := ⟨hN.ne'⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha ((algebraMap K Ω).injective (by rw [← hα, map_zero]))
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb ((algebraMap K Ω).injective (by rw [← hβ, map_zero]))
  obtain ⟨-, hgα, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hζfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hylc, -, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hζfix hβ0 ⟨b, hβ.symm⟩
  refine ⟨fun g => Units.mk0 α hα0 ^ (kum (N := N) ζ β g).val * (w g)⁻¹, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hylc hw (fun (i : ZMod N) (u : Ωˣ) => Units.mk0 α hα0 ^ i.val * u⁻¹)
  · intro g h
    have hwg : (w g : Ω) ≠ 0 := (w g).ne_zero
    have hwh : g (w h : Ω) ≠ 0 := by simpa using (w h).ne_zero
    have hwgh : (w (g * h) : Ω) ≠ 0 := (w (g * h)).ne_zero
    have hz : ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val =
        (ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val := by
      rw [ZMod.val_mul, pow_mod_of_pow_eq_one' hζ.pow_eq_one, pow_mul]
    have hc := hcoc g h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, Units.val_inv_eq_inv_val,
      map_inv₀, hgα g, hz]
    rw [pow_add] at hc
    field_simp
    rw [mul_pow]
    linear_combination -(ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val * hc

end GlobalTheory.NeedB.TwistCochain
end

