module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogCoordsUnitValueTwoVariableIntegralExpansion
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogCoordsUnitValueTwoVariableIntegralExpansionStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logCoords_unit_value_twoVariableIntegralExpansion : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (L : ℕ) (ψ : O0 p →+* Ωl) (ι : On p L →ₐ[O0 p] Ωl), 1 ≤ L → IsReb T L ψ → IsEmb T L ι →
  ∀ (A₁ g : ℤ) (θ : ℤ → ℤ → ℤ) (cU cE : ℤ → Ωl) (x x' : Ωl),
  (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) →
  (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) →
  (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) →
  (∀ r : ℤ, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k)) →
  (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i)) →
  (∀ r : ℤ, r < 0 → cE r = 0) → (∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L}) →
  Ev ψ cU x x' → x ≠ 0 → IsInt (p := p) x⁻¹ →
  ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = x ∧ Ev ψ cE z z' ∧
    Cong (p := p) L (ι α) (-(A₁ : Ωl) * z) ∧
    Cong (p := p) L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
  intro p hp Ω _ _ hc T L ψ ι hL hψ hι A₁ g θ cU cE x x' hB ⟨r0, h0⟩ hdiv hU hE hE0 hEm hx hx0 hxi
  have cong_sum : ∀ {L : ℕ} (S : Finset ℤ) (v : ℤ → ℤ) (e : ℤ → Ω) (he : ∀ k, IsInt (p := p) (e k)) (hv : ∀ k, (p : ℤ) ^ L ∣ v k),
      Cong (p := p) L (∑ k ∈ S, (v k : Ω) * e k) 0 := by
    intro L S v e he hv
    choose c hc using hv
    refine ⟨∑ k ∈ S, (c k : Ω) * e k, IsIntegral.sum _ fun k _ => IsIntegral.mul (Basic.isInt_intCast _) (he k), ?_⟩
    rw [sub_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc k]
    push_cast
    ring

  have cong_val : ∀ (hc : IsClo p Ω) {T : GlobalTheory.K5.Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (g A : ℤ)
      (θ v : ℤ → ℤ → ℤ) (S : ℤ → Finset ℤ) (cU cE : ℤ → Ω) (x x' z z' y y' : Ω)
      (hv : ∀ k r, θ k r ≠ 0 → (p : ℤ) ^ L ∣ v k r - A * k)
      (hE : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i))
      (hx : Ev ψ cU x x') (hz : Ev ψ cE z z')
      (hy : Ev ψ (fun r => ∑ k ∈ S r, (v k r : Ω) * (θ k r : Ω) * T.ζ L ^ (g * k)) y y'),
      Cong (p := p) L (y + A * (z * x)) 0 := by
    intro hc T L ψ hψ g A θ v S cU cE x x' z z' y y' hv hE hx hz hy
    have hN : 0 < p ^ L := pow_pos hp.out.pos L
    have hζ : T.ζ L ^ p ^ L = 1 := (T.prim L).pow_eq_one
    obtain ⟨R1, R2⟩ := EvRing.ev_ring p Ω hc T L ψ hψ
    obtain ⟨U, rfl⟩ := (R2 _ _ _ hx).2.2.1
    obtain ⟨E, rfl⟩ := (R2 _ _ _ hz).2.2.1
    obtain ⟨Y, hY⟩ := (R2 _ _ _ hy).2.2.1
    have h1 := (R2 _ _ _ (R1 E U _ _ _ _ hz hx).1).2.2.2.2.1 (A : Ω) (Basic.isInt_intCast _) (GlobalTheory.Glue.SiegLoc.isAlgZp_int _)
    obtain ⟨V, hV⟩ := (R2 _ _ _ h1).2.2.1
    rw [← hV] at h1
    rw [← hY] at hy
    refine ((GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ω hc T L ψ hψ L _ _ _ (R1 Y V _ _ _ _ hy h1).2.1).1).2 fun r => ?_
    have e : (Y + V).coeff r = ∑ k ∈ S r, (((v k r - A * k) * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) := by
      rw [HahnSeries.coeff_add, hY, hV]
      simp only
      rw [GlobalTheory.Glue.SiegLoc.coeff_mul_finsum, ← neg_eq_iff_eq_neg.2 (hE r), mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [e]
    refine cong_sum _ (fun k => (v k r - A * k) * θ k r) _ (fun k => ?_) fun k => ?_
    · rw [GlobalTheory.Glue.SiegLoc.zpow_emod hN hζ]
      exact IsIntegral.pow (EvTwist.isInt_of_pow hN hζ) _
    · by_cases h : θ k r = 0
      · simp [h]
      · exact Dvd.dvd.mul_right (hv k r h) _
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  choose B hB using hB
  let S : ℤ → Finset ℤ := fun r => Finset.Icc (-(B r : ℤ)) (B r)
  have hS : ∀ (r : ℤ) (f : ℤ → Ω), (∀ k, θ k r = 0 → f k = 0) → ∑ᶠ k, f k = ∑ k ∈ S r, f k := fun r f hf =>
    finsum_eq_sum_of_support_subset _ fun k hk => by
      rw [Finset.mem_coe, Finset.mem_Icc, ← abs_le]
      exact not_lt.1 fun h => hk (hf k (hB r k h))
  have hE' : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ (m + 1) ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i) := fun r => by
    rw [← hE r, hS r _ fun k hk => by simp [hk]]
  obtain ⟨z, z', hz⟩ := GlobalTheory.Glue.SiegLoc.ev_cyc T (m + 1) ψ cE hE0 hEm
  obtain ⟨a, ha⟩ := GlobalTheory.Glue.SiegLoc.rep hψ g θ S r0 h0
  obtain ⟨y0, e0⟩ := ha fun _ _ => 1
  obtain ⟨y1, e1⟩ := ha fun _ j => j
  obtain ⟨y2, e2⟩ := ha fun i _ => i
  have hN : (0 : ℤ) < ((p ^ (m + 1) : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.out.pos _
  have hmod : ∀ r : ℤ, (p : ℤ) ^ (m + 1) ∣ ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ) - r := fun r => by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg r hN.ne')]
    have := Int.emod_add_mul_ediv r ((p ^ (m + 1) : ℕ) : ℤ)
    push_cast at this ⊢
    exact ⟨-(r / (p : ℤ) ^ (m + 1)), by linarith⟩
  obtain ⟨c1, hc1, k1⟩ := cong_val hc hψ g A₁ θ (fun _ r => ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
    (fun k r h => by simpa using dvd_add (hmod r) (hdiv k r h)) hE' hx hz e1
  obtain ⟨c2, hc2, k2⟩ := cong_val hc hψ g g θ (fun k _ => ((g * k % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
    (fun k r _ => hmod _) hE' hx hz e2
  have hcU : cU = fun r => ∑ k ∈ S r, ((1 : ℤ) : Ω) * (θ k r : Ω) * T.ζ (m + 1) ^ (g * k) := funext fun r => by
    rw [hU r, hS r _ fun k hk => by simp [hk]]
    simp
  rw [← hcU] at e0
  have hxe := (GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients p Ω hc T (m + 1) ψ hψ _ _ _ _ _ hx e0).1
  set w0 : On p (m + 1) := ∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
    algebraMap (O0 p) (On p (m + 1)) (a i j) * xn p (m + 1) ^ (i : ℕ) * yn p (m + 1) ^ (j : ℕ) with hw0
  have hw : ι w0 = x := by
    rw [hxe, hw0]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, AlgHom.commutes, hι.1, hι.2, Int.cast_one, one_mul]
  obtain ⟨w, hwu⟩ := GlobalTheory.Glue.SiegLoc.isUnit_of_inv ι (_root_.GlobalTheory.K5.LevEmb.emb_inj_range p Ω hc T (m + 1) hL ι hι).1 w0 (hw ▸ hx0) (hw ▸ hxi)
  obtain ⟨α, β, hd⟩ := GlobalTheory.K5.exists_isDlog p (m + 1) w
  obtain ⟨d1, d2⟩ := GlobalTheory.Glue.SiegLoc.coef m a w α β (hwu.trans hw0) hd
  obtain ⟨f1, d1⟩ := Ideal.mem_span_singleton'.1 d1
  obtain ⟨f2, d2⟩ := Ideal.mem_span_singleton'.1 d2
  replace d1 := congrArg ι d1
  replace d2 := congrArg ι d2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, map_sub, map_natCast, map_one, AlgHom.commutes, hι.1, hι.2, hwu, hw, GlobalTheory.Glue.SiegLoc.zeta_one] at d1 d2
  simp only [Int.cast_natCast] at k1 k2
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  refine ⟨w, α, β, z, z', hd, hwu ▸ hw, hz, ⟨(ι f1 + c1) * x⁻¹,
    IsIntegral.mul (IsIntegral.add (GlobalTheory.Glue.SiegLoc.emb_int _ ι _) hc1) hxi, ?_⟩, ?_⟩
  · linear_combination x⁻¹ * k1 - x⁻¹ * d1 - (ι α + A₁ * z) * hinv
  · have hζ1 : T.ζ 1 - 1 ≠ 0 := sub_ne_zero.2 ((T.prim 1).ne_one (by simpa using hp.out.one_lt))
    have hpd := GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T 1 1 le_rfl (Nat.totient_pos.2 (pow_pos hp.out.pos _))
    rw [pow_one, div_eq_mul_inv] at hpd
    have hinv2 : (T.ζ 1 - 1) * (T.ζ 1 - 1)⁻¹ = 1 := mul_inv_cancel₀ hζ1
    have hpi : IsInt (p := p) (p : Ω) := by simpa using Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    refine ⟨(ι f2 * ((p : Ω) * (T.ζ 1 - 1)⁻¹) + p * c2) * x⁻¹,
      IsIntegral.mul (IsIntegral.add (IsIntegral.mul (GlobalTheory.Glue.SiegLoc.emb_int _ ι _) hpd) (IsIntegral.mul hpi hc2)) hxi, ?_⟩
    generalize (∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
      ((i : ℕ) : Ω) * algebraMap (O0 p) Ω (a i j) * T.ζ (m + 1) ^ (i : ℕ) * T.qq (m + 1) ^ (j : ℕ)) = Y at k2 d2
    linear_combination (p * x⁻¹) * k2 - (p * x⁻¹ * (T.ζ 1 - 1)⁻¹) * d2 - (p * x⁻¹ * (x * ι β - Y)) * hinv2
      - (p * (ι β + g * z)) * hinv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominators
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_bdd_den : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K),
    ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (T.exp f).coeff r) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hexpS : ∀ c : ring ε.range, ∃ S : Finset Ω, ∀ r, (T.exp (T.io c)).coeff r ∈ Subring.closure (S : Set Ω) := by
    intro c
    have hc : InR ε.range (c : ℍ → ℂ) := ((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 c).1 c.2
    exact _root_.GlobalTheory.FN.coeff_fg Ω ε c _ hc (T.exp_io c)
  obtain ⟨Sa, hSa⟩ := hexpS a
  obtain ⟨Sb, hSb⟩ := hexpS b
  have hiob : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have hexpb : T.exp (T.io b) ≠ 0 := by
    intro h
    apply hiob
    exact (injective_iff_map_eq_zero (T.exp : T.K →+* HahnSeries ℚ Ω)).1
      (T.exp : T.K →+* HahnSeries ℚ Ω).injective _ h
  have hf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹ := by
    rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ hexpb, mul_one]
  classical
  let S : Finset Ω := Sa ∪ Sb ∪ {(T.exp (T.io b)).leadingCoeff⁻¹}
  let A : Subring Ω := Subring.closure (S : Set Ω)
  have hA_a : ∀ r, (T.exp (T.io a)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSa r)
  have hA_b : ∀ r, (T.exp (T.io b)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSb r)
  have hA_l : (T.exp (T.io b)).leadingCoeff⁻¹ ∈ A := Subring.subset_closure (by simp [S])
  have hP := _root_.GlobalTheory.HahnSub.coeff_mul_inv_mem Ω A
  have hA_inv := hP.2 _ hA_b hA_l
  have hA_f : ∀ r, (T.exp f).coeff r ∈ A := by
    intro r
    rw [hf]
    exact hP.1 _ _ hA_a hA_inv r
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨D, hD, hDk⟩ := _root_.GlobalTheory.finite_subring_common_denominator Ω S
  exact ⟨D, hD, fun r => hDk _ (hA_f r)⟩

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldConstAndQuotient
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_const_and_quot : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ c : Ω, T.an (algebraMap Ω T.K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)) ∧ ∀ f : T.K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T
  have hmem := _root_.GlobalTheory.FN.mem_ring_iff_inR ε.range
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs := fun a =>
    ((_root_.GlobalTheory.FN.germ_ringHom_and_restrict).2.1 _).1 (_root_.GlobalTheory.FN.inR_mdifferentiable ε.range _ ((hmem.1 _).1 a.2))
  refine ⟨fun c => ?_, fun f => ?_⟩
  · have hc : (fun _ : ℍ => ε c) ∈ ring ε.range := (hmem.1 _).2 (hmem.2 _ ⟨c, rfl⟩)
    rw [← T.io_c c ⟨_, hc⟩ rfl, T.an_io]
    rfl
  · obtain ⟨a, b, hb, h⟩ := T.io_surj f
    refine ⟨up (a : ℍ → ℂ), up (b : ℍ → ℂ), hdiff a, hdiff b, ?_, ?_⟩
    · intro h0
      have h1 : T.an (T.io b) = T.an (T.io 0) := by
        rw [T.an_io, map_zero, map_zero]; exact h0
      exact hb (T.io_inj ((_root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T).2.2.2 h1))
    · have := congrArg T.an h
      rw [map_mul, T.an_io, T.an_io] at this
      exact this

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpUpperTriangular
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exp_sl_coeff_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (T : Frac Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : T.K) (r : ℚ) :
    (T.exp (T.sl g f)).coeff (r * ent g 0 0 / ent g 1 1) =
      eOm ε (r * ent g 0 1 / ent g 1 1) * (T.exp f).coeff r := by
  obtain ⟨hl, hmob⟩ := (_root_.GlobalTheory.FN.mob_props).2.2.2.2.2 g hg
  obtain ⟨_, hε, h0, hadd, _, _⟩ := _root_.GlobalTheory.FNRoots.main Ω ε
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.FNTwist.exists_scale_twist_ringHom Ω Ω (RingHom.id Ω) (ent g 0 0 / ent g 1 1)
    (fun r => eOm ε (r * (ent g 0 1 / ent g 1 1))) hl (by simpa using h0)
    (fun r r' => by simp only [add_mul, hadd])
  have key : (T.exp.toRingHom.comp (T.sl g).toRingEquiv.toRingHom) = Φ.comp T.exp.toRingHom := by
    apply (_root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T).1
    intro a
    obtain ⟨a', ha', hsl⟩ := (_root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T).2.1 g a
    have hE : IsExp ε a' (Φ (T.exp (T.io a))) := by
      refine _root_.GlobalTheory.FN.isExp_comp_affine Ω ε a a' (ent g 0 0 / ent g 1 1) (ent g 0 1 / ent g 1 1) _ _ hl
        (fun z hz => ?_) (fun s => ?_) (T.exp_io a)
      · rw [ha', (_root_.GlobalTheory.FN.cmp_props).2.2.2 g a z hz, hmob z]
      · rw [hΦ, map_mul, hε]
        rfl
    have hu := (_root_.GlobalTheory.FNExp.exp_props Ω ε).2.1 _ _ _ (T.exp_io a') hE
    show T.exp (T.sl g (T.io a)) = Φ (T.exp (T.io a))
    rw [hsl, hu]
  have hc := congrArg (fun h : HahnSeries ℚ Ω => h.coeff (r * (ent g 0 0 / ent g 1 1)))
    (RingHom.congr_fun key f)
  simp only [RingHom.comp_apply] at hc
  rw [mul_div_assoc, mul_div_assoc]
  refine (show (T.exp (T.sl g f)).coeff (r * (ent g 0 0 / ent g 1 1)) = _ from hc).trans ?_
  rw [hΦ]
  rfl

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSaturation
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_sat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T a b M hM ha hb hb0 hinv ⟨P, hP, hPe⟩
  obtain ⟨_, hMD, hAE, _, hmemHs⟩ := _root_.GlobalTheory.FN.germ_ringHom_and_restrict
  obtain ⟨hNT, hid, hunit⟩ := _root_.GlobalTheory.FN.germ_main
  obtain ⟨hmapsto, _, _, hmobSL, hmobD, _⟩ := _root_.GlobalTheory.FN.mob_props
  obtain ⟨p, u, hu, hpn, hp⟩ := _root_.GlobalTheory.FN.clear_denominators Ω ε T P hP
  set n := P.natDegree with hn
  have hR : ∀ i, InR ε.range (p i : ℍ → ℂ) := fun i => ((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 _).1 (p i).2
  have hpD : ∀ i, DifferentiableOn ℂ (up (p i : ℍ → ℂ)) Hs := fun i => (hMD _).1 (_root_.GlobalTheory.FN.inR_mdifferentiable _ _ (hR i))

  have hup : ∀ (g : ℂ → ℂ) (z : ℂ), z ∈ Hs → up (fun τ : ℍ => g τ) z = g z := by
    intro g z hz
    simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
  have hupT : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp [up]

  have hxb : (((a / b : ℂ → ℂ)) : Mero) * (b : Mero) = (a : Mero) := by
    rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
    filter_upwards [(hunit b hb hb0).1] with z hz
    simp [div_mul_cancel₀ _ hz]

  have hsum : ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i = 0 := by
    calc _ = T.an u * P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) := by
          rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hp i, map_mul, mul_assoc]
      _ = 0 := by rw [hPe, mul_zero]
  set F : ℂ → ℂ := fun z => ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) z * a z ^ i * b z ^ (n - i) with hF
  have e2 : F = ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) := by
    funext z; simp [hF, Finset.sum_apply]
  have hFg : (F : Mero) = 0 := by
    have e1 : (F : Mero) = Filter.Germ.coeRingHom _ F := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, e2, map_sum]
    change ∑ i ∈ _, ((up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) : ℂ → ℂ) : Mero) = _
    simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
    calc _ = (b : Mero) ^ n * ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [T.an_io, ← hxb]
          show (up (p i : ℍ → ℂ) : Mero) * _ * _ = _ * ((up (p i : ℍ → ℂ) : Mero) * _)
          rw [mul_pow, mul_assoc, mul_assoc, ← pow_mul_pow_sub (b : Mero) hin]
          ring
      _ = 0 := by rw [hsum, mul_zero]
  have hFD : DifferentiableOn ℂ F Hs := by
    rw [e2]
    refine DifferentiableOn.sum fun i _ => ?_
    exact ((hpD i).mul (ha.pow i)).mul (hb.pow (n - i))
  have hF0 : ∀ z ∈ Hs, F z = 0 := by
    have := hid F (fun _ => 0) hFD (differentiableOn_const 0) (by rw [hFg]; rfl)
    exact this

  have haM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => a τ) := (hMD _).2 (ha.congr fun z hz => hup a z hz)
  have hbM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => b τ) := (hMD _).2 (hb.congr fun z hz => hup b z hz)
  have hbne : (fun τ : ℍ => b τ) ≠ 0 := by
    intro h0
    apply hb0
    have : (b : Mero) = ((0 : ℂ → ℂ) : Mero) := hAE b 0 fun z hz => by
      simpa using congrFun h0 ⟨z, hz⟩
    rw [this]; rfl
  have hinvT : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a ((γ • τ : ℍ) : ℂ) * b τ = a τ * b ((γ • τ : ℍ) : ℂ) := by
    intro γ hγ τ
    have hmD : DifferentiableOn ℂ (mob (ofSL γ)) Hs := hmobD _
    have hmap : Set.MapsTo (mob (ofSL γ)) Hs Hs := fun z hz => hmapsto _ z hz
    have h1 : DifferentiableOn ℂ (fun z => a (mob (ofSL γ) z) * b z) Hs := (ha.comp hmD hmap).mul hb
    have h2 : DifferentiableOn ℂ (fun z => a z * b (mob (ofSL γ) z)) Hs := ha.mul (hb.comp hmD hmap)
    have := hid _ _ h1 h2 (hinv γ hγ) τ (hmemHs τ)
    simpa [hmobSL] using this
  have hpn' : (p n : ℍ → ℂ) ≠ 0 := by
    intro h0; apply hpn; ext1; exact h0
  have hsumT : ∀ τ : ℍ, ∑ i ∈ Finset.range (n + 1), (p i : ℍ → ℂ) τ * (fun τ : ℍ => a τ) τ ^ i * (fun τ : ℍ => b τ) τ ^ (n - i) = 0 := by
    intro τ
    have := hF0 τ (hmemHs τ)
    simpa [hF, hupT] using this
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := ℚ)
  obtain ⟨h, hhR, hh⟩ := _root_.GlobalTheory.FN.Sat.sat Ω ε M n (fun τ : ℍ => a τ) (fun τ : ℍ => b τ) (fun i => (p i : ℍ → ℂ)) hM haM hbM hbne
    hinvT hR hpn' hsumT
  let hr : ring ε.range := ⟨h, mem_ring_of_inR hhR⟩
  have hio0 : T.io (p n) ≠ 0 := by
    intro h0; apply hpn; exact T.io_inj (by rw [h0, map_zero])
  refine ⟨T.io hr / T.io (p n), ?_⟩
  have hg0 : (up (p n : ℍ → ℂ) : Mero) ≠ 0 := by
    intro h0
    have hinj : Function.Injective T.an := T.an.injective
    apply hio0; apply hinj; rw [map_zero, T.an_io]; exact h0
  have hU : IsUnit (up (p n : ℍ → ℂ) : Mero) := (hunit _ (hpD n) hg0).2
  have hrel : (up (p n : ℍ → ℂ) : Mero) * (a : Mero) = (up h : Mero) * (b : Mero) := by
    rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul]
    refine hAE _ _ fun z hz => ?_
    have e := hh ⟨z, hz⟩
    simp only [Pi.mul_apply]
    have q1 : up (p n : ℍ → ℂ) z = (p n : ℍ → ℂ) ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    have q2 : up h z = h ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    rw [q1, q2]; simpa using e
  have hf : T.an (T.io hr / T.io (p n)) * (up (p n : ℍ → ℂ) : Mero) = (up h : Mero) := by
    have : T.io hr / T.io (p n) * T.io (p n) = T.io hr := div_mul_cancel₀ _ hio0
    have := congrArg T.an this
    rw [map_mul, T.an_io, T.an_io] at this
    exact this
  apply hU.mul_left_cancel
  rw [hrel, ← hf]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightAction
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_sl_right_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ f, T.sl 1 f = f) ∧ ∀ g h f, T.sl (g * h) f = T.sl h (T.sl g f) := by
  intro Ω _ _ _ ε T
  obtain ⟨hext, hcl, -, -⟩ := _root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T
  obtain ⟨c1, cmul, -, -⟩ := _root_.GlobalTheory.FN.cmp_props
  refine ⟨fun f => ?_, fun g h f => ?_⟩
  · have e : (T.sl 1 : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom = RingHom.id T.K := by
      apply hext
      intro a
      exact T.sl_io 1 a a (c1 a).symm
    exact congrArg (fun φ : T.K →+* T.K => φ f) e
  · have e : (T.sl (g * h) : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom =
        ((T.sl h : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom).comp ((T.sl g : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom) := by
      apply hext
      intro a
      obtain ⟨a', ha', hga⟩ := hcl g a
      obtain ⟨a'', ha'', hha⟩ := hcl h a'
      have : (a'' : ℍ → ℂ) = cmp (g * h) a := by rw [ha'', ha', cmul]
      simp only [RingHom.comp_apply]
      show T.sl (g * h) (T.io a) = T.sl h (T.sl g (T.io a))
      rw [T.sl_io (g * h) a a'' this, hga, hha]
    exact congrArg (fun φ : T.K →+* T.K => φ f) e

end GlobalTheory.FN
end

