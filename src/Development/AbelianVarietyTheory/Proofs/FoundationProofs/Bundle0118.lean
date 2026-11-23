module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumNeZero
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hsne_re (N : ℕ) (z : ℂ) :
    (2 * Real.pi * Complex.I * z / N).re = -(2 * Real.pi * z.im / N) := by
  have : (2 * Real.pi * Complex.I * z / N) = ((2 * Real.pi / N : ℝ) : ℂ) * (Complex.I * z) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  simp [Complex.mul_re]
  ring

theorem fn_hsne_pre (N : ℕ) (hN : 0 < N) (C : ℝ) (x : ℂ) (hx : x ≠ 0)
    (hxr : ‖x‖ < Real.exp (-(2 * Real.pi * C / N))) :
    ∃ z : ℂ, C < z.im ∧ Complex.exp (2 * Real.pi * Complex.I * z / N) = x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi), ?_, ?_⟩
  · have hlog : Real.log ‖x‖ < -(2 * Real.pi * C / N) := by
      rw [Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hx)]; exact hxr
    have him : (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)).im
        = -(N * Real.log ‖x‖) / (2 * Real.pi) := by
      have : (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi))
          = ((-(N : ℝ) / (2 * Real.pi) : ℝ) : ℂ) * (Complex.I * Complex.log x) := by
        push_cast; ring
      rw [this, Complex.im_ofReal_mul]
      simp [Complex.mul_im, Complex.log_re]
      ring
    rw [him]
    rw [lt_div_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hlog hNr
    have e : (N : ℝ) * -(2 * Real.pi * C / N) = -(C * (2 * Real.pi)) := by
      field_simp
    nlinarith [this, e]
  · have : 2 * Real.pi * Complex.I * (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)) / N
        = Complex.log x := by
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      field_simp
      ring_nf
      rw [Complex.I_sq]; ring
    rw [this, Complex.exp_log hx]

end GlobalTheory

namespace GlobalTheory

theorem fn_hasSum_ne_zero : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω),
    Den h → h ≠ 0 → HS ε C φ h → ∃ C' : ℝ, ∀ z : ℂ, C' < z.im → φ z ≠ 0 := by
  intro Ω _ ε C φ h hD h0 hS
  obtain ⟨N, n₀, a, hN, ha0, ha, hz⟩ := _root_.GlobalTheory.fnShape Ω h hD h0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  set b : ℕ → ℂ := fun k => ε (a k) with hb
  have hb0 : b 0 ≠ 0 := by
    simp only [hb]; exact (map_ne_zero ε).mpr ha0

  have key : ∀ z : ℂ, C < z.im →
      HasSum (fun k : ℕ => b k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k)
        (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) := fun z hzC =>
    (fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN ha hz).mp (hS z hzC)
  set ρ : ℝ := Real.exp (-(2 * Real.pi * C / N)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hsum : ∀ x : ℂ, ‖x‖ < ρ → Summable fun n => b n * x ^ n := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      have : n ≠ 0 := by simpa using hn
      simp [zero_pow this]
    · obtain ⟨z, hzC, hzx⟩ := fn_hsne_pre N hN C x hx0 hx
      have := key z hzC
      rw [hzx] at this
      exact this.summable
  obtain ⟨ρ', hρ'0, hρ'⟩ := _root_.GlobalTheory.PowerSeriesInv.hasSum_inv b ρ hρ0 hb0 hsum
  refine ⟨max C (-(N * Real.log ρ') / (2 * Real.pi)), fun z hzi => ?_⟩
  have hzC : C < z.im := lt_of_le_of_lt (le_max_left _ _) hzi
  have hz2 : -(N * Real.log ρ') / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hzi
  set x := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef
  have hxn : ‖x‖ < ρ' := by
    rw [hxdef, Complex.norm_exp, fn_hsne_re]
    rw [← Real.exp_log hρ'0, Real.exp_lt_exp]
    rw [div_lt_iff₀ (by positivity)] at hz2
    rw [neg_lt, lt_div_iff₀ hNr]
    nlinarith [hz2]
  have hne := (hρ' x hxn).1
  rw [(key z hzC).tsum_eq] at hne
  intro hφ
  apply hne
  rw [hφ, zero_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisExponentRootOfUnityExpTwoPiI
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.ZetaExp

theorem pow_mod_eq {M : Type*} [Monoid M] {w : M} {N : ℕ} (h : w ^ N = 1) (a : ℕ) : w ^ (a % N) = w ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, h, one_pow, mul_one]

theorem ch_eq_pow (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / N : ℚ) : ℂ)) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) (N : ℕ), 0 < N → (∃ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d) ∧ ∀ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∃ u : (ZMod N)ˣ, (u : ZMod N) = d ∧ ∀ g : ℂ ≃+* ℂ, (∀ x, g (ε x) = ε (s x)) → ZetaAct g N u := by
  intro Ω _ _ _ ε s N hN
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨_, hval, _, _, hprim, _⟩ := _root_.GlobalTheory.FNRoots.main Ω ε
  set ζ := eOm ε (1 / N) with hζ
  have hp : IsPrimitiveRoot ζ N := hprim N hN
  have hsp : IsPrimitiveRoot (s ζ) N := hp.map_of_injective s.injective
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one hsp.pow_eq_one
    exact ⟨i, by rw [← hi, zpow_natCast]⟩
  · intro d hd
    set i : ℕ := (d % (N : ℤ)).toNat with hi
    have hnn : 0 ≤ d % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have hic : (i : ℤ) = d % (N : ℤ) := Int.toNat_of_nonneg hnn
    have hζi : ζ ^ d = ζ ^ i := by
      rw [← zpow_natCast, hic]
      have hz : ζ ≠ 0 := hp.ne_zero hN.ne'
      conv_lhs => rw [← Int.mul_ediv_add_emod d N, zpow_add₀ hz, zpow_mul, zpow_natCast, hp.pow_eq_one, one_zpow, one_mul]
    have hsi : s ζ = ζ ^ i := hd.trans hζi
    have hcop : i.Coprime N := (hp.pow_iff_coprime hN i).1 (hsi ▸ hsp)
    have hdi : ((d : ZMod N)) = (i : ZMod N) := by
      rw [← Int.cast_natCast, hic, ZMod.intCast_mod]
    have hu : IsUnit (i : ZMod N) := (ZMod.isUnit_iff_coprime i N).2 hcop
    refine ⟨hu.unit, by rw [IsUnit.unit_spec, hdi], ?_⟩
    intro g hg j
    have hεζ : ε ζ = Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / N : ℚ) : ℂ)) := hval _
    have hηN : (ε ζ) ^ N = 1 := by rw [← map_pow, hp.pow_eq_one, map_one]
    have hl : g ((ε ζ) ^ j.val) = (ε ζ) ^ (i * j.val) := by
      rw [map_pow, hg, hsi, map_pow, ← pow_mul]
    have hr : ((i : ZMod N) * j).val = (i * j.val) % N := by
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
    rw [ch_eq_pow, ch_eq_pow, ← hεζ, hl, IsUnit.unit_spec, hr, pow_mod_eq hηN]

end GlobalTheory.ZetaExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQOfIntegralQuot
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem hasQ_periodic {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N) (h : HasQ N f a) (τ : ℍ) :
    f ((N : ℝ) +ᵥ τ) = f τ := by
  have h1 := hasQ_vadd N f a (N : ℝ) h
  have hc : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N)) = a := by
    funext n
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : 2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; field_simp
    rw [this, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [hc] at h1
  exact congrFun (_root_.GlobalTheory.QFam.hasQ_unique_both.2 N _ _ a h1 h) τ

theorem hasQ_of_integral_quot : ∀ (N n : ℕ) (A D : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N →
    (∃ a, HasQ N A a) → (∃ d, HasQ N D d) → (∀ j, ∃ c, HasQ N (s j) c) → D ≠ 0 →
    (∀ τ, A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) = 0) →
    ∃ (h : ℍ → ℂ) (b : ℕ → ℂ), HasQ N h b ∧ ∀ τ, A τ = h τ * D τ := by
  intro N n A D s hN ⟨a, hA⟩ ⟨d, hD⟩ hs hD0 heq
  choose c hc using hs
  obtain ⟨hAm, -⟩ := _root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N A a hN hA
  obtain ⟨hDm, -⟩ := _root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N D d hN hD
  have hsm : ∀ j, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s j) ∧ UpperHalfPlane.IsBoundedAtImInfty (s j) :=
    fun j => _root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N (s j) (c j) hN (hc j)
  have hUo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, D τ ≠ 0 := by
    by_contra hc'
    push_neg at hc'
    exact hD0 (funext hc')
  have hofc : ∀ z : ℂ, 0 < z.im → ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  obtain ⟨h₀, hh₀d, hh₀A, hh₀p⟩ := _root_.GlobalTheory.quotient_integral_holomorphic {z : ℂ | 0 < z.im} n
    (A ∘ UpperHalfPlane.ofComplex) (D ∘ UpperHalfPlane.ofComplex)
    (fun j => s j ∘ UpperHalfPlane.ofComplex) hUo hUc (UpperHalfPlane.mdifferentiable_iff.1 hAm)
    (UpperHalfPlane.mdifferentiable_iff.1 hDm) (fun j => UpperHalfPlane.mdifferentiable_iff.1 (hsm j).1)
    ⟨(τ₀ : ℂ), τ₀.im_pos, by simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hτ₀⟩
    (fun z _ => heq _)
  set h : ℍ → ℂ := fun τ => h₀ τ with hdef
  have hAh : ∀ τ, A τ = h τ * D τ := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀A (τ : ℂ) τ.im_pos
  have hhp : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0 := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀p (τ : ℂ) τ.im_pos
  have hhm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    refine UpperHalfPlane.mdifferentiable_iff.2 (hh₀d.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, hofc z hz]
  have hhNm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => h ((N : ℝ) +ᵥ τ)) := by
    have hd : DifferentiableOn ℂ (fun z : ℂ => h₀ (((N : ℝ) : ℂ) + z)) {z : ℂ | 0 < z.im} :=
      hh₀d.comp ((differentiableOn_const _).add differentiableOn_id) fun z hz => by
        show 0 < (((N : ℝ) : ℂ) + z).im
        simpa using hz
    refine UpperHalfPlane.mdifferentiable_iff.2 (hd.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, UpperHalfPlane.coe_vadd, hofc z hz]
  have hper : ∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ := by
    have hz : ∀ τ, (fun τ => h ((N : ℝ) +ᵥ τ) - h τ) τ * D τ = 0 := fun τ => by
      have e1 := hAh ((N : ℝ) +ᵥ τ)
      rw [hasQ_periodic hN hA, hasQ_periodic hN hD, hAh τ] at e1
      simp only
      linear_combination -e1
    rcases _root_.GlobalTheory.fn_mul_eq_zero_dom _ D (hhNm.sub hhm) hDm hz with h0 | h0
    · exact fun τ => sub_eq_zero.1 (congrFun h0 τ)
    · exact absurd h0 hD0
  have hbd : UpperHalfPlane.IsBoundedAtImInfty h := by
    have hS : (fun τ => ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
      have hb : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (fun τ => ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := fun j _ => by
        have : (s j) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := (hsm j).2
        exact this.norm_left
      exact (Asymptotics.IsBigO.sum hb).congr_left fun τ => Finset.sum_apply _ _ _
    have h1 : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) :=
      ((Asymptotics.isBigO_refl (1 : ℍ → ℝ) _).add hS).congr_left fun τ => rfl
    have h2 : h =O[UpperHalfPlane.atImInfty] (fun τ => 1 + ∑ j, ‖s j τ‖) := by
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_)
      have hb := _root_.GlobalTheory.monic_root_norm_le_one_add_sum n (fun j => s j τ) (h τ) (hhp τ)
      have hnn : (0 : ℝ) ≤ 1 + ∑ j, ‖s j τ‖ := by positivity
      rw [Real.norm_of_nonneg hnn, one_mul]
      exact hb
    exact h2.trans h1
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.FN.hasQ_of_periodic_bounded N h hN hhm hper hbd
  exact ⟨h, b, hb, hAh⟩

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormPreservesDeltaPowerConditionStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeNorm_preserves_delta_powerCondition : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ¬ l ∣ N → ∀ f : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f →
  (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (ofSL δ) f = g ^ (l ^ n)) →
  (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧
        (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) *
          X.sl (ofSL δ) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) = g ^ (l ^ n)) := by
  first | exact @GlobalTheory.NormDelta.norm_delta | exact GlobalTheory.NormDelta.norm_delta | (intros; apply GlobalTheory.NormDelta.norm_delta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgZpOfPow
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5

noncomputable section

namespace GlobalTheory.Glue.EvTwist

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def part (N i : ℤ) (a : Lau p) : Lau p where
  coeff r := if r % N = i then a.coeff r else 0
  isPWO_support' := a.isPWO_support.mono (fun r hr h => hr (by simp [h]))

theorem part_coeff (N i : ℤ) (a : Lau p) (r : ℤ) :
    (part N i a).coeff r = if r % N = i then a.coeff r else 0 := rfl

def contr (N : ℤ) (hN : 0 < N) (b : Lau p) : Lau p where
  coeff j := b.coeff (N * j)
  isPWO_support' := by
    refine Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt ⟨-|b.order|, fun j hj => ?_⟩)
    have h : b.order ≤ N * j := HahnSeries.order_le_of_coeff_ne_zero hj
    have h1 := neg_abs_le b.order
    have h2 := abs_nonneg b.order
    by_contra hc
    push_neg at hc
    nlinarith

theorem sum_ite {M : Type} [AddCommMonoid M] (N : ℕ) (hN : 0 < N) (r : ℤ) (f : ℕ → M) :
    ∑ i : Fin N, (if r % (N : ℤ) = ((i : ℕ) : ℤ) then f i else 0) = f (r % (N : ℤ)).toNat := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 := Int.emod_nonneg r hN'.ne'
  have h1 := Int.emod_lt_of_pos r hN'
  rw [Finset.sum_eq_single (⟨(r % (N : ℤ)).toNat, by omega⟩ : Fin N)]
  · rw [if_pos (by simp only; omega)]
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (Fin.ext (by simp only; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem isAlgZp_of_pow {z : Ω} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : IsAlgZp (p := p) z :=
  ⟨Polynomial.X ^ N - 1, by simpa using Polynomial.X_pow_sub_C_ne_zero hN (1 : ℤ_[p]), by simp [h]⟩

theorem isInt_of_pow {z : Ω} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : IsInt (p := p) z :=
  IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)

end GlobalTheory.Glue.EvTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigTranslateOfSubMemAug
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem isEig_translate_of_sub_mem_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N₀ N₁ : Set G) (θ : G → ℂ) (z : G), Datum J θ → Datum N₀ (fun _ => 1) → (∀ y ∈ N₀, y ∈ J ∧ θ y = 1) → (∀ y, y ∈ N₁ ↔ z * y * z⁻¹ ∈ N₀) → (∀ j ∈ J, ∃ y ∈ N₀, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ u u' : V, IsEig π J θ u → IsEig π N₁ (fun _ => 1) u' → u - u' ∈ aug π N₁ (fun _ => 1) → IsEig π J θ (π z u') := by
  intro G V _ _ _ _ _ π hπ J N₀ N₁ θ z hJ hN hsub hconj hdec u u' hu hu' hd
  have hmul : ∀ (a b : G) (v : V), π a (π b v) = π (a * b) v := fun a b v => by
    rw [map_mul]; rfl
  have hw' : IsEig π N₀ (fun _ => 1) (π z u') := by
    intro y hy
    have h1 : z⁻¹ * y * z ∈ N₁ := (hconj _).2 (by
      have : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [this]; exact hy)
    have h2 := hu' _ h1
    have h3 : y * z = z * (z⁻¹ * y * z) := by group
    rw [hmul, h3, ← hmul, h2, map_smul]
  have hmap : ∀ x ∈ aug π N₁ (fun _ => 1), π z x ∈ aug π N₀ (fun _ => 1) := by
    intro x hx
    have : aug π N₁ (fun _ => 1) ≤ (aug π N₀ (fun _ => 1)).comap (π z) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, hh, w, rfl⟩
      refine Submodule.subset_span ⟨z * h * z⁻¹, (hconj h).1 hh, π z w, ?_⟩
      rw [map_sub, map_smul, hmul, hmul]
      congr 3
      group
    exact this hx
  have hww : π z u - π z u' ∈ aug π N₀ (fun _ => 1) := by
    rw [← map_sub]; exact hmap _ hd
  obtain ⟨R, hR1, hRJ, hS⟩ := _root_.GlobalTheory.PsType.avg_eig G V π hπ J θ hJ (π z u)
  have hterm : ∀ j ∈ R, (θ j)⁻¹ • π j (π z u) - π z u ∈ aug π N₀ (fun _ => 1) := by
    intro j hj
    have hjJ := hRJ j hj
    obtain ⟨y, hy, h1, h2⟩ := hdec j hjJ
    have hne : θ j ≠ 0 := by
      intro h0
      have := hJ.val_mul j hjJ j⁻¹ (hJ.inv j hjJ)
      rw [mul_inv_cancel, hJ.val_one, h0, zero_mul] at this
      exact one_ne_zero this
    have h3 := hu _ h1
    have h4 : j * z = y * (z * (z⁻¹ * (y⁻¹ * j) * z)) := by group
    have h5 : π j (π z u) = θ j • π y (π z u) := by
      rw [hmul, h4, ← hmul, ← hmul, h3, h2, map_smul, map_smul]
    rw [h5, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact Submodule.subset_span ⟨y, hy, π z u, by rw [one_smul]⟩
  set S : V := ∑ j ∈ R, (θ j)⁻¹ • π j (π z u) with hSdef
  have hc : (R.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨1, hR1⟩).ne'
  have hA : S - (R.card : ℂ) • π z u ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.sum_mem _ hterm
    rwa [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at this
  have hB : S - (R.card : ℂ) • π z u' ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.add_mem _ hA (Submodule.smul_mem _ (R.card : ℂ) hww)
    rwa [smul_sub, sub_add_sub_cancel] at this
  have hC : IsEig π N₀ (fun _ => 1) (S - (R.card : ℂ) • π z u') := by
    intro y hy
    rw [map_sub, map_smul, hS y (hsub y hy).1, (hsub y hy).2, hw' y hy]
    simp
  have h0 := (_root_.GlobalTheory.PsType.eig_compl_aug G V π hπ N₀ _ hN).1 _ hB hC
  have hE : π z u' = (R.card : ℂ)⁻¹ • S := by
    rw [sub_eq_zero.1 h0, smul_smul, inv_mul_cancel₀ hc, one_smul]
  intro j hj
  rw [hE, map_smul, hS j hj, smul_comm]

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelIntegralMatrixConj
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem germ_eq_of_eqOn_Hs {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) := by
  rw [Filter.Germ.coe_eq]
  exact Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) (fun z hz => h z hz)

theorem kum_kmap_sl : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), 0 < m.det →
      Kum X l n x χ → Kum X l n (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun δ => χ (cj m δ)) := by
  intro Ω _ _ ε X l _ n m x χ hm hK
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩ := hK
  obtain ⟨mobHs, mobMul, mobOne, mobDiff, -, -⟩ := _root_.GlobalTheory.KZ.mob_laws
  obtain ⟨cj1, -, cj3⟩ := _root_.GlobalTheory.KZ.cj_laws
  obtain ⟨-, -, gcomp, -, -⟩ := _root_.GlobalTheory.KZ.Germ.main
  have hcls := (_root_.GlobalTheory.KZ.H3.cls_props Ω ε X l n).2.2.2.2.2.1 (X.sl (toGQ m)).toRingEquiv x f hx
  refine ⟨Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f, fun z => a (mob (toGQ m) z),
    fun z => b (mob (toGQ m) z), M * m.det.natAbs, ?_, hcls, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Nat.mul_pos hM (Int.natAbs_pos.2 hm.ne')
  · exact ha.comp (mobDiff _) (fun z hz => mobHs _ z hz)
  · exact hb.comp (mobDiff _) (fun z hz => mobHs _ z hz)
  · intro h0
    apply hb0
    have h0' : ((fun z => b (mob (toGQ m) z) : ℂ → ℂ) : Mero) = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h0
    have h1 := gcomp (toGQ m)⁻¹ _ _ h0'
    calc (b : Mero) = ((fun z => b (mob (toGQ m) (mob (toGQ m)⁻¹ z)) : ℂ → ℂ) : Mero) := by
          refine germ_eq_of_eqOn_Hs fun z hz => ?_
          rw [← mobMul _ _ z hz, mul_inv_cancel, mobOne]
      _ = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h1
      _ = 0 := rfl
  · obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (f : X.K) = (φ : Mero) :=
      (Quotient.exists_rep (X.an (f : X.K))).imp fun _ h => h.symm
    have h1 : X.an ((Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f : X.Kˣ) : X.K) =
        ((fun z => φ (mob (toGQ m) z) : ℂ → ℂ) : Mero) := X.an_sl (toGQ m) f φ hφ
    rw [h1]
    rw [hφ] at hab
    have e := gcomp (toGQ m) (φ * b ^ (l ^ n)) (a ^ (l ^ n))
      (by rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow]; exact hab)
    rw [← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul]
    exact e
  · intro δ hδ z hz
    obtain ⟨hmδ, hcj⟩ := cj1 m M hm δ hδ
    have e := cj3 m δ (cj m δ) hm hmδ z hz
    show a (mob (toGQ m) (mob (ofSL δ) z)) * b (mob (toGQ m) z) = _ * (a (mob (toGQ m) z) * b (mob (toGQ m) (mob (ofSL δ) z)))
    rw [e]
    exact hrel (cj m δ) hcj (mob (toGQ m) z) (mobHs _ z hz)

end GlobalTheory.KZ.H3
end
end

