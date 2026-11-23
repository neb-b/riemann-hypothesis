module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AbelianFieldHasMuIffExistsPrimitiveRoot
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

private theorem lift_coprime {n N b : ℕ} [NeZero N] (h : n ∣ N) (hb : b.Coprime n) :
    ∃ a : ℕ, a.Coprime N ∧ a ≡ b [MOD n] := by
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime b hb)
  refine ⟨(v : ZMod N).val, ZMod.val_coe_unit_coprime v, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ← ZMod.unitsMap_val h v, hv]
  simp

private theorem exists_aut {N a : ℕ} [NeZero N] (ha : a.Coprime N) :
    ∃ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ, ∀ x : CyclotomicField N ℚ, x ^ N = 1 → τ x = x ^ a := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos N)
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
  set ζ := IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)
  set τ := (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ) hirr).symm (ZMod.unitOfCoprime a ha) with hτdef
  refine ⟨τ, ?_⟩
  have hτ : hζ.autToPow ℚ τ = ZMod.unitOfCoprime a ha :=
    (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ) hirr).apply_symm_apply (ZMod.unitOfCoprime a ha)
  have hτζ : τ ζ = ζ ^ a := by
    rw [← hζ.autToPow_spec ℚ τ, hτ, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  intro x hx
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hτζ, ← pow_mul, ← pow_mul, mul_comm]

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) (hb : A.ker b) : A.ker a := by
  obtain ⟨u, hu, e⟩ := hb
  exact ⟨u, hu, e.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm⟩

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.abelianField_hasMu_iff_exists_primitiveRoot :
    ∀ (A : AbF) (l : ℕ), l.Prime → l ≠ 2 → ∀ (L : Type) [Field L] [NumberField L], IsAbField A L →
      (A.HasMu l ↔ ∃ z : L, IsPrimitiveRoot z l) := by
  intro A l hl hl2 L _ _ hL
  obtain ⟨N, hN, j, ζ, hdvd, hζ, hfix⟩ := hL
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    omega
  have hker1 : A.ker 1 := ⟨1, A.H.one_mem, by simp⟩
  have haut : ∀ a : ℕ, a.Coprime N → ∃ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
      (∀ x : CyclotomicField N ℚ, x ^ N = 1 → τ x = x ^ a) ∧ ((∀ y : L, τ (j y) = j y) ↔ A.ker a) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := exists_aut ha
    exact ⟨τ, hτ, hfix τ a (hτ ζ hζ.pow_eq_one)⟩
  constructor
  · rintro ⟨hlm, hmu⟩
    have hlN : l ∣ N := hlm.trans hdvd
    have hz : IsPrimitiveRoot (ζ ^ (N / l)) l :=
      IsPrimitiveRoot.pow (NeZero.pos N) hζ (by rw [Nat.div_mul_cancel hlN])
    have hord : orderOf (ζ ^ (N / l)) = l := hz.eq_orderOf.symm
    have hfin : IsOfFinOrder (ζ ^ (N / l)) := isOfFinOrder_iff_pow_eq_one.2 ⟨l, hl.pos, hz.pow_eq_one⟩
    have hmem : ζ ^ (N / l) ∈ j.fieldRange := by
      haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
      rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      have hτj : ∀ y : L, τ (j y) = j y := fun y => hτ _ (AlgHom.mem_fieldRange.2 ⟨y, rfl⟩)
      have hτN : (τ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
      obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hτN
      have hka : A.ker a := (hfix τ a ha.symm).1 hτj
      have ha1 : a ≡ 1 [MOD l] := hmu a hka
      have hpow : (ζ ^ (N / l)) ^ a = (ζ ^ (N / l)) ^ 1 := by
        rw [hfin.pow_eq_pow_iff_modEq, hord]
        exact ha1
      rw [map_pow, ← ha, ← pow_mul, mul_comm, pow_mul, hpow, pow_one]
    obtain ⟨w, hw⟩ : ∃ w : L, j w = ζ ^ (N / l) := AlgHom.mem_fieldRange.1 hmem
    refine ⟨w, ?_⟩
    rw [← hw] at hz
    exact (IsPrimitiveRoot.map_iff_of_injective j.toRingHom.injective).1 hz
  · rintro ⟨z, hz⟩
    have hw : IsPrimitiveRoot (j z) l := hz.map_of_injective j.toRingHom.injective
    have hord : orderOf (j z) = l := hw.eq_orderOf.symm
    have hfin : IsOfFinOrder (j z) := isOfFinOrder_iff_pow_eq_one.2 ⟨l, hl.pos, hw.pow_eq_one⟩
    have hlN : l ∣ N := by
      by_contra hnd
      have hcop : Nat.Coprime N l := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      have hirr := Polynomial.cyclotomic.irreducible_rat (Nat.lcm_pos (NeZero.pos N) hl.pos)
      have h1 := IsPrimitiveRoot.lcm_totient_le_finrank hζ hw hirr
      rw [IsCyclotomicExtension.finrank (CyclotomicField N ℚ) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N)),
        Nat.Coprime.lcm_eq_mul hcop, Nat.totient_mul hcop, Nat.totient_prime hl] at h1
      have hpos : 0 < N.totient := Nat.totient_pos.2 (NeZero.pos N)
      have h2 : 2 ≤ l - 1 := by omega
      nlinarith
    have hwN : (j z) ^ N = 1 := by
      obtain ⟨k, hk⟩ := hlN
      have e1 : (j z) ^ N = ((j z) ^ l) ^ k := by rw [← pow_mul, ← hk]
      rw [e1, hw.pow_eq_one, one_pow]
    have key : ∀ a : ℕ, a.Coprime N → A.ker a → a ≡ 1 [MOD l] := by
      intro a ha hka
      obtain ⟨τ, hτ, hiff⟩ := haut a ha
      have h1 := hiff.2 hka z
      rw [hτ _ hwN] at h1
      have h2 : (j z) ^ a = (j z) ^ 1 := by rw [pow_one]; exact h1
      rw [hfin.pow_eq_pow_iff_modEq, hord] at h2
      exact h2
    have hlm : l ∣ A.m := by
      by_contra hnd
      have hcop : Nat.Coprime A.m l := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop 1 2
      have hbm : Nat.Coprime b A.m := by
        unfold Nat.Coprime
        rw [hb1.gcd_eq, Nat.gcd_one_left]
      have h2l : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm hl2)
      have hbl : Nat.Coprime b l := by
        unfold Nat.Coprime
        rw [hb2.gcd_eq]
        exact h2l
      have hbcop : Nat.Coprime b (A.m * l) := Nat.Coprime.mul_right hbm hbl
      have hmlN : A.m * l ∣ N := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd hlN
      obtain ⟨a, ha, hab⟩ := lift_coprime hmlN hbcop
      have ham : a ≡ 1 [MOD A.m] := (Nat.ModEq.of_mul_right l hab).trans hb1
      have hal : a ≡ 2 [MOD l] := (Nat.ModEq.of_mul_left A.m hab).trans hb2
      have hka : A.ker a := ker_congr A ham hker1
      have h21 : 2 ≡ 1 [MOD l] := hal.symm.trans (key a ha hka)
      unfold Nat.ModEq at h21
      rw [Nat.mod_eq_of_lt (by omega : 2 < l), Nat.mod_eq_of_lt (by omega : 1 < l)] at h21
      omega
    refine ⟨hlm, ?_⟩
    intro a hka
    have hacop : a.Coprime A.m := by
      obtain ⟨u, -, hu⟩ := hka
      exact (ZMod.isUnit_iff_coprime a A.m).1 ⟨u, hu⟩
    obtain ⟨a', ha', ha'a⟩ := lift_coprime hdvd hacop
    have hka' := ker_congr A ha'a hka
    exact (Nat.ModEq.of_dvd hlm ha'a).symm.trans (key a' ha' hka')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN
section
noncomputable section

open NumberField

namespace UpperTheory.V

open Formalism.HC UpperTheory.Top

theorem VVminusLe.mono {E : Type} [Field E] [NumberField E] [IsCMField E] {t : ℕ} {B B' : ℝ} (h : VVminusLe E t B)
    (hB : B ≤ B') : VVminusLe E t B' := by
  intro Ω _ _ _ ld
  obtain ⟨h1, h2⟩ := h Ω ld
  exact ⟨h1, fun S hS => (h2 S hS).trans hB⟩

theorem admissible_of_pageN {eps Ct : ℝ} (h0 : 0 < eps) (h1 : eps < 1 / 52) (hC : 1 ≤ Ct) {e : ℝ → ℕ}
    (he : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) : admitted 4 Ct e fun x => ⌊x ^ Ct⌋₊ := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  obtain ⟨a, b⟩ := he x hx1
  have h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h3 : x ^ (2 + 8 * eps) ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h4 : x ^ (4 : ℝ) = x * x ^ (3 : ℝ) := by
    rw [show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have h5 : (0 : ℝ) ≤ x ^ (3 : ℝ) := by positivity
  have h6 : x ≤ x ^ Ct := Real.self_le_rpow_of_one_le hx1 hC
  have h8 : 2 * x ^ (3 : ℝ) ≤ x * x ^ (3 : ℝ) := mul_le_mul_of_nonneg_right hx h5
  refine ⟨?_, b.trans ((mul_le_mul_of_nonneg_left h3 zero_le_two).trans (h8.trans h4.ge)), Nat.le_floor (by push_cast; linarith), Nat.floor_le (by linarith)⟩
  rw [Real.rpow_two] at h2
  have h7 : (2 : ℝ) ^ 2 ≤ 2 ^ e x := by nlinarith
  exact (pow_le_pow_iff_right₀ (by norm_num)).1 h7

theorem vwinAt_of_joint {Ct : ℝ} (hC : 1 ≤ Ct) (hJ : JointWin Ct) (hc : ThmBc Ct) (ψ : PChar) : VWinAt ψ Ct := by
  intro eps h0 h1 e he
  set t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊ with ht
  have hadm : admitted 4 Ct e t := admissible_of_pageN h0 h1 hC he
  obtain ⟨J, C, P, XJ, hJ0, hmain⟩ := hJ ψ eps 4 h0 h1 e t hadm
  obtain ⟨Cb, hCb⟩ := hc
  obtain ⟨K, hK0, hK⟩ := minusBound_le_exp_of_log_le Cb (AbF.ofChar ψ).deg
  obtain ⟨xT, hxT⟩ := error_terms_le_sqrt_exp_rpow eps K C h0
  obtain ⟨xN, hxN⟩ := log_conductor_mul_height_le_of_pageN eps Ct ψ.N h0 h1
  obtain ⟨Y0, hY0⟩ := log_mul_le_rpow_of_winPair eps h0
  obtain ⟨J', hJ'1, hJJ'⟩ : ∃ J' : ℝ, 1 ≤ J' ∧ J ≤ J' := ⟨max J 1, le_max_right _ _, le_max_left _ _⟩
  have hJ'0 : 0 < J' := by linarith
  obtain ⟨P', hPP', hNP'⟩ : ∃ P' : ℝ, P ≤ P' ∧ (ψ.N : ℝ) ≤ P' := ⟨max P (ψ.N : ℝ), le_max_left _ _, le_max_right _ _⟩
  obtain ⟨XB, hXB⟩ := eventually_winPair_gt_power eps J' Ct P' h0 hJ'0
  obtain ⟨L, hxTL, hxNL, hY0L, h2L⟩ : ∃ L : ℝ, xT ≤ L ∧ xN ≤ L ∧ Y0 ≤ L ∧ 2 ≤ L :=
    ⟨max (max xT xN) (max Y0 2), le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  refine ⟨J', hJ'1, max (max XJ XB) (L ^ J'), ?_⟩
  intro X hX q d hw
  have hXJ : XJ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXB' : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXL : L ^ J' ≤ X := le_trans (le_max_right _ _) hX
  have hLX : L ≤ X ^ (1 / J') := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hXL (le_of_lt (one_div_pos.mpr hJ'0))
    rwa [← Real.rpow_mul hL0, mul_one_div_cancel hJ'0.ne', Real.rpow_one] at this
  have hX1 : 1 ≤ X := by
    have : 1 ≤ L ^ J' := Real.one_le_rpow hL1 hJ'0.le
    linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  obtain ⟨hq3, hd3, hPq, hPd⟩ := hXB X hXB' q d hw
  have hlog := hY0 _ (hY0L.trans hLX) q d hw
  have hpow : (X ^ (1 / J')) ^ (eps / 4) = X ^ (eps / (4 * J')) := by
    rw [← Real.rpow_mul hX0]
    congr 1
    field_simp
  have hmono : X ^ (eps / (4 * J')) ≤ X ^ (eps / (4 * J)) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (div_le_div_of_nonneg_left h0.le (by positivity) (by linarith))
  have hlogJ : Real.log (↑q * ↑d) ≤ X ^ (eps / (4 * J)) := by
    rw [hpow] at hlog
    exact hlog.trans hmono
  have hN0 : 0 < ψ.N := (AbF.ofChar ψ).pos
  have hcop : ∀ r : ℕ, Nat.Prime r → (ψ.N : ℝ) < r → Nat.Coprime r ψ.N := by
    intro r hr hlt
    have hlt' : ψ.N < r := by exact_mod_cast hlt
    exact (Nat.Prime.coprime_iff_not_dvd hr).2 (fun hdvd => absurd (Nat.le_of_dvd hN0 hdvd) (not_le.2 hlt'))
  have hpp : PrimePair ψ.N q d :=
    ⟨hw.q_prime, hw.q_mod, hw.d_prime, hw.d_mod,
      Nat.Coprime.mul_left (hcop q hw.q_prime (lt_of_le_of_lt hNP' hPq)) (hcop d hw.d_prime (lt_of_le_of_lt hNP' hPd))⟩
  obtain ⟨Y, ⟨hYlo, hYhi⟩, hY⟩ :=
    hmain X hXJ q d hpp hq3 hd3 (lt_of_le_of_lt hPP' hPq) (lt_of_le_of_lt hPP' hPd) hlogJ
  have hWY : X ^ (1 / J') ≤ Y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (one_div_le_one_div_of_le (by linarith) hJJ')) hYlo
  refine ⟨Y, hWY, hYhi, ?_⟩
  intro x hxY hxY2
  have hWx : X ^ (1 / J') ≤ x := hWY.trans hxY
  have hLx : L ≤ x := hLX.trans hWx
  have hx2 : 2 ≤ x := h2L.trans hLx
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hBa, hHV⟩ := hY x hxY hxY2
  intro E _ _ hE
  have hq0 : 0 < q := hw.q_prime.pos
  have hd0 : 0 < d := hw.d_prime.pos
  have hq4 : q % 4 = 3 := by
    have := hw.q_mod
    omega
  haveI : IsCMField E := isCMField_of_isChiField ψ (e x) q d hw.q_prime hq4 E hE
  have hE' : IsCompField (AbF.ofChar ψ) (e x) q d E := (isCompField_ofChar ψ (e x) q d E).2 hE
  have h2 := hBa E hE'
  have hp := hHV E hE
  have hm := hCb (AbF.ofChar ψ) 4 e t hadm x hx2 q d hpp E hE'
  obtain ⟨hc1, hc2, hc3⟩ := conductor_bounds_of_isChiField ψ (e x) q d hq0 hd0 E hE
  obtain ⟨-, -, ht2, htle⟩ := hadm x hx2
  have ht1 : 1 ≤ t x := by omega
  have hWpos : (0 : ℝ) ≤ X ^ (1 / J') := Real.rpow_nonneg hX0 _
  have hqd : Real.log (↑q * ↑d) ≤ x ^ (eps / 4) := by
    have hlog0 := hY0 _ (hY0L.trans hLX) q d hw
    exact hlog0.trans (Real.rpow_le_rpow hWpos hWx (by linarith))
  have hNt := hxN x (hxNL.trans hLx) (condF E) (t x) (e x) q d hc1 hc2 (he x hx1) ht1 htle hqd
  have hmb := hK (Module.finrank ℚ E) (condF E) (t x) (x ^ (eps / 4)) hc1 ht1 hc3 hNt
  have hm' := VVminusLe.mono hm hmb
  have hv := vvle_of_parts h2 hm' hp
  have hu1 : (1 : ℝ) ≤ ↑(condF E) * ↑(t x) := by
    have a : (1 : ℝ) ≤ condF E := by exact_mod_cast hc1
    have b : (1 : ℝ) ≤ t x := by exact_mod_cast ht1
    nlinarith
  have htot := hxT x (hxTL.trans hLx) _ hu1 hNt
  exact VVle.mono hv le_rfl htot

theorem vwin_of_joint (hJ : JointWin 401) (hc : ThmBc 401) : VWin := by
  intro ψ
  exact vwinAt_of_joint (by norm_num) hJ hc ψ

end UpperTheory.V

end
end

