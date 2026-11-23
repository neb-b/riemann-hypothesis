module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearFixedSpan
section
namespace GlobalTheory

theorem semilinear_fixed_span (L : Type) [Field L] (s : L ≃+* L) (r : ℕ) (hr : 0 < r)
    (hsr : ∀ x, (⇑s)^[r] x = x) (hsi : ∀ i, 0 < i → i < r → ∃ x, (⇑s)^[i] x ≠ x)
    (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (F : V →+ V)
    (hF : ∀ (a : L) (v : V), F (a • v) = s a • F v) (hFr : ∀ v, (⇑F)^[r] v = v) :
    Submodule.span L {v | F v = v} = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (LinearMap.ext h)

  have hFi : ∀ (i : ℕ) (a : L) (w : V), (⇑F)^[i] (a • w) = (⇑s)^[i] a • (⇑F)^[i] w := by
    intro i
    induction i with
    | zero => intro a w; simp
    | succ n ih =>
      intro a w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, hF]

  have htr : ∀ w : V, F (∑ i ∈ Finset.range r, (⇑F)^[i] w) = ∑ i ∈ Finset.range r, (⇑F)^[i] w := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have h1 := Finset.sum_range_succ' (fun i => (⇑F)^[i] w) r
    have h2 := Finset.sum_range_succ (fun i => (⇑F)^[i] w) r
    simp only [Function.iterate_succ_apply'] at h1
    rw [hFr w] at h2
    rw [show (⇑F)^[0] w = w from rfl] at h1
    exact add_right_cancel (h1.symm.trans h2)

  let χ : Fin r → (L →* L) := fun i => (((s : L →+* L) ^ (i : ℕ) : L →+* L) : L →* L)
  have hχ : ∀ (i : Fin r) (a : L), χ i a = (⇑s)^[i] a := by
    intro i a
    simp [χ, RingHom.coe_pow]
  have hinj : Function.Injective χ := by
    intro i j hij
    have key : ∀ (i j : Fin r), (i : ℕ) < j → χ i = χ j → False := by
      intro i j hlt he
      obtain ⟨x, hx⟩ := hsi ((j : ℕ) - i) (Nat.sub_pos_of_lt hlt) (by omega)
      apply hx
      have h3 := congrArg (fun g : L →* L => g x) he
      simp only [hχ] at h3
      have hj : (j : ℕ) = (i : ℕ) + ((j : ℕ) - i) := by omega
      rw [hj, Function.iterate_add_apply] at h3
      exact ((s.injective.iterate _) h3).symm
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact (key i j h hij).elim
    · exact Fin.ext h
    · exact (key j i h hij.symm).elim
  have hli := (linearIndependent_monoidHom L L).comp χ hinj
  have hsum : ∑ i : Fin r, f ((⇑F)^[i] v) • (((fun g : L →* L => (g : L → L)) ∘ χ) i) = 0 := by
    funext a
    have hfix : (∑ i ∈ Finset.range r, (⇑F)^[i] (a • v)) ∈ Submodule.span L {v | F v = v} :=
      Submodule.subset_span (htr (a • v))
    have h0 := hfk hfix
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.mem_ker, map_sum] at h0
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, hχ,
      Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range (fun i => f ((⇑F)^[i] v) * (⇑s)^[i] a)]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFi, map_smul, smul_eq_mul, mul_comm]
  exact hv ((Fintype.linearIndependent_iff.1 hli) (fun i => f ((⇑F)^[(i : ℕ)] v)) hsum ⟨0, hr⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SevenMulHeightBoundLeHalfOfParameters
section
namespace GlobalTheory

theorem seven_mul_height_bound_le_half :
    ∀ (D T ρ PP κ b f r m k H TO Nb nW t : ℝ), 1 ≤ D → 0 < b → 1 ≤ f → 2 ≤ m → m ≤ k →
      r = k + m - 1 → 0 ≤ t → 0 ≤ κ → κ ≤ 4 * f * r * b → PP ^ 2 * D ^ 2 * k / m ≤ T →
      T ≤ TO → 4 * D + 4 ≤ T →
      ρ ≤ 3 * r * (f * (r * r * (2 * (T + D + 1)) / H + 2 * r * r * T * (2 / Real.sqrt b))) →
      TO * Nb * f ^ 2 * m ^ 2 * k * D * PP ≤ H → 2500 * r * (D + 1) ≤ TO →
      f * r * (r + 1) ≤ nW → (2 * f * m) ^ 4 * nW ≤ PP → PP ^ 3 * TO ^ 2 ≤ Real.sqrt b →
      TO * nW ≤ r + t → m * (t + 1) ≤ Nb → 7 * (D ^ 2 / T + D * ρ) * (PP * κ) ≤ b / 2 := by
  intro D T ρ PP κ b f r m k H TO Nb nW t hD hb hf hm hmk hr ht hκ0 hκ hT1 hTTO hT2 hρ hH hTO
    hnW hPP hPPb htn hNb
  have hk0 : 0 < k := by linarith
  have hr3 : 3 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hf0 : 0 < f := by linarith
  have hm0 : 0 < m := by linarith
  have hT0 : 0 < T := by linarith
  have hTO0 : 0 < TO := by linarith
  have hD0 : 0 < D := by linarith

  have hnW2 : f * r ^ 2 ≤ nW := by linarith [mul_pos hf0 hr0]
  have h4f : 4 * f ≤ 2 * f * m := by linarith [mul_le_mul_of_nonneg_left hm hf0.le]
  have hfm4 : (4 * f) ^ 4 ≤ (2 * f * m) ^ 4 := pow_le_pow_left₀ (by linarith) h4f 4
  have hf3 : 1 ≤ f ^ 3 := one_le_pow₀ hf
  have h256 : 256 * f ≤ (2 * f * m) ^ 4 := by
    have e : (4 * f) ^ 4 = 256 * f * f ^ 3 := by ring
    linarith [mul_le_mul_of_nonneg_left hf3 hf0.le]
  have hPPlow : 256 * f * (f * r ^ 2) ≤ PP := by
    have := mul_le_mul h256 hnW2 (mul_nonneg hf0.le (sq_nonneg r)) (by positivity)
    linarith
  have hPP0 : 0 < PP := lt_of_lt_of_le (by positivity) hPPlow

  have hX0 : 0 ≤ D ^ 2 / T := div_nonneg (sq_nonneg D) hT0.le
  have hXT : D ^ 2 / T * T = D ^ 2 := div_mul_cancel₀ _ hT0.ne'
  have h1 : PP ^ 2 * D ^ 2 * k ≤ T * m := by
    rw [div_le_iff₀ hm0] at hT1; linarith
  have hXPP2 : D ^ 2 / T * PP ^ 2 ≤ 1 := by
    have e : D ^ 2 / T * PP ^ 2 * (T * k) = PP ^ 2 * D ^ 2 * k := by
      rw [show D ^ 2 / T * PP ^ 2 * (T * k) = (D ^ 2 / T * T) * PP ^ 2 * k by ring, hXT]; ring
    have hTk : 0 < T * k := mul_pos hT0 hk0
    have : D ^ 2 / T * PP ^ 2 * (T * k) ≤ 1 * (T * k) := by
      rw [e]; linarith [mul_le_mul_of_nonneg_left hmk hT0.le]
    exact le_of_mul_le_mul_right this hTk
  have hfr : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf (by linarith)
  have h224 : 224 * (f * r) ≤ PP := by
    linarith [mul_le_mul_of_nonneg_left hfr (by linarith : (0:ℝ) ≤ f * r)]
  have hXPP : 0 ≤ D ^ 2 / T * PP := mul_nonneg hX0 hPP0.le
  have ha1 : D ^ 2 / T * PP * (224 * (f * r)) ≤ 1 := by
    calc D ^ 2 / T * PP * (224 * (f * r)) ≤ D ^ 2 / T * PP * PP :=
          mul_le_mul_of_nonneg_left h224 hXPP
      _ = D ^ 2 / T * PP ^ 2 := by ring
      _ ≤ 1 := hXPP2
  have ha : 7 * (D ^ 2 / T) * (PP * κ) ≤ b / 8 := by
    have e1 : PP * κ ≤ PP * (4 * f * r * b) := mul_le_mul_of_nonneg_left hκ hPP0.le
    have e2 := mul_le_mul_of_nonneg_left e1 (by linarith [hX0] : (0:ℝ) ≤ 7 * (D ^ 2 / T))
    have e3 := mul_le_mul_of_nonneg_right ha1 hb.le
    linarith

  have hNb0 : 0 < Nb := by linarith [mul_pos hm0 (by linarith : (0:ℝ) < t + 1)]
  have hH0 : 0 < H := by
    have : 0 < TO * Nb * f ^ 2 * m ^ 2 * k * D * PP :=
      mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hTO0 hNb0) (pow_pos hf0 2))
        (pow_pos hm0 2)) hk0) hD0) hPP0
    linarith
  generalize hs : Real.sqrt b = s at hρ hPPb
  have hs0 : 0 < s := by rw [← hs]; exact Real.sqrt_pos.mpr hb
  have hss : s * s = b := by rw [← hs]; exact Real.mul_self_sqrt hb.le
  generalize hS1 : r * r * (2 * (T + D + 1)) / H = S1 at hρ
  generalize hS2 : 2 * r * r * T * (2 / s) = S2 at hρ
  have hS1H : S1 * H = r * r * (2 * (T + D + 1)) := by
    rw [← hS1]; exact div_mul_cancel₀ _ hH0.ne'
  have hS1_0 : 0 ≤ S1 := by
    rw [← hS1]; exact div_nonneg (mul_nonneg (mul_self_nonneg r) (by linarith)) hH0.le
  have h2s : (2:ℝ) / s * s = 2 := div_mul_cancel₀ 2 hs0.ne'
  have hS2s : S2 * s = 4 * r ^ 2 * T := by
    rw [← hS2]
    calc 2 * r * r * T * (2 / s) * s = 2 * r * r * T * (2 / s * s) := by ring
      _ = 4 * r ^ 2 * T := by rw [h2s]; ring
  have hS2_0 : 0 ≤ S2 := by
    rw [← hS2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr0.le) hr0.le) hT0.le)
      (div_nonneg (by norm_num) hs0.le)

  have hS1b : S1 * H ≤ 4 * r ^ 2 * TO := by
    rw [hS1H]
    linarith [mul_le_mul_of_nonneg_left (show 2 * (T + D + 1) ≤ 4 * TO by linarith)
      (mul_self_nonneg r)]
  have hYQ : S1 * D * f ^ 2 * PP * (Nb * m ^ 2 * k) ≤ 4 * r ^ 2 := by
    have e1 : S1 * (TO * Nb * f ^ 2 * m ^ 2 * k * D * PP) ≤ S1 * H :=
      mul_le_mul_of_nonneg_left hH hS1_0
    have e2 : S1 * D * f ^ 2 * PP * (Nb * m ^ 2 * k) * TO ≤ 4 * r ^ 2 * TO := by
      calc _ = S1 * (TO * Nb * f ^ 2 * m ^ 2 * k * D * PP) := by ring
        _ ≤ S1 * H := e1
        _ ≤ _ := hS1b
    exact le_of_mul_le_mul_right e2 hTO0
  have hTO5 : 5000 * r ≤ TO := by
    linarith [mul_le_mul_of_nonneg_left (show (2:ℝ) ≤ D + 1 by linarith) hr0.le]
  have hrr1 : 0 ≤ r * (r + 1) := mul_nonneg hr0.le (by linarith)
  have hnW3 : r * (r + 1) ≤ nW := by
    linarith [mul_le_mul_of_nonneg_right hf hrr1]
  have hTOnW : 5000 * r * (r * (r + 1)) ≤ TO * nW := mul_le_mul hTO5 hnW3 hrr1 hTO0.le
  have ht1 : 5000 * r ^ 3 ≤ t + 1 := by
    linarith [mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ r by linarith) hr0.le]
  have hm3 : 8 ≤ m ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm 3
    linarith [show (2:ℝ) ^ 3 = 8 by norm_num]
  have hm3k : 4 * r ≤ m ^ 3 * k := by linarith [mul_le_mul_of_nonneg_right hm3 hk0.le]
  have hQlow : 20000 * r ^ 4 ≤ Nb * m ^ 2 * k := by
    have e1 : m * (t + 1) * (m ^ 2 * k) ≤ Nb * (m ^ 2 * k) :=
      mul_le_mul_of_nonneg_right hNb (mul_nonneg (sq_nonneg m) hk0.le)
    have e2 : (4 * r) * (5000 * r ^ 3) ≤ (m ^ 3 * k) * (t + 1) :=
      mul_le_mul hm3k ht1 (mul_nonneg (by norm_num) (pow_nonneg hr0.le 3))
        (mul_nonneg (pow_nonneg hm0.le 3) hk0.le)
    linarith [e1, e2]
  have hY0 : 0 ≤ S1 * D * f ^ 2 * PP :=
    mul_nonneg (mul_nonneg (mul_nonneg hS1_0 hD0.le) (sq_nonneg f)) hPP0.le
  have hY : S1 * D * f ^ 2 * PP * (5000 * r ^ 2) ≤ 1 := by
    have e1 := mul_le_mul_of_nonneg_left hQlow hY0
    have hr2 : 0 < 4 * r ^ 2 := by have := pow_pos hr0 2; linarith
    have e2 : (4 * r ^ 2) * (S1 * D * f ^ 2 * PP * (5000 * r ^ 2)) ≤ (4 * r ^ 2) * 1 := by
      linarith [hYQ, e1]
    exact le_of_mul_le_mul_left e2 hr2
  have hterm1 : 7 * (D * (3 * r * (f * S1))) * (PP * κ) ≤ b / 8 := by
    have e1 : PP * κ ≤ PP * (4 * f * r * b) := mul_le_mul_of_nonneg_left hκ hPP0.le
    have hc : 0 ≤ 7 * (D * (3 * r * (f * S1))) :=
      mul_nonneg (by norm_num) (mul_nonneg hD0.le
        (mul_nonneg (mul_nonneg (by norm_num) hr0.le) (mul_nonneg hf0.le hS1_0)))
    have e2 := mul_le_mul_of_nonneg_left e1 hc
    have e3 := mul_le_mul_of_nonneg_right hY hb.le
    linarith

  have hPP2 : 2688 * D * r ^ 4 * f ^ 2 ≤ PP ^ 2 * TO := by
    have hTOD : D ≤ TO := by
      linarith [mul_le_mul_of_nonneg_right hr3 (by linarith : (0:ℝ) ≤ D + 1)]
    have e1 : (256 * f * (f * r ^ 2)) ^ 2 ≤ PP ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by norm_num) hf0.le)
        (mul_nonneg hf0.le (sq_nonneg r))) hPPlow 2
    have hf2 : 1 ≤ f ^ 2 := one_le_pow₀ hf
    have e2 : 2688 * r ^ 4 * f ^ 2 ≤ (256 * f * (f * r ^ 2)) ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right hf2 (by positivity : (0:ℝ) ≤ f ^ 2 * r ^ 4),
        (by positivity : (0:ℝ) ≤ f ^ 2 * r ^ 4)]
    have e3 := mul_le_mul (le_trans e2 e1) hTOD hD0.le (sq_nonneg PP)
    linarith [e3]
  have hterm2 : 7 * (D * (3 * r * (f * S2))) * (PP * κ) ≤ b / 8 := by
    have e1 : PP * κ ≤ PP * (4 * f * r * b) := mul_le_mul_of_nonneg_left hκ hPP0.le
    have hc : 0 ≤ 7 * (D * (3 * r * (f * S2))) :=
      mul_nonneg (by norm_num) (mul_nonneg hD0.le
        (mul_nonneg (mul_nonneg (by norm_num) hr0.le) (mul_nonneg hf0.le hS2_0)))
    have e2 := mul_le_mul_of_nonneg_left e1 hc
    have e3 : 7 * (D * (3 * r * (f * S2))) * (PP * (4 * f * r * b))
        = 336 * D * r ^ 4 * f ^ 2 * T * PP * s := by
      rw [← hss]
      calc _ = 84 * D * r ^ 2 * f ^ 2 * PP * (S2 * s) * s := by ring
        _ = _ := by rw [hS2s]; ring
    have e4 : 2688 * D * r ^ 4 * f ^ 2 * T * PP ≤ s := by
      have f1 := mul_le_mul hPP2 hTTO hT0.le (mul_nonneg (sq_nonneg PP) hTO0.le)
      have f2 := mul_le_mul_of_nonneg_right f1 hPP0.le
      calc 2688 * D * r ^ 4 * f ^ 2 * T * PP ≤ PP ^ 2 * TO * TO * PP := f2
        _ = PP ^ 3 * TO ^ 2 := by ring
        _ ≤ s := hPPb
    have e5 := mul_le_mul_of_nonneg_right e4 hs0.le
    linarith [e2, e3, e5, hss]
  have hDρ : D * ρ * (PP * κ) ≤ D * (3 * r * (f * (S1 + S2))) * (PP * κ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ hD0.le) (mul_nonneg hPP0.le hκ0)
  have e : 7 * (D ^ 2 / T + D * ρ) * (PP * κ)
      = 7 * (D ^ 2 / T) * (PP * κ) + 7 * (D * ρ * (PP * κ)) := by ring
  have e' : D * (3 * r * (f * (S1 + S2))) * (PP * κ)
      = D * (3 * r * (f * S1)) * (PP * κ) + D * (3 * r * (f * S2)) * (PP * κ) := by ring
  rw [e]
  linarith [ha, hterm1, hterm2, hDρ, e', hb]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMulPrimeZmodTensorComplex
section
open CategoryTheory Limits

noncomputable section

namespace GlobalTheory

abbrev pMultiples (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] : Submodule ℤ M :=
  LinearMap.range ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M)

lemma zmultiples_mkQ_p (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    zmultiplesHom (M →+ M ⧸ pMultiples p M) (pMultiples p M).mkQ.toAddMonoidHom (p : ℤ) = 0 := by
  ext m
  simp only [zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, AddMonoidHom.zero_apply]
  show (p : ℤ) • Submodule.Quotient.mk m = (0 : M ⧸ pMultiples p M)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨m, by simp⟩

def modPPairing (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    ZMod p →+ M →+ (M ⧸ pMultiples p M) :=
  ZMod.lift p ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩

lemma modPPairing_one (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] (m : M) :
    modPPairing p M 1 m = Submodule.Quotient.mk m := by
  have h := ZMod.lift_coe p (A := M →+ (M ⧸ pMultiples p M))
    ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩ 1
  simp only [Int.cast_one] at h
  unfold modPPairing
  rw [h]
  simp

abbrev zmodOverInt (p : ℕ) : ModuleCat.{0} ℤ :=
  (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of (ZMod p) (ZMod p))

def tensorToModP (p : ℕ) (M : ModuleCat.{0} ℤ) :
    TensorProduct ℤ (zmodOverInt p) M →+ (M ⧸ pMultiples p M) :=
  TensorProduct.liftAddHom (modPPairing p M) (fun r a m => by
    have key : ∀ b : ZMod p, modPPairing p M ((r : ZMod p) * b) m = r • modPPairing p M b m := by
      intro b
      rw [← zsmul_eq_mul, map_zsmul]
      rfl
    refine (key a).trans ?_
    rw [← map_zsmul]
    congr 1
    exact (int_smul_eq_zsmul _ r m).symm)

lemma tensorToModP_unit (p : ℕ) (M : ModuleCat.{0} ℤ) (m : M) :
    tensorToModP p M
      (((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom m) =
      Submodule.Quotient.mk m := by
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  unfold tensorToModP
  exact (TensorProduct.liftAddHom_tmul _ _ _ _).trans (modPPairing_one p M m)

end GlobalTheory

end

noncomputable section

namespace GlobalTheory

def oneZ (p : ℕ) : zmodOverInt p := (1 : ZMod p)

lemma oneZ_tmul_surjective (p : ℕ) (M : ModuleCat.{0} ℤ) :
    ∀ t : TensorProduct ℤ (zmodOverInt p) M, ∃ m : M, oneZ p ⊗ₜ[ℤ] m = t := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul a m =>
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := p) a
    have h1 := map_zsmul (AddMonoidHom.mk' (fun x : M => oneZ p ⊗ₜ[ℤ] x) (TensorProduct.tmul_add _)) k m
    have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] m)
      (fun b c => TensorProduct.add_tmul b c m)) k (oneZ p)
    refine ⟨_, (h1.trans h2.symm).trans (congrArg (fun x => x ⊗ₜ[ℤ] m) ?_)⟩
    show (k • (1 : ZMod p) : ZMod p) = a
    rw [zsmul_one]
    exact hk
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, (TensorProduct.tmul_add _ u v).trans (by rw [hu, hv])⟩

lemma unit_surjective_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom := by
  intro t
  obtain ⟨m, hm⟩ := oneZ_tmul_surjective p M t
  exact ⟨m, (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans hm⟩

lemma unit_kernel_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) (y : M)
    (hy : ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom y = 0) :
    ∃ x : M, ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x = y := by
  have h := tensorToModP_unit p M y
  rw [hy] at h
  exact (Submodule.Quotient.mk_eq_zero _).mp (h.symm.trans (map_zero (tensorToModP p M)))

lemma oneZ_tmul_p (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    oneZ p ⊗ₜ[ℤ] ((p : ℤ) • x) = 0 := by
  have h1 := map_zsmul (AddMonoidHom.mk' (fun y : M => oneZ p ⊗ₜ[ℤ] y) (TensorProduct.tmul_add _)) (p : ℤ) x
  have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] x)
      (fun b c => TensorProduct.add_tmul b c x)) (p : ℤ) (oneZ p)
  refine (h1.trans h2.symm).trans ((congrArg (fun b => b ⊗ₜ[ℤ] x) ?_).trans (TensorProduct.zero_tmul _ _))
  show ((p : ℤ) • (1 : ZMod p) : ZMod p) = 0
  simp

lemma unit_pmul_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom
      (((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x) = 0 :=
  (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans (oneZ_tmul_p p M x)

lemma pmul_injective (p : ℕ) (M : ModuleCat.{0} ℤ) (h : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Function.Injective (ConcreteCategory.hom ((p : ℤ) • 𝟙 M)) := by
  intro a b hab
  have hab' : (p : ℤ) • a = (p : ℤ) • b := hab
  apply sub_eq_zero.mp
  apply h
  rw [zsmul_sub, hab', sub_self]

theorem shortExact_mul_p_modP :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) →
      ∃ (π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C)) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0),
        (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact := by
  intro C p _ hinj
  let π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C) :=
    { f := fun n => (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app (C.X n)
      comm' := fun i j _ =>
        ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.naturality (C.d i j)) }
  have hz : ((p : ℤ) • 𝟙 C) ≫ π = 0 := by
    ext n x
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f,
      ModuleCat.hom_comp, ModuleCat.hom_zsmul, ModuleCat.hom_id, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact unit_pmul_zmod p (C.X n) x
  refine ⟨π, hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map,
      HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_zsmul,
      ModuleCat.hom_id] at hy ⊢
    exact unit_kernel_zmod p (C.X n) y hy
  · rw [ModuleCat.mono_iff_injective]
    exact pmul_injective p (C.X n) (hinj n)
  · rw [ModuleCat.epi_iff_surjective]
    exact unit_surjective_zmod p (C.X n)

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilOrbitalMeasure
section
open NumberField

namespace GlobalTheory

theorem padicAlgCl_norm_ratCast (q : ℕ) [Fact q.Prime] (c : ℚ) :
    ‖(c : PadicAlgCl q)‖ = ‖((c : ℚ) : ℚ_[q])‖ := by
  rw [← PadicAlgCl.norm_extends q (c : ℚ_[q]), map_ratCast]

theorem norm_conj_le_one_of_bounded_coords :
    ∀ (M : Type) [CommRing M] [Algebra ℚ M] (q : ℕ) [Fact q.Prime] (ι : Type) [Fintype ι]
      (f : M →ₗ[ℚ] (ι → ℚ)), Function.Injective f → ∀ (a : M) (B : ℝ),
      (∀ (k : ℕ) (i : ι), ‖((f (a ^ k) i : ℚ) : ℚ_[q])‖ ≤ B) →
      ∀ τ : M →+* PadicAlgCl q, ‖τ a‖ ≤ 1 := by
  intro M _ _ q _ ι _ f hf a B hB τ
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hf)
  have hgf : ∀ m, g (f m) = m := fun m => by
    simpa using LinearMap.congr_fun hg m
  have hsmul : ∀ (c : ℚ) (m : M), τ (c • m) = (c : PadicAlgCl q) * τ m := by
    intro c m
    rw [Algebra.smul_def, map_mul]
    congr 1
    exact eq_ratCast (τ.comp (algebraMap ℚ M)) c
  set C : ℝ := ∑ i, ‖τ (g (Pi.single i 1))‖ with hC
  have hbound : ∀ k : ℕ, ‖τ a‖ ^ k ≤ B * C := by
    intro k
    rw [← norm_pow, ← map_pow, ← hgf (a ^ k)]
    have hv : f (a ^ k) = ∑ i, f (a ^ k) i • (Pi.single i 1 : ι → ℚ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv, map_sum, map_sum, hC, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul, hsmul, norm_mul, padicAlgCl_norm_ratCast]
    exact mul_le_mul_of_nonneg_right (hB k i) (norm_nonneg _)
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B * C) h
  exact (lt_irrefl _ ((hbound k).trans_lt hk))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanOneTmulEqTopAlt
section
open scoped TensorProduct

namespace GlobalTheory.OneTensorSpanTop

theorem span_one_tmul_eq_top (k : Type) [Field k] (C O : Type) [CommRing C] [Ring O]
    [Algebra C O] [Algebra C k] :
    Submodule.span k (Set.range fun (o : O) ↦ (1 : k) ⊗ₜ[C] o) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a o =>
    have h : a ⊗ₜ[C] o = a • ((1 : k) ⊗ₜ[C] o) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨o, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end GlobalTheory.OneTensorSpanTop
end

