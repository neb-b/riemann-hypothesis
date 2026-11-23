module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensLsA
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0008
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle0001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensLs
section
open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

def Φe (j : ZMod 2) : ℂ := if j = 0 then -1 else 1

def eps (n : ℕ) : ℂ := Φe (n : ZMod 2)

lemma Φe_sum : ∑ j, Φe j = 0 := by
  show ∑ j : Fin 2, (if j = 0 then (-1 : ℂ) else 1) = 0
  simp [Fin.sum_univ_two]

lemma eps_eq (n : ℕ) : eps n = if n % 2 = 0 then -1 else 1 := by
  unfold eps Φe
  have h : ((n : ZMod 2) = 0) ↔ n % 2 = 0 := by rw [ZMod.natCast_eq_zero_iff]; omega
  by_cases hn : n % 2 = 0
  · rw [if_pos (h.mpr hn), if_pos hn]
  · rw [if_neg (fun h' => hn (h.mp h')), if_neg hn]

lemma Ap_eps (n : ℕ) : Ap eps n = ((n % 2 : ℕ) : ℂ) := by
  induction n with
  | zero => simp [Ap_zero]
  | succ n ih =>
    rw [Ap_succ, ih, eps_eq]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      rw [h, h']
      norm_num
    · have h' : (n + 1) % 2 = 0 := by omega
      rw [h, h']
      norm_num

lemma norm_Ap_eps_le (M : ℕ) : ‖Ap eps M‖ ≤ 1 := by
  rw [Ap_eps]
  rcases Nat.mod_two_eq_zero_or_one M with h | h <;> rw [h] <;> simp

lemma LFunction_eq_G_of_one_lt {s : ℂ} (hs : 1 < s.re) : ZMod.LFunction Φe s = G eps s := by
  rw [ZMod.LFunction_eq_LSeries Φe hs]
  have h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, eps n * (n : ℂ) ^ (-s)) atTop
      (𝓝 (LSeries (fun n => Φe n) s)) := by
    have hsum := (ZMod.LSeriesSummable_of_one_lt_re Φe hs).hasSum.tendsto_sum_nat
    have h2 := hsum.comp (tendsto_add_atTop_nat 1)
    refine h2.congr (fun M => ?_)
    simp only [Function.comp_apply]
    rw [← Formalism.FX.LFunctionPartialSum.sum_Icc_eq_sum_range _ (LSeries.term_zero _ _)]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : n ≠ 0 := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
    rfl
  exact tendsto_nhds_unique h1 (partial_tendsto_G eps norm_Ap_eps_le (by linarith))

lemma LFunction_eq_G {s : ℂ} (hs : 0 < s.re) : ZMod.LFunction Φe s = G eps s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (ZMod.LFunction Φe) {s : ℂ | 0 < s.re} :=
    (ZMod.differentiable_LFunction_of_sum_zero Φe_sum).differentiableOn.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (G eps) {s : ℂ | 0 < s.re} :=
    (G_differentiableOn eps norm_Ap_eps_le).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : ZMod.LFunction Φe =ᶠ[𝓝 (2 : ℂ)] G eps := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs
    exact LFunction_eq_G_of_one_lt hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 hev hs

lemma two_cpow_one_sub (s : ℂ) : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]

lemma Φe_eq (j : ZMod 2) :
    Φe j = (1 : DirichletCharacter ℂ 2) j - (if j = 0 then 1 else 0) := by
  by_cases hj : j = 0
  · subst hj
    rw [MulChar.map_nonunit _ not_isUnit_zero]
    simp [Φe]
  · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hj)]
    simp [Φe, hj]

lemma LFunction_Φe {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction Φe s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have h2 : ZMod.LFunction Φe s =
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2) s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [DirichletCharacter.LFunction, ZMod.LFunction, ZMod.LFunction]
    simp_rw [Φe_eq, sub_mul, Finset.sum_sub_distrib, mul_sub, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, HurwitzZeta.hurwitzZeta_zero]
    push_cast
    ring
  have h3 := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) hs
  rw [DirichletCharacter.LFunctionTrivChar, Nat.Prime.primeFactors Nat.prime_two,
    Finset.prod_singleton] at h3
  rw [h2, h3, two_cpow_one_sub]
  push_cast
  ring

lemma alt_sum (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2 * N), (n : ℂ) ^ (-s) - (2 : ℂ) ^ (1 - s) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 (2 * N), eps n * (n : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hA : ∀ g : ℕ → ℂ, (Finset.Icc 1 (2 * (N + 1))).sum g =
        (Finset.Icc 1 (2 * N)).sum g + g (2 * N + 1) + g (2 * N + 2) := by
      intro g
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
    have hB : ∀ g : ℕ → ℂ, (Finset.Icc 1 (N + 1)).sum g = (Finset.Icc 1 N).sum g + g (N + 1) :=
      fun g => Finset.sum_Icc_succ_top (by omega) _
    rw [hA (fun n => (n : ℂ) ^ (-s)), hA (fun n => eps n * (n : ℂ) ^ (-s)),
      hB (fun n => (n : ℂ) ^ (-s))]
    have e1 : eps (2 * N + 1) = 1 := by rw [eps_eq, if_neg (by omega)]
    have e2 : eps (2 * N + 2) = -1 := by rw [eps_eq, if_pos (by omega)]
    have hb : ((2 * N + 2 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
      have h := natCast_mul_natCast_cpow 2 (N + 1) (-s)
      rw [show ((2 * N + 2 : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) by push_cast; ring, h]
      norm_num
    rw [e1, e2, hb]
    rw [two_cpow_one_sub] at ih ⊢
    linear_combination ih

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet EtaPartialSums

theorem eta_partial_sums : EtaPartial := by
  intro s hs hs1 N hN
  have hG : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = EtaPartialSums.G eps s := by
    rw [← LFunction_Φe hs1, LFunction_eq_G hs]
  rw [hG, alt_sum]
  refine (norm_G_sub_partial_le eps norm_Ap_eps_le hs (2 * N)).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : (((2 * N : ℕ) : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) := by
    apply Real.rpow_le_rpow_of_nonpos hNpos _ (by linarith)
    push_cast
    linarith
  have hq : 0 ≤ 1 + ‖s‖ / s.re := by
    have := div_nonneg (norm_nonneg s) hs.le
    linarith
  have h4 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  calc 1 * (1 + ‖s‖ / s.re) * (((2 * N : ℕ) : ℝ) + 1) ^ (-s.re)
      ≤ 1 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ ≤ 4 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have := mul_nonneg hq h4
        nlinarith

theorem principal_zeta_bound : PrincipalZeta := by
  intro M _ s hs hz
  have hs1 : s ≠ 1 := by
    rcases hz.1 with h | h
    · exact absurd rfl h
    · exact h
  have h := hz.2
  rw [← DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1] at h
  rcases mul_eq_zero.mp h with h | h
  · exfalso
    rw [Finset.prod_eq_zero_iff] at h
    obtain ⟨p, hp, hp0⟩ := h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
    have : (p : ℂ) ^ (-s) = 1 := by linear_combination -hp0
    rw [this, norm_one] at hlt
    exact lt_irrefl _ hlt
  · exact h

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSpace
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma space_harm (x : ℕ) : ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ ≤ 1 + Real.log x := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; simp
  · have h := harmonic_le_one_add_log x
    have e : ((harmonic x : ℚ) : ℝ) = ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [← e]; exact h

lemma floor_eq_close {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ⌊a⌋₊ = ⌊b⌋₊) : |a - b| < 1 := by
  have h1 := Nat.floor_le ha
  have h2 := Nat.lt_floor_add_one a
  have h3 := Nat.floor_le hb
  have h4 := Nat.lt_floor_add_one b
  rw [h] at h1 h2
  rw [abs_lt]; constructor <;> linarith

lemma space_side (Q : Finset ℝ) (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (h1 : ∀ x ∈ Q, 1 ≤ f x)
    (h2 : ∀ x ∈ Q, f x ≤ 2 * T) (hsp : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → 1 ≤ |f x - f y|) :
    ∑ x ∈ Q, 1 / f x ≤ 1 + Real.log (2 * T + 1) := by
  have hinj : Set.InjOn (fun x => ⌊f x⌋₊) Q := by
    intro x hx y hy hxy
    by_contra hne
    have := floor_eq_close (by linarith [h1 x hx]) (by linarith [h1 y hy]) hxy
    have := hsp x hx y hy hne
    linarith
  have step1 : ∑ x ∈ Q, 1 / f x ≤ ∑ x ∈ Q, ((⌊f x⌋₊ : ℕ) : ℝ)⁻¹ := by
    refine sum_le_sum (fun x hx => ?_)
    have hf1 := h1 x hx
    have hfl : (1 : ℝ) ≤ (⌊f x⌋₊ : ℝ) := by
      have : 1 ≤ ⌊f x⌋₊ := Nat.le_floor (by exact_mod_cast hf1)
      exact_mod_cast this
    rw [one_div]
    exact inv_anti₀ (by linarith) (Nat.floor_le (by linarith))
  have step2 : ∑ x ∈ Q, ((⌊f x⌋₊ : ℕ) : ℝ)⁻¹ = ∑ k ∈ Q.image (fun x => ⌊f x⌋₊), ((k : ℕ) : ℝ)⁻¹ := by
    rw [sum_image hinj]
  have hsub : Q.image (fun x => ⌊f x⌋₊) ⊆ Icc 1 ⌊2 * T⌋₊ := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    rw [mem_Icc]
    exact ⟨Nat.le_floor (by exact_mod_cast h1 x hx), Nat.floor_le_floor (h2 x hx)⟩
  have step3 : ∑ k ∈ Q.image (fun x => ⌊f x⌋₊), ((k : ℕ) : ℝ)⁻¹ ≤ ∑ k ∈ Icc 1 ⌊2 * T⌋₊, ((k : ℕ) : ℝ)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have step4 : Real.log (⌊2 * T⌋₊ : ℝ) ≤ Real.log (2 * T + 1) := by
    rcases Nat.eq_zero_or_pos ⌊2 * T⌋₊ with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast h0) (by linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)])
  linarith [space_harm ⌊2 * T⌋₊]

theorem zero_spacing : Spacing := by
  intro P T hT hP hsp
  constructor
  · have hinj : Set.InjOn (fun x => ⌊x + T⌋₊) P := by
      intro x hx y hy hxy
      by_contra hne
      have hx' := abs_le.1 (hP x hx)
      have hy' := abs_le.1 (hP y hy)
      have := floor_eq_close (by linarith) (by linarith) hxy
      have := hsp x hx y hy hne
      rw [show x + T - (y + T) = x - y by ring] at *
      linarith
    have hsub : P.image (fun x => ⌊x + T⌋₊) ⊆ range (⌊2 * T⌋₊ + 1) := by
      intro k hk
      rw [mem_image] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      rw [mem_range, Nat.lt_succ_iff]
      exact Nat.floor_le_floor (by linarith [(abs_le.1 (hP x hx)).2])
    have h1 : P.card ≤ ⌊2 * T⌋₊ + 1 := by
      rw [← card_image_of_injOn hinj]
      exact (card_le_card hsub).trans (by simp)
    have h2 : ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T + 1 := by
      push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)]
    exact (by exact_mod_cast h1 : (P.card : ℝ) ≤ ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ)).trans h2
  · intro t ht
    have hsplit := sum_filter_add_sum_filter_not (P.erase t) (fun x => t < x) (fun x => 1 / |t - x|)
    rw [← hsplit]
    have hR : ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / |t - x| ≤ 1 + Real.log (2 * T + 1) := by
      have e : ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / |t - x| =
          ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / (x - t) := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [mem_filter] at hx
        rw [abs_sub_comm, abs_of_pos (by linarith [hx.2])]
      rw [e]
      refine space_side _ (fun x => x - t) T hT (fun x hx => ?_) (fun x hx => ?_) (fun x hx y hy hne => ?_)
      · rw [mem_filter, mem_erase] at hx
        have := hsp x hx.1.2 t ht hx.1.1
        rw [abs_of_pos (by linarith [hx.2])] at this
        exact this
      · rw [mem_filter, mem_erase] at hx
        have a := abs_le.1 (hP x hx.1.2)
        have b := abs_le.1 (hP t ht)
        show x - t ≤ 2 * T
        linarith
      · rw [mem_filter, mem_erase] at hx hy
        have := hsp x hx.1.2 y hy.1.2 hne
        rwa [show x - t - (y - t) = x - y by ring]
    have hL : ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / |t - x| ≤ 1 + Real.log (2 * T + 1) := by
      have e : ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / |t - x| =
          ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / (t - x) := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [mem_filter, mem_erase] at hx
        have hlt : x < t := lt_of_le_of_ne (not_lt.1 hx.2) hx.1.1
        rw [abs_of_pos (by linarith)]
      rw [e]
      refine space_side _ (fun x => t - x) T hT (fun x hx => ?_) (fun x hx => ?_) (fun x hx y hy hne => ?_)
      · rw [mem_filter, mem_erase] at hx
        have hlt : x < t := lt_of_le_of_ne (not_lt.1 hx.2) hx.1.1
        have := hsp x hx.1.2 t ht hx.1.1
        rw [abs_of_neg (by linarith)] at this
        show 1 ≤ t - x
        linarith
      · rw [mem_filter, mem_erase] at hx
        have a := abs_le.1 (hP x hx.1.2)
        have b := abs_le.1 (hP t ht)
        show t - x ≤ 2 * T
        linarith
      · rw [mem_filter, mem_erase] at hx hy
        have := hsp x hx.1.2 y hy.1.2 hne
        rwa [show t - x - (t - y) = -(x - y) by ring, abs_neg]
    linarith

theorem space_card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  have h : (Finset.univ : Finset (DirichletCharacter ℂ M)).card = M.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  rw [h]
  exact_mod_cast Nat.totient_le M

theorem trivial_bound : Triv := by
  intro M _ T S hT hS hsp
  classical
  have hfib : ∀ χ : DirichletCharacter ℂ M, ((S.filter (fun p => p.1 = χ)).card : ℝ) ≤ 2 * T + 1 := by
    intro χ
    set F := S.filter (fun p => p.1 = χ) with hF
    have hinj : Set.InjOn (fun p : DirichletCharacter ℂ M × ℂ => p.2.im) F := by
      intro p hp p' hp' h
      by_contra hne
      rw [hF, coe_filter] at hp hp'
      have := hsp p hp.1 p' hp'.1 hne (hp.2.trans hp'.2.symm)
      simp only at h
      rw [h, sub_self, abs_zero] at this
      linarith
    have hsp' := (zero_spacing (F.image (fun p => p.2.im)) T hT
      (fun x hx => by
        rw [mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact hS p (mem_of_mem_filter _ hp))
      (fun x hx y hy hne => by
        rw [mem_image] at hx hy
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨p', hp', rfl⟩ := hy
        have hpp : p ≠ p' := fun h => hne (by rw [h])
        rw [hF, mem_filter] at hp hp'
        exact hsp p hp.1 p' hp'.1 hpp (hp.2.trans hp'.2.symm))).1
    rwa [card_image_of_injOn hinj] at hsp'
  have hsum : (S.card : ℝ) = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)),
      ((S.filter (fun p => p.1 = χ)).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := fun p : DirichletCharacter ℂ M × ℂ => p.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast; rfl
  rw [hsum]
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)), ((S.filter (fun p => p.1 = χ)).card : ℝ)
      ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)), (2 * T + 1) := sum_le_sum (fun χ _ => hfib χ)
    _ = ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) * (2 * T + 1) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * (2 * T + 1) := mul_le_mul_of_nonneg_right (space_card_char_le M) (by linarith)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ZeroDetectionSecond
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

attribute [local irreducible] qd pYd pJd pNd in
theorem zero_detection_second : Detect1 := by
  intro M _ χ hχ1 T hT hM ρ hρ hρim hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, qd M T = X := ⟨_, rfl⟩
  have hMT : (M : ℝ) * T ≤ X := by rw [← hX]; unfold qd; exact Nat.le_ceil _
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX6 : (6 : ℝ) ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hre0 : 0 < ρ.re := by linarith
  have hNX : X ^ 8 ≤ pNd M T := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pNd pJd
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pYd M T = X ^ 3 := by unfold pYd; rw [hX]
  have hYN : pYd M T ≤ pNd M T := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pYd M T := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pNd M T := le_trans hY1 hYN
  have hB := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ1
  have hP := Formalism.FX.l_function_partial_sum M χ hχ1 _ hB ρ hre0 (pNd M T) hN1
  rw [hL, zero_sub, norm_neg] at hP
  have hMI := mollifier_identity M χ ρ (pYd M T) (pNd M T) (pYd M T * pNd M T) hY1 hYN le_rfl
  have hMo := mollM_norm_le χ ρ hre0.le (pYd M T)
  set P := ∑ n ∈ Icc 1 (pNd M T), χ (n : ZMod M) * (n : ℂ) ^ (-ρ) with hPdef
  set Mo := ∑ d ∈ Icc 1 (pYd M T), (((ArithmeticFunction.moebius d : ℤ)) : ℂ) * χ (d : ZMod M) * (d : ℂ) ^ (-ρ)
    with hMdef
  set D := ∑ n ∈ Ioc (pYd M T) (pYd M T * pNd M T), mco (pYd M T) (pNd M T) n * χ (n : ZMod M) * (n : ℂ) ^ (-ρ)
    with hD
  have hnum : ‖P‖ * (pYd M T : ℝ) ≤ 1 / 2 := by
    have hXpos : (0 : ℝ) < X := by linarith
    have hNpos : (0 : ℝ) < pNd M T := by exact_mod_cast hN1
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * T := by
      have h1 : ‖ρ‖ ≤ ρ.re + T := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + T / ρ.re := by
        rw [div_le_iff₀ hre0, add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : T / ρ.re ≤ 4 / 3 * T := by
        rw [div_le_iff₀ hre0]; nlinarith
      linarith
    have hpow : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pNd M T : ℝ) := by exact_mod_cast hNX
    have hpow2 : (X : ℝ) ^ (6 : ℕ) ≤ ((pNd M T : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (3 / 4 : ℝ) = (X : ℝ) ^ (6 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_natCast]
        norm_num
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pYd M T : ℝ) = (X : ℝ) ^ (3 : ℕ) := by rw [hY, Nat.cast_pow]
    have hc : 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 8 * X := by
      have hpos : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 2 * ((M : ℝ) + 1) * (3 * T) :=
            mul_le_mul_of_nonneg_left hrho (by positivity)
        _ ≤ 8 * X := by nlinarith
    have hPle : ‖P‖ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := by
      refine hP.trans ?_
      have a3 : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := hpow.trans hinv
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 8 * X * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P‖ * (X : ℝ) ^ (3 : ℕ) ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) * (X : ℝ) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 8 / X ^ 2 := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
  have h1D : ‖1 + D‖ ≤ 1 / 2 := by
    rw [← hMI, norm_mul]
    calc ‖P‖ * ‖Mo‖ ≤ ‖P‖ * (pYd M T : ℝ) := mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
      _ ≤ 1 / 2 := hnum
  have hDge : 1 / 2 ≤ ‖D‖ := by
    have := norm_sub_le (1 + D) D
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have hsplit : D = ∑ j ∈ range (pJd M T),
      blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ := by
    rw [hD, show pNd M T = 2 ^ pJd M T by unfold pNd; rfl, sum_blocks]
    rfl
  by_contra hcon
  push Not at hcon
  have hJ8 : 8 ≤ pJd M T := by unfold pJd; omega
  have hJpos : (0 : ℝ) < pJd M T := by exact_mod_cast (by omega : 0 < pJd M T)
  have hlt : ‖D‖ < 1 / 2 := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    have hne : (range (pJd M T)).Nonempty := nonempty_range_iff.mpr (by omega)
    calc ∑ j ∈ range (pJd M T), ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ‖
        < ∑ j ∈ range (pJd M T), 1 / (2 * (pJd M T : ℝ)) := sum_lt_sum_of_nonempty hne hcon
      _ = 1 / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

