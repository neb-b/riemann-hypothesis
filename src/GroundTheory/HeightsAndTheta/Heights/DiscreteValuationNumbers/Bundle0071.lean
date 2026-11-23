module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0058

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocFamilyFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P W Q : Ideal A} (hP : P.IsPrime) (hQ : Q.IsPrime) {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P ≤ Q) (hQW : Q ≤ W) : Q = P ∨ Q = W := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hQP, hQW'⟩ := h
  have hWp : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ Q := by rw [Ideal.mk_ker]; exact hPQ
  have hkerW : RingHom.ker f ≤ W := hker.trans hQW
  have : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hkerW
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map f := by
    refine bot_lt_iff_ne_bot.mpr fun h0 => hQP (le_antisymm (fun q hq => ?_) hPQ)
    have hq' : f q ∈ Q.map f := Ideal.mem_map_of_mem f hq
    rw [h0, Ideal.mem_bot] at hq'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq'
  have h2 : Q.map f < W.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun e => hQW' ?_
    have e' := congrArg (Ideal.comap f) e
    rwa [Ideal.comap_map_of_surjective' f hf, Ideal.comap_map_of_surjective' f hf,
      sup_eq_left.mpr hker, sup_eq_left.mpr hkerW] at e'
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have e3 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  rw [Ideal.height_bot] at e1
  have e4 : (0 : ℕ∞) + 1 + 1 ≤ 1 := ((add_le_add e1 le_rfl).trans e2).trans e3
  norm_num at e4

theorem eq_blowUpOf_of_comap_liftForm_le {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {u : J → MRing ι R} {Q : Ideal (MRing (extIdx ι J) R)}
    (hQp : Q.IsPrime) (hQh : IsMultiHomogIdeal Q) (hle : blowUpOf P u ≤ Q) {j : J}
    (hj : (newVar j : MRing (extIdx ι J) R) ∉ Q)
    (hc : Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ P) : Q = blowUpOf P u := by
  classical
  refine le_antisymm (fun F hF => ?_) hle
  have hcomp : ∀ b, weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F ∈ blowUpOf P u := by
    intro b
    set G := weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F
    have hG : IsMultiHomog G b := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hGQ : G ∈ Q := hQh F hF b
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (blowUpEval P u G)
    have hrel : liftForm (u j) ^ (b none) * G - newVar j ^ (b none) * liftForm f ∈ blowUpOf P u := by
      rw [blowUpOf, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow,
        aeval_blowUpSubst_of_isMultiHomog P u hG, aeval_blowUpSubst_liftForm, aeval_blowUpSubst_liftForm,
        aeval_blowUpSubst_newVar, ← hf]
      ring
    have h1 : newVar j ^ (b none) * liftForm f ∈ Q := by
      have h := Q.sub_mem (Q.mul_mem_left (liftForm (u j) ^ (b none)) hGQ) (hle hrel)
      rwa [sub_sub_cancel] at h
    have h2 : liftForm f ∈ Q :=
      (hQp.mem_or_mem h1).resolve_left fun h => hj (hQp.mem_of_pow_mem _ h)
    have h3 : f ∈ P := hc h2
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_of_isMultiHomog P u hG, ← hf,
      Ideal.Quotient.eq_zero_iff_mem.mpr h3, map_zero, zero_mul]
  rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) F]
  exact finsum_induction (· ∈ blowUpOf P u) (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) hcomp

theorem BlowUpOverLocFamilyFinite.proof (h₁ : BlowUpOverLocFibreFinite.Statement.{u}) :
    BlowUpOverLocFamilyFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have hPp : P.IsPrime := hP.multiProj.isPrime
  refine ((Set.finite_singleton (blowUpOf P u)).union
    (h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel)).subset ?_
  rintro Q ⟨hQp, hQh, hQr, hQle, hQW⟩
  obtain ⟨hcp, hPc, -, j, hj⟩ := comap_liftForm_facts hQp hQle hQr
  rcases prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span hPp hcp hWmin hPc hQW with h | h
  · exact Or.inl (eq_blowUpOf_of_comap_liftForm_le hQp hQh hQle hj h.le)
  · exact Or.inr ⟨hQp, hQh, hQr, hQle, h⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocLocalization.proof (hfam : BlowUpOverLocFamilyFinite.Statement.{u}) :
    BlowUpOverLocLocalization.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW'p hmh hW'rel hbl hW'W
  have hW'fam : W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := ⟨hW'p, hmh, hW'rel, hbl, hW'W⟩
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' := iInf₂_le W' hW'fam
  obtain ⟨e, L, hL, he, hLQ⟩ := MultiHomogPrimeAvoid.proof O (Option K) (extIdx ι J) _
    (hfam O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel) (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩)
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof O K ι J P u W' hbl
  obtain ⟨hlocT, -⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing

  have hne : ∀ (d : Option K → ℕ) (H : MRing (extIdx ι J) O), IsMultiHomog H d → H ∉ W' →
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) ≠ 0 := by
    intro d H hH hHW h0
    have h1 := hφ d H H hH hH hHW
    rw [h0, div_zero] at h1
    have h2 : (⟨_, Subring.subset_closure ⟨d, H, H, hH, hH, hHW, rfl⟩⟩ :
        homLocRing (blowUpOf P u) W') = 1 := by
      apply Subtype.ext
      show _ / _ = (1 : FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
      apply div_self
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => hHW (hbl h)
    rw [h2, map_one] at h1
    exact one_ne_zero h1

  have hgen : ∀ (b : Option K → ℕ) (F G : MRing (extIdx ι J) O), IsMultiHomog F b → IsMultiHomog G b →
      G ∉ W' → ∃ bb ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
        (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) * s = bb := by
    intro b F G hF hG hGW
    set k := ∑ o, b o with hk
    obtain ⟨M, hM, hMW⟩ := homLocRing_form_not_mem hW'p hW'rel (fun o => k * e o - b o)
    have hdeg : b + (fun o => k * e o - b o) = k • e := by
      funext o
      have : b o ≤ k * e o := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ o)) (Nat.le_mul_of_pos_right _ (he o))
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      omega
    have hFM : IsMultiHomog (F * M) (k • e) := hdeg ▸ hF.mul hM
    have hGM : IsMultiHomog (G * M) (k • e) := hdeg ▸ hG.mul hM
    have hLk : IsMultiHomog (L ^ k) (k • e) := hL.pow k
    have hLkQ : ∀ Q : Ideal (MRing (extIdx ι J) O), Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W → L ^ k ∉ Q :=
      fun Q hQ h => hLQ Q hQ (hQ.1.mem_of_pow_mem k h)
    have hmemB : ∀ H, IsMultiHomog H (k • e) →
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (L ^ k)) ∈
          blowUpOverLoc P W u := fun H hH =>
      Subring.mem_iInf.mpr fun Q => Subring.mem_iInf.mpr fun hQ =>
        Subring.subset_closure ⟨k • e, H, L ^ k, hH, hLk, hLkQ Q hQ, rfl⟩
    have hGMW : G * M ∉ W' := fun h => (hW'p.mem_or_mem h).elim hGW hMW
    have hLkW : L ^ k ∉ W' := hLkQ W' hW'fam
    have hG0 := hne _ _ hG hGW
    have hGM0 := hne _ _ hGM hGMW
    have hLk0 := hne _ _ hLk hLkW
    refine ⟨_, hmemB _ hFM, _, hmemB _ hGM, ⟨_,
      Subring.subset_closure ⟨k • e, L ^ k, G * M, hLk, hGM, hGMW, rfl⟩, ?_⟩, ?_⟩
    · rw [div_mul_div_comm, mul_comm]
      exact div_self (mul_ne_zero hLk0 hGM0)
    · rw [map_mul, map_mul] at hGM0 ⊢
      rw [map_mul, map_mul]
      field_simp

  have hfrac : ∀ z ∈ blowUpLocRing P u W', ∃ b ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
      (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧ z * s = b := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨b, F, G, hF, hG, hGW, rfl⟩ := hz
      exact hgen b F G hF hG hGW
    | zero => exact ⟨0, zero_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, zero_mul 1⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, one_mul 1⟩
    | add x y _ _ h₁ h₂ =>
      obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
      obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
      refine ⟨b₁ * s₂ + b₂ * s₁, add_mem (mul_mem hb₁ hs₂) (mul_mem hb₂ hs₁), s₁ * s₂, mul_mem hs₁ hs₂,
        ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
      rw [← hx₁, ← hx₂]
      ring
    | neg x _ h =>
      obtain ⟨b₁, hb₁, s₁, hs₁, ht, hx₁⟩ := h
      exact ⟨-b₁, neg_mem hb₁, s₁, hs₁, ht, by rw [← hx₁]; ring⟩
    | mul x y _ _ h₁ h₂ =>
      obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
      obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
      refine ⟨b₁ * b₂, mul_mem hb₁ hb₂, s₁ * s₂, mul_mem hs₁ hs₂,
        ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
      rw [← hx₁, ← hx₂]
      ring

  let 𝔭 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)
  have h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  refine ⟨hBR, 𝔭, h𝔭, ?_⟩
  letI := (Subring.inclusion hBR).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  · rintro ⟨z, hz⟩
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ := hfrac z hz
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    intro hm
    have hm' := (IsLocalRing.mem_maximalIdeal _).mp hm
    exact hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))
  · intro a a' h
    exact ⟨1, by rw [Subring.inclusion_injective hBR h]⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

