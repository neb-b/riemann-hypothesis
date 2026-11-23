module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFiberMulCardRange
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardSumNormFibres

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountPowSuccInert
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.NormLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  first
  | exact RingOfIntegers.ext (star_star (x : K))
  | (apply RingOfIntegers.ext; simp [conjO])
  | (apply RingOfIntegers.ext; unfold conjO; simp)

theorem eq_conjO_of {θ t : 𝓞 K} (h : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ)) :
    t = conjO K θ := by
  apply RingOfIntegers.ext
  have h' : (t : K) = star (θ : K) := h
  rw [h']
  first
  | rfl
  | simp [conjO]
  | (unfold conjO; simp)

def conjQ (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) : (𝓞 K ⧸ J) →+* (𝓞 K ⧸ J) :=
  Ideal.quotientMap J (conjO K) (fun a ha => hJ a ha)

theorem conjQ_mk (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) (a : 𝓞 K) :
    conjQ J hJ (Ideal.Quotient.mk J a) = Ideal.Quotient.mk J (conjO K a) := by
  first
  | rfl
  | exact Ideal.quotientMap_mk
  | simp [conjQ]

theorem normRepCount_eq (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) (M : ℕ) (n : 𝓞 K) :
    normRepCount K J M n =
      Nat.card {x : Fin M → 𝓞 K ⧸ J // ∑ i, conjQ J hJ (x i) * x i = Ideal.Quotient.mk J n} := by
  unfold normRepCount
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  have key : ∀ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk J (y i) = x i) →
      Ideal.Quotient.mk J (∑ i, conjO K (y i) * y i) = ∑ i, conjQ J hJ (x i) * x i := by
    intro y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hy i, conjQ_mk]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [← key y hy, h]
  · intro h
    refine ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
      fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec, ?_⟩
    rw [key _ (fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec), h]

theorem exists_inv_mod {J : Ideal (𝓞 K)} {a : 𝓞 K} (h : IsCoprime (Ideal.span {a}) J) :
    ∃ b : 𝓞 K, Ideal.Quotient.mk J a * Ideal.Quotient.mk J b = 1 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  refine ⟨b, ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq, ← hij]
  have e : a * b - (b * a + j) = -j := by ring
  rw [e]
  exact J.neg_mem hj

theorem stable_pow {Q : Ideal (𝓞 K)} (hQ : Q.map (conjO K) = Q) (k : ℕ) :
    ∀ a ∈ Q ^ k, conjO K a ∈ Q ^ k := by
  intro a ha
  have h1 := Ideal.mem_map_of_mem (conjO K) ha
  rwa [Ideal.map_pow, hQ] at h1

theorem normRepCount_pow_succ_of {Q : Ideal (𝓞 K)} (hQ0 : Q ≠ ⊥) (hQ : Q.map (conjO K) = Q)
    (θ n : 𝓞 K) (hθ : IsCoprime (Ideal.span {θ - conjO K θ}) Q)
    (hnQ : IsCoprime (Ideal.span {n}) Q) (hn : conjO K n = n) (q : ℕ)
    (hq : Ideal.absNorm Q = q ^ 2) (M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k) :
    normRepCount K (Q ^ (k + 1)) M n = q ^ (2 * M - 1) * normRepCount K (Q ^ k) M n := by
  rw [normRepCount_eq _ (stable_pow hQ (k + 1)), normRepCount_eq _ (stable_pow hQ k)]
  have hle : Q ^ (k + 1) ≤ Q ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
  have : Finite (𝓞 K ⧸ Q ^ (k + 1)) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hQ0)
  obtain ⟨e, he⟩ := exists_inv_mod (hθ.pow_right (n := k + 1))
  obtain ⟨m, hm⟩ := exists_inv_mod (hnQ.pow_right (n := k + 1))
  have h := card_lift (σ := conjQ _ (stable_pow hQ (k + 1))) (τ := conjQ _ (stable_pow hQ k))
    (π := Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [conjQ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, conjQ_mk])
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [conjQ_mk, conjQ_mk, conjO_conjO])
    (by
      intro a b ha hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have h2 : a * b ∈ Q ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul ha hb
      exact Ideal.pow_le_pow_right (by omega) h2)
    (θ := Ideal.Quotient.mk _ θ) (e := Ideal.Quotient.mk _ e)
    (by rw [conjQ_mk, ← map_sub]; exact he)
    (n := Ideal.Quotient.mk _ n) (m := Ideal.Quotient.mk _ m) hm
    (by rw [conjQ_mk, hn]) q
    (by
      have h1 : ∀ J : Ideal (𝓞 K), Nat.card (𝓞 K ⧸ J) = Ideal.absNorm J := fun J => by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h1, h1, map_pow, map_pow, hq]; ring) M hM
  rw [Ideal.Quotient.factor_mk] at h
  exact h

theorem isCoprime_span_of_notMem {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {a : 𝓞 K} (ha : a ∉ P) :
    IsCoprime (Ideal.span {a}) P := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  have h2 := hP.eq_of_le h le_sup_right
  exact ha (by rw [h2]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))

end Formalism.HermitianLattices.Ext.L3.NormLifting

namespace Formalism.HermitianLattices.Ext.L3

open NormLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private lemma map_conjO_eq_conjIdeal (P : Ideal (𝓞 K)) :
    P.map (conjO K) = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal Ideal.map
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    show ((conjO K s : 𝓞 K) : K) = star ((s : 𝓞 K) : K)
    first
    | rfl
    | (symm; simp [conjO])
    | simp [conjO]
    | (unfold conjO; simp)
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (eq_conjO_of h).symm⟩

theorem normRepCount_pow_succ_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) (q : ℕ)
    (hq : Ideal.absNorm P = q ^ 2) :
    normRepCount K (P ^ (k + 1)) M n = q ^ (2 * M - 1) * normRepCount K (P ^ k) M n := by
  obtain ⟨θ, t, ht, hθP⟩ := hK.2.2 P hP
  rw [eq_conjO_of ht] at hθP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hmap : P.map (conjO K) = P := by rw [map_conjO_eq_conjIdeal]; exact hc
  exact normRepCount_pow_succ_of hP0 hmap θ n (isCoprime_span_of_notMem hP hθP)
    (isCoprime_span_of_notMem hP hnP) hn q hq M k hM hk

theorem normRepCount_pow_succ_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ (k + 1)) M n =
      Ideal.absNorm P ^ (2 * M - 1) *
        normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) M n := by
  obtain ⟨θ, t, ht, hθP⟩ := hK.2.2 P hP
  rw [eq_conjO_of ht] at hθP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  generalize hPbdef : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = Pb
  have hm : P.map (conjO K) = Pb := by rw [← hPbdef]; exact map_conjO_eq_conjIdeal P
  have hcc : (conjO K).comp (conjO K) = RingHom.id _ := RingHom.ext conjO_conjO
  have hmm : ∀ I : Ideal (𝓞 K), (I.map (conjO K)).map (conjO K) = I := fun I => by
    rw [Ideal.map_map, hcc, Ideal.map_id]
  have hPb0 : Pb ≠ ⊥ := by
    intro h
    apply hP0
    rw [← hmm P, hm, h, Ideal.map_bot]
  have hQ0 : P * Pb ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨hP0, hPb0⟩
  have hQ : (P * Pb).map (conjO K) = P * Pb := by
    rw [Ideal.map_mul, ← hm, hmm, mul_comm]
  have hcop : ∀ a, IsCoprime (Ideal.span {a}) P → IsCoprime (Ideal.span {conjO K a}) Pb := by
    intro a ha
    rw [Ideal.isCoprime_iff_sup_eq] at ha ⊢
    have h3 := congrArg (Ideal.map (conjO K)) ha
    rwa [Ideal.map_sup, Ideal.map_top, hm, Ideal.map_span, Set.image_singleton] at h3
  have h1 := isCoprime_span_of_notMem hP hθP
  have h4 := hcop _ h1
  rw [map_sub, conjO_conjO, ← Ideal.span_singleton_neg (conjO K θ - θ), neg_sub] at h4
  have hθ : IsCoprime (Ideal.span {θ - conjO K θ}) (P * Pb) := IsCoprime.mul_right h1 h4
  have h5 := isCoprime_span_of_notMem hP hnP
  have h6 := hcop _ h5
  rw [hn] at h6
  have hnQ : IsCoprime (Ideal.span {n}) (P * Pb) := IsCoprime.mul_right h5 h6
  have hnorm : Ideal.absNorm Pb = Ideal.absNorm P := by
    have hbij : Function.Bijective (conjO K) :=
      ⟨Function.LeftInverse.injective (g := conjO K) (fun x => conjO_conjO x),
        Function.RightInverse.surjective (g := conjO K) (fun x => conjO_conjO x)⟩
    let f : 𝓞 K ≃+* 𝓞 K := RingEquiv.ofBijective (conjO K) hbij
    have e := Ideal.quotientEquiv P Pb f (by rw [← hm]; rfl)
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr e.toEquiv).symm
  have hq : Ideal.absNorm (P * Pb) = Ideal.absNorm P ^ 2 := by rw [map_mul, hnorm, sq]
  have hQ' : (P * Pb).map (conjO K) = P * Pb := hQ
  exact normRepCount_pow_succ_of hQ0 hQ' θ n hθ hnQ hn (Ideal.absNorm P) hq M k hM hk

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountSplitOne
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace NormResidues

theorem coe_conjO (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO, coe_conjO, star_star]

theorem mem_conjIdeal (P : Ideal (𝓞 K)) (x : 𝓞 K) :
    x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ↔ conjO K x ∈ P := by
  rw [conjIdeal_eq_comap, Ideal.mem_comap]

theorem conjO_sum_norm {M : ℕ} (y : Fin M → 𝓞 K) :
    conjO K (∑ i, conjO K (y i) * y i) = ∑ i, conjO K (y i) * y i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, conjO_conjO, mul_comm]

theorem finite_quot {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : Finite (𝓞 K ⧸ P) := by
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hcard : Nat.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Nat.card (𝓞 K ⧸ P) ≠ 0 := by
    rw [hcard]
    exact fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
  exact Nat.finite_of_card_ne_zero h0

theorem natCard_quot (P : Ideal (𝓞 K)) : Nat.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

def sigHom (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) : (𝓞 K ⧸ P) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.lift P ((Ideal.Quotient.mk P).comp (conjO K)) (by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← mem_conjIdeal, hc]
    exact ha)

theorem sigHom_mk (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K) :
    sigHom P hc (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (conjO K x) := rfl

theorem sigHom_sigHom (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K ⧸ P) :
    sigHom P hc (sigHom P hc x) = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sigHom_mk, sigHom_mk, conjO_conjO]

def sigEquiv (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) : (𝓞 K ⧸ P) ≃+* (𝓞 K ⧸ P) :=
  RingEquiv.ofRingHom (sigHom P hc) (sigHom P hc)
    (RingHom.ext (sigHom_sigHom P hc)) (RingHom.ext (sigHom_sigHom P hc))

theorem sigEquiv_mk (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K) :
    sigEquiv P hc (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (conjO K x) := rfl

end NormResidues

open NormResidues

theorem normRepCount_inert_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M : ℕ) (hM : 1 ≤ M) (n : 𝓞 K) (hn : conjO K n = n)
    (hnP : n ∉ P) (q : ℕ) (hq : Ideal.absNorm P = q ^ 2) :
    (normRepCount K P M n : ℤ) = (q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M) := by
  have := hP
  have := finite_quot hP
  let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hq' : Fintype.card (𝓞 K ⧸ P) = q ^ 2 := by
    rw [Fintype.card_eq_nat_card, natCard_quot, hq]
  have hne : ∃ x, sigEquiv P hc x ≠ x := by
    obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    refine ⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩
    rw [sigEquiv_mk] at h
    exact Ideal.Quotient.eq.mp h.symm
  have hcσ : sigEquiv P hc (Ideal.Quotient.mk P n) = Ideal.Quotient.mk P n := by
    rw [sigEquiv_mk, hn]
  have hc0 : Ideal.Quotient.mk P n ≠ 0 := fun h => hnP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have key : ∀ x : Fin M → 𝓞 K ⧸ P,
      (∃ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk P (y i) = x i) ∧
        Ideal.Quotient.mk P (∑ i, conjO K (y i) * y i) = Ideal.Quotient.mk P n) ↔
      ∑ i, sigEquiv P hc (x i) * x i = Ideal.Quotient.mk P n := by
    intro x
    constructor
    · rintro ⟨y, hy, h⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hy i, sigEquiv_mk]
    · intro h
      choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
      refine ⟨y, hy, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hy i, sigEquiv_mk]
  unfold normRepCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact card_herm_norm_eq (sigEquiv P hc) (fun x => sigHom_sigHom P hc x) hne q hq' M hM _ hcσ hc0

namespace NormResidues

theorem sup_conjIdeal_eq_top {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) : P ⊔ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = ⊤ := by
  have := hP
  have hQ : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).IsMaximal := by
    rw [conjIdeal_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _ fun x => ⟨conjO K x, conjO_conjO x⟩
  exact Ideal.IsMaximal.coprime_of_ne hP hQ (Ne.symm hc)

theorem mem_mul_conjIdeal {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (x : 𝓞 K) :
    x ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ↔ x ∈ P ∧ conjO K x ∈ P := by
  rw [Ideal.mul_eq_inf_of_coprime (sup_conjIdeal_eq_top hP hc), Ideal.mem_inf, mem_conjIdeal]

def pairHom (P : Ideal (𝓞 K)) : 𝓞 K →+* (𝓞 K ⧸ P) × (𝓞 K ⧸ P) :=
  ((Ideal.Quotient.mk P).comp (conjO K)).prod (Ideal.Quotient.mk P)

theorem pairHom_apply (P : Ideal (𝓞 K)) (x : 𝓞 K) :
    pairHom P x = (Ideal.Quotient.mk P (conjO K x), Ideal.Quotient.mk P x) := rfl

theorem pairHom_eq_zero_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (x : 𝓞 K) :
    pairHom P x = 0 ↔ x ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  rw [pairHom_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
    mem_mul_conjIdeal hP hc, and_comm]

theorem pairHom_surjective {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) : Function.Surjective (pairHom P) := by
  rintro ⟨a, b⟩
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : (1 : 𝓞 K) ∈ P ⊔ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [sup_conjIdeal_eq_top hP hc]
    exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have hf' : conjO K f ∈ P := (mem_conjIdeal P f).mp hf
  refine ⟨b' * f + conjO K a' * e, ?_⟩
  rw [pairHom_apply, Prod.mk.injEq]
  constructor
  · rw [Ideal.Quotient.eq]
    have hconj : conjO K e + conjO K f = 1 := by rw [← map_add (f := _), hef, map_one]
    have h2 : conjO K (b' * f + conjO K a' * e) - a' = conjO K b' * conjO K f - a' * conjO K f := by
      rw [map_add (f := _), map_mul, map_mul, conjO_conjO]
      linear_combination a' * hconj
    rw [h2]
    exact P.sub_mem (P.mul_mem_left _ hf') (P.mul_mem_left _ hf')
  · rw [Ideal.Quotient.eq]
    have h3 : b' * f + conjO K a' * e - b' = conjO K a' * e - b' * e := by
      linear_combination b' * hef
    rw [h3]
    exact P.sub_mem (P.mul_mem_left _ he) (P.mul_mem_left _ he)

def pairLift {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    (𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) →+* (𝓞 K ⧸ P) × (𝓞 K ⧸ P) :=
  Ideal.Quotient.lift _ (pairHom P) fun a ha => (pairHom_eq_zero_iff hP hc a).2 ha

theorem pairLift_mk {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (x : 𝓞 K) : pairLift hP hc (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk P (conjO K x), Ideal.Quotient.mk P x) := rfl

theorem pairLift_bijective {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) : Function.Bijective (pairLift hP hc) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [pairLift_mk] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((pairHom_eq_zero_iff hP hc x).mp hz)
  · obtain ⟨x, hx⟩ := pairHom_surjective hP hc y
    exact ⟨Ideal.Quotient.mk _ x, hx⟩

def vecEquiv {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M : ℕ) :
    (Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≃ (Fin M → 𝓞 K ⧸ P) × (Fin M → 𝓞 K ⧸ P) :=
  (Equiv.piCongrRight fun _ => Equiv.ofBijective _ (pairLift_bijective hP hc)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

theorem vecEquiv_fst {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (i : Fin M) :
    (vecEquiv hP hc M x).1 i = (pairLift hP hc (x i)).1 := rfl

theorem vecEquiv_snd {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (i : Fin M) :
    (vecEquiv hP hc M x).2 i = (pairLift hP hc (x i)).2 := rfl

theorem norm_cond_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (n : 𝓞 K) (hn : conjO K n = n) (y : Fin M → 𝓞 K) :
    Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (∑ i, conjO K (y i) * y i) =
        Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) n ↔
      ∑ i, Ideal.Quotient.mk P (conjO K (y i)) * Ideal.Quotient.mk P (y i) =
        Ideal.Quotient.mk P n := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Ideal.Quotient.eq, mem_mul_conjIdeal hP hc, map_sub, conjO_sum_norm, hn, and_self,
    ← Ideal.Quotient.eq, map_sum]
  simp only [map_mul]

end NormResidues

theorem normRepCount_split_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M : ℕ) (hM : 1 ≤ M) (n : 𝓞 K) (hn : conjO K n = n)
    (hnP : n ∉ P) :
    (normRepCount K (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) M n : ℤ) =
      (Ideal.absNorm P : ℤ) ^ (2 * M - 1) - (Ideal.absNorm P : ℤ) ^ (M - 1) := by
  have := hP
  have := finite_quot hP
  let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Fintype.card_eq_nat_card, natCard_quot]
  have hc0 : Ideal.Quotient.mk P n ≠ 0 := fun h => hnP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have key : ∀ x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P,
      (∃ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk _ (y i) = x i) ∧
        Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (∑ i, conjO K (y i) * y i) =
          Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) n) ↔
      ∑ i, (vecEquiv hP hc M x).1 i * (vecEquiv hP hc M x).2 i = Ideal.Quotient.mk P n := by
    intro x
    constructor
    · rintro ⟨y, hy, h⟩
      rw [norm_cond_iff hP hc M n hn y] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [vecEquiv_fst, vecEquiv_snd, ← hy i, pairLift_mk]
    · intro h
      choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
      refine ⟨y, hy, ?_⟩
      rw [norm_cond_iff hP hc M n hn y, ← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [vecEquiv_fst, vecEquiv_snd, ← hy i, pairLift_mk]
  unfold normRepCount
  rw [Nat.card_congr ((Equiv.subtypeEquivRight key).trans
    (Equiv.subtypeEquiv (q := fun z : (Fin M → 𝓞 K ⧸ P) × (Fin M → 𝓞 K ⧸ P) =>
      ∑ i, z.1 i * z.2 i = Ideal.Quotient.mk P n) (vecEquiv hP hc M) fun x => Iff.rfl))]
  exact card_dot_eq (Ideal.absNorm P) hq M hM _ hc0

end Formalism.HermitianLattices.Ext.L3
end
end

