module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionKerRangeMul
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pTor_eq_card_inf_ker (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pTor p U = Nat.card (U ⊓ (powMonoidHom p : G →* G).ker : Subgroup G) := by
  unfold pTor
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, powMonoidHom_apply])

theorem pIdx_pTor_ker_range :
    ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p g.ker ≠ 0 → pTor p g.ker ≠ 0 → pIdx p g.range ≠ 0 → pTor p g.range ≠ 0 → pIdx p (⊤ : Subgroup A) ≠ 0 ∧ pTor p (⊤ : Subgroup A) ≠ 0 ∧ pIdx p (⊤ : Subgroup A) * pTor p g.ker * pTor p g.range = pIdx p g.ker * pIdx p g.range * pTor p (⊤ : Subgroup A) := by
  intro p A A' _ _ g hIK hTK hIR hTR
  have hcomm : (powMonoidHom p : A' →* A').comp g = g.comp (powMonoidHom p : A →* A) := by
    ext a; simp [map_pow]
  have hRp : pows p g.range = (powMonoidHom p : A →* A).range.map g := by
    simp only [pows, MonoidHom.range_eq_map, Subgroup.map_map, hcomm]
  have hKpow : g.ker.map (powMonoidHom p : A →* A) ≤ g.ker := by
    rintro _ ⟨k, hk, rfl⟩
    exact g.ker.pow_mem hk p

  have eA : pIdx p (⊤ : Subgroup A) =
      (powMonoidHom p : A →* A).range.relIndex g.ker * pIdx p g.range := by
    have h1 : pIdx p (⊤ : Subgroup A) = (powMonoidHom p : A →* A).range.index := by
      rw [pIdx, Subgroup.relIndex_top_right, pows, ← MonoidHom.range_eq_map]
    rw [h1, ← Subgroup.relIndex_mul_index
      (le_sup_left : (powMonoidHom p : A →* A).range ≤ (powMonoidHom p : A →* A).range ⊔ g.ker),
      Subgroup.relIndex_sup_left, ← Subgroup.comap_map_eq, Subgroup.index_comap, pIdx, hRp]

  have eK : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex
      ((powMonoidHom p : A →* A).range ⊓ g.ker) * (powMonoidHom p : A →* A).range.relIndex g.ker := by
    have h0 : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex g.ker := rfl
    rw [h0, ← Subgroup.relIndex_mul_relIndex _ ((powMonoidHom p : A →* A).range ⊓ g.ker) _
      (le_inf (Subgroup.map_le_range _ _) hKpow) inf_le_right, Subgroup.inf_relIndex_right]

  have hB : g.ker.comap (powMonoidHom p : A →* A) = (powMonoidHom p : A' →* A').ker.comap g := by
    ext a; simp [MonoidHom.mem_ker, map_pow]
  have hKB : g.ker ≤ g.ker.comap (powMonoidHom p : A →* A) := fun x hx => g.ker.pow_mem hx p
  have hQB : (powMonoidHom p : A →* A).ker ≤ g.ker.comap (powMonoidHom p : A →* A) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simp [Subgroup.mem_comap, hx]

  have eR : pTor p g.range = g.ker.relIndex (powMonoidHom p : A →* A).ker *
      (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
    have h1 : pTor p g.range = g.ker.relIndex (g.ker.comap (powMonoidHom p : A →* A)) := by
      rw [pTor_eq_card_inf_ker, Subgroup.relIndex_ker, hB, Subgroup.map_comap_eq]
    have h2 : (g.ker ⊔ (powMonoidHom p : A →* A).ker).relIndex
        (g.ker.comap (powMonoidHom p : A →* A)) =
        (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
      rw [← Subgroup.comap_map_eq, Subgroup.relIndex_comap, Subgroup.map_comap_eq]
    rw [h1, ← Subgroup.relIndex_mul_relIndex g.ker (g.ker ⊔ (powMonoidHom p : A →* A).ker) _
      le_sup_left (sup_le hKB hQB), h2,
      Subgroup.relIndex_sup_left]

  have eT : pTor p (⊤ : Subgroup A) = pTor p g.ker * g.ker.relIndex (powMonoidHom p : A →* A).ker := by
    have h := Subgroup.relIndex_mul_relIndex ⊥ (g.ker ⊓ (powMonoidHom p : A →* A).ker)
      (powMonoidHom p : A →* A).ker bot_le inf_le_right
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] at h
    rw [pTor_eq_card_inf_ker, pTor_eq_card_inf_ker, top_inf_eq, ← h]
  rw [eK] at hIK ⊢
  rw [eR] at hTR ⊢
  rw [eA, eT]
  refine ⟨mul_ne_zero (right_ne_zero_of_mul hIK) hIR, mul_ne_zero hTK (left_ne_zero_of_mul hTR), ?_⟩
  ring

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowPrimeRangeEqIteratedDifference
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private lemma pow_apply_ofMul_eq_iterate {M : Type} [CommGroup M] (ψ : AddMonoid.End (Additive M))
    (φ : M →* M) (hψ : ∀ a, ψ (Additive.ofMul a) = Additive.ofMul (φ a)) (n : ℕ) (a : M) :
    (ψ ^ n) (Additive.ofMul a) = Additive.ofMul ((⇑φ)^[n] a) := by
  rw [AddMonoid.End.coe_pow]
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hψ]

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private lemma cyclotomic_comp_X_add_one_eq (p : ℕ) [Fact p.Prime] :
    ∃ H : ℤ[X], (cyclotomic p ℤ).comp (X + 1) = X ^ (p - 1) + (p : ℤ[X]) * (1 + X * H) := by
  have hp : p.Prime := Fact.out
  have hE := cyclotomic_comp_X_add_one_isEisensteinAt p
  have hm : ((cyclotomic p ℤ).comp (X + 1)).Monic := (cyclotomic.monic p ℤ).comp_X_add_C 1
  have hd : ((cyclotomic p ℤ).comp (X + 1)).natDegree = p - 1 := by
    rw [natDegree_comp, natDegree_cyclotomic, Nat.totient_prime hp, ← C_1, natDegree_X_add_C, mul_one]
  obtain ⟨G, hG⟩ : C (p : ℤ) ∣ (cyclotomic p ℤ).comp (X + 1) - X ^ (p - 1) := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_X_pow]
    rcases lt_trichotomy i (p - 1) with h | h | h
    · rw [if_neg h.ne, sub_zero]
      exact Ideal.mem_span_singleton.1 (hE.mem (by rwa [hd]))
    · rw [if_pos h, h, ← hd, hm.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, coeff_eq_zero_of_natDegree_lt (by rwa [hd])]
      exact dvd_zero _
  have h0 : G.coeff 0 = 1 := by
    have h : ((cyclotomic p ℤ).comp (X + 1) - X ^ (p - 1)).coeff 0 = (C (p : ℤ) * G).coeff 0 := by
      rw [hG]
    have hp1 : (0 : ℕ) ≠ p - 1 := (Nat.sub_pos_of_lt hp.one_lt).ne
    rw [coeff_sub, coeff_X_pow, if_neg hp1, sub_zero, coeff_C_mul, coeff_zero_eq_eval_zero,
      eval_comp] at h
    simp only [eval_add, eval_X, eval_one, zero_add, eval_one_cyclotomic_prime] at h
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (mul_right_eq_self₀.1 h.symm).resolve_right hpz
  obtain ⟨H, hH⟩ : X ∣ G - 1 := by
    rw [X_dvd_iff, coeff_sub]
    simp [h0]
  refine ⟨H, ?_⟩
  rw [← hH, ← C_eq_natCast]
  linear_combination hG

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private lemma exists_pow_factor_of_aeval_cyclotomic {S : Type*} [Ring S] (p : ℕ) [Fact p.Prime]
    (y : S) (hy : aeval y ((cyclotomic p ℤ).comp (X + 1)) = 0) :
    ∃ W V : S, y ^ (p - 1) = (p : S) * W ∧ y ^ (p - 1) = W * p ∧
      (p : S) = y ^ (p - 1) * V ∧ (p : S) = V * y ^ (p - 1) := by
  obtain ⟨H, hf⟩ := cyclotomic_comp_X_add_one_eq p
  have hg := mul_neg_geom_sum (-(X * H)) (p - 1)
  have h2 : (-(X * H)) ^ (p - 1) = X ^ (p - 1) * (-H) ^ (p - 1) := by rw [← mul_pow, mul_neg]
  have e1 : X ^ (p - 1) = (p : ℤ[X]) * (-(1 + X * H)) + (cyclotomic p ℤ).comp (X + 1) := by
    linear_combination -hf
  have e2 : X ^ (p - 1) = (-(1 + X * H)) * (p : ℤ[X]) + (cyclotomic p ℤ).comp (X + 1) := by
    linear_combination -hf
  have e3 : (p : ℤ[X]) = X ^ (p - 1) * ((p : ℤ[X]) * (-H) ^ (p - 1) -
      ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i) +
      (cyclotomic p ℤ).comp (X + 1) * ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i := by
    linear_combination (-(∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i)) * hf +
      (-(p : ℤ[X])) * hg + (p : ℤ[X]) * h2
  have e4 : (p : ℤ[X]) = ((p : ℤ[X]) * (-H) ^ (p - 1) -
      ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i) * X ^ (p - 1) +
      (∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i) * (cyclotomic p ℤ).comp (X + 1) := by
    linear_combination e3
  refine ⟨aeval (R := ℤ) y (-(1 + X * H) : ℤ[X]),
    aeval (R := ℤ) y ((p : ℤ[X]) * (-H) ^ (p - 1) - ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i),
    ?_, ?_, ?_, ?_⟩
  · have h := congrArg (aeval y) e1
    rwa [map_add, map_mul, map_natCast, hy, add_zero, map_pow, aeval_X] at h
  · have h := congrArg (aeval y) e2
    rwa [map_add, map_mul, map_natCast, hy, add_zero, map_pow, aeval_X] at h
  · have h := congrArg (aeval y) e3
    rwa [map_add, map_mul, map_mul, map_natCast, hy, zero_mul, add_zero, map_pow, aeval_X] at h
  · have h := congrArg (aeval y) e4
    rwa [map_add, map_mul, map_mul, map_natCast, hy, mul_zero, add_zero, map_pow, aeval_X] at h


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.pows_eq_range_dif_pow : ∀ (p : ℕ) (M : Type) [CommGroup M] (τ : M →* M)
    (lam : Monoid.End M), p.Prime → (∀ a, lam a = τ a / a) →
    (∀ a, _root_.GlobalTheory.CNorm.nrm τ p a = 1) →
    _root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup M) = MonoidHom.range (lam ^ (p - 1) : Monoid.End M) ∧
      ∀ a : M, a ^ p = 1 ↔ (lam ^ (p - 1) : Monoid.End M) a = 1 := by
  intro p M _ τ lam hp hlam hN
  haveI : Fact p.Prime := ⟨hp⟩
  let T : AddMonoid.End (Additive M) := MonoidHom.toAdditive τ
  let Y : AddMonoid.End (Additive M) := MonoidHom.toAdditive (lam : M →* M)
  have hYT : Y + 1 = T := by
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨a, rfl⟩ : ∃ a, Additive.ofMul a = x := ⟨_, ofMul_toMul x⟩
    show Additive.ofMul (lam a) + Additive.ofMul a = Additive.ofMul (τ a)
    rw [hlam, ← ofMul_mul, div_mul_cancel]
  have hT : aeval T (cyclotomic p ℤ) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cyclotomic_prime, map_sum]
    simp only [map_pow, aeval_X]
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨a, rfl⟩ : ∃ a, Additive.ofMul a = x := ⟨_, ofMul_toMul x⟩
    have hs := map_sum (AddMonoidHom.mk' (fun g : AddMonoid.End (Additive M) =>
      g (Additive.ofMul a)) (fun _ _ => rfl)) (fun i => T ^ i) (Finset.range p)
    change (∑ i ∈ Finset.range p, T ^ i) (Additive.ofMul a) =
      ∑ i ∈ Finset.range p, (T ^ i) (Additive.ofMul a) at hs
    rw [hs, Finset.sum_congr rfl fun i _ => pow_apply_ofMul_eq_iterate T τ (fun _ => rfl) i a]
    rw [← ofMul_prod, ← _root_.GlobalTheory.CNorm.nrm_apply, hN, ofMul_one]
    rfl
  have hy : aeval Y ((cyclotomic p ℤ).comp (X + 1)) = 0 := by
    rw [aeval_comp, map_add (f := _), aeval_X, map_one, hYT, hT]
  obtain ⟨W, V, h1, h2, h3, h4⟩ := exists_pow_factor_of_aeval_cyclotomic p Y hy
  have hL : ∀ a, Additive.ofMul ((lam ^ (p - 1) : Monoid.End M) a) =
      (Y ^ (p - 1)) (Additive.ofMul a) := fun a => by
    rw [Monoid.End.coe_pow]
    exact (pow_apply_ofMul_eq_iterate Y lam (fun _ => rfl) _ _).symm
  have hP : ∀ a : M, ((p : AddMonoid.End (Additive M))) (Additive.ofMul a) =
      Additive.ofMul (a ^ p) := fun a => by
    rw [AddMonoid.End.natCast_apply, ofMul_pow]
  have K1 : ∀ a, (lam ^ (p - 1) : Monoid.End M) a = (Additive.toMul (W (Additive.ofMul a))) ^ p :=
    fun a => by
      apply Additive.ofMul.injective
      rw [hL, h1, ofMul_pow, ofMul_toMul, ← AddMonoid.End.natCast_apply]
      rfl
  have K2 : ∀ a, (lam ^ (p - 1) : Monoid.End M) a = Additive.toMul (W (Additive.ofMul (a ^ p))) :=
    fun a => by
      apply Additive.ofMul.injective
      rw [hL, h2, ofMul_toMul, ← hP]
      rfl
  have K3 : ∀ a : M, a ^ p = (lam ^ (p - 1) : Monoid.End M) (Additive.toMul (V (Additive.ofMul a))) :=
    fun a => by
      apply Additive.ofMul.injective
      rw [hL, ofMul_toMul, ← hP, h3]
      rfl
  have K4 : ∀ a : M, a ^ p =
      Additive.toMul (V (Additive.ofMul ((lam ^ (p - 1) : Monoid.End M) a))) := fun a => by
    apply Additive.ofMul.injective
    rw [hL, ofMul_toMul, ← hP, h4]
    rfl
  refine ⟨?_, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · ext x
    simp only [_root_.GlobalTheory.CNorm.pows, Subgroup.mem_map, Subgroup.mem_top, true_and,
      powMonoidHom_apply, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (K3 y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨_, (K1 y).symm⟩
  · rw [K2, ha, ofMul_one, map_zero, toMul_zero]
  · rw [K4, ha, ofMul_one, map_zero, toMul_zero]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeIdempotentEqIndicatorPrime
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.isPrimeIdem_eq_indicator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  intro F E _ _ _ _ _ σ Φ hΦ hint hplace P e f hprime
  unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem at hprime
  rcases hprime with ⟨hat, -⟩ | ⟨-, ⟨v, ε, hε, rfl⟩, hcrit⟩
  · unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsIdemAt _root_.HeckeCharacterZeroLocus.ThmBIn.IsSplitIdem at hat
    obtain ⟨⟨he, hce, v, ε, hε, hsum⟩, hcrit⟩ := hat
    have heε : e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e := by
      rw [← hsum, mul_add, he, hce, add_zero]
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace e P v ε hε he heε).mp hcrit
  · obtain ⟨h0, hind⟩ := hplace v ε hε
    have he : algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε =
        algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε := by
      apply Φ.injective
      rw [map_mul]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_mul, h0, mul_zero]
      · ext Q : 1
        change (Φ _).2 Q * (Φ _).2 Q = (Φ _).2 Q
        rw [hind Q]
        split_ifs <;> simp
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace _ P v ε hε he he).mp hcrit

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexOneUnitsMulEqCardQuotient
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_oneUnits_iff_exists_eq_one_add {O : Type} [CommRing O] (t : O) (u : Oˣ) :
    u ∈ oneUnits t ↔ ∃ x : O, (u : O) = 1 + t * x := by
  unfold oneUnits
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change Ideal.Quotient.mk (Ideal.span {t}) (u : O) = Ideal.Quotient.mk (Ideal.span {t}) 1 ↔ _
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← hx]; ring⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [hx]; ring⟩

theorem relIndex_oneUnits_mul_eq_card_quotient :
    ∀ (O : Type) [CommRing O] [IsDomain O] (t s : O), t ≠ 0 → s ∣ t →
      Ideal.span {t} ≤ Ideal.jacobson (⊥ : Ideal O) →
      (oneUnits (s * t)).relIndex (oneUnits t) = Nat.card (O ⧸ Ideal.span {s}) := by
  intro O _ _ t s ht hst hJ
  have hex : ∀ u : oneUnits t, ∃ x : O, ((u : Oˣ) : O) = 1 + t * x := fun u =>
    (mem_oneUnits_iff_exists_eq_one_add t u).1 u.2
  choose c hc using hex
  have huniq : ∀ (u : oneUnits t) (x : O), ((u : Oˣ) : O) = 1 + t * x → c u = x := by
    intro u x hx
    have h := hc u
    rw [hx] at h
    exact (mul_left_cancel₀ ht (add_left_cancel h)).symm
  let f : oneUnits t →* Multiplicative (O ⧸ Ideal.span {s}) :=
    { toFun := fun u => Multiplicative.ofAdd (Ideal.Quotient.mk (Ideal.span {s}) (c u))
      map_one' := by
        rw [huniq 1 0 (by simp)]
        simp
      map_mul' := by
        intro u v
        rw [huniq (u * v) (c u + c v + t * (c u * c v)) (by
          rw [Subgroup.coe_mul, Units.val_mul, hc u, hc v]; ring), ← ofAdd_add, ← map_add (f := _)]
        congr 1
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        have : c u + c v + t * (c u * c v) - (c u + c v) = t * (c u * c v) := by ring
        rw [this]
        exact hst.mul_right _ }
  have hf : ∀ u, f u = Multiplicative.ofAdd (Ideal.Quotient.mk (Ideal.span {s}) (c u)) :=
    fun _ => rfl
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (Multiplicative.toAdd y)
    have hu : IsUnit (t * x + 1) :=
      Ideal.mem_jacobson_bot.1 (hJ (Ideal.mem_span_singleton_self t)) x
    have hval : ((hu.unit : Oˣ) : O) = 1 + t * x := by rw [hu.unit_spec, add_comm]
    refine ⟨⟨hu.unit, (mem_oneUnits_iff_exists_eq_one_add t _).2 ⟨x, hval⟩⟩, ?_⟩
    rw [hf, huniq _ x hval, hx]
    rfl
  have hker : (oneUnits (s * t)).subgroupOf (oneUnits t) = f.ker := by
    ext u
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hf, mem_oneUnits_iff_exists_eq_one_add,
      ofAdd_eq_one, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, huniq u _ (by rw [hx]; ring)⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [hc u, hx]; ring⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj,
    Subgroup.card_top]
  rfl

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsPlacesOverAndQuadraticConj
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sUnits_over_and_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → (∀ x : Fˣ, Units.map (algebraMap F E : F →* E) x ∈ sUnits E SE ↔ x ∈ sUnits F S) ∧ ∀ y : Eˣ, y ∈ sUnits E SE → Units.map (σ : E →* E) y ∈ sUnits E SE := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hS
  obtain ⟨-, hup, hval⟩ := places_over F E
  obtain ⟨hconj, -⟩ := conj_places_transitive F E δ θ σ hq
  refine ⟨fun x => ⟨fun h => ?_, fun h => ?_⟩, fun y hy => ?_⟩
  · rw [mem_sUnits] at h ⊢
    intro v hv
    obtain ⟨w, rfl⟩ := hup v
    obtain ⟨e, he, hx⟩ := hval w
    have h1 : w.valuation E (algebraMap F E (x : F)) = 1 := h w (fun a => hv ((hS w).1 a))
    rw [hx] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le he.ne').1 h1
  · rw [mem_sUnits] at h ⊢
    intro w hw
    obtain ⟨e, he, hx⟩ := hval w
    change w.valuation E (algebraMap F E (x : F)) = 1
    rw [hx, h _ (fun a => hw ((hS w).2 a)), one_pow]
  · rw [mem_sUnits] at hy ⊢
    intro w hw
    obtain ⟨w', hu, hv⟩ := hconj w
    change w.valuation E (σ (y : E)) = 1
    rw [← hv]
    exact hy w' (fun a => hw ((hS w).2 (hu ▸ (hS w').1 a)))

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorExistsOfGaloisFixed
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem tensor_exists_of_galois_fixed :
    ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional M E] [IsGalois M E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), (∀ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K) ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) y = y) → ∃ z : K ⊗[F] M, Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z = y := by
  intro F M E K _ _ _ _ _ _ _ _ _ _ _ _ y hy
  classical
  have key : ∀ x : K ⊗[F] E, ∃ z : K ⊗[F] M,
      Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z =
      ∑ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K)
        ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul k e =>
      refine ⟨k ⊗ₜ Algebra.trace M E e, ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← TensorProduct.tmul_sum]
      congr 1
      exact trace_eq_sum_automorphisms e
    | add a b ha hb =>
      obtain ⟨za, ha⟩ := ha
      obtain ⟨zb, hb⟩ := hb
      refine ⟨za + zb, ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]
  obtain ⟨z, hz⟩ := key y
  simp only [hy, Finset.sum_const, Finset.card_univ] at hz
  have hm : ((Fintype.card (E ≃ₐ[M] E) : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨((Fintype.card (E ≃ₐ[M] E) : ℕ) : F)⁻¹ • z, ?_⟩
  rw [LinearMapClass.map_smul_of_tower, hz, ← Nat.cast_smul_eq_nsmul F, smul_smul,
    inv_mul_cancel₀ hm, one_smul]

end GlobalTheory.CNorm
end

