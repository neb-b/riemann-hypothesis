module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOne
section
open Polynomial

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F]

theorem mangoldtConv_eq_of_dvd_pow {f g : F[X]} (hf : f.Monic) (hf' : Irreducible f) (hg : g.Monic)
    (hg' : Irreducible g) {n : ℕ} (h : g ∣ f ^ n) : g = f :=
  eq_of_monic_of_associated hg hf (hg'.associated_of_dvd hf' (hg'.prime.dvd_of_dvd_pow h))

theorem mangoldt_pow (s : F[X] → ℂ) (f : F[X]) (m : ℕ) (hf : f.Monic) (hf' : Irreducible f) (hm : 0 < m) :
    mangoldt s (f ^ m) = s f := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ f ^ m = g ^ k} = {f} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hg, hg', k, hk, h⟩
      exact mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := m) (h ▸ dvd_pow_self g hk.ne')
    · rintro rfl
      exact ⟨hf, hf', m, hm, rfl⟩
  rw [mangoldt, this, finsum_mem_singleton]

theorem mangoldt_eq_zero (s : F[X] → ℂ) (P : F[X])
    (h : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) : mangoldt s P = 0 := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ P = g ^ k} = ∅ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hg, hg', k, hk, h'⟩
    exact h ⟨g, k, hg, hg', hk, h'⟩
  rw [mangoldt, this, finsum_mem_empty]

theorem conv_const_one_eq_divisorSum (a : F[X] → ℂ) (P : F[X]) (hP : P.Monic) :
    conv a (fun _ => 1) P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, a D := by
  unfold conv
  refine finsum_mem_eq_of_bijOn (fun x => x.1) ⟨?_, ?_, ?_⟩ ?_
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩
    exact ⟨hD, E, h.symm⟩
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩ ⟨D', E'⟩ ⟨_, _, h'⟩ h''
    simp only at h h' h'' hD
    subst h''
    rw [mul_left_cancel₀ hD.ne_zero (h.trans h'.symm)]
  · rintro D ⟨hD, E, h⟩
    exact ⟨(D, E), ⟨hD, hD.of_mul_monic_left (h ▸ hP), h.symm⟩, rfl⟩
  · intro x _
    simp

theorem mangoldtConv_finite_monicDivisors (P : F[X]) (hP : P.Monic) :
    {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by
  have := Polynomial.fintypeSubtypeMonicDvd P hP.ne_zero
  exact Set.finite_coe_iff.mp (Finite.of_fintype {g : F[X] // g.Monic ∧ g ∣ P})

theorem mangoldt_divisorSum_mul (s : F[X] → ℂ) (f Q : F[X]) (hf : f.Monic) (hf' : Irreducible f)
    (hQ : Q.Monic) :
    ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ f * Q}, mangoldt s D =
      s f + ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ Q}, mangoldt s D := by
  obtain ⟨n, R, hR, hQR⟩ := WfDvdMonoid.max_power_factor hQ.ne_zero hf'
  have hnot : f ^ (n + 1) ∉ {D : F[X] | D.Monic ∧ D ∣ Q} := by
    rintro ⟨_, h⟩
    rw [hQR, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n hf.ne_zero)] at h
    exact hR h
  rw [← mangoldt_pow s f (n + 1) hf hf' n.succ_pos,
    ← finsum_mem_insert _ hnot (mangoldtConv_finite_monicDivisors Q hQ)]
  refine finsum_mem_inter_support_eq _ _ _ ?_
  ext D
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Function.mem_support]
  refine and_congr_left fun hD => ?_
  constructor
  · rintro ⟨hDm, hd⟩
    obtain ⟨g, m, hg, hg', hm, rfl⟩ := not_not.mp (mt (mangoldt_eq_zero s D) hD)
    by_cases hgf : g = f
    · subst hgf
      rcases lt_trichotomy m (n + 1) with h | h | h
      · exact Or.inr ⟨hDm, hQR ▸ (pow_dvd_pow g (by omega)).mul_right R⟩
      · exact Or.inl (by rw [h])
      · exfalso
        have h2 : g ^ (n + 1) * g ∣ g ^ (n + 1) * R := by
          have h3 : g ^ (n + 1 + 1) ∣ g * Q := (pow_dvd_pow g (by omega)).trans hd
          rw [hQR, ← mul_assoc, ← pow_succ', pow_succ g (n + 1)] at h3
          exact h3
        exact hR ((mul_dvd_mul_iff_left (pow_ne_zero _ hf.ne_zero)).mp h2)
    · refine Or.inr ⟨hDm, ?_⟩
      have hc : IsCoprime g f := by
        rw [hg'.coprime_iff_not_dvd]
        intro h
        exact hgf (mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := 1) (by simpa using h))
      exact (hc.pow_left (m := m)).dvd_of_dvd_mul_left hd
  · rintro (rfl | ⟨hDm, hd⟩)
    · refine ⟨hf.pow _, ?_⟩
      rw [hQR, ← mul_assoc, ← pow_succ']
      exact dvd_mul_right _ _
    · exact ⟨hDm, hd.mul_left f⟩

theorem IsAdditive.eq_divisorSum_mangoldt {s : F[X] → ℂ} (hs : IsAdditive s) (P : F[X]) (hP : P.Monic) :
    s P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, mangoldt s D := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases hu : IsUnit P
    · have h1 : P = 1 := hP.isUnit_iff.mp hu
      subst h1
      have h0 : s 1 = 0 := by
        have := hs 1 1 monic_one monic_one
        rw [mul_one] at this
        exact left_eq_add.mp this
      rw [h0]
      symm
      refine finsum_mem_of_eqOn_zero fun D hD => ?_
      refine mangoldt_eq_zero s D ?_
      rintro ⟨g, m, _, hg', hm, rfl⟩
      exact hg'.not_isUnit (isUnit_of_dvd_one ((dvd_pow_self g hm.ne').trans hD.2))
    · obtain ⟨f, hf, hf', Q, rfl⟩ := Polynomial.exists_monic_irreducible_factor P hu
      have hQ : Q.Monic := hf.of_mul_monic_left hP
      have hlt : Q.natDegree < n := by
        rw [← hn, hf.natDegree_mul hQ]
        have := hf'.natDegree_pos
        omega
      rw [mangoldt_divisorSum_mul s f Q hf hf' hQ, hs f Q hf hQ, ih _ hlt Q hQ rfl]

theorem mangoldt_conv_spec : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s →
    (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧
    (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧
    ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) →
      mangoldt s P = 0 := by
  intro F _ s hs
  refine ⟨fun P hP => ?_, mangoldt_pow s, mangoldt_eq_zero s⟩
  rw [conv_const_one_eq_divisorSum _ P hP]
  exact hs.eq_divisorSum_mangoldt P hP

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByPowPrimePowModEqStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy : ∀ (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X] (x : G) (p k : ℕ), p.Prime → Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  first | exact @GlobalTheory.card_fixedBy_pow_prime_pow_modEq | exact GlobalTheory.card_fixedBy_pow_prime_pow_modEq | (intros; apply GlobalTheory.card_fixedBy_pow_prime_pow_modEq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardNonregularResiduesModPowSubOneLe
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem card_nonregular_residues_le (q n : ℕ) (hq : 2 ≤ q) (hn : 0 < n) :
    ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤
      ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by
  classical
  have hsub : ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])) ⊆
      n.primeFactors.biUnion (fun p => (Finset.Ioo 0 (q ^ (n / p) - 1)).image
        (fun k => k * ((q ^ n - 1) / (q ^ (n / p) - 1)))) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Ioo] at hj
    obtain ⟨⟨hj0, hjN⟩, e, he, hje⟩ := hj
    rw [Finset.mem_Ioo] at he
    have hqe : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
    have h1 : q ^ n - 1 ∣ j * (q ^ e - 1) := by
      rw [Nat.mul_sub_one]
      exact (Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_right j hqe)).1 hje.symm
    have h2 : q ^ n - 1 ∣ j * (q ^ Nat.gcd e n - 1) := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one, ← Nat.gcd_mul_left]
      exact Nat.dvd_gcd h1 (Dvd.intro_left j rfl)
    obtain ⟨m, hm⟩ := Nat.gcd_dvd_right e n
    have hglt : Nat.gcd e n < n := lt_of_le_of_lt (Nat.gcd_le_left n he.1) he.2
    have hm1 : m ≠ 1 := by
      rintro rfl
      omega
    obtain ⟨p, hp, r, hr⟩ := Nat.exists_prime_and_dvd hm1
    have hnp : n = p * (Nat.gcd e n * r) := by
      conv_lhs => rw [hm, hr]
      ring
    have hd : n / p = Nat.gcd e n * r := Nat.div_eq_of_eq_mul_right hp.pos hnp
    have hpn : p ∣ n := ⟨_, hnp⟩
    have hd0 : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos).ne'
    have h3 : q ^ n - 1 ∣ j * (q ^ (n / p) - 1) :=
      h2.trans (Nat.mul_dvd_mul_left j
        (Nat.pow_sub_one_dvd_pow_sub_one q ⟨r, hd⟩))
    have h4 : q ^ (n / p) - 1 ∣ q ^ n - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one q (Nat.div_dvd_of_dvd hpn)
    have hD : 0 < q ^ (n / p) - 1 := by
      have := Nat.one_lt_pow hd0 (show 1 < q by omega)
      omega
    obtain ⟨M, hM⟩ := h4
    rw [Finset.mem_biUnion]
    refine ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpn, hn.ne'⟩, ?_⟩
    rw [hM, mul_comm j] at h3
    obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left hD h3
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Ioo.2 ⟨?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    · rw [hM, hk, mul_comm _ M] at hjN
      exact lt_of_mul_lt_mul_left hjN (Nat.zero_le _)
    · rw [hM, Nat.mul_div_cancel_left _ hD, hk, mul_comm]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine Finset.sum_le_sum fun p _ => Finset.card_image_le.trans ?_
  rw [Nat.card_Ioo]
  omega

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesOfFinrankMulCardBases
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.SubspaceNumber

theorem card_fibre {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (a : ℕ) (W : Submodule F V) (hW : Module.finrank F W = a) :
    Nat.card {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} = Nat.card {t : Fin a → W // LinearIndependent F t} := by
  symm
  have hspan : ∀ t : Fin a → W, LinearIndependent F t →
      Submodule.span F (Set.range (W.subtype ∘ t)) = W := by
    intro t ht
    have h1 : Submodule.span F (Set.range t) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card ht, Fintype.card_fin, hW]
    rw [Set.range_comp, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_subtype]
  refine Nat.card_congr (Equiv.ofBijective
    (fun t => ⟨⟨W.subtype ∘ t.1, t.2.map' _ W.ker_subtype⟩, hspan t.1 t.2⟩) ⟨?_, ?_⟩)
  · intro t u h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (congrArg (fun x => x.1.1) h) i
  · rintro ⟨⟨s, hs⟩, h⟩
    have hm : ∀ i, s i ∈ W := fun i => by
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨⟨fun i => ⟨s i, hm i⟩, LinearIndependent.of_comp W.subtype hs⟩, rfl⟩

theorem card_subspaces_mul :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V →
      Nat.card {W : Submodule F V // Module.finrank F W = a} *
        ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) =
      ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by
  intro F _ _ V _ _ _ a ha
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
  haveI : Fintype {W : Submodule F V // Module.finrank F W = a} := Fintype.ofFinite _
  let f : {s : Fin a → V // LinearIndependent F s} →
      {W : Submodule F V // Module.finrank F W = a} := fun s =>
    ⟨Submodule.span F (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩
  have hfib : ∀ W, Nat.card {s // f s = W} =
      ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) := by
    rintro ⟨W, hW⟩
    have e : {s // f s = ⟨W, hW⟩} ≃ {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} :=
      Equiv.subtypeEquivRight (fun s => Subtype.ext_iff)
    rw [Nat.card_congr e, card_fibre a W hW, card_linearIndependent hW.ge, hW,
      Finset.prod_range, Nat.card_eq_fintype_card]
  have h := card_linearIndependent (K := F) (V := V) ha
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma] at h
  simp_rw [hfib] at h
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  rw [h, Finset.prod_range]

end GlobalTheory.SubspaceNumber
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterCosetSumEqZeroOfSubgroupSum
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI


open Polynomial in
theorem _root_.GlobalTheory.BI.char_coset_sum_eq_zero :
    ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ χ → ∀ H : Subgroup G,
      ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by
  intro G _ _ χ hχc H hH g
  obtain ⟨n, ρ, hρ⟩ := hχc
  have := Fintype.ofFinite H
  have hχ : ∀ x, χ x = LinearMap.trace ℂ _ (ρ x) := fun x => by
    simp [hρ, Representation.character]
  rw [finsum_eq_sum_of_fintype] at hH ⊢
  simp only [hχ] at hH ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum] at hH
  set S : Module.End ℂ (Fin n → ℂ) := ∑ u : H, ρ u with hS
  have habs : ∀ v : H, ρ v * S = S := by
    intro v
    rw [hS, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun u => ?_)
    simp [map_mul]
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hSS : S * S = (Fintype.card H : ℂ) • S := by
    conv_lhs => arg 1; rw [hS]
    rw [Finset.sum_mul]
    simp only [habs, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hidem : IsIdempotentElem ((Fintype.card H : ℂ)⁻¹ • S) := by
    unfold IsIdempotentElem
    rw [smul_mul_smul, hSS, smul_smul]
    congr 1
    field_simp
  have hP : (Fintype.card H : ℂ)⁻¹ • S = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff hidem).1 (by rw [map_smul, hH, smul_zero])
  have hS0 : S = 0 := by simpa [hcard] using hP
  have hsum : ∑ u : H, LinearMap.trace ℂ _ (ρ (g * u)) = LinearMap.trace ℂ _ (ρ g * S) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    simp [map_mul]
  rw [hsum, hS0, mul_zero, map_zero]

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterExtendScalarsRep
section
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type} [Group G] {n : ℕ}
    (ρ : Representation K G (Fin n → K)) : Representation L G (Fin n → L) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L))
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem character_extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type}
    [Group G] {n : ℕ} (ρ : Representation K G (Fin n → K)) (g : G) :
    (extendScalarsRep K L ρ).character g = algebraMap K L (ρ.character g) := by
  have h1 : (extendScalarsRep K L ρ).character g
      = ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L)).trace := by
    change LinearMap.trace L _ (Matrix.toLin' _) = _
    exact Matrix.trace_toLin'_eq _
  have h2 : ρ.character g = (LinearMap.toMatrix' (ρ g)).trace := by
    change LinearMap.trace K _ (ρ g) = _
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  rw [h1, h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem isChar_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G]
    (χ : G → L), IsChar K L χ → IsChar L L χ := by
  intro K L _ _ _ G _ χ ⟨n, ρ, h⟩
  refine ⟨n, extendScalarsRep K L ρ, fun g => ?_⟩
  rw [h g, character_extendScalarsRep]
  rfl

end GlobalTheory.BI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic
section
open Polynomial GlobalTheory.CuspGL Module.Basis

namespace GlobalTheory.CuspGL


open Module Module.Basis in
theorem charpoly_eq_restrict_mul_mapQ {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A) :
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) := by
  classical
  let bA := Module.finBasis F A
  let bQ := Module.finBasis F (V ⧸ A)
  let b := sumQuot bA bQ
  have hmat : LinearMap.toMatrix b b g = Matrix.fromBlocks (LinearMap.toMatrix bA bA (g.restrict hg))
      (Matrix.of fun i j => b.repr (g (b (Sum.inr j))) (Sum.inl i)) 0
      (LinearMap.toMatrix bQ bQ (A.mapQ A g (fun x hx => hg x hx))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁, b, sumQuot_inl]
      rw [sumQuot_repr_inl_of_mem bA bQ _ (hg _ (bA j).2)]
      rfl
    · simp [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, b]
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₁, b, sumQuot_inl,
        Matrix.zero_apply]
      exact sumQuot_repr_inr_of_mem bA bQ _ (hg _ (bA j).2) i
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₂, b]
      rw [sumQuot_repr_inr, ← sumQuot_inr bA bQ j, Submodule.mapQ_apply]
      rfl
  rw [← LinearMap.charpoly_toMatrix g b, hmat, Matrix.charpoly_fromBlocks_zero₂₁,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

theorem charpoly_block : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A),
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) ∧
    ∀ h ∈ nilRad A, LinearMap.charpoly (g + h) = LinearMap.charpoly g := by
  intro F _ V _ _ _ A g hg
  refine ⟨charpoly_eq_restrict_mul_mapQ A g hg, ?_⟩
  rintro h ⟨himg, hker⟩
  have hgh : ∀ x ∈ A, (g + h) x ∈ A := fun x hx => by
    simpa [LinearMap.add_apply, hker x hx] using hg x hx
  have hres : (g + h).restrict hgh = g.restrict hg := by
    ext x
    simp [LinearMap.restrict_apply, hker x x.2]
  have hquot : A.mapQ A (g + h) (fun x hx => hgh x hx) = A.mapQ A g (fun x hx => hg x hx) := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simpa [LinearMap.add_apply] using himg x
  rw [charpoly_eq_restrict_mul_mapQ A (g + h) hgh, charpoly_eq_restrict_mul_mapQ A g hg, hres, hquot]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassEqOfLinearEquivInvariant
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem mass_eq_mass_pi_of_invariant : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.natDegree = Module.finrank F V → mass (Φ V) P = mass (Φ (Fin P.natDegree → F)) P := by
  intro F _ _ V _ _ _ Φ hΦ P hP
  let e : V ≃ₗ[F] (Fin P.natDegree → F) := LinearEquiv.ofFinrankEq _ _ (by simp [hP])
  unfold mass
  refine finsum_mem_eq_of_bijOn (fun g => e.conj g) ⟨?_, ?_, ?_⟩ ?_
  · intro g hg
    simpa using hg
  · intro g _ h _ hgh
    simpa using congrArg e.symm.conj hgh
  · intro h hh
    refine ⟨e.symm.conj h, ?_, by simp⟩
    simpa using hh
  · intro g _
    exact (hΦ V _ e g).symm

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCoprimeOrderOfPowPrimePowStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  first | exact @GlobalTheory.exists_coprime_orderOf_pow_prime_pow | exact GlobalTheory.exists_coprime_orderOf_pow_prime_pow | (intros; apply GlobalTheory.exists_coprime_orderOf_pow_prime_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsSylowOverSubgroupStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex : ∀ (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ), p.Prime → ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧ ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by
  first | exact @GlobalTheory.exists_sylow_over_subgroup | exact GlobalTheory.exists_sylow_over_subgroup | (intros; apply GlobalTheory.exists_sylow_over_subgroup <;> assumption)
end

