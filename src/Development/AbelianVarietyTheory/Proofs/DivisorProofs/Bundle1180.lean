module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartEqOneMulInvMemSplitCongruenceIdeles
section
noncomputable section

namespace GlobalTheory.HeckeSplitGen.FinF

section Ports

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.CMPrimeIdele
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}

theorem ev_sub (a b : AE F E) (Q : HeightOneSpectrum (𝓞 E)) : Φ (a - b) Q = Φ a Q - Φ b Q := by
  rw [map_sub]; rfl

theorem ev_one (Q : HeightOneSpectrum (𝓞 E)) : Φ 1 Q = 1 := by rw [map_one]; rfl

theorem ev_inc (hΦ : Comp Φ) (y : E) (Q : HeightOneSpectrum (𝓞 E)) :
    Φ (incA F E y) Q = algebraMap E (Q.adicCompletion E) y := by rw [hΦ.2.2.1]; rfl

theorem isSplitIdem_of_delta (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {P : HeightOneSpectrum (𝓞 E)}
    (hc : cP hσ P ≠ P) {e : AE F E} (he : IsDelta Φ P e) : IsSplitIdem σ e := by
  obtain ⟨ε, hε⟩ := exists_placeIdem (F := F) (P.under (𝓞 F))
  obtain ⟨h0, h1, h2⟩ := place_comp (E := E) hΦ hε
  have he' := delta_conj hΦ hσ he
  refine ⟨delta_idem hΦ he, ?_, _, ε, hε, ?_⟩
  · refine hΦ.ext' (by rw [RingHom.map_mul, he.1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P
    · subst hQ
      rw [he'.2.2 Q (Ne.symm hc), mul_zero]
    · rw [he.2.2 Q hQ, zero_mul]
  · refine hΦ.ext' (by rw [RingHom.map_add (f := _), he.1, he'.1, add_zero, h0]) fun Q => ?_
    rw [ev_add]
    by_cases hQ : Q = P
    · subst hQ
      rw [he.2.1, he'.2.2 Q (Ne.symm hc), add_zero, h1 Q rfl]
    · by_cases hQ' : Q = cP hσ P
      · subst hQ'
        rw [he.2.2 _ hQ, he'.2.1, zero_add, h1 _ (under_cP hσ P)]
      · rw [he.2.2 Q hQ, he'.2.2 Q hQ', add_zero, h2 Q fun h => (eq_or_eq_cP hσ h).elim hQ hQ']

theorem mem_modSet (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N) (x : (AE F E)ˣ) (h0 : infPart F E (x : AE F E) = 1)
    (h : ∀ Q, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) :
    x ∈ modSetF F E N := by
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨h0, ⟨finPart F E (((x : AE F E) - 1) * incA F E (N : E)⁻¹), (hΦ.2.2.2.1 _).2 fun Q => ?_, ?_⟩,
    (hΦ.2.2.2.1 _).2 fun Q => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, ev_sub, ev_one, ev_inc hΦ, map_inv₀, map_natCast,
      Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ (h Q).2 zero_le
  · have e : (N : AE F E) * incA F E (N : E)⁻¹ = 1 := by
      rw [← map_natCast (incA F E), ← map_mul, mul_inv_cancel₀ hN', map_one]
    have e2 : (x : AE F E) - 1 = N * (((x : AE F E) - 1) * incA F E (N : E)⁻¹) := by
      linear_combination (1 - (x : AE F E)) * e
    have e3 := congrArg (finPart F E) e2
    rwa [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, map_natCast] at e3
  · have e : Φ x Q * Φ (x⁻¹ : (AE F E)ˣ) Q = 1 := by rw [← ev_mul, Units.mul_inv, ev_one]
    have e2 := congrArg Valued.v e
    rw [Valuation.map_mul, (h Q).1, one_mul, Valuation.map_one] at e2
    exact e2.le

theorem mem_grpH_of_good (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N)
    {B : Set (HeightOneSpectrum (𝓞 E))} (hB : B.Finite) : (∀ P ∈ B, cP hσ P ≠ P) → ∀ x : (AE F E)ˣ,
      infPart F E (x : AE F E) = 1 →
      (∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) →
      x ∈ grpHF σ N := by
  induction B, hB using Set.Finite.induction_on with
  | empty =>
    exact fun _ x h0 h => Subgroup.subset_closure (Or.inr (mem_modSet hΦ hN x h0 fun Q => h Q (Set.notMem_empty Q)))
  | @insert P B _ _ ih =>
    intro hB x h0 h
    obtain ⟨e, he⟩ := exists_delta hΦ P
    have hs := isSplitIdem_of_delta hσ hΦ (hB P (Set.mem_insert _ _)) he
    have h1 : GlobalTheory.HeckeSplitAll.Fin.part hs.1 x ∈ grpHF σ N := by
      refine Subgroup.subset_closure (Or.inl (Or.inr ⟨e, hs, ?_⟩))
      change (e + cA σ e) * (e * x + (1 - e) - 1) = e * x + (1 - e) - 1
      linear_combination ((x : AE F E) - 1) * hs.1 + ((x : AE F E) - 1) * hs.2.1
    have h2 : x * (GlobalTheory.HeckeSplitAll.Fin.part hs.1 x)⁻¹ ∈ grpHF σ N := by
      refine ih (fun Q hQ => hB Q (Set.mem_insert_of_mem _ hQ)) _ ?_ fun Q hQ => ?_
      · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub,
          RingHom.map_one, he.1, h0]
        simp
      · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv, ev_add, ev_mul, ev_sub, ev_one]
        by_cases hQP : Q = P
        · subst hQP
          rw [he.2.1]
          simp
        · rw [he.2.2 Q hQP, zero_add, sub_zero, one_mul]
          exact h Q fun h' => h'.elim hQP hQ
    simpa using mul_mem h2 h1

theorem exists_fin_idem (hΦ : Comp Φ) :
    ∃ f : AE F E, f * f = f ∧ infPart F E f = 0 ∧ finPart F E f = 1 ∧ Φ f = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have he1 : ∀ z, (e z).1 = infPart F E z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart F E z := fun z => (he z).2
  obtain ⟨f, hf⟩ := e.surjective (0, 1)
  have hf0 : infPart F E f = 0 := by rw [← he1, hf]
  have hf1 : finPart F E f = 1 := by rw [← he2, hf]
  have key : ∀ g, infPart F E g = 0 → g * f = g := fun g hg => e.injective (Prod.ext
    (by rw [he1, he1, RingHom.map_mul, hg, zero_mul]) (by rw [he2, he2, RingHom.map_mul, hf1, mul_one]))
  refine ⟨f, key f hf0, hf0, hf1, ?_⟩
  obtain ⟨g, hg0, hg1⟩ := hΦ.2.1 1
  have h4 := congrArg Φ (key g hg0)
  rwa [map_mul, hg1, one_mul] at h4

theorem exists_of_good (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N)
    {B : Set (HeightOneSpectrum (𝓞 E))} (hB : B.Finite) (hB1 : ∀ P ∈ B, cP hσ P ≠ P) (x : (AE F E)ˣ)
    (h : ∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) :
    ∃ z : (AE F E)ˣ, finPart F E (z : AE F E) = 1 ∧ x * z⁻¹ ∈ grpHF σ N := by
  obtain ⟨f, hf, hf0, hf1, hf2⟩ := exists_fin_idem hΦ
  have h3 : GlobalTheory.HeckeSplitAll.Fin.part hf x ∈ grpHF σ N := by
    refine mem_grpH_of_good hσ hΦ hN hB hB1 _ (GlobalTheory.HeckeSplitAll.Fin.map_mix_zero _ hf0 _) fun Q hQ => ?_
    have : Φ (GlobalTheory.HeckeSplitAll.Fin.part hf x : (AE F E)ˣ) = Φ x :=
      (GlobalTheory.HeckeSplitAll.Fin.map_mix_one Φ hf2 _).1
    rw [this]
    exact h Q hQ
  refine ⟨x * (GlobalTheory.HeckeSplitAll.Fin.part hf x)⁻¹, ?_, ?_⟩
  · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv]
    exact (GlobalTheory.HeckeSplitAll.Fin.map_mix_one _ hf1 _).2
  · rwa [mul_inv, inv_inv, mul_inv_cancel_left]

theorem exists_not_fixed (hσ : IsCMExt F E σ) : ∃ δ : 𝓞 E, cO σ δ ≠ δ := by
  by_contra h
  push_neg at h
  have hs : Function.Surjective (algebraMap F E) := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) x
    have ha : σ (a : E) = a := congrArg (fun t : 𝓞 E => (t : E)) (h a)
    have hb : σ (b : E) = b := congrArg (fun t : 𝓞 E => (t : E)) (h b)
    exact exists_of_conj_eq hσ (by rw [map_div₀, ha, hb])
  have h1 : Module.finrank F E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap F E).injective, hs⟩
  have h2 := hσ.2.2.1
  omega

theorem exists_finite_part_one_idele_split_congruence_quotient (hσ : IsCMExt F E σ) {N : ℕ} (hN : 0 < N) (x : (AE F E)ˣ) :
    ∃ z : (AE F E)ˣ, finPart F E (z : AE F E) = 1 ∧ x * z⁻¹ ∈ grpHF σ N := by
  obtain ⟨Φ, hΦ⟩ := exists_comp F E
  obtain ⟨δ, hδ⟩ := exists_not_fixed hσ
  obtain ⟨m, hm, hm'⟩ := GlobalTheory.HeckeSplitAll.Fin.exists_den (Φ x)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hj : ∀ y : E, y ≠ 0 → ∃ u ∈ grpHF σ N, (u : AE F E) = incA F E y := fun y hy =>
    ⟨_, Subgroup.subset_closure (Or.inl (Or.inl ⟨Units.mk0 y hy, rfl⟩)), rfl⟩
  obtain ⟨a, ha, ha'⟩ := hj _ hm0
  have hx₁ : ∀ Q, Valued.v (Φ (a * x : (AE F E)ˣ) Q) ≤ 1 := fun Q => by
    rw [Units.val_mul, ha', ev_mul, ev_inc hΦ, map_natCast]
    exact hm' Q
  obtain ⟨y, hy, B, hB, hB1, hB2⟩ := GlobalTheory.HeckeSplitAll.Fin.approx_int
    ({ cO σ with invFun := cO σ, left_inv := fun t => cO_cO hσ t, right_inv := fun t => cO_cO hσ t } : 𝓞 E ≃+* 𝓞 E)
    (fun t => cO_cO hσ t) δ hδ N hN (Φ (a * x : (AE F E)ˣ))
    (Φ ((a * x)⁻¹ : (AE F E)ˣ)) (by rw [← map_mul, Units.mul_inv, map_one]) hx₁
  obtain ⟨b, hb, hb'⟩ := hj _ (inv_ne_zero hy)
  obtain ⟨z, hz, hz'⟩ := exists_of_good hσ hΦ hN hB
    (fun P hP h => hB1 P hP fun t ht => (mem_cP hσ P t).1 (h.symm ▸ ht)) (a * x * b) fun Q hQ => by
      rw [Units.val_mul, hb', ev_mul, ev_inc hΦ, map_inv₀]
      exact hB2 Q hQ
  exact ⟨z, hz, GlobalTheory.HeckeSplitAll.Fin.mem_of_mul_mem ha hb hz'⟩

end Ports

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct

theorem exists_finPart_eq_one_mul_inv_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ x : (AF F ⊗[F] E)ˣ, ∃ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitGen.grpHF σ N := by
  intro F E _ _ _ _ _ σ hσ N hN x
  exact exists_finite_part_one_idele_split_congruence_quotient hσ hN x

end GlobalTheory.HeckeSplitGen.FinF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimeSetAvoidingGridPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

theorem exists_primeFactor_mem_of_natCast_mem {D : D7} (w : Pl D.host.E) {M : ℕ} (hM : M ≠ 0)
    (h : (M : 𝓞 D.host.E) ∈ w.asIdeal) : ∃ p ∈ M.primeFactors, (p : 𝓞 D.host.E) ∈ w.asIdeal := by
  have e := Nat.prod_factorization_pow_eq_self hM
  rw [← e, Finsupp.prod, Nat.cast_prod] at h
  obtain ⟨p, hp, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h
  refine ⟨p, by simpa [Nat.support_factorization] using hp, ?_⟩
  rw [Nat.cast_pow] at hmem
  exact w.isPrime.mem_of_pow_mem _ hmem

theorem natCast_mem_of_under_eq {D : D7} (w : Pl D.host.E) {v : Pl D.host.F} (h : w.under (𝓞 D.host.F) = v) (n : ℕ)
    (hn : (n : 𝓞 D.host.F) ∈ v.asIdeal) : (n : 𝓞 D.host.E) ∈ w.asIdeal := by
  subst h
  have : (n : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hn
  rw [Ideal.mem_comap, map_natCast] at this
  exact this

theorem exists_std_primes : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (U : Set T), U.Finite →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧
      (∀ t ∈ U, ∀ w' ∈ L.Q t, w.under (𝓞 D.host.F) ≠ w'.under (𝓞 D.host.F)) ∧
      ((D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D T L sc G U hU
  set N : ℕ := D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK with hN
  set A : ℕ := ∏ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal with hA
  set B : ℕ := ∏ t ∈ hU.toFinset, ∏ w' ∈ L.Q t, Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal with hB
  have hN0 : N ≠ 0 := by
    have h1 := D.host.hyp.1.ne_zero
    have h2 := D.host.hyp.2.1.ne_zero
    have h3 := (D.host.g_prime 0).ne_zero
    have h4 := (D.host.g_prime 1).ne_zero
    have h5 : Ideal.absNorm D.host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
    have h0 : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3) h4) h5
  have hA0 : A ≠ 0 := by
    rw [hA, Finset.prod_ne_zero_iff]
    intro v _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hB0 : B ≠ 0 := by
    rw [hB, Finset.prod_ne_zero_iff]
    intro t _
    rw [Finset.prod_ne_zero_iff]
    intro w' _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (w'.under (𝓞 D.host.F)).ne_bot
  have hM0 : N * A * B ≠ 0 := mul_ne_zero (mul_ne_zero hN0 hA0) hB0
  refine ⟨(N * A * B).primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩
  intro w hw
  have key : ∀ n : ℕ, n ∣ N * A * B → (n : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro n hn hmem
    obtain ⟨k, hk⟩ := hn
    have hM : ((N * A * B : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [hk, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hmem
    obtain ⟨p, hp, hpm⟩ := exists_primeFactor_mem_of_natCast_mem w hM0 hM
    exact hw p hp hpm
  refine ⟨fun hv => ?_, fun t ht w' hw' heq => ?_, key N (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)⟩
  · apply key (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _) _
    · exact natCast_mem_of_under_eq w rfl _ (Ideal.absNorm_mem _)
  · apply key (Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_right ((Finset.dvd_prod_of_mem (fun w'' : Pl D.host.E => Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal) hw').trans
        (Finset.dvd_prod_of_mem (fun t => ∏ w'' ∈ L.Q t, Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal)
          (hU.mem_toFinset.2 ht))) _
    · exact natCast_mem_of_under_eq w heq _ (Ideal.absNorm_mem _)

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPairFlagsDifferingOneStep
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Gen

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap g = spMap (h.comp g) := by
  rw [← Spec.map_comp]
  rfl

theorem exists_genPair : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∃ ψ₂ : Y.Fn →+* RatFunc Y.Fn, GenPair Y (algebraMap Y.Fn (RatFunc Y.Fn)) ψ₂ ∧ (∀ u : X.Fn, algebraMap Y.Fn (RatFunc Y.Fn) (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) * (B.map (algebraMap Y.Fn (RatFunc Y.Fn)) * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hf B hB τ a b hab
  obtain ⟨V, c, t, hc, ht, hr⟩ := _root_.GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero Y.Fn
  obtain ⟨A, hA⟩ := E.nonempty (f (genericPoint Y.X))
  have hM : Par 0 ((ratOf Y).O (genericPoint Y.X)).toSubring (B * (A.map φ)⁻¹) := hf.sub _ B hB A hA
  obtain ⟨pt, hpt⟩ : ∃ pt : Sp Y.Fn ⟶ Y.X, pt = (ratOf Y).pt := ⟨_, rfl⟩
  have hpa (w) : pt w = genericPoint Y.X := hpt ▸ (ratOf Y).pt_apply w
  have hps : pt ≫ Y.str = spMap (algebraMap F Y.Fn) := hpt ▸ (ratOf Y).pt_s
  have hq : spMap (algebraMap V (RatFunc Y.Fn)) ≫ spMap c ≫ pt = spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt := by
    rw [← Category.assoc, spMap_comp, hc]
  have hh : Par 0 ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) := by
    refine Par.mul (ClosedPt.par_zero_top fun σ => ?_) (hM.map _ fun _ _ => trivial)
    rw [(_root_.GlobalTheory.FlagPush.shear_props ι m τ a b hab _ _).1 σ]
    exact one_ne_zero
  have hx : ((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn)) = f (genericPoint Y.X) :=
    congrArg f (hpa _)
  have hA' : A ∈ E.S (((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn))) := (congrArg (fun z : X.X => A ∈ E.S z) hx).mpr hA
  obtain ⟨q₂, hq₂, hb⟩ : ∃ q₂ : Sp (RatFunc Y.Fn) ⟶ Y.X,
      q₂ ≫ f = (spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f ∧ Bears E' φ A (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) q₂ := (hf.lifts (RatFunc Y.Fn) _ A hA' _ hh).exists
  have hs : f ≫ X.str = Y.str := hf.hom.inducedModelMorphism_comp_structureMap
  obtain ⟨v₂, hv₂, hv₂f⟩ := _root_.GlobalTheory.FlagPush.exists_lift_of_var F X Y f hs _ V (spMap c ≫ pt) q₂ (by
    rw [hq₂, ← hq]; simp only [Category.assoc])
  have hmeet : spMap (IsLocalRing.residue V) ≫ spMap c ≫ pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
    subst hpt
    exact _root_.GlobalTheory.FlagPush.Meet.meet F X Y ι m E E' φ f hf B hB A hA τ a b hab _ V c t hr v₂
      (hv₂f.trans (Category.assoc _ _ _)) (by subst hv₂; rw [hc, ht]; exact hb)
  have h1 : (spMap c ≫ pt) (IsLocalRing.closedPoint V) = genericPoint Y.X := hpa _
  have h2 : v₂ (IsLocalRing.closedPoint V) = genericPoint Y.X := by
    rw [← ClosedPt.closedPt_comp v₂, ← hmeet, ClosedPt.closedPt_comp, h1]
  letI : Algebra F (RatFunc Y.Fn) := ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)).toAlgebra
  have hsp : q₂ (IsLocalRing.closedPoint (RatFunc Y.Fn)) ⤳ genericPoint Y.X := by
    have := ClosedPt.gen_specializes v₂ (IsLocalRing.closedPoint (RatFunc Y.Fn))
    rwa [hv₂, h2] at this
  have hstr : q₂ ≫ Y.str = spMap ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)) := by
    rw [← hs, ← Category.assoc, hq₂, Category.assoc, hs, Category.assoc, ← spMap_comp, hps]
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_specializes_genericPoint F Y (RatFunc Y.Fn) q₂ hsp hstr
  subst hpt
  have hcv := _root_.GlobalTheory.FlagPush.flag_conv F X Y ι m E E' φ f hf B hB A hA _ (algebraMap Y.Fn (RatFunc Y.Fn)) ψ.toRingHom
    (shear τ a b RatFunc.X) (by
      subst hψ
      exact (Category.assoc _ _ _).symm.trans (hq₂.symm.trans (Category.assoc _ _ _))) (by subst hψ; exact hb)
  refine ⟨ψ.toRingHom, ⟨?_, V, spMap c ≫ (ratOf Y).pt, v₂, hq, hv₂.trans hψ, hmeet, h1⟩, hcv.1, hcv.2⟩
  exact RingHom.ext fun r => (ψ.commutes r).symm

end GlobalTheory.FlagPush.Gen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPatchOfComplexPointOpenPart
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem exists_goodPatch_of_mem : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ y ∈ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hH y hy
  classical
  obtain ⟨ch, hc⟩ := AlgChart.exists_mem_source (D := X.dim) (p := X.str) (σ := σ) y
  obtain ⟨A, hA⟩ := E.nonempty (under y)
  have hhol : IsHoloChart ch.e := ch.holo
  obtain ⟨hsm, hu⟩ := _root_.GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart E O H hH hhol hy hc hA
  set G : V X.dim → Matrix (Fin m) (Fin m) ℂ := fun v => H A (ch.e.symm v) () with hG
  have h1 : ((0 : WithTop ℕ∞) + 1) ≤ ∞ := by exact_mod_cast le_top
  have h2 : ((0 : WithTop ℕ∞) + 2) ≤ ∞ := by
    rw [zero_add]
    first
    | exact (WithTop.coe_le_coe (a := (2 : ℕ∞)) (b := ⊤)).2 le_top
    | exact ENat.LEInfty.out
    | simp
    | decide
  have hconn : ∀ (a : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => conn G (ch.e z) (coordVec a) i j) y := fun a i j =>
    ((hsm.conn hu h1 (coordVec a)) i j).continuousAt.comp (ch.e.continuousAt hc)
  have hcurv : ∀ (a b : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => curv G (ch.e z) (coordVec a) (coordVec b) i j) y := fun a b i j =>
    ((hsm.curv hu h2 (coordVec a) (coordVec b)) i j).continuousAt.comp (ch.e.continuousAt hc)
  let C : ℝ := (∑ a : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1)) +
    ∑ a : Fin X.dim, ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m,
      (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
  have hP1 : ∀ a i j, ‖conn G (ch.e y) (coordVec a) i j‖ + 1 ≤ C := by
    intro a i j
    refine le_add_of_le_of_nonneg ?_ (by positivity)
    refine (Finset.single_le_sum (f := fun j => ‖conn G (ch.e y) (coordVec a) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  have hP2 : ∀ a b i j, ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1 ≤ C := by
    intro a b i j
    refine le_add_of_nonneg_of_le (by positivity) ?_
    refine (Finset.single_le_sum (f := fun j => ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    refine (Finset.single_le_sum (f := fun b => ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ b)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  let T : Set (CxPts X.str σ) := {z | z ∈ ch.e.source ∧ z ∈ ptsIn X.str σ O ∧ A ∈ E.S (under z) ∧
    (∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C) ∧
    (∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C)}
  have hT : T ∈ 𝓝 y := by
    have e1 : ∀ᶠ z in 𝓝 y, ∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a i j
      filter_upwards [(hconn a i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP1 a i j]))
    have e2 : ∀ᶠ z in 𝓝 y, ∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a b i j
      filter_upwards [(hcurv a b i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP2 a b i j]))
    filter_upwards [ch.e.open_source.mem_nhds hc, (isOpen_ptsIn (p := X.str) (σ := σ) O).mem_nhds hy,
      GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA, e1, e2] with z h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨ch.e, ∅, A, interior T, C, mem_interior_iff_mem_nhds.2 hT, ?_⟩
  have hsub : ∀ z ∈ interior T, z ∈ T := fun z hz => interior_subset hz
  refine ⟨hhol, isOpen_interior, fun z hz => (hsub z hz).1, fun z hz => (hsub z hz).2.2.1,
    fun z _ a ha => absurd ha (Finset.notMem_empty a), fun z hz => ?_, fun z hz _ a i j => ?_,
    fun z hz _ a b i j => ?_⟩
  · simp only [Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    exact (hsub z hz).2.1
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.1 a i j
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.2 a b i j

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZeroStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G), GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0 → ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  first | exact @GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | exact GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | (intros; apply GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIsDomainOfSmoothComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory

theorem exists_open_isDomain_of_smooth_complex :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ x : Y,
      ∃ U : Y.Opens, x ∈ U ∧ ∀ V : Y.Opens, V ≤ U → x ∈ V → IsDomain Γ(Y, V) := by
  intro Y p D hp x
  have hs : Smooth p := SmoothOfRelativeDimension.smooth D p
  obtain ⟨-, hn, hl⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hs
  have := IsNormalScheme.of_pred hn
  obtain ⟨U, hx, hU⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y x
  exact ⟨U, hx, fun V hV hxV => hU V hxV hV⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisMemOfIsLocalRingOfVarietyPointStatement
section
open GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trBasis_mem_of_isLocalRingOfVarietyPoint : ∀ {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K) (n : ℕ), IsLocModel c R →
    (∃ x : Fin n → K, TrBasis c x) → ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) := by
  first | exact @GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel | exact GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel | (intros; apply GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel <;> assumption)
end

