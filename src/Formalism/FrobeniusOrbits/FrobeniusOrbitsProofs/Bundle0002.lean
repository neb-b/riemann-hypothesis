module

public import Mathlib
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.FrobeniusOrbits.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow

@[expose] public section

-- bundled from Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardExtendedGaloisGroup
section
open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Misc2

theorem units_ne_one_iff (x : ℤˣ) : x ≠ 1 ↔ x = -1 := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> decide

end Misc2

open Misc2

theorem hostPartner : HostPartner := by
  intro e τ hτ
  rw [mem_Psi_iff] at hτ
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [Set.mem_ofPred_eq, mem_Psi_iff, units_ne_one_iff] at hg
    show _ ∈ Psi e
    rw [mem_Psi_iff]
    simp [cc, c0, hg, hτ]
  · intro g _ g' _ hgg
    simpa using hgg
  · intro t ht
    rw [SetLike.mem_coe, mem_Psi_iff] at ht
    refine ⟨(cc e)⁻¹ * t * τ⁻¹, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, mem_Psi_iff]
      simp [cc, c0, ht, hτ]
    · simp only
      group

namespace Misc2

def conjHom {G : Type*} [Group G] (χ : G →* ℂˣ) : G →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp χ)

def twHom (e : ℕ) (χ : GG e →* ℂˣ) : GG e →* ℂ :=
  (Units.coeHom ℂ).comp (chC e) * conjHom χ

theorem chC_apply (e : ℕ) (g : GG e) : ((chC e g : ℂˣ) : ℂ) = (((g.1.2 : ℤˣ) : ℤ) : ℂ) := rfl

theorem conjHom_eq_one_iff {G : Type*} [Group G] (χ : G →* ℂˣ) : conjHom χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    ext g
    have := DFunLike.congr_fun h g
    simp only [conjHom, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.one_apply] at this
    have := congrArg (starRingEnd ℂ) this
    simpa using this
  · rintro rfl
    ext g
    simp [conjHom]

theorem int_units_sq_C (x : ℤˣ) : (((x : ℤ) : ℂ)) * ((x : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> simp

theorem twHom_eq_one_iff (e : ℕ) (χ : GG e →* ℂˣ) : twHom e χ = 1 ↔ χ = chC e := by
  constructor
  · intro h
    ext g
    have := DFunLike.congr_fun h g
    simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.one_apply, chC_apply] at this
    have h2 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = (((g.1.2 : ℤˣ) : ℤ) : ℂ) := by
      have := congrArg (fun z => (((g.1.2 : ℤˣ) : ℤ) : ℂ) * z) this
      simp only [← mul_assoc, int_units_sq_C, one_mul, mul_one] at this
      exact this
    have := congrArg (starRingEnd ℂ) h2
    rw [chC_apply]
    simpa using this
  · rintro rfl
    ext g
    simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.one_apply, chC_apply]
    simp [int_units_sq_C]

theorem chC_ne_one (e : ℕ) : chC e ≠ 1 := by
  intro h
  have := DFunLike.congr_fun h (cc e)
  have h2 := congrArg (fun u : ℂˣ => (u : ℂ)) this
  simp only [chC_apply, MonoidHom.one_apply, Units.val_one] at h2
  simp [cc, c0] at h2
  norm_num at h2

theorem card_extended_galois_group (e : ℕ) [Fintype (GG e)] : (Fintype.card (GG e) : ℂ) = 2 ^ (e + 2) := by
  rw [← Nat.card_eq_fintype_card, (hostGroup e).1]
  push_cast; rfl

end Misc2

open Classical in
theorem hostCharSum : HostCharSum := by
  intro e
  refine ⟨fun χ => ?_, fun g => ?_⟩
  · have hpt : ∀ g : GG e, 2 * (if g ∉ Psi e then starRingEnd ℂ ((χ g : ℂˣ) : ℂ) else 0) =
        conjHom χ g - twHom e χ g := by
      intro g
      simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
        Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, chC_apply, mem_Psi_iff]
      rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> simp <;> ring
    have hA := sum_hom_units (conjHom χ)
    have hB := sum_hom_units (twHom e χ)
    simp only [conjHom_eq_one_iff, twHom_eq_one_iff, Nat.cast_ite, Nat.cast_zero] at hA hB
    have hS : 2 * (∑ g ∈ Finset.univ.filter (fun g : GG e => g ∉ Psi e),
        starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        (∑ g : GG e, conjHom χ g) - ∑ g : GG e, twHom e χ g := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun g _ => hpt g)
    rw [hA, hB, card_extended_galois_group] at hS
    have hne := chC_ne_one e
    split_ifs at hS ⊢ with h1 h2 h2
    · exact absurd (h1.symm.trans h2) (Ne.symm hne)
    · linear_combination hS / 2
    · linear_combination hS / 2
    · linear_combination hS / 2
  · simp only [chD, chQ, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd, Prod.ext_iff]
    rcases Int.units_eq_one_or g.1.1 with h | h <;> rcases Int.units_eq_one_or g.1.2 with h' | h' <;>
      rw [h, h'] <;> decide

end Formalism.FrobeniusOrbits
end
end

-- bundled from Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
section
open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace EFG

theorem two_isPrime : (span {(2 : ℤ)}).IsPrime := by
  exact (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two

theorem card_trivial_first_component (e : ℕ) : Nat.card {g : GG e // g.1 = 1} = 2 ^ e := by
  rw [← Group.card_H e]
  exact Nat.card_congr
    { toFun := fun g => g.1.2
      invFun := fun h => ⟨(1, h), rfl⟩
      left_inv := fun g => by
        obtain ⟨⟨g1, g2⟩, hg⟩ := g
        simp only at hg
        subst hg
        rfl
      right_inv := fun _ => rfl }

theorem card_Psi (e : ℕ) : Nat.card (Psi e) = 2 ^ (e + 1) := by
  have hmem : ∀ g : GG e, g ∈ Psi e ↔ g.1.2 = 1 := fun g => by
    simp [Psi, chD, MonoidHom.mem_ker]
  have : Nat.card (Psi e) = Nat.card (ℤˣ × HGrp e) :=
    Nat.card_congr
      { toFun := fun g => (g.1.1.1, g.1.2)
        invFun := fun x => ⟨((x.1, 1), x.2), (hmem _).2 rfl⟩
        left_inv := fun g => by
          obtain ⟨⟨⟨g1, g2⟩, g3⟩, hg⟩ := g
          have h2 : g2 = 1 := (hmem _).1 hg
          subst h2
          rfl
        right_inv := fun _ => rfl }
  rw [this, Nat.card_prod, Group.card_H, Nat.card_eq_fintype_card, Fintype.card_units_int]
  ring

theorem coprime_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    Nat.Coprime p (2 ^ (e + 2)) :=
  Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

end EFG

open EFG

theorem hostEFGTwo_of (hI : HostInertia) (hD : HostDecomp) : HostEFGTwo := by
  intro e q d hh L _ _ ζ a b h
  have hqd := hh.toHypOdd
  obtain ⟨hEgal, hfin, hmulE, hbijE⟩ := hostGalois e q d hqd L ζ a b h
  have := hEgal
  have : IsGaloisGroup Gal(hostE ζ a b/ℚ) ℤ (𝓞 (hostE ζ a b)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostE ζ a b)
  have := Formalism.FrobeniusOrbits.EFG.two_isPrime
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(2 : ℤ)}).primesOver (𝓞 (hostE ζ a b))) :=
    inferInstance
  have hcardG : Nat.card Gal(hostE ζ a b/ℚ) = 2 ^ (e + 2) := by
    rw [IsGalois.card_aut_eq_finrank, hfin]

  have hIn : Nat.card (P.inertia Gal(hostE ζ a b/ℚ)) = 2 ^ e := by
    rw [← card_trivial_first_component e]
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbijE) (fun σ => ?_))
    rw [AddSubgroup.mem_inertia]
    exact (hI e q d hh L ζ a b h σ).1 P
  have heE : (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (hostE ζ a b)) = 2 ^ e := by
    rw [← card_inertia_eq_ramificationIdxIn (G := Gal(hostE ζ a b/ℚ)) (span {(2 : ℤ)}) P, hIn]

  have hq2 : q ≠ 2 := by have := hh.2.2.1; omega
  have hd2 : d ≠ 2 := by have := hh.2.2.2.1; omega
  have hDec := fun σ => hD e q d hh L ζ a b h
    (ZMod.unitOfCoprime q (coprime_two_pow hh.1 hq2 e))
    (ZMod.unitOfCoprime d (coprime_two_pow hh.2.1 hd2 e))
    (ZMod.coe_unitOfCoprime _ _) (ZMod.coe_unitOfCoprime _ _) σ
  have hStab : Nat.card (MulAction.stabilizer Gal(hostE ζ a b/ℚ) P) = 2 ^ (e + 1) := by
    rw [← card_Psi e]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbijE) (fun σ => (hDec σ).1 P))
  have hfE : (span {(2 : ℤ)}).inertiaDegIn (𝓞 (hostE ζ a b)) = 2 := by
    have := card_stabilizer_eq (G := Gal(hostE ζ a b/ℚ)) (span {(2 : ℤ)}) P
    rw [hStab, heE, pow_succ] at this
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm
  have hgE : (primesOver (span {(2 : ℤ)}) (𝓞 (hostE ζ a b))).ncard = 2 := by
    have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(2 : ℤ)})
      (𝓞 (hostE ζ a b)) Gal(hostE ζ a b/ℚ)
    rw [heE, hfE, hcardG, show 2 ^ (e + 2) = 2 * (2 ^ e * 2) by ring] at this
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this

  have hcomm : IsMulCommutative Gal(hostE ζ a b/ℚ) :=
    ⟨⟨fun σ τ => hbijE.1 (by rw [hmulE, hmulE, mul_comm])⟩⟩
  have hAb : IsAbelianGalois ℚ (hostE ζ a b) := {}
  have hFab : IsAbelianGalois ℚ (hostF ζ a b) :=
    IsAbelianGalois.tower_bot ℚ (hostF ζ a b) (hostE ζ a b)
  have : IsGaloisGroup Gal(hostF ζ a b/ℚ) ℤ (𝓞 (hostF ζ a b)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ (hostF ζ a b)
  obtain ⟨hFfin, hFmem⟩ :=
    hostReal_of hostGalois hostGalSpec (hostConj_of hostGalois hostGalSpec) e q d hqd L ζ a b h
  have hcardF : Nat.card Gal(hostF ζ a b/ℚ) = 2 ^ (e + 1) := by
    rw [IsGalois.card_aut_eq_finrank, hFfin]
  obtain ⟨-, σc, -, -, hσc, -⟩ := ConjReal.conj_main hostGalois hostGalSpec hqd h
  have hσcP : σc • P ≠ P := by
    intro heq
    have hmem : σc ∈ MulAction.stabilizer Gal(hostE ζ a b/ℚ) P := heq
    rw [(hDec σc).1 P, hσc] at hmem
    exact (hostGroup e).2.2.1 hmem
  have hfixF : ∀ x : 𝓞 (hostF ζ a b),
      σc • (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)) x) =
        algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)) x := by
    intro x
    apply RingOfIntegers.coe_injective
    have hx : (((x : hostF ζ a b) : hostE ζ a b)) ∈ hostF ζ a b := (x : hostF ζ a b).2
    exact ((hFmem _).1.1 hx) σc hσc
  let PF := P.under (𝓞 (hostF ζ a b))
  have hσcPl : (σc • P).LiesOver PF := by
    constructor
    ext x
    show x ∈ P.under (𝓞 (hostF ζ a b)) ↔ _
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_eq_iff.mpr (hfixF x).symm]
  have hgF : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard = 1 := by
    have ht := ncard_primesOver_mul_ncard_primesOver (A := ℤ) (p := span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ) (𝓞 (hostE ζ a b))
      Gal(hostE ζ a b/ℚ)
    rw [hgE] at ht
    have hne : (PF.primesOver (𝓞 (hostE ζ a b))).ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at ht; exact absurd ht (by norm_num)
    have h2le : 2 ≤ (PF.primesOver (𝓞 (hostE ζ a b))).ncard := by
      have hsub : ({P, σc • P} : Set (Ideal (𝓞 (hostE ζ a b)))) ⊆
          PF.primesOver (𝓞 (hostE ζ a b)) := by
        intro I hI
        rcases hI with rfl | rfl
        · exact ⟨hPp, inferInstance⟩
        · exact ⟨inferInstance, hσcPl⟩
      calc 2 = ({P, σc • P} : Set (Ideal (𝓞 (hostE ζ a b)))).ncard :=
            (Set.ncard_pair hσcP.symm).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero hne)
    have hF0 : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard ≠ 0 := by
      intro h0; rw [h0, zero_mul] at ht; exact absurd ht (by norm_num)
    have hF1 : (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard ≤ 1 := by
      by_contra hc
      have hc' := not_le.mp hc
      nlinarith
    omega

  have hte := Ideal.ramificationIdx_tower (R := ℤ) PF P
  have htf := Ideal.inertiaDeg_tower (R := ℤ) PF P
  have heF0 := ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ)
  have hfF0 := inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) PF Gal(hostF ζ a b/ℚ)
  have heE0 := ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(hostE ζ a b/ℚ)
  have hfE0 := inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(hostE ζ a b/ℚ)
  have hfundF := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(2 : ℤ)})
    (𝓞 (hostF ζ a b)) Gal(hostF ζ a b/ℚ)
  rw [hgF, hcardF, one_mul, heF0, hfF0] at hfundF
  rw [← heE0, heE] at hte
  rw [← hfE0, hfE] at htf
  have hpos : PF.ramificationIdx ℤ * PF.inertiaDeg ℤ ≠ 0 := by
    rw [hfundF]; positivity
  have hprod : P.ramificationIdx (𝓞 (hostF ζ a b)) * P.inertiaDeg (𝓞 (hostF ζ a b)) = 1 := by
    have : PF.ramificationIdx ℤ * PF.inertiaDeg ℤ * 1 = PF.ramificationIdx ℤ * PF.inertiaDeg ℤ *
        (P.ramificationIdx (𝓞 (hostF ζ a b)) * P.inertiaDeg (𝓞 (hostF ζ a b))) := by
      rw [mul_one]
      calc PF.ramificationIdx ℤ * PF.inertiaDeg ℤ = 2 ^ e * 2 := by rw [hfundF, pow_succ]
        _ = (PF.ramificationIdx ℤ * P.ramificationIdx (𝓞 (hostF ζ a b))) *
            (PF.inertiaDeg ℤ * P.inertiaDeg (𝓞 (hostF ζ a b))) := by rw [← hte, ← htf]
        _ = _ := by ring
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) this).symm
  have he1 := Nat.eq_one_of_mul_eq_one_right hprod
  have hf1 := Nat.eq_one_of_mul_eq_one_left hprod
  rw [he1, mul_one] at hte
  rw [hf1, mul_one] at htf
  exact ⟨heE, hfE, hgE, hgF, heF0.trans hte.symm, hfF0.trans htf.symm⟩

end Formalism.FrobeniusOrbits
end
end

-- bundled from Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits
section
open Polynomial

noncomputable section

namespace Formalism.FrobeniusOrbits

namespace Orbits

lemma prim_bound {E K : Type*} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] [Algebra E K]
    [IsScalarTower ℚ E K] [FiniteDimensional ℚ E] [FiniteDimensional E K] (g : ℕ) (hg : g.Prime)
    (μ : K) (hμ : IsPrimitiveRoot μ g) :
    g - 1 ≤ Module.finrank ℚ E * Module.finrank E K := by
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : CharZero K := by
    first
    | exact algebraRat.charZero K
    | exact (algebraMap ℚ K).charZero
  rw [Module.finrank_mul_finrank ℚ E K]
  have hint : IsIntegral ℚ μ := .of_finite ℚ μ
  have h1 : Module.finrank ℚ (IntermediateField.adjoin ℚ {μ}) = g - 1 := by
    haveI : NeZero g := ⟨hg.ne_zero⟩
    have hroot : aeval μ (cyclotomic g ℚ) = 0 := by
      rw [aeval_def, ← eval_map, map_cyclotomic]
      exact (isRoot_cyclotomic_iff.mpr hμ)
    rw [IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic
      (cyclotomic.irreducible_rat hg.pos) hroot (cyclotomic.monic g ℚ),
      natDegree_cyclotomic, Nat.totient_prime hg]
  rw [← h1, ← (letI : Module.Free (IntermediateField.adjoin ℚ {μ}) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {μ}) K)]
  exact Nat.le_mul_of_pos_right _ Module.finrank_pos

lemma dim_bound {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (k g : ℕ) (hg : g.Prime) (M : Matrix (Fin k) (Fin k) E) (hM : M ^ g = 1) (hne : M ≠ 1) :
    g - 1 ≤ Module.finrank ℚ E * k := by
  classical
  haveI := Fact.mk hg
  have hint : IsIntegral E M := IsIntegral.of_finite E M
  have hm0 : minpoly E M ≠ 0 := minpoly.ne_zero hint
  have hmk : (minpoly E M).natDegree ≤ k := by
    have h1 : minpoly E M ∣ M.charpoly := minpoly.dvd E M (Matrix.aeval_self_charpoly M)
    have h2 := natDegree_le_of_dvd h1 M.charpoly_monic.ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  have hfac : (X ^ g - 1 : E[X]) = (X - 1) * cyclotomic g E := by
    rw [mul_comm, cyclotomic_prime_mul_X_sub_one]
  have hdvd : minpoly E M ∣ (X - 1) * cyclotomic g E := by
    rw [← hfac]
    apply minpoly.dvd
    simp [hM]
  have hnd : ¬ minpoly E M ∣ X - 1 := by
    rintro ⟨q, hq⟩
    apply hne
    have h0 : aeval M (X - 1 : E[X]) = 0 := by rw [hq, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h0
  obtain ⟨f, hf, hfm, hfΦ⟩ : ∃ f : E[X], Irreducible f ∧ f ∣ minpoly E M ∧ f ∣ cyclotomic g E := by
    by_contra hcon
    push_neg at hcon
    have hcop : IsCoprime (minpoly E M) (cyclotomic g E) :=
      isCoprime_of_irreducible_dvd (fun h => hm0 h.1) (fun z hz hzm hzΦ => hcon z hz hzm hzΦ)
    exact hnd (hcop.dvd_of_dvd_mul_right hdvd)
  have hfk : f.natDegree ≤ k := (natDegree_le_of_dvd hfm hm0).trans hmk
  haveI : Fact (Irreducible f) := ⟨hf⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  haveI : FiniteDimensional E (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have hrank : Module.finrank E (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim]
  haveI : CharZero (AdjoinRoot f) := by
    first
    | exact algebraRat.charZero (AdjoinRoot f)
    | exact (algebraMap ℚ (AdjoinRoot f)).charZero
  haveI : NeZero g := ⟨hg.ne_zero⟩
  have hμ : IsPrimitiveRoot (AdjoinRoot.root f) g := by
    rw [← isRoot_cyclotomic_iff, ← map_cyclotomic g (algebraMap E (AdjoinRoot f)), IsRoot, eval_map]
    obtain ⟨q, hq⟩ := hfΦ
    rw [hq, eval₂_mul, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, zero_mul]
  have hb := prim_bound (E := E) (K := AdjoinRoot f) g hg _ hμ
  rw [hrank] at hb
  exact hb.trans (Nat.mul_le_mul_left _ hfk)

end Orbits

open Orbits

theorem hostOrbitsPlaces : HostOrbitsPlaces := by
  unfold HostOrbitsPlaces
  intro e φ hφ τ hτ i
  have hτ2 : τ.1.2 = 1 := by simpa [Psi, chD] using hτ
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Nat.even_or_odd i with hi | hi
  · have hc : φ.1 ^ i = 1 := by
      rcases hφ with h | h
      · rw [h, c0]; ext <;> simp [hi.neg_one_pow]
      · rw [h]; ext <;> simp [hi.neg_one_pow]
    have hp : placeOf (φ ^ i * τ) = φ ^ i * τ := by
      unfold placeOf
      rw [if_pos]
      simp [Prod.pow_fst, hc, hτ2]
    rw [hp]
    refine ⟨by simp, fun _ => by simp [hc], fun _ => by simp [hc, hi]⟩
  · have hp : placeOf (φ ^ i * τ) = cc e * (φ ^ i * τ) := by
      unfold placeOf
      rw [if_neg]
      rcases hφ with h | h
      · simp [h, c0, hi.neg_one_pow, hτ2, hne]
      · simp [h, hi.neg_one_pow, hτ2, hne]
    rw [hp]
    refine ⟨by simp [cc], fun h => ?_, fun h => ?_⟩
    · ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2]
    · have hni : ¬ Even i := Nat.not_even_iff_odd.mpr hi
      ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2, hni, sg]

theorem hostOrbitCount : HostOrbitCount := by
  unfold HostOrbitCount
  intro e φ h0 τ hτ
  have hpl : ∀ i : ℕ, placeOf (φ ^ i * τ) = (τ.1, φ.2 ^ i * τ.2) := by
    intro i
    obtain ⟨h2, h1, -⟩ := hostOrbitsPlaces e φ (Or.inl h0) τ hτ i
    exact Prod.ext (h1 h0) h2
  have hr : (Set.range fun i : ℕ => placeOf (φ ^ i * τ)) =
      (fun x : HGrp e => ((τ.1, x * τ.2) : GG e)) '' Set.range (fun i : ℕ => φ.2 ^ i) := by
    ext y
    simp [hpl]
  rw [hr, Set.ncard_image_of_injective _ (fun x y hxy => by simpa using hxy)]
  rw [show Set.range (fun i : ℕ => φ.2 ^ i) = (Submonoid.powers φ.2 : Set (HGrp e)) from
    (Submonoid.coe_powers φ.2).symm, ← Nat.card_coe_set_eq]
  exact Nat.card_submonoidPowers

theorem hostFiniteOrder : HostFiniteOrder := by
  unfold HostFiniteOrder
  intro e q d hqd L _ _ ζ a b h k g hg M hM hne
  have := dim_bound k g hg M hM hne
  rwa [Galois.finrank_cmField hqd h] at this

end Formalism.FrobeniusOrbits
end
end

