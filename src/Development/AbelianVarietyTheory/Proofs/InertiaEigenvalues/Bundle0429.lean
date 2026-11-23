module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
public import Formalism.SharpRestriction.LevelLetterCocycles.TWSet
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0003
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0389

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharpolyLatticeKillsSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory

theorem charpoly_split_kills_span : ∀ (O V B : Type) [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V] [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B] (e : B →ₗ[O] V) (t : Module.End O B) (T : Module.End (FractionRing O) V), (∀ x, e (t x) = T (e x)) → ((LinearMap.charpoly t).map (algebraMap O (FractionRing O))).Splits → ∃ p : (FractionRing O)[X], p ≠ 0 ∧ p.Splits ∧ ∀ x ∈ Submodule.span (FractionRing O) (Set.range e), Polynomial.aeval T p x = 0 := by
  intro O V B _ _ _ _ _ _ _ _ _ _ _ e t T he hs
  refine ⟨(LinearMap.charpoly t).map (algebraMap O (FractionRing O)), ?_, hs, ?_⟩
  · exact ((LinearMap.charpoly_monic t).map _).ne_zero
  · have hpow : ∀ (n : ℕ) (b : B), (T ^ n) (e b) = e ((t ^ n) b) := by
      intro n
      induction n with
      | zero => intro b; simp
      | succ n ih => intro b; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← he, ih]
    have key : ∀ (q : O[X]) (b : B), Polynomial.aeval T (q.map (algebraMap O (FractionRing O))) (e b) = e (Polynomial.aeval t q b) := by
      intro q b
      induction q using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq]
      | monomial n a =>
          simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, LinearMap.map_smul_of_tower]
          rw [algebraMap_smul]
    have hle : Submodule.span (FractionRing O) (Set.range e) ≤ LinearMap.ker (Polynomial.aeval T ((LinearMap.charpoly t).map (algebraMap O (FractionRing O)))) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, key, LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero]
    intro x hx
    exact hle hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeMemPadicCyclotomic
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory

theorem sqrt_neg_l_mem_adjoin_roots_of_unity :
    ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → ∀ y : Om l, y ^ 2 = -(l : Om l) →
      y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} := by
  intro l _ h4 y hy
  set K := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} with hK
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hm1 : quadraticChar (ZMod l) (-1) = -1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
  set χ := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom (Om l)) with hχdef
  have hχm1 : χ (-1) = -1 := by
    simp [χ, MulChar.ringHomComp_apply, hm1]
  have h2 : (2 : Om l) ≠ 0 := two_ne_zero
  have hχ1 : χ ≠ 1 := by
    intro h
    rw [h, MulChar.one_apply (isUnit_one.neg)] at hχm1
    apply h2; linear_combination hχm1
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod l)).comp _
  have hψ := AddChar.zmodChar_primitive_of_primitive_root l hζ
  have hsq := gaussSum_sq hχ1 hq hψ
  rw [hχm1, ZMod.card] at hsq
  set g := gaussSum χ (AddChar.zmodChar l hζ.pow_eq_one) with hg

  have hgK : g ∈ K := by
    rw [hg, gaussSum]
    refine sum_mem fun a _ => mul_mem ?_ ?_
    · rw [hχdef, MulChar.ringHomComp_apply]
      exact intCast_mem K _
    · rw [AddChar.zmodChar_apply]
      refine pow_mem (IntermediateField.subset_adjoin _ _ ?_) _
      show ζ ^ (l ^ 1) = 1
      rw [pow_one]; exact hζ.pow_eq_one

  have hyg : (y - g) * (y + g) = 0 := by
    linear_combination hy - hsq
  rcases mul_eq_zero.1 hyg with h | h
  · rw [sub_eq_zero.1 h]; exact hgK
  · rw [eq_neg_of_add_eq_zero_left h]; exact neg_mem hgK

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeNotMemMaxUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory

theorem sqrt_neg_l_not_mem_Kur : ∀ (l : ℕ) [Fact l.Prime] (y : Om l), y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l := by
  intro l _ y hy hK
  have hl1 : (1 : ℝ) < (l : ℝ) := Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖y‖ ^ 2 = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hy, norm_neg]
    exact Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hn
    have : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero hl0.ne'
    exact this (by rw [← hn]; norm_num)
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hK hy0
  rw [hk, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one] at hn
  have h := zpow_right_injective₀ hl0 hl1.ne' hn
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StructureUnramifiedAdjoinSqrtNegPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegL

open Polynomial

theorem natDegree_minpoly_sqrt (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (y : Om l)
    (hF : F ≤ MaximalUnramifiedExtension l) (hy : y ^ 2 = -(l : Om l)) (hyK : y ∉ MaximalUnramifiedExtension l) :
    (minpoly F y).natDegree = 2 := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  have hmon : (X ^ 2 + C ((l : ℕ) : F)).Monic :=
    (monic_X_pow 2).add_of_left (degree_C_le.trans_lt (by simp))
  have hdeg : (X ^ 2 + C ((l : ℕ) : F)).natDegree = 2 := by
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp
  have hev : aeval y (X ^ 2 + C ((l : ℕ) : F)) = 0 := by
    simp [hy]
  have h1 : (minpoly F y).natDegree ≤ 2 :=
    hdeg ▸ natDegree_le_natDegree (minpoly.min F y hmon hev)
  have h2 : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hint
  have h3 : (minpoly F y).natDegree ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := minpoly.natDegree_eq_one_iff.mp h
    apply hyK
    rw [← ha]
    exact hF a.2
  omega

theorem structure_sqrt_neg : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : FinExt l) (M : IntermediateField ℚ_[l] (Om l)) (y : Om l), M ≤ MaximalUnramifiedExtension l → y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} → K.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} → K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} ∧ K.1 ≤ Ks K 1 ∧ Module.finrank ↥(K0 K) ↥K.1 = 2 ∧ Module.finrank ℚ_[l] ↥(Ks K 1) = (l - 1) / 2 * Module.finrank ℚ_[l] ↥K.1 := by
  intro l _ hl2 K M y hM hy hyK hyz hK
  have hyK1 : y ∈ K.1 := hK ▸ (le_sup_right : IntermediateField.adjoin ℚ_[l] {y} ≤ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  have hMK0 : M ≤ K0 K := le_inf (hK ▸ le_sup_left) hM
  have hA : IntermediateField.adjoin ℚ_[l] {y} ≤ K.1 :=
    (IntermediateField.adjoin_simple_le_iff).2 hyK1
  have e1 : K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} :=
    le_antisymm (hK.le.trans (sup_le_sup_right hMK0 _)) (sup_le inf_le_left hA)
  have e2 : K.1 ≤ Ks K 1 := by
    rw [e1]
    exact sup_le_sup_left ((IntermediateField.adjoin_simple_le_iff).2 hyz) _
  have hd := natDegree_minpoly_sqrt l (K0 K) y inf_le_right hy hyK
  have hf : Module.finrank ℚ_[l] ↥K.1 = Module.finrank ℚ_[l] ↥(K0 K) * 2 := by
    rw [← hd, ← GlobalTheory.HubLoc.finrank_sup_adjoin, ← e1]
  have hpos := GlobalTheory.HubLoc.finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have := K.2
  have : Module.Free ↥(K0 K) ↥K.1 := Module.Free.of_divisionRing _ _
  have htow := Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥K.1
  have e3 : Module.finrank ↥(K0 K) ↥K.1 = 2 := by
    rw [hf] at htow
    exact Nat.eq_of_mul_eq_mul_left hpos htow
  refine ⟨e1, e2, e3, ?_⟩
  rw [GlobalTheory.HubLoc.finrank_Ks_eq l K 1 one_pos, hf]
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two hl2
  have hev : 2 ∣ l - 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  obtain ⟨k, hk⟩ := hev
  rw [hk]
  rw [Nat.sub_self, pow_zero, one_mul]
  rw [Nat.mul_div_cancel_left k two_pos]
  ring

end GlobalTheory.SqrtNegL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjConj
section
noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.UnivCharIne

theorem surj_conj (D : D7) {B : Type} [CommGroup B] (χ : G D.host.E D.nd.Om →* B) (hA : AntiHom D.ntw.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring D.nd.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := D.ntw.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  have hs' : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, D.ntw.cc (D.ntw.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, D.ntw.cc.symm x = D.ntw.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap D.ntw.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap D.ntw.cc.symm.toRingHom).comap D.ntw.cc.symm.toRingHom = A := by
    ext y
    show D.ntw.cc.symm (D.ntw.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

theorem delU_ine : ∀ D : D7, GlobalTheory.UnivChar.IsUnivChar D.nexp → (∀ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ D.ntw i Q M → ∀ P (hP : P ∈ Q), (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩) ∧ ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' → ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ = 0) := by
  intro D hU i Q M hQ P hP
  obtain ⟨-, hQ'⟩ := hQ
  have hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q := fun P hP P' h => by
    obtain ⟨⟨P'', hP'', h''⟩, -⟩ := hQ' P hP
    rwa [GlobalTheory.GalChar.isConjPl_unique h h'']
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hQ' P hP
  have hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
    obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
    exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
  have hDel : GlobalTheory.GalChar.IsDel D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun v hv => h4 v (fun e => hv (Or.inl e)) (fun e => hv (Or.inr e)), fun v hv A hA b => ?_⟩
    rcases hv with rfl | hv
    · exact hsP A hA b
    · exact surj_conj D χ h2 hv hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host D.ntw.cc (D.ntw.l i) ⟨χ, hDel⟩
  have e : ∀ σ, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ =
      Multiplicative.toAdd (GlobalTheory.GalChar.delOf D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) σ) := by
    intro σ
    rw [hU]
    exact (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.2.2.1 Q M hcl P hP σ
  refine ⟨fun A hA x => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩
  · obtain ⟨σ, hσ, hx⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)
    exact ⟨⟨σ, hσ⟩, by simp only [e, hx, toAdd_ofAdd]⟩
  · rw [e, hD.2.2.2.1 P' (by rintro (h | h); exacts [hne h, hnc h]) A hA σ hσ]
    rfl

end GlobalTheory.UnivCharIne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedLift
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.TameFixedLift

open Pointwise

theorem transfer {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hfix : ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) :
    ∃ g ∈ Ine (F := E) A, cycZ (F := E) (Ω := Ω) l g = cycZ (F := ℚ) (Ω := Ω) l σ := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) hfix, ⟨?_, hσ.2⟩, rfl⟩
  have h : σ • A = A := hσ.1
  exact h

theorem root_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (σ : G ℚ Ω) (u : ℤ_[l])
    (h : ((cycZ (F := ℚ) (Ω := Ω) l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u)
    (t : Ω) (ht : t ^ l ^ n = 1) : σ t = t := by
  have : CharZero Ω := algebraRat.charZero Ω
  have : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Ω) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero i (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec l (n := n) (σ : Ω ≃+* Ω) t ht
  have h2 : ((cyclotomicCharacter Ω l (σ : Ω ≃+* Ω) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u := h
  have h3 : PadicInt.toZModPow n ((l : ℤ_[l]) ^ n) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]; exact Ideal.mem_span_singleton_self _
  rw [h2, map_add (f := _), map_mul, h3, zero_mul, add_zero, map_one] at h1
  have h4 : t ^ (1 : ZMod (l ^ n)).val = t := by
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 ht, pow_one]
  rw [h4] at h1
  exact h1

theorem exists_place (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ w, w ∈ placesOver E l := by
  have hl : l.Prime := Fact.out
  have hnu : Ideal.span {(l : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    rcases Nat.pow_eq_one.mp h1 with h2 | h2
    · exact hl.one_lt.ne' h2
    · exact Module.finrank_pos.ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hmem : (l : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hl.ne_zero (by exact_mod_cast hmem)

private theorem eq_one_of_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hc : Nat.Coprime m l) {z : Ω} (hz : z ^ m = 1)
    (h1 : A.valuation (z - 1) < 1) : z = 1 := by
  by_contra hne
  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have hz1 : A.valuation z ≤ 1 := by
    have := Valuation.map_add_le A.valuation h1.le (le_of_eq (map_one A.valuation))
    simpa using this
  have hp : ∀ i : ℕ, A.valuation (z ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show z ^ (i + 1) - 1 = (z ^ i - 1) * z + (z - 1) by ring]
      refine Valuation.map_add_lt _ ?_ h1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hz1) ih
  have hs : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := mul_geom_sum z m
    rw [hz, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hm : A.valuation (m : Ω) < 1 := by
    have h2 : A.valuation (∑ i ∈ Finset.range m, (z ^ i - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun i _ => hp i
    rw [Finset.sum_sub_distrib, hs] at h2
    simpa using h2
  have hb : (1 : Ω) = (m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω) := by
    have h3 := Nat.gcd_eq_gcd_ab m l
    rw [hc.gcd_eq_one] at h3
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) h3
  have h4 : A.valuation ((m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hm
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hA
  rw [← hb, map_one] at h4
  exact lt_irrefl _ h4

private theorem tame_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hm : m ≠ 0) (hc : Nat.Coprime m l) (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (z : Ω) (hz : z ^ m = 1) : σ z = z := by
  have hv : A.valuation z = 1 := by
    have := congrArg A.valuation hz
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hm).mp this
  have hz0 : z ≠ 0 := by rintro rfl; simp at hv
  have h3 : A.valuation (σ z - z) < 1 := hσ.2 z hv.le
  have h4 : σ z / z = 1 := eq_one_of_cong A hA hc
    (by rw [div_pow, ← map_pow, hz, map_one, div_one]) (by
      rw [show σ z / z - 1 = (σ z - z) / z by field_simp, map_div₀, hv, div_one]
      exact h3)
  exact (div_eq_one_iff_eq hz0).mp h4

private theorem loc_fix {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime) (hA : A.valuation (l : Ω) < 1)
    (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hroot : ∀ t : Ω, t ^ l ^ H.condN.factorization l = 1 → σ t = t) (x : H.E) :
    σ (algebraMap H.E Ω x) = algebraMap H.E Ω x := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  refine H.image_mem_of_roots (algebraMap H.E Ω) (RingHom.eqLocusField (σ : Ω →+* Ω) (RingHom.id Ω))
    (fun y hy => ?_) x
  show σ y = y
  have hy0 : y ≠ 0 := by rintro rfl; simp [hN] at hy
  have hmul := Nat.ordProj_mul_ordCompl_eq_self H.condN l
  have hco : Nat.Coprime l (ordCompl[l] H.condN) := Nat.coprime_ordCompl hl hN
  have h1 := hroot (y ^ ordCompl[l] H.condN) (by rw [← pow_mul, mul_comm, hmul, hy])
  have h2 := tame_fix A hA (Nat.ordCompl_pos l hN).ne' hco.symm σ hσ (y ^ ordProj[l] H.condN)
    (by rw [← pow_mul, hmul, hy])
  rw [map_pow] at h1 h2
  have h3 : (σ y / y) ^ Nat.gcd (ordProj[l] H.condN) (ordCompl[l] H.condN) = 1 :=
    pow_gcd_eq_one.2 ⟨by rw [div_pow, h2, div_self (pow_ne_zero _ hy0)],
      by rw [div_pow, h1, div_self (pow_ne_zero _ hy0)]⟩
  rw [(Nat.Coprime.pow_left _ hco).gcd_eq_one, pow_one] at h3
  exact (div_eq_one_iff_eq hy0).mp h3

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) , ∃ w ∈ placesOver H.E (N.l i), ∀ u : ℤ_[N.l i], ∃ g ∈ Ine (F := H.E) (N.plOm.1 w), ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) = 1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by
  intro R H what₂ N i
  obtain ⟨w, hw⟩ := exists_place H.E (N.l i)
  refine ⟨w, hw, fun u => ?_⟩
  have : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap H.E N.Om).injective
  have : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed H.E
  have : IsScalarTower ℚ H.E N.Om := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : IsAlgClosure ℚ N.Om := IsAlgClosure.ofAlgebraic ℚ H.E N.Om
  have hA : (N.plOm.1 w).valuation (N.l i : N.Om) < 1 := by
    have := (N.plOm.2 w (N.l i : 𝓞 H.E)).2 hw
    simpa using this
  have hs : 1 ≤ N.s0 i := UpperTheory.KStar.S0.one_le_localLevel N i
  have hunit : IsUnit (1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u) := by
    have hm : -((N.l i : ℤ_[N.l i]) ^ N.s0 i * u) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
      rw [PadicInt.maximalIdeal_eq_span_p, neg_mem_iff, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm
    simpa using this
  obtain ⟨σ, hσ, hv⟩ := GlobalTheory.T.cyclotomicChar_inertia_surjective N.Om (N.l i) (N.plOm.1 w) hA hunit.unit
  have hv' : ((cycZ (F := ℚ) (Ω := N.Om) (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by rw [hv]; rfl
  obtain ⟨k, hk⟩ := pow_dvd_pow (N.l i) (UpperTheory.KStar.S0.factorization_conductor_le_localLevel N i)
  obtain ⟨g, hg, hc⟩ := transfer (E := H.E) (N.plOm.1 w) (N.l i) σ hσ
    (loc_fix H _ (N.lPrime i).out hA σ hσ fun t ht =>
      root_fix (N.l i) (N.s0 i) σ u hv' t (by rw [hk, pow_mul, ht, one_pow]))
  exact ⟨g, hg, by rw [hc, hv']⟩

end GlobalTheory.TameFixedLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocycles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem tateDuality_degreeOne_cocycles : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1)) ∧ (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 A.ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 A'.ρ := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_rational_tatePairing_bilinear hT l P K LL O hO A A' m hm
  have hflip : IsDual1 (P.PD K) A'.ρ A.ρ m.flip :=
    ⟨fun g x y => hm.1 g y x, hm.2.2.1, hm.2.1, hm.2.2.2.symm⟩
  have hanti := GlobalTheory.T.cup_one_cocycles_anticomm_up_to_coboundary l P K LL O hO A A' m hm
  refine ⟨β, hβ, fun a => ⟨fun h => ?_, fun ha b => ?_⟩, fun b => ⟨fun h => ?_, fun hb a => ?_⟩⟩
  · refine GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal hT l P K LL O hO A' A m.flip hflip a.1 a.2 (fun b hb => ?_)
    exact ((hanti a.1 a.2 b hb).1).1 ((hβ a ⟨b, hb⟩).1 (h ⟨b, hb⟩))
  · exact (hβ a b).2 ((hanti a.1 a.2 b.1 b.2).2 (Or.inl ha))
  · exact GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal hT l P K LL O hO A A' m hm b.1 b.2
      (fun a ha => (hβ ⟨a, ha⟩ b).1 (h ⟨a, ha⟩))
  · exact (hβ a b).2 ((hanti a.1 a.2 b.1 b.2).2 (Or.inr hb))

end GlobalTheory
end

