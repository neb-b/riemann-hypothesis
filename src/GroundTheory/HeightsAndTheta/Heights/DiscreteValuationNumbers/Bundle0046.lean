module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI

universe u

theorem mem_minimalPrimes_of_locCycle_ne_zero' {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dite_eq_right hc])

theorem LocalCoeffLocal.proof (h₁ : LocCycleSpanMul.Statement.{u}) (h₂ : LocCyclePos.Statement.{u})
    (h₃ : MinimalPrimesSpanSingleton.Statement.{u}) (h₄ : LocalDomainDimTwo.Statement.{u})
    (h₅ : DimTwoSumReading.Statement.{u}) : LocalCoeffLocal.Statement.{u} := by
  intro A _ _ _ _ hchain f g s u v hf hg hs hu huv hno

  have hv : v ≠ 0 := by
    rintro rfl
    rw [zero_mul] at huv
    exact hf ((IsUnit.mul_right_eq_zero hu).mp huv)
  have hspan : Ideal.span {f} = Ideal.span {v * g} := by
    rw [← huv]
    exact (Ideal.span_singleton_mul_left_unit hu f).symm
  have hcolon : (Ideal.span {f}).colon {g} = Ideal.span {v} := by
    ext x
    rw [hspan, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton, mul_dvd_mul_iff_right hg]
  have hadd : ∀ W : Ideal A, locCycle (Ideal.span {f}) W =
      locCycle (Ideal.span {v}) W + locCycle (Ideal.span {g}) W := by
    intro W
    rw [hspan]
    exact h₁ A v g hv hg W

  have hmin1 : ∀ x : A, x ≠ 0 → ∀ W : Ideal A, locCycle (Ideal.span {x}) W ≠ 0 →
      W.IsPrime ∧ W.height = 1 ∧ x ∈ W :=
    fun x hx W h => (h₃ A x hx W).mp (mem_minimalPrimes_of_locCycle_ne_zero' h)
  have hpos : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, p.IsPrime → p.height = 1 → x ∈ p →
      locCycle (Ideal.span {x}) p ≠ 0 :=
    fun x hx p hp h1 hxp => (h₂ A _ p ((h₃ A x hx p).mpr ⟨hp, h1, hxp⟩)).ne'

  have nb : ∀ p : Ideal A, p.IsPrime → p.height = 1 → v ∈ p → s ∉ p := by
    intro p hp h1 hvp hsp
    have e := hno p (hpos s hs p hp h1 hsp)
    rw [hadd] at e
    exact hpos v hv p hp h1 hvp (by omega)
  have hne : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, x ∈ p → p ≠ ⊥ :=
    fun x hx p hxp h => hx (by rw [h] at hxp; exact (Submodule.mem_bot A).mp hxp)
  have hL : ∀ G : Ideal A, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
      locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      locCycle (Ideal.span {v}) G * locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) := by
    intro G
    rw [hadd]
    ring
  rw [finsum_congr hL, hcolon]
  by_cases hQ : ∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A
  ·
    obtain ⟨hd, -, hht⟩ := h₄ A hchain hQ
    obtain ⟨n₁, e₁, e₁'⟩ := h₅ A hd v s hv nb
    obtain ⟨n₂, e₂, e₂'⟩ := h₅ A hd s v hs (fun p hp h1 hsp hvp => nb p hp h1 hvp hsp)
    have hlen : Module.length A (A ⧸ Ideal.span {v, s}) ≠ ⊤ := by
      by_cases hvs : Ideal.span {v, s} = ⊤
      · have : Subsingleton (A ⧸ Ideal.span {v, s}) := Ideal.Quotient.subsingleton_iff.mpr hvs
        rw [Module.length_eq_zero]
        exact ENat.zero_ne_top
      · have hvm : v ∈ Ideal.span {v, s} := Ideal.subset_span (Set.mem_insert _ _)
        have hsm : s ∈ Ideal.span {v, s} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
        have hI : IsLocalRing.maximalIdeal A ∈ (Ideal.span {v, s}).minimalPrimes := by
          refine ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hvs⟩, fun Q hQ' hQm => ?_⟩
          obtain ⟨hQp, hQI⟩ := hQ'
          by_contra hmQ
          have hlt : Q < IsLocalRing.maximalIdeal A := lt_of_le_of_ne hQm fun h => hmQ h.ge
          have h0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr (hne v hv Q (hQI hvm))
          exact nb Q hQp (hht Q hQp h0 hlt) (hQI hvm) (hQI hsm)
        have : IsArtinianRing (A ⧸ Ideal.span {v, s}) :=
          IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
        have : IsArtinian A (A ⧸ Ideal.span {v, s}) :=
          isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := Ideal.span {v, s}))
        exact Module.length_ne_top
    have key := (lengthFormulaDimTwo A v s hd hv hs hlen).2.2
    rw [e₁', e₂'] at key
    rw [e₁, e₂, Nat.cast_inj.mp key]
  ·
    have hQ' : ∀ Q : Ideal A, Q.IsPrime → Q ≠ ⊥ → Q = IsLocalRing.maximalIdeal A := by
      intro Q hQp h0
      by_contra hQm
      exact hQ ⟨Q, hQp, bot_lt_iff_ne_bot.mpr h0,
        lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQp.ne_top) hQm⟩
    have zl : ∀ G : Ideal A, locCycle (Ideal.span {v}) G *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) = 0 := by
      intro G
      by_contra h
      obtain ⟨hGp, hG1, hvG⟩ := hmin1 v hv G (left_ne_zero_of_mul h)
      have hGm := hQ' G hGp (hne v hv G hvG)
      have hsG : s ∈ G := by
        have h' := (mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2
        rw [← hGm] at h'
        exact h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
      exact nb G hGp hG1 hvG hsG
    have zr : ∀ W : Ideal A, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ Ideal.span {v}) (IsLocalRing.maximalIdeal A) = 0 := by
      intro W
      by_contra h
      obtain ⟨hWp, hW1, hsW⟩ := hmin1 s hs W (left_ne_zero_of_mul h)
      have hWm := hQ' W hWp (hne s hs W hsW)
      have hvW : v ∈ W := by
        have h' := (mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2
        rw [← hWm] at h'
        exact h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self v))
      exact nb W hWp hW1 hvW hsW
    rw [(finsum_congr zl).trans finsum_zero, (finsum_congr zr).trans finsum_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalDomainDimTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem enat_eq_two_of_le_of_lt {x : ℕ∞} (h2 : 2 ≤ x) (h3 : x < 3) : x = 2 := by
  induction x using ENat.recTopCoe with
  | top => exact absurd h3 (by simp)
  | coe n =>
    have a : 2 ≤ n := by exact_mod_cast h2
    have b : n < 3 := by exact_mod_cast h3
    have : n = 2 := by omega
    subst this; rfl

private theorem enat_le_one_of_add_one_le_two {x : ℕ∞} (h : x + 1 ≤ 2) : x ≤ 1 := by
  induction x using ENat.recTopCoe with
  | top => exact absurd h (by simp)
  | coe n =>
    have : n + 1 ≤ 2 := by exact_mod_cast h
    exact_mod_cast (by omega : n ≤ 1)

theorem LocalDomainDimTwo.proof : LocalDomainDimTwo.Statement := by
  intro A _ _ _ _ hno hQ
  obtain ⟨Q, hQp, h0, hQm⟩ := hQ
  have := hQp
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hQm
  have hm2 : (2 : ℕ∞) ≤ (IsLocalRing.maximalIdeal A).height :=
    le_trans (by rw [← one_add_one_eq_two]; exact add_le_add (le_trans le_add_self e1) le_rfl) e2
  have hm3 : (IsLocalRing.maximalIdeal A).height < 3 := by
    by_contra h3
    have hle : ((3 : ℕ) : ℕ∞) ≤ Order.height (IsLocalRing.closedPoint A) := by
      rw [← PrimeSpectrum.height_eq_orderHeight]
      exact not_lt.mp h3
    obtain ⟨p, hlast, hlen⟩ := Order.exists_series_of_le_height _ hle
    have s0 := p.step ⟨0, by omega⟩
    have s1 := p.step ⟨1, by omega⟩
    have s2 := p.step ⟨2, by omega⟩
    have e01 : (Fin.succ (⟨0, by omega⟩ : Fin p.length)) = Fin.castSucc ⟨1, by omega⟩ := Fin.ext rfl
    have e12 : (Fin.succ (⟨1, by omega⟩ : Fin p.length)) = Fin.castSucc ⟨2, by omega⟩ := Fin.ext rfl
    have e2l : (Fin.succ (⟨2, by omega⟩ : Fin p.length)) = Fin.last p.length := Fin.ext (by simp [hlen])
    rw [e01] at s0
    rw [e12] at s1
    rw [e2l] at s2
    have hl : p.toFun (Fin.last p.length) = IsLocalRing.closedPoint A := hlast
    rw [hl] at s2
    refine hno (p.toFun (Fin.castSucc ⟨1, by omega⟩)).asIdeal (p.toFun (Fin.castSucc ⟨2, by omega⟩)).asIdeal
      (p.toFun _).isPrime (p.toFun _).isPrime ?_ ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s1)
      ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s2)
    exact lt_of_le_of_lt bot_le ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s0)
  have hm : (IsLocalRing.maximalIdeal A).height = 2 := enat_eq_two_of_le_of_lt hm2 hm3
  refine ⟨?_, hm, ?_⟩
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hm]
    rfl
  · intro Q' hQ' h0' hQm'
    have := hQ'
    have f1 := Ideal.height_add_one_le_of_lt_of_isPrime h0'
    have f2 := Ideal.height_add_one_le_of_lt_of_isPrime hQm'
    rw [hm] at f2
    exact le_antisymm (enat_le_one_of_add_one_le_two f2) (le_trans le_add_self f1)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalizedQuotLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem length_self_eq_of_ringEquiv' {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this

private theorem length_localizedModule_quot' {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem LocalizedQuotLength.proof : LocalizedQuotLength.Statement.{u} := by
  intro S _ P W₀ _ z
  set W := W₀.comap (Ideal.Quotient.mk P) with hWdef
  set A := Localization.AtPrime W₀
  set J := P ⊔ Ideal.span {z} with hJdef
  let ψ : Localization.AtPrime W →+* A := Localization.localRingHom W W₀ (Ideal.Quotient.mk P) rfl

  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective W₀.primeCompl x
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨t', ht'⟩ := Ideal.Quotient.mk_surjective (t : S ⧸ P)
    have hs : t' ∈ W.primeCompl := by
      intro h
      apply t.2
      rw [← ht']
      exact h
    refine ⟨IsLocalization.mk' _ a' ⟨t', hs⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht'

  have hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap S (Localization.AtPrime W)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htr⟩ := hx
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    have ht'W : t' ∈ W.primeCompl := ht
    have hmemP : t' * r ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact htr
    have hrJ : algebraMap S (Localization.AtPrime W) r ∈ J.map (algebraMap S (Localization.AtPrime W)) := by
      rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, ht'W⟩),
        ← map_mul]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hmemP)
    show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hrJ

  have hcomp : ψ.comp (algebraMap S (Localization.AtPrime W)) =
      (algebraMap (S ⧸ P) A).comp (Ideal.Quotient.mk P) :=
    RingHom.ext fun x => Localization.localRingHom_to_map W W₀ (Ideal.Quotient.mk P) rfl x
  have hJmk : J.map (Ideal.Quotient.mk P) = Ideal.span {Ideal.Quotient.mk P z} := by
    rw [hJdef, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  have hI : (J.map (algebraMap S (Localization.AtPrime W))).map ψ =
      Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)} := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hJmk, Ideal.map_span, Set.image_singleton]
  let : CommRing A := inferInstance
  let g := (Ideal.Quotient.mk (Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)})).comp ψ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hψ
  have hgk : J.map (algebraMap S (Localization.AtPrime W)) = RingHom.ker g := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]
  have key := length_self_eq_of_ringEquiv'
    ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [length_localizedModule_quot', key]
  exact (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialLocalizedLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IsLocalRing

universe u

theorem length_localizedModule_quotient_eq {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

theorem comap_C_map_C_polynomial {R : Type*} [CommRing R] (p : Ideal R) :
    (p.map (Polynomial.C : R →+* Polynomial R)).comap (Polynomial.C : R →+* Polynomial R) = p := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h n
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem

theorem PolynomialLocalizedLength.full : PolynomialLocalizedLength.Statement.{u} := by
  intro R _ q _ I
  set Q := q.map (Polynomial.C : R →+* Polynomial R) with hQdef
  have : Q.LiesOver q := ⟨by
    rw [Ideal.under, Polynomial.algebraMap_eq, hQdef]
    exact (comap_C_map_C_polynomial q).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver q Q
  set A := Localization.AtPrime q
  set B := Localization.AtPrime Q
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom q Q (algebraMap R (Polynomial R))
      Ideal.LiesOver.over))
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq,
      ← hQdef, Localization.AtPrime.map_eq_maximalIdeal]
  have h1 : Module.length B (B ⧸ maximalIdeal B) = 1 := by
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have key := IsLocalRing.length_baseChange A B (A ⧸ I.map (algebraMap R A))
  rw [hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (I.map (algebraMap R A))).toLinearEquiv.length_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq R (Polynomial R) B, ← Ideal.map_map, Polynomial.algebraMap_eq] at key
  rw [length_localizedModule_quotient_eq, length_localizedModule_quotient_eq]
  exact key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (liftVar pullDeg joinCoord mcIdeal IsVertDiv)


open JoinPointVerticalDivisor in
theorem JoinVerticalDivisor.proof : JoinVerticalDivisor.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨Sum.elim α 0, Sum.elim β 0, isMultiHomog_rename hf, isMultiHomog_rename hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k)
    · simpa [pullDeg] using hb k
    · simp [pullDeg]
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O x ≤ Q.comap (rename (liftVar (ι := ι) ι')) := fun h hh =>
      Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x z h).mpr hh))
    have hO : (Q.comap (rename (liftVar (ι := ι) ι'))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (liftVar ι') u, rename (liftVar ι') v, ⟨_, isMultiHomog_rename hu⟩,
      ⟨_, isMultiHomog_rename hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O x z _).mpr huv
    simpa only [map_sub, map_mul] using this

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimQuotComapRename
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace ProjectiveBundleNumbers

theorem sum_choose_succ (n : ℕ) (U : ℕ → ℤ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℤ) * U k =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U k +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (n.choose k : ℤ) * U k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℤ) * U (k + 1)),
    Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  ring

section ProjBundle

variable {K : Type*} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section Rename

variable {F : Type} [Field F] {S : Type} [Fintype S] [DecidableEq S] {κ ι' : S → Type}
  [∀ s, Fintype (κ s)] [∀ s, Fintype (ι' s)]

end Rename

end ProjectiveBundleNumbers

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

