module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0369
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0205
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoefRestrictSmallCoverInjective

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsPointOfVal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.CompanionTheory.SmallFin

theorem exists_prime_eq {L : Type} [Field L] [NumberField L] (O : ValuationSubring L)
    (x₀ : 𝓞 L) (h0 : x₀ ≠ 0) (hn : (x₀ : L) ∈ O.nonunits) :
    ∃ w : HeightOneSpectrum (𝓞 L), w.valuationSubringAtPrime L = O := by
  have hint : ∀ x : 𝓞 L, (x : L) ∈ O := fun x => ReciprocityTheory.Gal.mem_of_isIntegral_int O x.isIntegral_coe
  let b : 𝓞 L →+* O := (algebraMap (𝓞 L) L).codRestrict O hint
  have hb : ∀ x, ((b x : O) : L) = (x : L) := fun _ => rfl
  have hpm : x₀ ∈ (IsLocalRing.maximalIdeal O).comap b := by
    rw [Ideal.mem_comap]
    obtain ⟨h, hh⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hn
    exact hh
  let v : HeightOneSpectrum (𝓞 L) := ⟨(IsLocalRing.maximalIdeal O).comap b, inferInstance, fun h => by
    rw [h, Ideal.mem_bot] at hpm
    exact h0 hpm⟩
  refine ⟨v, ?_⟩
  haveI : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime L) :=
    Localization.subalgebra.isLocalization_ofField L v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (v.valuationSubringAtPrime L) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) v.ne_bot _
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ ?_
  · intro x hx
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj v.asIdeal.primeCompl (⟨x, hx⟩ : v.valuationSubringAtPrime L)
    have hs : IsUnit (b s) := by
      by_contra h'
      exact s.2 h'
    obtain ⟨u, hu⟩ := hs.exists_right_inv
    have h1 : x * ((s : 𝓞 L) : L) = (a : L) := congrArg Subtype.val h
    have h2 : ((s : 𝓞 L) : L) * (u : L) = 1 := by
      rw [← hb]
      exact congrArg Subtype.val hu
    have : x = ((b a * u : O) : L) := by
      push_cast
      rw [hb, ← h1, mul_assoc, h2, mul_one]
    rw [this]
    exact (b a * u).2
  · intro h
    have hx0 : (x₀ : L) ≠ 0 := by exact_mod_cast h0
    have := ((ValuationSubring.mem_nonunits_iff_or O).1 hn).resolve_left hx0
    exact this (h ▸ ValuationSubring.mem_top _)


end GlobalTheory.CompanionTheory.SmallFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RestrictTrivEqZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PdChern

theorem restrict_triv_eq_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ z : SecondDeRham s, IsChern (dp0 R) s L z → (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).pull2 z = 0 := by
  intro R _ X s L hL z hz
  obtain ⟨i, hi, u, ℓ, -, hℓ, hz⟩ := hz
  obtain ⟨c, rfl⟩ := H2.mk_surjective _ z
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hz
  obtain ⟨f, hf⟩ := hz
  apply _root_.GlobalTheory.CompanionTheory.TrivSmall.pull_restrict_small_injective R X s L.ι L.U hL.cover
  rw [map_zero, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
  let P : ObjectProperty (IsTriv s).FullSubcategory :=
    fun T : (IsTriv s).FullSubcategory => IsSmall (dp0 R) s L.U T.obj
  let F : P.FullSubcategory ⥤ (IsSmall (dp0 R) s L.U).FullSubcategory :=
    ObjectProperty.lift _ (P.ι ⋙ (IsTriv s).ι) (fun T => T.property)
  refine ⟨fun T T' φ => f (F.obj T) (F.obj T') (F.map φ), ?_⟩
  funext T T' T'' φ ψ
  have h := congrFun (congrFun (congrFun (congrFun (congrFun hf (F.obj T)) (F.obj T'))
    (F.obj T'')) (F.map φ)) (F.map ψ)
  have h0 : (ℓ.1 (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ) : T''.obj.obj.B) = 0 := by
    have hm : (ℓ.1 (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ) : T''.obj.obj.B) ∈
      T''.obj.obj.J := (hℓ (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ)).1
    have e : T''.obj.obj.J = ⊥ := T''.obj.property
    rw [e] at hm
    exact Ideal.mem_bot.1 hm
  exact h.trans (sub_eq_self.2 h0)

end GlobalTheory.CompanionTheory.PdChern
end

