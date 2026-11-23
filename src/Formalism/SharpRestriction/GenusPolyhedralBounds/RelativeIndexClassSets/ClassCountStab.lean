module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0013
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralClass
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.ThetaLiftIndependence.Statement
public import Formalism.HermitianLattices.Bundle0003
public import Mathlib
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0005
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0009
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.HermitianLattices.StatementLat
public import Formalism.HermitianLattices.FinalNeighbourConstruct

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Stab

open Formalism.UG Formalism.UG.CS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem exists_place_two : ∃ v : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hpZ : Prime ((2 : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨Q, hQ, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F)
    (Ideal.span {((2 : ℕ) : ℤ)})
  have hmem : ((2 : ℕ) : 𝓞 F) ∈ Q := by
    have : ((2 : ℕ) : ℤ) ∈ Q.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : ((2 : ℕ) : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

instance finiteAdeleRing_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨v, -⟩ := exists_place_two (F := F)
  exact (evalV F v).toRingHom.domain_nontrivial

section Herm

variable [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
  (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E)







section Mass

variable (hsymm : h.IsSymm) (hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
  (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
  (hIn : ∀ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ ∈ Formalism.HermitianLatticesTheory.genus h Λ)
  (hSurj : ∀ M ∈ Formalism.HermitianLatticesTheory.genus h Λ, ∃ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ = M)






end Mass

end Herm

section Std

open Formalism.MainNotions.StandardLattice

variable {k : ℕ} [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)


variable (hc : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))





end Std

end Formalism.MainNotions.Gaps.CC.Stab
