module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfConormalRankOne

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfNotMemSupportStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_at_of_not_mem_support : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (x : X), x ∉ J.support → CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalRankOneOfLocallyPrincipalStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conormal_rank_one_of_locally_principal : ∀ {A : Type} [CommRing A] [IsDomain A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) → Module.rankAtStalk I.Cotangent P = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSmoothAffinePresentationPairStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_affine_presentation_pair : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (U : X.affineOpens), Smooth g → Smooth (Z.subschemeι ≫ g) → ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | exact GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfConormalRankOneStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_principal_of_conormal_rank_one : ∀ {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), Module.rankAtStalk I.Cotangent P = 1 → LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one <;> assumption)
end

