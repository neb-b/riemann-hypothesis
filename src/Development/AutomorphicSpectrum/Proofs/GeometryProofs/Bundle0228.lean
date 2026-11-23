module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0063
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0211
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PartOneOfSemistableReductionPadicPolarized
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_cmPoint_locBasis_frames :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (τ : E →+* ℂ) (ℓ : Nat.Primes) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → ∃ (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (X : CMPack Z c FU i hP) (v : Vecs X.y D.p) (w : Vecs X.y D.q), k ≤ X.K ∧ IsLocBasis (𝓞 E) ℓ x ∧ X.IsCMFrame τ hx v w := by
  intro E _ _ _ H D l Xo c g ty FU i Z τ ℓ k hk hty hτ
  obtain ⟨P₀, hP₀⟩ := PeriodNonempty.exists_isPeriod E H (FU.Di i) g ty
    (by rw [(FU.sig i).1, (FU.sig i).2]; exact hty)
  have hsum : D.p + D.q = (FU.Di i).p + (FU.Di i).q := by rw [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨P, hP, x, hloc, hx⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period E H (FU.Di i) g ty P₀ D.p D.q ℓ hP₀ hty hsum
  obtain ⟨hli, n, hn, hspan⟩ := id hloc
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn (dvd_zero _))
  obtain ⟨hsplit, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.pure_family_spans_pure_sublattice E H (FU.Di i) g ty P hP D.p D.q x n hx hspan
  obtain ⟨X, hkX⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given E H D l Xo c g ty FU i Z P hP n k hk hn0 hsplit
  obtain ⟨⟨v, w, hvw⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hli
  exact ⟨P, hP, x, hx, X, v, w, hkX, hloc, hvw⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PartIHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem partI_holds : PartI :=
  GlobalTheory.partI_of_semistableReduction GlobalTheory.SS.semistableReductionSt

end GlobalTheory.CompanionTheory.Ar.Top
end

