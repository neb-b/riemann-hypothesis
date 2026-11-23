module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

def AgreementPos : Prop :=
  Inputs → ∀ (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (abelian₂ : ℝ), 0 < S.t₀ → ∃ C₃ s₀ : ℝ, 0 < s₀ ∧
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P),
      (∀ w, Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w))) ∧
      ∀ s, 0 < s → s ≤ s₀ → Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ ∧ ∀ c : σ → ℝ, ∑ a, |c a| ≤ abelian₂ →
        |eval c (Re.FT II (Real.exp (-(s ^ 2)⁻¹))) - eval c (Re.PB II)| ≤ C₃ * s

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.CompactConjugacyDomainLocal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat

def CptFlatInputs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c))
    (Z : CptOver Y U) (φ : FrameFn Xo c) (τ : CMType H) (t : (c.F →+* ℂ) → ℝ) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (A : HermLine J) (n : ℕ)
    (F' : Type) [Field F'] [NumberField F'] (ι : c.F →+* F') (ψ : F' →+* Ω),
    Z.IsGeom → FlatOnModel Z τ.1 φ → (∀ s, HasInfNorm U τ.1 φ s (t s)) →
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) →
    ψ.comp ι = 𝔐.cst → (∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ) →
    Birational y → IsArithVar (mCoordIdeal y) n →
    Fl.RootLines xdeg e → (∀ r, Fl.IsHodgeLine r (e r) (hx r)) →
    IsSmoothHerm A → IsConjInvariantH A → A.a = ∑ i, xdeg (τ, i) →
    (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      A.h w = ∏ i, (hx (τ, i)).h w) →
    (∀ p ∈ S, ExactModLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (p : Ω) (D.p + D.q)) →
    (∀ p : ℕ, p.Prime → p ∉ S →
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (p : Ω)) →
    ∃ (c₀ : Ω) (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (cinf : (F' →+* ℂ) → ℝ), c₀ ≠ 0 ∧
      (∀ σ, cinf σ = Real.exp (t (σ.comp ι))) ∧
      (∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p
          (c₀ * ∏ i, e (τ, i))) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
        ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt 𝔐.ξ,
          (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt 𝔐.ξ p) →
          OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))))
            (c₀ * ∏ i, e (τ, i)) (ψ π) m k p) ∧
      (∀ σ, 0 < cinf σ) ∧
      ∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg →
        IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h →
          ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖

namespace CptInputs

theorem exists_constants {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} (hy : Birational y) {F : Type} [Field F] [NumberField F] (cst : F →+* Ω) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (ι : F →+* F') (ψ : F' →+* Ω), ψ.comp ι = cst ∧
      ∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ := by
  classical
  letI : Algebra F Ω := cst.toAlgebra
  have hle : ∀ g : MRing J, aeval y g ∈ IntermediateField.adjoin F (Set.range y) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, aeval_X]; exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  haveI : Algebra.EssFiniteType F Ω := by
    rw [← IntermediateField.fg_top_iff]
    refine ⟨(Set.finite_range y).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset, eq_top_iff]
    intro a _
    obtain ⟨d, g, h, -, -, h0, e⟩ := hy a
    rw [eq_div_of_mul_eq h0 e.symm]
    exact div_mem (hle g) (hle h)
  let L := algebraicClosure F Ω
  haveI : FiniteDimensional F L := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType F Ω
  haveI : NumberField L := NumberField.of_module_finite F L
  refine ⟨L, inferInstance, inferInstance, algebraMap F L, algebraMap L Ω, rfl, ?_⟩
  rintro x ⟨f, hf, hx⟩
  have h1 : IsAlgebraic L x := ⟨f, hf, hx⟩
  exact ⟨⟨x, mem_algebraicClosure_iff.2 (h1.restrictScalars F)⟩, rfl⟩

end CptInputs

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

def ThmFlatA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) [NumberField c.F] (U : Set ((Xo l).XF c)) (τ : E →+* ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif (Xo l) (algebraMap (KA l) ℂ) ty) (i : Fin FU.n),
    1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → (∀ p : ℕ, p.Prime → l.GoodAt p) → IsTypeFn H D.p D.q ty →
    IsClopen U → IsIrreducible U →
    (∀ y : Sp ℂ ⟶ (Xo l).XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P)) →
    ∃ (φ : FrameFn (Xo l) c) (N : LogNorms c.F), IsFlatGen U τ φ FU i ∧ HasNorms U τ φ N ∧ N.IsAdelic

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

