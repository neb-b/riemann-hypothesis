module

public import Mathlib
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.WeaklyAdmissibleFiltrations.Bundle0001
public import Formalism.GaloisCohomology.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0010
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
section
noncomputable section

namespace Formalism.MainNotions.EmbeddingTypeJumps

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open scoped Pointwise

section Lemma1

variable (D : D7)

def InPhi (φ : D.host.E →+* ℂ) : Prop := φ ∈ D.host.cmType

abbrev decG (v : HeightOneSpectrum (𝓞 D.host.E)) : Subgroup (D.host.E ≃ₐ[ℚ] D.host.E) :=
  MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) v.asIdeal

abbrev ineG (v : HeightOneSpectrum (𝓞 D.host.E)) : Subgroup (D.host.E ≃ₐ[ℚ] D.host.E) :=
  Ideal.inertia (D.host.E ≃ₐ[ℚ] D.host.E) v.asIdeal

def Conclusion1 : Prop :=
  ∀ l ∈ ({D.host.q, D.host.d} : Finset ℕ), l % 4 = 3 ∧
    ∀ v ∈ placesOver D.host.E l,
      v.asIdeal.ramificationIdx ℤ = 2 ∧
      D.host.conj • v.asIdeal ≠ v.asIdeal ∧
      (l = D.host.q → ∀ σ ∈ decG D v, ∀ φ : D.host.E →+* ℂ,
        (InPhi D (φ.comp (σ : D.host.E →+* D.host.E)) ↔ InPhi D φ)) ∧
      (l = D.host.d → ∀ σ ∈ ineG D v, σ ≠ 1 → ∀ φ : D.host.E →+* ℂ,
        (InPhi D (φ.comp (σ : D.host.E →+* D.host.E)) ↔ ¬ InPhi D φ))

end Lemma1

def epsL (l : ℕ) : ℝ := ((l : ℝ) ^ 2)⁻¹

def polyVal (P : MvPolynomial (Fin 3) ℕ) (f r t : ℕ) : ℕ := MvPolynomial.eval ![f, r, t] P

def bndB (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (P : MvPolynomial (Fin 3) ℕ) (l : ℕ) : ℝ :=
  C * D.R.f * (D.R.r * (large₂.sc.b / l + large₂.Sc + D.R.t + large₂.etaSz + Real.log large₂.sc.b) + D.R.m * large₂.sc.b) +
    (polyVal P D.R.f D.R.r D.R.t : ℝ) * Real.log large₂.sc.b

def TwLoc (D : D7) (i : D.nd.Loc) : Prop := D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0

def vZeta (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1})

section Glob

open Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.BasicNotions.Loc Formalism.MainNotions.N

variable {D : D7}
  (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

def AtQD (i : D.nd.Loc) : Prop :=
  ((D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) ∧ TwLoc D i) ∧ HG D.nd D.naut i

def Conclusion2 (large₂ : SizeData₂ D) (C : ℝ) (P : MvPolynomial (Fin 3) ℕ) : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → TwLoc D i →
    large₂.sc.x ^ (2 * large₂.Ct + 5) < (D.nd.l i : ℝ) →
    ∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i (ρ i) π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      (D.nd.vcc i π : ℝ) ≤ bndB D large₂ C P (D.nd.l i) +
        ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) +
        (padicValNat (D.nd.l i) (hE D.host) : ℝ) +
        (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) + epsL (D.nd.l i)

def admA (CA : ℝ) : Prop := Formalism.MainNotions.ElementDenominator.Conclusion1 D CA

def GlobalIndexAwayFromTypes : Prop :=
  ∀ (i : D.nd.Loc) (π : D.nd.X i) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admitted i (r i) (ρ i) π dc lenRow e' cB → Formalism.MainNotions.TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i (ρ i) π dc lenRow e' cB

def admG1 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG1 i (r i)

def admG2 : Prop :=
  ∀ i : D.nd.Loc, AtQD i → ∀ π ∈ D.nd.Zgood i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG2 i (r i) (ρ i) π

def admG3 : Prop :=
  ∀ i : D.nd.Loc, AtQD i → ∀ π ∈ D.nd.Zgood i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG3 i (r i) (ρ i) π

def admG4 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG4 i (r i)

def admG5 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG5 i (r i)

def admG6 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG6 i (r i)

def iwahoriAdmissibleSet : Prop :=
  ∀ i : D.nd.Loc, AtQD i → ∀ π ∈ D.nd.Zgood i,
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous i (r i) ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admSS i (r i) ∧
      Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i

def admTB (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.Conclusion4 D HW F

def admBK : Prop := Formalism.MainNotions.LocalSituation.Conclusion5 D

def KillingTwistedPlaces : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → TwLoc D i →
    ((∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∨
      D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E)) →
    ∀ π ∈ D.nd.Zgood i, (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) ≤ epsL (D.nd.l i) ∧
      (D.R.t : ℝ) * ((∑ v ∈ D.nd.Q i, vZeta D i v : ℚ) : ℝ) ≤ epsL (D.nd.l i)

def WachHypothesisLocal (S : Formalism.MainNotions.LocalSituation.Sit) (E : S.Comparison₂) : Prop :=
  ∀ (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ), Formalism.WeaklyAdmissibleFiltrations.IsCrys S.PD Y.ρ →
    (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) → Formalism.MainNotions.LocalSituation.HypW S E Y M0 h0

def admW (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL),
      WachHypothesisLocal (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h)
        ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie

def LiteratureHypotheses : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.TameGeneratorConditions i ∧
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw),
      Formalism.MainNotions.TruncatedSeriesCountingIdentities.TateDualityH2Torsion (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL) ∧
      BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) ∧
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admH2 i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i

def EmbTypeUc {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) : Prop :=
  (∀ x : D.host.E, ∃ y : D.what₂.LL,
    Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ₀ (Br.cEw D.nbr i w hw x)) ∧
  ∃ φ ∈ D.host.cmType,
    ∀ (x : D.host.E) (y : D.what₂.LL),
      Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ₀ (Br.cEw D.nbr i w hw x) →
        D.what₂.embLL y = starRingEnd ℂ (φ x)

def EmbTypeUe (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) : Prop :=
  if ep then Br.EmbTypeU D.nbr i w hw τ₀ else EmbTypeUc τ₀

def UpAt (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) : Prop :=
  ∃ τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw,
    EmbTypeUe ep τ₀ ∧ ∀ x, τ x = C.inc (τ₀ x)

def DownAt (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) : Prop :=
  ∃ τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw,
    EmbTypeUe (!ep) τ₀ ∧ ∀ x, τ x = C.inc (τ₀ x)

def HodgeJumpWindowsAtDistinguishedPrimes (ep : Bool) (large₂ : SizeData₂ D) : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
      ∃ (s : ℤ) (Jc Jl : Finset ℤ),
        large₂.etaSz + D.R.t + 1 < (s : ℝ) ∧ (s : ℝ) ≤ large₂.sc.b + large₂.etaSz + D.R.t + 1 ∧
        Jc.card = D.R.k - 1 ∧ Jl.card = D.R.m ∧
        (∀ a ∈ Jl,
          ((-large₂.etaSz + ((D.R.t : ℝ) - 1) / 2 ≤ (a : ℝ) ∧ a ≤ -2) ∨
            ((D.R.t : ℤ) + 1 ≤ a ∧ (a : ℝ) ≤ large₂.etaSz + ((D.R.t : ℝ) - 1) / 2)) ∧
          ¬ (0 ≤ a ∧ a < D.R.t) ∧ a ≠ -1 ∧ a ≠ D.R.t) ∧
        ((∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + large₂.Sc) ∨ (∀ a ∈ Jc, -((s : ℝ) + large₂.Sc) ≤ a ∧ a ≤ -s)) ∧
        (UpAt ep C τ → ∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + large₂.Sc) ∧
        (DownAt ep C τ → ∀ a ∈ Jc, -((s : ℝ) + large₂.Sc) ≤ a ∧ a ≤ -s) ∧
        ∀ (x : D.nd.X i) (a : ℤ),
          IsJumpV (Br.PD D.loc D.nbr i w hw)
              (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) x))) τ a ↔
            a ∈ Jc ∨ a ∈ Jl ∨ (0 ≤ a ∧ a < D.R.t)

def FontaineSubOfSumsAtDistinguishedPrimes : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw),
      (∀ (V1 : Type) [AddCommGroup V1] [Module ↥C.LL.1 V1] [Module ℚ_[D.nd.l i] V1]
          [IsScalarTower ℚ_[D.nd.l i] ↥C.LL.1 V1] [FiniteDimensional ↥C.LL.1 V1]
          (ρ1 : Representation ↥C.LL.1 (Br.G D.nbr i w hw) V1),
          IsSubOfSums ρ1 (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (r i) x))) →
          IsCrys (Br.PD D.loc D.nbr i w hw) ρ1 ∧
          ∀ τ a, IsJumpV (Br.PD D.loc D.nbr i w hw) ρ1 τ a →
            ∃ x : D.nd.X i, IsJumpV (Br.PD D.loc D.nbr i w hw)
              (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) x))) τ (-a - 1)) ∧
      (∀ π ∈ D.nd.Zgood i,
          IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (ρ i) π))) ∧
          ∀ τ (a : ℤ),
            ((IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) →
              multV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (ρ i) π))) τ a = 1) ∧
            (¬ (IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) →
              multV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (ρ i) π))) τ a = 0))

def ParametersPolynomiallyBounded (large₂ : SizeData₂ D) : Prop := large₂.Sc + large₂.etaSz + D.R.t + 2 ≤ large₂.sc.b

def Conclusion0 (D : D7) : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      (∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧
        (D.nbr i w hw).Kw.1 = K0 (D.nbr i w hw).Kw ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y}) ∧
      (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
      finrank ↥(K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 = 2 ∧
      finrank ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1) =
        (D.nd.l i - 1) / 2 * finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1

end Glob

end Formalism.MainNotions.EmbeddingTypeJumps

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms
section
noncomputable section

namespace Formalism.MainNotions.HerrComplexNaturality

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FN (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.adm9 D HW F

def HerrNaturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm17 D HW F

def AdmNat (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F

def HerrNaturalityTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmNat D HW F → HerrNaturality D HW F

theorem herr_naturality_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrNaturalityTheorem D HW F := by
  intro h l _ K s LL g
  refine ⟨(h l K s LL g).2.2, ?_⟩
  intro hg T T' f pr pr' hp
  have h1 := (h l K s LL g).1 hg T
  exact (h1.2.2 T' f pr pr' hp).symm

def HerrExtensionClass (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm16 D HW F

def HerrExtensionUpToUnit (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.ElementDenominator.coreHerrExt ((HW l).W K s LL h) ∧ Formalism.MainNotions.ElementDenominator.coreHerrExtΔ ((HW l).W K s LL h)

theorem herr_class_maps_of_naturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h1 : HerrNaturality D HW F) (h2 : HerrExtensionUpToUnit D HW F) : Formalism.MainNotions.ElementDenominator.HerrClassMapsLocal D HW F :=
  fun l _ K s LL h => ⟨(h1 l K s LL h).1, (h1 l K s LL h).2, (h2 l K s LL h).1, (h2 l K s LL h).2⟩

end Formalism.MainNotions.HerrComplexNaturality
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheoremOfExplicit
section
noncomputable section

namespace Formalism.MainNotions.ElementDenominator

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Orbit

variable {G LL : Type} [Group G] [Field LL] (I : Subgroup G) [hI : I.Normal] (Fr : G)

end Orbit

section Iner

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)

end Iner

section PartII

variable {l : ℕ} [Fact l.Prime]
    {K₀' K' B BdR : Type} [Field K₀'] [Field K'] [Algebra ℚ_[l] K₀'] [Algebra ℚ_[l] K']
    [Algebra K₀' K'] [IsScalarTower ℚ_[l] K₀' K'] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B]
    [Algebra ↥(K0 (qlExt l)) B] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) B] [Algebra K₀' B]
    [IsScalarTower ℚ_[l] K₀' B] [Algebra ℚ_[l] BdR] [Algebra ↥(K0 (qlExt l)) BdR]
    [Algebra ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(qlExt l).1 BdR]
    [IsScalarTower ↥(K0 (qlExt l)) ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower ℚ_[l] K' BdR] [IsScalarTower K₀' K' BdR]
    [IsScalarTower ℚ_[l] K₀' BdR]
    (PC : PotCrysData ↥(GK (qlExt l)) ℚ_[l] ↥(K0 (qlExt l)) ↥(qlExt l).1 K₀' K' B BdR)
    (LL : FinExt l)

def HypT (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))) : Prop :=
  PC.IsPotCrys T₁.ρ ∧ PC.IsPotCrys T₂.ρ ∧ F.Onto ∧
    PC.IsFrob Fr ∧ FrobStable PC.Iner Fr Sig ∧ 1 ∈ Sig ∧ Sig.card ≤ N ∧ 2 ≤ N ∧
    PC.InertiaThrough T₁.ρ Sig ∧ PC.InertiaThrough T₂.ρ Sig ∧
    (∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) ∧ (0 : ℤ) ∈ U ∧ U.card ≤ N + 1 ∧ 1 ≤ η ∧ η < H ∧
    (∀ τ, JumpsInV PC.PD T₁.ρ τ (U : Set ℤ)) ∧ (∀ τ, JumpsInV PC.PD T₂.ρ τ (U : Set ℤ))

def thmTLift (C : ℕ) : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))),
    HypT PC LL T₁ T₂ F N η H U Sig Fr → C * (H * N ^ 2 + N ^ 3) < l →
      F.LiftF PC.PD (C * (N * rPrime PC.Iner Fr Sig + η * (N + rPrime PC.Iner Fr Sig)))

variable {PC LL}

variable (PC LL)

end PartII

def LiftingClause (D : D7) (C : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc l).PD (qlExt l)).actB g (algebraMap ↥(K0 K') (D.loc l).R.B c) =
        algebraMap ↥(K0 K') (D.loc l).R.B c')
    (LL : FinExt l), thmTLift (pc (D.loc l) h hN hF hS) LL C

def TwoStep {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (l g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) : Prop :=
  ∃ s s₀ : Finset M, s.card ≤ g ∧ Submodule.span O (s : Set M) ⊔ Bc = Z ∧
    s₀.card ≤ g₀ ∧ (s₀ : Set M) ⊆ Z ∧
    (∀ p ∈ Z, (l ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) ∧
    (∀ p ∈ Submodule.span O (s₀ : Set M), (l ^ e' : ℕ) • p ∈ I)

theorem len_ne_top {O : Type} [CommRing O] [IsDedekindDomain O] (x : O) (h : x ≠ 0) :
    Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ := by
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  rwa [mem_nonZeroDivisors_iff_ne_zero]

theorem len_le_nat {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (l p g g₀ y e' k : ℕ)
    (Z Bc I : Submodule O M) (h : TwoStep l g g₀ y e' Z Bc I) (hB : Bc ≤ I) (hp : p = l)
    (hk : Module.length O (O ⧸ Ideal.span {((p : ℕ) : O)}) = (k : ℕ∞)) :
    ∃ m : ℕ, Module.length O (↥Z ⧸ I.comap Z.subtype) = (m : ℕ∞) ∧ m ≤ (g * y + g₀ * e') * k := by
  subst hp
  obtain ⟨s, s₀, hs, hgen, hs₀, hsub, h1, h2⟩ := h
  have key := Formalism.IrreducibleCountingLemmas.WindowSums.colength_bound_two_layers O M p g g₀ y e' Z Bc I s s₀ hs hgen hB hs₀ hsub h1 h2
  rw [hk] at key
  have hcol : Module.length O (↥Z ⧸ I.comap Z.subtype) ≤ (((g * y + g₀ * e') * k : ℕ) : ℕ∞) := by
    push_cast
    exact key
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hcol)
  refine ⟨m, hm.symm, ?_⟩
  rw [← hm] at hcol
  exact_mod_cast hcol

section PartI

variable {l : ℕ} [Fact l.Prime]

theorem lenOl_finite (P : LocPrime l) (K LL : FinExt l) :
    ∃ k : ℕ, lenOl (P.PD K) (O := ↥(OL LL)) = (k : ℕ∞) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  have hne : lenOl (P.PD K) (O := ↥(OL LL)) ≠ ⊤ := by
    apply len_ne_top
    rw [P.PD_p K]
    intro h
    have h2 := congrArg (Subtype.val : ↥(OL LL) → ↥LL.1) h
    have h3 : ((l : ℕ) : ↥LL.1) = 0 := by simpa using h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h3)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
  exact ⟨k, hk.symm⟩

theorem colLe_mono (P : LocPrime l) (K LL : FinExt l) {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)}
    (F : LatHom T₁.L T₂.L) {b b' : ℝ} (hb : b ≤ b') (h : colLe P K LL F b) : colLe P K LL F b' := by
  obtain ⟨m, k, h1, h2, h3⟩ := h
  exact ⟨m, k, h1, h2, h3.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg k))⟩

theorem colLe_of_twoStep (P : LocPrime l) (K LL : FinExt l)
    {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (F : LatHom T₁.L T₂.L) (g g₀ y e' : ℕ)
    (h : TwoStep l g g₀ y e' (latticeFiniteCocycles (P.PD K) T₂.L) (latticeCoboundaries T₂.L) (F.ImF (P.PD K))) :
    colLe P K LL F ((g : ℝ) * y + (g₀ : ℝ) * e') := by
  obtain ⟨k, hk⟩ := lenOl_finite P K LL
  obtain ⟨m, hm, hmk⟩ := len_le_nat l (P.PD K).p g g₀ y e' k _ _ _ h le_sup_right (P.PD_p K) hk
  refine ⟨m, k, hm, hk, ?_⟩
  exact_mod_cast hmk

def HypA (P : LocPrime l) (K LL : FinExt l) (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (F : LatHom T₁.L T₂.L) (r S η m h : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) : Prop :=
  IsCrys (P.PD K) T₁.ρ ∧ IsCrys (P.PD K) T₂.ρ ∧ F.Onto ∧
    finrank ↥LL.1 T₂.V = r ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, η < b τ) ∧
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) ∧
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ')

end PartI

end Formalism.MainNotions.ElementDenominator

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.VKEqOfFrac
section
noncomputable section

namespace Formalism.MainNotions.TwOe

open Formalism.MainNotions.BlochKatoReduction.Gen

variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']

private theorem exists_ne_zero_addVal_algebraMap_eq_mul (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ y : R, IsDiscreteValuationRing.addVal R' (algebraMap R R' y) =
      (e : ℕ∞) * IsDiscreteValuationRing.addVal R y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible R'
  have h0 : algebraMap R R' ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'
  have hnu : ¬ IsUnit (algebraMap R R' ϖ) := by
    intro hu
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R)
      (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (IsLocalRing.maximalIdeal R')
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have hmem : ϖ ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') := by
      rw [heq]; exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem)) hu
  have he : e ≠ 0 := by
    rintro rfl
    apply hnu
    rw [hw, pow_zero, mul_one]
    exact w.isUnit
  refine ⟨e, he, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, AddValuation.map_zero, AddValuation.map_zero, ENat.mul_top (by exact_mod_cast he)]
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    rw [IsDiscreteValuationRing.addVal_def y u hϖ n hu]
    have hy' : algebraMap R R' y =
        ↑(Units.map (algebraMap R R' : R →* R') u * w ^ n) * ϖ' ^ (e * n) := by
      rw [hu, map_mul, map_pow, hw]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass]
      ring
    rw [IsDiscreteValuationRing.addVal_def _ _ hϖ' _ hy']
    push_cast
    ring

theorem nval_map (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] (l : ℕ) (x : R) :
    nval R' l (algebraMap R R' x) = nval R l x := by
  obtain ⟨e, he, hE⟩ := exists_ne_zero_addVal_algebraMap_eq_mul hinj
  simp only [nval]
  rw [hE x, ← map_natCast (algebraMap R R') l, hE]
  simp only [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast he)

end Formalism.MainNotions.TwOe

end
end

