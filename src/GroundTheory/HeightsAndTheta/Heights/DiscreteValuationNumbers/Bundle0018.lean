module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def truncCoord {N : ℕ} {Φ : Type*} [Zero Φ] (t : Fin N → Φ) (i : ℕ) : Fin N → Φ :=
  fun j => if (j : ℕ) < i then t j else 0

def FlagBundleDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsMultiProjPrime (projIdeal F y w φ (truncCoord t i)) ∧
        FieldNumbers.relDim (projIdeal F y w φ (truncCoord t i)) =
          ((e + i - 1 : ℕ) : WithBot (WithTop ℤ))

def FlagBundleCut.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : Fin N, 1 ≤ (i : ℕ) → ∀ L : List (Option K → ℤ), L.length + 1 = e + i →
      intNumL F (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)))
          ((zetaDeg + liftDeg (b i - a)) :: L) =
        intNumL F (projIdeal F y w φ (truncCoord t i)) L

def FlagBundlePullbackVanish.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : ℕ, 2 ≤ i → i ≤ N → ∀ L : List (K → ℤ), L.length + 1 = e + i →
      intNumL F (projIdeal F y w φ (truncCoord t i)) (L.map liftDeg) = 0

def FlagBundleLineBase.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (h0 : 0 < N) (n : ℕ) (Y : List (K → ℤ)), n + Y.length = e →
      intNumL F (projIdeal F y w φ (truncCoord t 1)) (List.replicate n zetaDeg ++ Y.map liftDeg) =
        intNumL F (pointIdeal F y) (List.replicate n (a - b ⟨0, h0⟩) ++ Y)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPointIdealMultiProj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PointIdealMultiProj.Statement : Prop :=
  ∀ (F : Type) [Field F] (L : Type) [Field L] [Algebra F L]
    (K : Type) [DecidableEq K] (ι : K → Type) (z : (Σ k, ι k) → L),
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → IsMultiProjPrime (pointIdeal F z)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensSpan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensSpan.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle R (segreVec y) N E)
    (a : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω E),
    IsTwistedDualGens y B a φ → ∀ c, segreVec y c ≠ 0 →
      Submodule.span Ω (Set.range φ) = ⊤

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalDivisorJoinPullback
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def VerticalDivisorJoinPullback.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (b : K → ℤ) (f g : MRing ι O),
    IsVerticalDivisor (pointIdeal O y) ϖ b f g →
      IsVerticalDivisor (pointIdeal O (joinCoords y y')) ϖ (joinDeg b) (joinForm f) (joinForm g)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.TrivBundleIsTwistedForms
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w u₁ u₂

section Coordinates

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

def segreVec (pt : MRingOver o ι →ₐ[o] Ω) : ((k : K) → ι k) → Ω :=
  fun i => ∏ k, pt (X ⟨k, i k⟩)

end Coordinates

section Flags

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Flags

section ProjBundle

variable {K : Type*} [Fintype K]

variable {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section PolyNum

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def monoList {N : ℕ} (mono : Fin N →₀ ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun l => List.replicate (mono l) l

def tupleOfList {α : Type*} [Zero α] {n : ℕ} (L : List α) : Fin n → α := fun j => L.getD j 0

variable {F : Type*} [Field F]

def polyNum (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ) {N : ℕ} (cls : Fin N → K → ℤ)
    (Q : MvPolynomial (Fin N) ℤ) (Y : List (K → ℤ)) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * I V n (tupleOfList ((monoList mono).map cls ++ Y))

end PolyNum

section Pairs

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

structure VPair (K : Type*) [Fintype K] (O : Type*) [CommRing O] (ι : K → Type*) [∀ k, Fintype (ι k)] where

  y : K → ℤ

  b : K → ℤ

  f : MRingOver O ι

  g : MRingOver O ι

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def vNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    (p : VPair K O ι) (L : List (K → ℤ)) : ℤ :=
  redEval (fun W => Iκ W n (tupleOfList L)) (divO P p.f p.g)

def monoPairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (ls : List (Fin r)) : ℤ :=
  ∑ k : Fin ls.length, vNum P Iκ n (pr (ls.get k))
    ((ls.take k).map (fun l => (pr l).y - (pr l).b) ++ (ls.drop (k + 1)).map fun l => (pr l).y)

def pairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (Q : MvPolynomial (Fin r) ℤ) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * monoPairNum P Iκ n pr (monoList mono)

variable {Ω : Type*} [Field Ω] [Algebra O Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Pairs

section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

variable {o}





variable (o) in
def genPt (R : Type*) [CommRing R] [IsDomain R] (ι : K → Type*) [∀ k, Fintype (ι k)] :
    MRingOver R ι →ₐ[R] FractionRing (MRingOver R ι) :=
  IsScalarTower.toAlgHom R _ _


section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end DVR

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
end
end

