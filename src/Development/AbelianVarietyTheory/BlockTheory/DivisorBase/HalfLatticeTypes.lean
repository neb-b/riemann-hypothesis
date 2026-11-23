module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes

open NumberField IsDedekindDomain Module AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AllWt
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

section Action

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

abbrev Rs (l : Level H) : Type := 𝓞 E ⧸ l.Mb

theorem half_ne_bot (l : Level H) : l.Mb ≠ ⊥ := fun h => by
  have h1 := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at h1
  have := l.three_le
  omega

instance (l : Level H) : Finite (Rs l) := Ideal.finiteQuotientOfFreeOfNeBot _ (half_ne_bot l)

abbrev Gz (l : Level H) (r : ℕ) : Type := GL (Fin r) (Rs l)

instance (l : Level H) (r : ℕ) : Fintype (Gz l r) := Fintype.ofFinite _

variable {l l' : Level H} {r : ℕ}

def Reads (e : Basis (Fin r) (Rs l) (LaMod Dw l)) (γ : LaMod Dw l' ≃ₗ[𝓞 E] LaMod Dw l')
    (g : Matrix (Fin r) (Fin r) (Rs l)) : Prop :=
  ∀ a : Dw.La, (Submodule.Quotient.mk (liftLa γ a) : LaMod Dw l) = Matrix.toLin e e g (Submodule.Quotient.mk a)

def IsUnip {R : Type} [CommRing R] (u : Matrix (Fin r) (Fin r) R) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0

def superSum {R : Type} [CommRing R] (u : Matrix (Fin r) (Fin r) R) : R :=
  ∑ i : Fin r, ∑ j : Fin r, if (j : ℕ) = i + 1 then u i j else 0

variable (Xo' : Moduli Dw l') (c' : Coeff l') {K : Type} [Field K] (ι : K →+* c'.F)
  (e : Basis (Fin r) (Rs l) (LaMod Dw l))


set_option synthInstance.maxHeartbeats 400000 in
def typeSub (ψ₀ : AddChar (Rs l) K) : Submodule c'.F (Rul Xo' c') where
  carrier := {f | ∀ (γ : LaMod Dw l' ≃ₗ[𝓞 E] LaMod Dw l') (u : Matrix (Fin r) (Fin r) (Rs l)), Reads e γ u → IsUnip u →
    ∀ (p : TRing c'.F) (y y' : FrPt Xo' c' p.R), levR (liftLa γ, LinearMap.id) y y' →
      f p y' = ι (ψ₀ (-superSum u)) • f p y}
  zero_mem' := fun γ u _ _ p y y' _ => by simp
  add_mem' := fun {f g} hf hg γ u h1 h2 p y y' h => by
    simp only [Pi.add_apply, hf γ u h1 h2 p y y' h, hg γ u h1 h2 p y y' h, smul_add]
  smul_mem' := fun a f hf γ u h1 h2 p y y' h => by
    simp only [Pi.smul_apply, hf γ u h1 h2 p y y' h]
    exact smul_comm _ _ _

def MoveG (g : Gz l r) {S : Type} [CommRing S] [Algebra c'.F S] (y y' : FrPt Xo' c' S) : Prop :=
  ∃ γ : LaMod Dw l' ≃ₗ[𝓞 E] LaMod Dw l', Reads e γ g ∧
    (∀ q ∈ l.Mb • (⊤ : Submodule (𝓞 E) (LaMod Dw l')), γ q = q) ∧ levR (liftLa γ, LinearMap.id) y y'

def actG (g : Gz l r) : Rul Xo' c' →ₗ[c'.F] Rul Xo' c' :=
  actL (K := c'.F) (fun S _ _ => FrPt Xo' c' S)
    (fun {S : Type} [CommRing S] [Algebra c'.F S] (g' : Gz l r) (y y' : FrPt Xo' c' S) => MoveG Xo' c' e g' y y') g

def idemCoeff (X : Finset (Gz l r → K)) (χ : (Rs l)ˣ →* Kˣ) (k : Gz l r) : K :=
  (Formalism.L2.DIV.idemOf X).coeff k * (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : Kˣ) : K)


set_option synthInstance.maxHeartbeats 400000 in
def idemOp (X : Finset (Gz l r → K)) (χ : (Rs l)ˣ →* Kˣ) : Rul Xo' c' →ₗ[c'.F] Rul Xo' c' :=
  ∑ k : Gz l r, HSMul.hSMul (α := c'.F) (ι (idemCoeff X χ k)) (actG Xo' c' e k)

variable {Xo' c'} {n : ℕ} (U' : ∀ σ : c'.F →+* ℂ, Unf Xo' c' σ n)

def typeLat (ψ₀ : AddChar (Rs l) K) (G : WTZ E) : Submodule (𝓞 c'.F) (cuspW Xo' c' U' G) :=
  latW U' G ⊓ ((typeSub Xo' c' ι e ψ₀).comap (cuspW Xo' c' U' G).subtype).restrictScalars (𝓞 c'.F)

def goodLat (ψ₀ : AddChar (Rs l) K) (X : Finset (Gz l r → K)) (χ : (Rs l)ˣ →* Kˣ) (G : WTZ E) :
    Submodule (𝓞 c'.F) (cuspW Xo' c' U' G) :=
  typeLat ι e U' ψ₀ G ⊓
    (((Submodule.span c'.F (typeLat ι e U' ψ₀ G : Set (cuspW Xo' c' U' G))).map
      (idemOp Xo' c' ι e X χ ∘ₗ (cuspW Xo' c' U' G).subtype)).comap
        (cuspW Xo' c' U' G).subtype).restrictScalars (𝓞 c'.F)



end Action

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (T : CoreJ D) (i : Fin D.R.m)

variable {T i} {l' : Level T.Q.H} {Xo' : Moduli (T.Q.Dw ((i : ℕ) + 1)) l'} {c' : Coeff l'}

def ringCost (K : Type) [Field K] [NumberField K] : ℝ := Real.log (finrank ℚ K) + Real.log (rootDiscr K)

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes
