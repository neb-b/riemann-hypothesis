module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree

section Adelic

variable {L : Type} [Field L] [NumberField L]

def adDeg (r : HeightOneSpectrum (𝓞 L) → ℝ) (N : (L →+* ℂ) → ℝ) : ℝ :=
  (∑ᶠ 𝔭, r 𝔭 * Real.log (Ideal.absNorm 𝔭.asIdeal) - (1 / 2) * ∑ σ, Real.log (N σ)) / Module.finrank ℚ L

end Adelic

section Eigen

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G]

def IsEigVec (act : OAct O G) (χ : O →+* R) (v : epsR R ⟶ G) : Prop :=
  IsTangent v ∧ ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left

def IsEigBasis (act : OAct O G) (χ : O →+* R) {m : ℕ} (v : Fin m → (epsR R ⟶ G)) : Prop :=
  (∀ i, IsEigVec act χ (v i)) ∧ ∀ w, IsEigVec act χ w → ∃! c : Fin m → R, IsLieComb c v w

end Eigen

section Local

variable {L : Type} [Field L] [NumberField L] (A : Over (Sp L)) [GrpObj A] {m : ℕ}

def IsArchSq (𝓛 : LB A.left) (v : Fin m → (epsR L ⟶ A)) (σ : L →+* ℂ) (N : ℝ) : Prop :=
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ A.left) (g : ℕ) (u : HolUnif A' (𝓛.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' : Fin m → (epsR ℂ ⟶ A')) (W : Fin m → Fin g → ℂ),
    IsGrpPullback A' A (spMap σ) φ ∧ u.IsAH Hm χ ∧ (∀ i, IsVecOver σ φ (v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
    0 < N ∧ (N : ℂ) = (Matrix.of fun i k => (Real.pi : ℂ) * (W i ⬝ᵥ Hm.mulVec (star (W k)))).det

end Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lines

variable {L : Type} [Field L] [NumberField L]

def ordIdeal (τ : E →+* L) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  FractionalIdeal.count L 𝔭
    ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)

def ordTwist (H : Host E) (τ : E →+* L) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  (ordIdeal τ (differentIdeal ℤ (𝓞 E)) 𝔭 - ordIdeal τ (Ideal.span {H.rt}) 𝔭) - ordIdeal τ (Ideal.span {H.rt}) 𝔭

end Lines

def cOne (H : Host E) (p q : ℕ) (logOm : ℝ) : ℝ :=
  -(((p : ℝ) - q) / 2 * logOm) - q * (2 * Real.log √(H.d : ℝ) - Real.log (rootDiscr E))

def IsHostField (H : Host E) : Prop :=
  IsAbelianGalois ℚ E ∧
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ differentIdeal ℤ (𝓞 E) →
    w.asIdeal.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w.asIdeal ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 E) ∈ w.asIdeal →
      (ℓ ≠ H.d ∧ IsSquare (-(H.d : ZMod ℓ))) ∨ (ℓ = H.d ∧ ¬ w.asIdeal ^ 3 ∣ Ideal.span {(ℓ : 𝓞 E)})

end GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev LevGrp (Dw : Datum H) (l : Level H) : Type := LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l

def levDet (Dw : Datum H) (l : Level H) : LevGrp Dw l →* (𝓞 E ⧸ l.Mb)ˣ where
  toFun γ := LinearEquiv.det
    (γ.extendScalarsOfSurjective (S := 𝓞 E ⧸ l.Mb) Ideal.Quotient.mk_surjective)
  map_one' := by
    rw [← map_one (LinearEquiv.det (R := 𝓞 E ⧸ l.Mb) (M := LaMod Dw l))]
    rfl
  map_mul' γ δ := by
    rw [← map_mul]
    rfl

end Level

variable {D : D7}

def idealHat (D : D7) (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ b ∈ I, ∃ y ∈ intAE D, z = ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * y}

def CongMod (I : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) (u : 𝓞 D.host.E) : Prop :=
  finPart D (x : AE D) - (1 : Af D.host.F) ⊗ₜ (u : D.host.E) ∈ idealHat D I

def IsInvTame {K : Type} [Field K] (σ : K →+* ℂ) (Mb Mc : Ideal (𝓞 D.host.E)) (μ : (AE D)ˣ →* Circle)
    (χ : (𝓞 D.host.E ⧸ Mb)ˣ →* Kˣ) : Prop :=
  ∀ x : (AE D)ˣ, FinUnit x → ∀ (u : 𝓞 D.host.E) (ub : (𝓞 D.host.E ⧸ Mb)ˣ),
    (ub : 𝓞 D.host.E ⧸ Mb) = Ideal.Quotient.mk Mb u → CongMod Mb x u → CongMod Mc x 1 →
      σ ((χ ub : Kˣ) : K) * ((μ x : Circle) : ℂ) = 1

def IsLevLift {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (γ : LevGrp Dw l) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
    ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a) →
      ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = (l.M : ℕ) • w

end GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions
end
end

