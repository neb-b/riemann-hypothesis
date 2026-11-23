module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyEq

def Val (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8

def Nrm (x : KeyIn ℂ) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) : Prop :=
  ∃ (h : x.P.g = g) (M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ), c ≠ 0 ∧
    NormalAt x (τ.submatrix (Fin.cast h) (Fin.cast h)) M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c

def frac {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (m n : Fin g → ℤ) : Fin g → ℂ :=
  (k : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))

def trl {S : Scheme.{0}} (A : Over S) [GrpObj A] (p : 𝟙_ (Over S) ⟶ A) : A ⟶ A := (toUnit A ≫ p) * 𝟙 A

def IsTrl (x' x : KeyIn ℂ) (p : 𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) (ν : ℂˣ) : Prop :=
  ∃ (φ : x'.P.A ≅ x.P.A) (hg : x'.P.g = x.P.g) (w : LB.Iso x'.P.L (x.P.L.pull (φ.hom ≫ trl x.P.A p).left))
    (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ 2).left, 𝟙 x.P.A.left] ![1, -4]))
    (rp : LB.Gen (x.P.L.pull p.left)),
    p ^ 2 = 1 ∧ IsMonHom φ.hom ∧ w.IsGen ∧ mu.IsGen ∧ rp.IsGen ∧
    (∀ i, x'.v i ≫ φ.hom = x.v (i.cast hg)) ∧
    (∀ (z : x'.P.A.left) (j : x.P.L.ι) (k : x'.P.L.ι), (φ.hom ≫ trl x.P.A p).left z ∈ x.P.L.U j → z ∈ x'.P.L.U k →
      gs (φ.hom ≫ trl x.P.A p).left z (x.P.L.U j) (x.th.f j) =
        (gw w (𝟙 _) z j k).val * gs (𝟙 _) z (x'.P.L.U k) (x'.th.f k)) ∧
    (∀ (q : (𝟙_ (Over (Sp ℂ))).left) J J', Good x.P.L q J → Good x'.P.L q J' →
      val rp (𝟙 _) q J = gw w (eSec x'.P.A) q (J (𝟙 _ ≫ p.left)) (J' (𝟙 _ ≫ eSec x'.P.A)) * val x'.rig (𝟙 _) q J') ∧
    (∀ (q : (𝟙_ (Over (Sp ℂ))).left) J, Good x.P.L q J → val mu (eSec x.P.A) q J = val x.rig (𝟙 _) q J ^ (-3 : ℤ)) ∧
    ∀ (q : (𝟙_ (Over (Sp ℂ))).left) J, Good x.P.L q J →
      val mu p.left q J = gm (𝟙 _) q ⊤ (show Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ from unitOn ν) * val x.rig (𝟙 _) q J * val rp (𝟙 _) q J ^ (-4 : ℤ)

variable {S : Type} [CommRing S]

end GlobalTheory.KeyEq
end
