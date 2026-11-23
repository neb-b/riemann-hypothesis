module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.FormalGroupTorsionCharts
section
noncomputable section

open IsLocalRing TensorProduct ReciprocityTheory.PGsh

namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts

universe u v

section Eval

variable {A : Type*} {R : Type*} [CommRing A] [CommRing R] [Algebra A R] {σ : Type*}

def evalTerm (F : MvPowerSeries σ A) (x : σ → R) (d : σ →₀ ℕ) : R :=
  MvPowerSeries.coeff d F • d.prod fun i n => x i ^ n

theorem evalTerm_finite [Finite σ] (F : MvPowerSeries σ A) (x : σ → R)
    (hx : ∀ i, IsNilpotent (x i)) : (Function.support (evalTerm F x)).Finite := by
  classical
  choose N hN using hx
  haveI := Fintype.ofFinite σ
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm N)).subset fun d hd => ?_
  by_contra hcon
  apply hd
  have : ∃ i, N i < d i := by
    by_contra h
    push Not at h
    exact hcon fun i => by simpa using h i
  obtain ⟨i, hi⟩ := this
  have hi0 : i ∈ d.support := by
    rw [Finsupp.mem_support_iff]; omega
  unfold evalTerm
  have h0 : x i ^ d i = 0 := pow_eq_zero_of_le hi.le (hN i)
  rw [Finsupp.prod, Finset.prod_eq_zero (f := fun a => x a ^ d a) hi0 h0, smul_zero]

def evalNil [Finite σ] (F : MvPowerSeries σ A) (x : σ → R) (hx : ∀ i, IsNilpotent (x i)) : R :=
  ∑ d ∈ (evalTerm_finite F x hx).toFinset, evalTerm F x d

theorem evalNil_eq_finsum [Finite σ] (F : MvPowerSeries σ A) (x : σ → R)
    (hx : ∀ i, IsNilpotent (x i)) : evalNil F x hx = ∑ᶠ d, evalTerm F x d :=
  (finsum_eq_sum _ (evalTerm_finite F x hx)).symm

end Eval



variable {R₀ : Type u} [CommRing R₀]

structure ResAlg (k : LAlg R₀) where

  alg : LAlg R₀

  res : LHom alg k
  res_surj : Function.Surjective res.1
  res_ker : RingHom.ker res.1 = maximalIdeal (alg : Type u)

structure NilAlg (k : LAlg R₀) extends ResAlg k where
  nil : ∀ x ∈ maximalIdeal (alg : Type u), IsNilpotent x

variable {k : LAlg R₀}

abbrev Tors (B : BX R₀) (n : ℕ) (R : LAlg R₀) : AddSubgroup (B.G R) :=
  AddSubgroup.torsionBy (B.G R) n

structure TorsionRep (B : BX R₀) (p : ℕ) (O : ResAlg k) where

  A : Tors B p k → ResAlg k

  str : ∀ x, LHom O.alg (A x).alg
  str_res : ∀ x, (A x).res.comp (str x) = O.res

  y : ∀ x, Tors B p (A x).alg
  y_res : ∀ x, B.map (A x).res (y x : B.G (A x).alg) = (x : B.G k)
  universal : ∀ (S : LAlg R₀) (s : LHom O.alg S) (t : Tors B p S),
    ∃! c : Σ x : Tors B p k, LHom (A x).alg S,
      c.2.comp (str c.1) = s ∧ B.map c.2 (y c.1 : B.G (A c.1).alg) = (t : B.G S)

namespace TorsionRep

variable {B : BX R₀} {p : ℕ} {O : ResAlg k} (D : TorsionRep B p O)

variable (C : Type v) [Field C] [Algebra (O.alg : Type u) C]

end TorsionRep

end GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.FundamentalSetFrames
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open scoped ENNReal NNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def GapsNonneg (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i)

def pairing (X : Data E r) (h0 : 0 < X.p0) (h1 : X.p0 < r) (la : Wt X.Ψ r) (τ : X.Ψ) : ℤ :=
  la τ ⟨r - 1, by omega⟩ - la τ ⟨0, by omega⟩

def IsInvWeight (X : Data E r) (u : Frame X.Ψ r → EReal) : Prop :=
  Measurable (fun x : X.dom => u x) ∧
  (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (lact γ (rmul x b)) = u x) ∧
  ∃ C : ℝ, ∀ x ∈ X.dom, u x ≤ (C : EReal)

def phi (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (z : V (nd X)) : ℝ :=
  -2 * Real.log (X.nfac la (cpt X x0 z))

def psi (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (z : V (nd X)) : EReal :=
  (phi X x0 la z : EReal) + u (cpt X x0 z)

def wsq (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (F : V (nd X) → ℂ) (z : V (nd X)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖F z‖ ^ 2) * EReal.exp (-psi X x0 la u z)

def normSq (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (F : V (nd X) → ℂ) : ℝ≥0∞ :=
  ∫⁻ z, wsq X x0 la u F z * ENNReal.ofReal (kaF X x0 bb z)⁻¹ ∂muF X x0

def ATilde (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal) :
    Set (V (nd X) → ℂ) :=
  {F | DifferentiableOn ℂ F (OmF X x0) ∧ normSq X x0 bb la u F < ⊤}

def IsFundSet (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
    lact γ (cpt X x0 z) = rmul (cpt X x0 z') b → γ = 1) ∧
  ∀ᵐ z ∂muF X x0, ∃ γ ∈ X.Γ, ∃ z' ∈ FF, ∃ b ∈ Bor X.Ψ r,
    cpt X x0 z = lact γ (rmul (cpt X x0 z') b)

def fundSq (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (u : Frame X.Ψ r → EReal)
    (FF : Set (V (nd X))) (f : Frame X.Ψ r → ℂ) : ℝ≥0∞ :=
  ∫⁻ z in FF, wsq X x0 la u (fun w => f (cpt X x0 w)) z ∂muF X x0

def IsExt (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)
    (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) ∧
  ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

def rhoFrame (X : Data E r) (x0 x : Frame X.Ψ r) : ℝ :=
  ∑ τ, (-Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ +
    Real.log (‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2))

def kappaFrame (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (x : Frame X.Ψ r) : ℝ :=
  Real.exp (-bb * rhoFrame X x0 x)

def idFrame (X : Data E r) : Frame X.Ψ r := fun _ a b => if a = b then 1 else 0

def flagBall (X : Data E r) (ε : ℝ) (y : Frame X.Ψ r) : Set (Frame X.Ψ r) :=
  {y' | y' ∈ X.dom ∧ ∃ x, IsOrth X x ∧ (∃ b ∈ Bor X.Ψ r, y = rmul x b) ∧
    ∃ z : Frame X.Ψ r, ‖z‖ < ε ∧ y' = rmul x (idFrame X + z)}

def ballSup (X : Data E r) (ε : ℝ) (u : Frame X.Ψ r → EReal) (y : Frame X.Ψ r) : ℝ≥0∞ :=
  ⨆ y' ∈ flagBall X ε y, EReal.exp (u y') ^ (1 / 2 : ℝ)

def term (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (γ : X.Γ) (x : Frame X.Ψ r) : ℂ :=
  (X.χ la γ.1)⁻¹ * P (lact γ.1 x)

def ConvergesNormally (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ K : Set (Frame X.Ψ r), IsCompact K → K ⊆ X.dom →
    ∃ M : X.Γ → ℝ, Summable M ∧ ∀ γ, ∀ x ∈ K, ‖term X la P γ x‖ ≤ M γ

def PoincareStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
  ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∀ la : Wt X.Ψ r,
    (∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u, ∃ P, IsExt X x0 la F P) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u,
      ∀ P, IsExt X x0 la F P → ∀ y ∈ X.dom,
        ENNReal.ofReal (X.pnorm la P y) ≤ C * normSq X x0 bb la u F ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.sqrt (kappaFrame X x0 bb y)) * ballSup X ε u y ∧
        ENNReal.ofReal (X.pnorm la (poin X la P) y) ≤
          C * normSq X x0 bb la u F ^ (1 / 2 : ℝ) * ballSup X ε u y) ∧
    ∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u, ∀ P, IsExt X x0 la F P →
      ConvergesNormally X la P ∧ X.IsBddSec la (poin X la P) ∧
      (∀ FF, IsFundSet X x0 FF → fundSq X x0 la u FF (poin X la P) < ⊤) ∧
      ∀ (la' : Wt X.Ψ r) (g : Frame X.Ψ r → ℂ), X.IsSec la' g →
        ConvergesNormally X (la' + la) (g * P) ∧
        ∀ x ∈ X.dom, poin X (la' + la) (g * P) x = g x * poin X la P x

def CuspidalStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), GapsNonneg X la →
    (∀ (h0 : 0 < X.p0) (h1 : X.p0 < r), ∃ τ : X.Ψ, 0 < pairing X h0 h1 la τ) →
    ∀ P, X.IsBddSec la P → P ∈ X.SS la

def PoincareCuspidalStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  PoincareStatement (E := E) ∧ CuspidalStatement (E := E)

end

end GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
end

