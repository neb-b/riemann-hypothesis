module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

def IsReps (g : GL (A ⊕ D) k) (R : Finset (GL (A ⊕ D) k)) (d : GL (A ⊕ D) k → kˣ) : Prop :=
  (∀ j ∈ R, j ∈ parahoric k A D ∧ (d j : k) = j.1.toBlocks₂₂.det) ∧
    ∀ j ∈ parahoric k A D, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ parahoric k A D

def IsTOp {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (g : GL (A ⊕ D) k)
    (x y : V) : Prop :=
  ∀ R d, IsReps g R d → y = ∑ j ∈ R, (((ξ (d j))⁻¹ : ℂˣ) : ℂ) • π (j * g) x

def indic (s : Finset D) : D → ℤ := fun i => if i ∈ s then 1 else 0

def genVal (q r N : ℕ) (B : Multiset ℂˣ) (n : ℕ) : ℂ :=
  ((Real.sqrt q : ℝ) : ℂ) ^ (r * n + n * (N - n)) * (B.map fun b : ℂˣ => (b : ℂ)).esymm n

def IsGen {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (ϖ : kˣ)
    (B : Multiset ℂˣ) (x : V) : Prop :=
  x ∈ typeSpace π ξ ∧ B.card = Fintype.card D ∧ ∀ s : Finset D,
    IsTOp π ξ (mtor ϖ (indic s)) x (genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • x)

def IsCoType {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (ℓ : V →ₗ[ℂ] ℂ) : Prop :=
  ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ v, ℓ (π j v) = (ξ d : ℂ) * ℓ v

def schur (x : Matrix (A ⊕ D) (A ⊕ D') k) : Matrix D D' k := x.toBlocks₂₂ - x.toBlocks₂₁ * x.toBlocks₁₁⁻¹ * x.toBlocks₁₂

def liftS (ξ : kˣ →* ℂˣ) (ψ : Matrix D D' k → ℂ) (x : Matrix (A ⊕ D) (A ⊕ D') k) : ℂ := datum ξ x * ψ (schur x)


open Classical in
def intInd (y : Matrix D D' k) : ℂ := if ∀ i j, y i j ∈ 𝒪[k] then 1 else 0

def IsRepsK (g₀ : GL D k) (R : Finset (GL D k)) : Prop :=
  (∀ g ∈ R, ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * g₀ * κ') ∧ ∀ κ ∈ KO k D, ∃! g, g ∈ R ∧ g⁻¹ * (κ * g₀) ∈ KO k D

def IsHgt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (H : GL n k → ℝ) : Prop :=
  (∀ κ ∈ KO k n, ∀ g, H (κ * g) = H g ∧ H (g * κ) = H g) ∧ ∀ e : n → ℤ, H (torusElt k n ϖ e) = (resCard k : ℝ) ^ (-(sumAbs e))

def segL (ϖ : kˣ) (z : ℂˣ) (t : ℕ) : Multiset ℂˣ :=
  (Multiset.range t).map fun n : ℕ => z * absPow k ((n : ℂ) - ((t : ℂ) - 1) / 2) ϖ

def omTwo {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μS μT : kˣ →* ℂˣ) (g : GL a k) (h : GL b k)
    (u : Matrix b a k → ℂ) : Matrix b a k → ℂ :=
  (((μS * μT⁻¹) (GeneralLinearGroup.det h) : ℂˣ) : ℂ) • om μT⁻¹ g h u

end GlobalTheory.ParHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymChain
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

structure SymData (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) where

  ψ : AddChar k Circle

  ϖ : kˣ

  ρ : ℕ

  P : TypeDatum k (Fin κ ⊕ Fin (s + 1))

  μ : ℕ → kˣ →* ℂˣ
  tame : ∀ j, IsTame (μ j)
  cond : HasConductor ψ 1
  unif : IsUnif ϖ
  odd : s + 1 = 2 * ρ + 1
  sym : IsSymLevel ψ ϖ ρ P

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def FreeTop (ρ : ℕ) {κ l : ℕ} : Fin κ ⊕ Fin l → Fin κ ⊕ Fin l → Prop
  | .inl i, .inl j => i < j
  | .inr i, .inl _ => i.val < ρ
  | .inl _, .inr j => ρ < j.val
  | .inr i, .inr j => i < j

def FreeIx (ρ : ℕ) {κ l j : ℕ} {t : Type} : Ix (Fin κ ⊕ Fin l) t j → Ix (Fin κ ⊕ Fin l) t j → Prop
  | .inl a, .inl b => FreeTop ρ a b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False
  | .inr p, .inr p' => p.1 ≤ p'.1

namespace SymData

def Pattern : Prop :=
  ∀ j (g : GL (Ix (Fin κ ⊕ Fin (s + 1)) t j) k), g ∈ (S.P.iter t S.μ S.tame j).J ↔
    g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx S.ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1

abbrev T : Chain k s (XIx (Fin κ) t) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2)) := typeChain t S.ϖ S.P S.μ S.tame

def y0 : XIx (Fin κ) t (s + 1) → k := Pi.single (Sum.inl (Sum.inr 0)) ((S.ϖ⁻¹ : kˣ) : k)

def PrLevel : Prop :=
  ∀ j c (h : j + c = s + 1), prX (Cgrp ((S.T t).lev j c h).J 1) = ((S.T t).lev j c h).J.comap (embX c)

def OneCoupling : Prop :=
  (∀ x₀ y, (S.T t).Psi 1 x₀ y ≠ 0 → y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ)) ∧
  (∀ x₀ y, y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) → (S.T t).Psi 1 x₀ y = (S.T t).Psi 1 x₀ (S.y0 t)) ∧
  ∀ γ : GL (XIx (Fin κ) t (s + 1)) k, embX 0 γ ∈ ((S.T t).lev (s + 1) 0 rfl).J →
    γ.val *ᵥ S.y0 t - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ)

def SupportOne : Prop :=
  ∀ j c (H : j + 1 + c = s) (h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k),
    h ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)) → ∀ x₀ e,
      (S.T t).Phi j (c + 1) (by omega) ((h⁻¹).val * affPt 1 x₀ e) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) 1, ∃ u ∈ ((S.T t).lev (j + 1) (c + 1) (by omega)).J, h = r * u

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

def OneClass : Prop :=
  ∀ j c (H : j + 1 + c = s) (h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k),
    flat S.ψ ν (S.μ (j + 1)) ((S.T t).Phi j (c + 1) (by omega)) 1 h ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) 1, ∃ u ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)), h = r * u

def OneIndex : Prop :=
  ∀ j c (h : j + 1 + c = s), ∀ β ∈ (S.T t).idx S.ψ ν j c h 1,
    β = DoubleCoset.mk (R k (XIx (Fin κ) t (j + 1)) (c + 1) 1) ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1


end SymData

def AtMostOne : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
      S.OneIndex t ν ∧ S.PrLevel t ∧ S.OneCoupling t

end GlobalTheory.SymChain
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
section
open MeasureTheory ValuativeRel Matrix
open scoped ENNReal

noncomputable section
namespace GlobalTheory.PosOne
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]

def IsSrc {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (ρ' : Representation ℂ (GL a k) (SB (Matrix b a k))) : Prop :=
  ∀ g (Φ : SB (Matrix b a k)), ((ρ' g Φ : SB (Matrix b a k)) : Matrix b a k → ℂ) = om μ g 1 Φ.1

def BilPos (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ Ψ, IsNEquiv ψ p σ (B Ψ)) ∧ ∀ (g : GL n k) (Ψ Ψ₁ : SB (Matrix n n' k)) (v : A), Ψ₁.1 = om μ 1 g Ψ.1 →
    B Ψ₁ (σ (embX c g) v) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * B Ψ v

def comb {G : Type} (e : G →₀ ℂ) (f : G → ℂ) : ℂ := e.sum fun g a => a * f g

def Covers {V : Type} [Zero V] (p : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (T : Finset (GL (n ⊕ Fin c) k))
    (f : GL (n ⊕ Fin c) k → V) : Prop :=
  Set.InjOn (DoubleCoset.mk (R k n c p) J) (T : Set (GL (n ⊕ Fin c) k)) ∧
    ∀ h, f h ≠ 0 → ∃ t ∈ T, DoubleCoset.mk (R k n c p) J h = DoubleCoset.mk (R k n c p) J t

variable [MeasurableSpace k] [BorelSpace k]

def toOne (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ) : (A → ℂ) → A → ℂ :=
  Nat.rec (motive := fun _ => (A → ℂ) → A → ℂ) (fun l => l)
    (fun p rec l => rec (exDown ν (p + 1) σ l)) (P - 1)

def tInt (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (h : GL (n ⊕ Fin c) k) : ℂ :=
  app B (opE ψ ν p (om μ 1 h Φ)) (σ h F)

def tIntOne (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (P : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (h : GL (n ⊕ Fin c) k) : ℂ :=
  toOne ν σ P (fun v => app B (opE ψ ν 1 (om μ 1 h Φ)) v) (σ h F)

def volCell (ν : Measure k) (m : Measure (GL n k)) (p : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k))
    (h : GL (n ⊕ Fin c) k) : ℝ≥0∞ :=
  ∫⁻ g, volN ν n c p {u : N k n c p | h⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k)) * h ∈ J} ∂m

def SrcComb (ψ : AddChar k Circle) (ν : Measure k) (P : ℕ) {b : Type} [Fintype b] [DecidableEq b]
    (ρ' : Representation ℂ (GL (n ⊕ Fin c) k) (SB (Matrix b (n ⊕ Fin c) k))) (Φ : SB (Matrix b (n ⊕ Fin c) k))
    (e : GL (n ⊕ Fin c) k →₀ ℂ) : Prop :=
  ∀ L : SB (Matrix b (n ⊕ Fin c) k) →ₗ[ℂ] ℂ, IsNEquiv ψ P ρ' L → toOne ν ρ' P L Φ = comb e fun g => L (ρ' g Φ)

def FJInt (ψ : AddChar k Circle) (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k))
    (μ : kˣ →* ℂˣ) (ρ : ℕ) (w : GL (n ⊕ Fin c) k → SB (Matrix n n' k) → SB (n → k) → ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (z : ℂ) : Prop :=
  ∃ f : GL (n ⊕ Fin c) k → ℂ,
    (∀ h, HasTensorVal (w h) (fl ψ ν μ ρ (om μ 1 h Φ)) (f h)) ∧ IsQuotIntFJ ν μX μG ρ f z

section Double
variable {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]


omit [MeasurableSpace k] [BorelSpace k] in
def TriPos (ψ : AddChar k Circle) (μ₁ μ₂ : kˣ →* ℂˣ) (ρ : ℕ) (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A)
    (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ Ψ₁, BilPos ψ μ₂ ρ σ (T Ψ₁)) ∧ ∀ (g : GL n₁ k) (Ψ₁ Ψ₁' : SB (Matrix n₁ n₀ k)) (Ψ₂ Ψ₂' : SB (Matrix n₂ n₁ k)),
    Ψ₁'.1 = om μ₁ 1 g Ψ₁.1 → Ψ₂'.1 = om μ₂ g 1 Ψ₂.1 → T Ψ₁' Ψ₂' = T Ψ₁ Ψ₂

def SymDbl (ψ : AddChar k Circle) (ν : Measure k) (m₁ : Measure (GL n₁ k)) (μ₁G : Measure (GL (n₁ ⊕ Fin (c + 1)) k))
    (m₂ : Measure (GL n₂ k)) (μ₂G : Measure (GL (n₂ ⊕ Fin c) k)) (μ₁ μ₂ : kˣ →* ℂˣ) (ρ : ℕ)
    (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A)
    (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A)
    (Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
    (Φ₂ : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ) (z : ℂ) : Prop :=
  ∃ w : GL (n₁ ⊕ Fin (c + 1)) k → SB (Matrix n₁ n₀ k) → SB (n₁ → k) → ℂ,
    (∀ h Ψ Φ₀, IsQuotInt ν m₂ μ₂G ρ
      (fun h' => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ h h' Φ₂)) (σ h' F)) (w h Ψ Φ₀)) ∧
    FJInt ψ ν m₁ μ₁G μ₁ ρ w Φ₁ z

def OneDbl (ψ : AddChar k Circle) (ν : Measure k) (m₁ : Measure (GL n₁ k)) (μ₁G : Measure (GL (n₁ ⊕ Fin (c + 1)) k))
    (m₂ : Measure (GL n₂ k)) (μ₂G : Measure (GL (n₂ ⊕ Fin c) k)) (μ₁ μ₂ : kˣ →* ℂˣ) (ρ : ℕ)
    (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A)
    (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A)
    (Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
    (Φ₂ : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ) (z : ℂ) : Prop :=
  ∃ w : GL (n₁ ⊕ Fin (c + 1)) k → SB (Matrix n₁ n₀ k) →ₗ[ℂ] ℂ,
    (∀ h Ψ, IsQuotInt ν m₂ μ₂G 1 (tIntOne ψ ν μ₂ ρ σ (T Ψ) F (om μ₂ h 1 Φ₂)) (w h Ψ)) ∧
    IsQuotInt ν m₁ μ₁G 1 (fun h => app (w h) (opE ψ ν 1 (om μ₁ 1 h Φ₁))) z

end Double

theorem toOne_one (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A → ℂ) : toOne ν σ 1 l = l := rfl

theorem toOne_succ (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (p : ℕ) (l : A → ℂ) :
    toOne ν σ (p + 2) l = toOne ν σ (p + 1) (exDown ν (p + 1) σ l) := rfl

end GlobalTheory.PosOne
end
end

