module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.DiagonalDivisors.ModelsSt

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.T

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

universe u

inductive WBlk | base | det | line0 | line1
  deriving DecidableEq

instance : Fintype WBlk := ⟨{.base, .det, .line0, .line1}, by intro k; cases k <;> simp⟩

inductive YBlk | base | det | line
  deriving DecidableEq

instance : Fintype YBlk := ⟨{.base, .det, .line}, by intro k; cases k <;> simp⟩

def wwIdx (ι ν κ : Type u) : WBlk → Type u
  | .base => ι
  | .det => ν
  | .line0 => κ
  | .line1 => κ

def yyIdx (ι ν κ : Type u) : YBlk → Type u
  | .base => ι
  | .det => ν
  | .line => κ

instance wwIdx.fintype {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ] :
    (k : WBlk) → Fintype (wwIdx ι ν κ k)
  | .base => inferInstanceAs (Fintype ι)
  | .det => inferInstanceAs (Fintype ν)
  | .line0 => inferInstanceAs (Fintype κ)
  | .line1 => inferInstanceAs (Fintype κ)

instance yyIdx.fintype {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ] :
    (k : YBlk) → Fintype (yyIdx ι ν κ k)
  | .base => inferInstanceAs (Fintype ι)
  | .det => inferInstanceAs (Fintype ν)
  | .line => inferInstanceAs (Fintype κ)

def multiConeMap {K : Type*} {ι : K → Type*} {Φ : Type*} [Field Φ] (c : (Σ k, ι k) → Φ) :
    MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K Φ :=
  eval₂Hom (Int.castRingHom _) fun p => C (c p) * X p.1

section Models

variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def IsTwistedDetGen {x : ι → Ω} (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) (δ : ν → Ω) :
    Prop :=
  ∀ i, x i ≠ 0 →
    (∀ l, δ l ∈ Submodule.span (chartRing ℤ x i)
      {d | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, d = x i * detE e u w}) ∧
    ∀ u ∈ B.lat i, ∀ w ∈ B.lat i,
      detE e u w ∈ Submodule.span (chartRing ℤ x i) (Set.range fun l => (x i)⁻¹ * δ l)

def wwCoord (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ) :
    (Σ k, wwIdx ι ν κ k) → Φ
  | ⟨.base, i⟩ => algebraMap Ω Φ (x i)
  | ⟨.det, l⟩ => algebraMap Ω Φ (δ l)
  | ⟨.line0, k⟩ => lineVal e (φ k) a₀
  | ⟨.line1, k⟩ => lineVal e (φ k) a₁

def yyCoord (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Φ) :
    (Σ k, yyIdx ι ν κ k) → Φ
  | ⟨.base, i⟩ => algebraMap Ω Φ (x i)
  | ⟨.det, l⟩ => algebraMap Ω Φ (δ l)
  | ⟨.line, k⟩ => lineVal e (φ k) a

def wwIdeal (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ) :
    Ideal (MRing (wwIdx ι ν κ)) :=
  RingHom.ker (multiConeMap (wwCoord x δ e φ a₀ a₁))

def yyIdeal (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a : Φ) :
    Ideal (MRing (yyIdx ι ν κ)) :=
  RingHom.ker (multiConeMap (yyCoord x δ e φ a))

def wwDeg (n m : ℕ) : WBlk → ℕ
  | .base => n
  | _ => m

def toZCycle {α : Type*} (z : α →₀ ℕ) : α →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) z

end Models

section Degrees

end Degrees

section Diagonal

variable {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]


end Diagonal

end ReciprocityTheory.ChartRestriction.G.AI.T
