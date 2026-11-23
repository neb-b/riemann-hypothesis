module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology

@[expose] public section

noncomputable section

namespace UpperTheory.V.Lit

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc IsLocalRing TensorProduct GlobalTheory.Pst

section

variable {l : ℕ} [Fact l.Prime] {B V : Type} [CommRing B] [Algebra ℚ_[l] B] [AddCommGroup V] [Module B V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] B V] (K : FinExt l) (ρ : Representation B ↥(GK K) V)

def FilHom (i : ℤ) : Set (V →ₗ[B] B ⊗[ℚ_[l]] Bdr l) :=
  {f | (∀ (g : ↥(GK K)) v, f (ρ g v) = LinearMap.lTensor B ((PP l).actQdR (g : GQ l)).toLinearMap (f v)) ∧
    ∀ v, f v ∈ FilT B B i}

def toDR : B ⊗[ℚ_[l]] ↥K.1 →ₐ[B] B ⊗[ℚ_[l]] Bdr l :=
  Algebra.TensorProduct.map (AlgHom.id B B) (IsScalarTower.toAlgHom ℚ_[l] ↥K.1 (Bdr l))

def HodgeLit (h : ℕ) (m : ℕ → ℕ) : Prop :=
  DeRham K ρ ∧ (∀ i ≤ (0 : ℤ), FilHom K ρ i = FilHom K ρ 0) ∧ FilHom K ρ ((h : ℤ) + 1) = {0} ∧
  ∀ i ≤ h, ∃ x : Fin (m i) → V →ₗ[B] B ⊗[ℚ_[l]] Bdr l, (∀ a, x a ∈ FilHom K ρ i) ∧
    ∀ y ∈ FilHom K ρ i, ∃! c : Fin (m i) → B ⊗[ℚ_[l]] ↥K.1,
      y - ∑ a, (LinearMap.mulLeft B (toDR K (c a))).comp (x a) ∈ FilHom K ρ ((i : ℤ) + 1)

def actBst (g : GQ l) : B ⊗[ℚ_[l]] Bst (PP l) →ₗ[B] B ⊗[ℚ_[l]] Bst (PP l) :=
  AlgebraTensorModule.map LinearMap.id ((actSt (PP l) g).toLinearMap.restrictScalars ℚ_[l])

def DpstHom : Set (V →ₗ[B] B ⊗[ℚ_[l]] Bst (PP l)) :=
  {f | ∃ K' : FinExt l, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ v, f (ρ g v) = actBst (g : GQ l) (f v)}

def toSt : B ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l) →ₐ[B] B ⊗[ℚ_[l]] Bst (PP l) :=
  Algebra.TensorProduct.map (AlgHom.id B B) (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) (Bst (PP l)))

def TypeLit (n : ℕ) (t : ↥(GK K) → B) : Prop :=
  ∃ x : Fin n → V →ₗ[B] B ⊗[ℚ_[l]] Bst (PP l), (∀ a, x a ∈ DpstHom K ρ) ∧
    (∀ y ∈ DpstHom K ρ, ∃! c : Fin n → B ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      y = ∑ a, (LinearMap.mulLeft B (toSt (c a))).comp (x a)) ∧
    ∀ γ : ↥(GK K), (γ : GQ l) ∈ Iq l → ∀ M : Matrix (Fin n) (Fin n) (B ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l)),
      (∀ b, (actBst (γ : GQ l)).comp ((x b).comp (ρ γ⁻¹)) = ∑ a, (LinearMap.mulLeft B (toSt (M a b))).comp (x a)) →
      M.trace = t γ ⊗ₜ[ℚ_[l]] 1

end

end UpperTheory.V.Lit
