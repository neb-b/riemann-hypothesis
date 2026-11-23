module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain

structure RowSide (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] where

  Amb : D.what₂.Tup → Type
  [instAmb : ∀ μ, NormedAddCommGroup (Amb μ)]
  [instAmbi : ∀ μ, InnerProductSpace ℂ (Amb μ)]
  [instAmbf : ∀ μ, FiniteDimensional ℂ (Amb μ)]

  Mult : D.what₂.Tup → ℕ → Type
  [instMult : ∀ μ j, NormedAddCommGroup (Mult μ j)]
  [instMulti : ∀ μ j, InnerProductSpace ℂ (Mult μ j)]
  [instMultf : ∀ μ j, FiniteDimensional ℂ (Mult μ j)]
  multZero : ∀ μ, Mult μ 0 ≃ₗᵢ[ℂ] EE
  multTop : ∀ μ, Mult μ D.R.m ≃ₗᵢ[ℂ] Amb μ

  io : ∀ μ j, Mult μ (j + 1) →ₗ[ℂ] Mult μ j

  Mtilde : ∀ μ, Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) (Amb μ)

  cen : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] Module.End ℂ (Amb μ)

  eOp : ∀ μ, Amb μ →ₗ[ℂ] Amb μ
  eOp_idem : ∀ μ, eOp μ ∘ₗ eOp μ = eOp μ
  eOp_sa : ∀ μ, (eOp μ).IsSymmetric

  eOp_tie : ∀ μ, eOp μ = (open Classical in
    if h : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) then cen μ ⟨D.ntypes.e0, h⟩ else 0)

  RR : HLat D.what₂.LL
  RR_frames : ∀ v, IsUnit (RR.X v).det

  jEE : RR.V →ₛₗ[D.what₂.embLL] EE
  jEE_basis : LinearIndependent ℂ (fun i => jEE (RR.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jEE (RR.b i))) = ⊤

  jEE_norm : ∀ x : RR.V,
    Formalism.HermitianLatticesTheory.normAt RR.b RR.X (InfinitePlace.mk D.what₂.embLL) x = ‖jEE x‖

attribute [instance] RowSide.instAmb RowSide.instAmbi RowSide.instAmbf RowSide.instMult
  RowSide.instMulti RowSide.instMultf

namespace RowSide

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (S : RowSide D EE)

def downTo (μ : D.what₂.Tup) : (j : ℕ) → S.Mult μ j →ₗ[ℂ] S.Mult μ 0
  | 0 => LinearMap.id
  | j + 1 => (downTo μ j).comp (S.io μ j)

def iota (μ : D.what₂.Tup) : S.Amb μ →ₗ[ℂ] EE :=
  (S.multZero μ).toLinearEquiv.toLinearMap ∘ₗ S.downTo μ D.R.m ∘ₗ
    (S.multTop μ).symm.toLinearEquiv.toLinearMap

def V0 (μ : D.what₂.Tup) : Submodule ℂ (S.Amb μ) := LinearMap.range (S.eOp μ)

def Usp (μ : D.what₂.Tup) : Submodule ℂ (S.Amb μ) := S.V0 μ ⊓ LinearMap.ker (S.iota μ)

def Qsp (μ : D.what₂.Tup) : Submodule ℂ (S.Amb μ) := S.V0 μ ⊓ (S.Usp μ)ᗮ

def LamSet (μ : D.what₂.Tup) : Set (S.Amb μ) :=
  (fun x => (S.Qsp μ).starProjection x) '' ((S.Mtilde μ).carrier ∩ (S.V0 μ : Set (S.Amb μ)))

def RRset (μ : D.what₂.Tup) : Set EE := S.iota μ '' S.LamSet μ

def iotaQ (μ : D.what₂.Tup) : S.Qsp μ →ₗ[ℂ] EE := (S.iota μ).domRestrict (S.Qsp μ)

def RRDef : Prop :=
  ∀ x : S.RR.V, x ∈ S.RR.L ↔ ∀ w : D.what₂.places.Pl, ∃ d : 𝓞 D.what₂.LL,
    d ∉ (D.plEq w).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 D.what₂.LL) {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)}

def AIntegral : Prop :=
  ∀ μ x, x ∈ (S.Mtilde μ).carrier → ((D.what₂.restRowsFiniteGroupCard : ℂ) • S.eOp μ x) ∈ (S.Mtilde μ).carrier

def sharp (D : D7) : RowSide D D.what₂.EE where
  Amb := D.what₂.Amb
  Mult := D.what₂.Mult
  multZero := D.what₂.multZero
  multTop := D.what₂.multTop
  io := D.what₂.io
  Mtilde := D.what₂.Mtilde
  cen := D.ntypes.cenAmb
  eOp := D.what₂.eOp
  eOp_idem := D.what₂.eOp_idem
  eOp_sa := D.what₂.eOp_sa
  eOp_tie := fun μ => by
    rw [D.nStage_trivialCharacter_compat.1 μ]; rfl
  RR := D.div.RR
  RR_frames := D.div_good.1
  jEE := D.jEE
  jEE_basis := D.jEE_basis
  jEE_norm := D.jEE_norm

end RowSide

structure BaseLevelRowSide (D : D7) where
  s : RowSide D D.what₂.EE0

namespace BaseLevelRowSide

variable {D : D7} (X : BaseLevelRowSide D)

def principalHermitianLattice : HLat D.what₂.LL := X.s.RR

end BaseLevelRowSide

def lam0 (D : D7) : ℝ := Real.log (D.what₂.restRowsFiniteGroupCard : ℝ)

end Formalism.BasicNotions

end
