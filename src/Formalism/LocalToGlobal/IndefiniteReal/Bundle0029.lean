module

public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.PeriodIntegrals.Bundle0020
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

abbrev RowSideT (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T) (cX : CoefA D.sp.X') (pl : Pl0 → Pl D.host.E) (t : T) : Type :=
  Bridge.SideReal D D.sp.X' (Bridge.envOf cX.coef (levEnvOf D.sp.X' L.βX (L.datXt t) pl (A3.A.ok t)))
    (A3.A.MtildeCSD t) (A3.A.leftGroupActionRight t) (A3.A.heckeR t) (fun i => i.2)

abbrev LiftSideT (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T) (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (i : Fin D.R.m) (t : T) : Type :=
  Bridge.SideReal D (Vc D i) (Bridge.envOf (cV i).coef (levEnvOf (Vc D i) (L.βV i) (L.datVt i t) pl (A3.A.ok t)))
    (A3.A.MtCSD i t) (A3.A.leftGroupActionLift i t) (A3.A.heckeL i t) (fun i => i.2)


open Classical in
def PrIso {D : D7} (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (cX : CoefA D.sp.X') (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ) : Prop :=
  ∀ (ι : D.what₂.Tau → Type) [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (MX.sm τ)) (w w' : cX.W),
    inner ℂ w w' = ∑ f : (∀ τ, ι τ),
      starRingEnd ℂ (prX w (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) * prX w' (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))

end Formalism.IndefR.Seed
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.SchurOrthogonalityAlt
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))


open Classical in
structure EqCont (M : DSModel V S) (T : MMap M) : Prop where
  equiv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)
  cont : ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ}


open Classical in
theorem eqCont_of_mem {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : T ∈ Mult θ M J χ) : EqCont θ M T := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact ⟨hT.equiv, hT.cont⟩
  | zero =>
    refine ⟨fun τ g _ v w _ => ?_, fun τ v x => ⟨0, sobCont_zero, fun w => ?_⟩⟩
    · rw [MultilinearMap.zero_apply, MultilinearMap.zero_apply]; rfl
    · simp
  | add T T' _ _ h h' =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.add_apply, MultilinearMap.add_apply, h.equiv τ g hg v w hw, h'.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      obtain ⟨ℓ', hℓ', e'⟩ := h'.cont τ v x
      exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by
        rw [LinearMap.add_apply, e, e', MultilinearMap.add_apply, Pi.add_apply]⟩
  | smul a T _ h =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.smul_apply, MultilinearMap.smul_apply, h.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by
        rw [LinearMap.smul_apply, e, MultilinearMap.smul_apply, Pi.smul_apply]⟩




end Formalism.IndefR.AutomorphicEvaluation

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

def ConjLevel (t : GA D (D.sp.Y 0)) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ)
    (J' : Set (GA D (D.sp.Y 0))) (χ' : GA D (D.sp.Y 0) → ℂ) : Prop :=
  ∀ k, (k ∈ J ↔ t⁻¹ * k * t ∈ J') ∧ (k ∈ J → χ' (t⁻¹ * k * t) = χ k)

def EvalTieT (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) : Prop :=
  ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∃ j : E ≃ₗ[ℂ] EEC X G, ∀ T : E,
    ((j T : EEC X G) : L2X X) =ᵐ[muX X] (fun x => ev M v₀ (T : MMap M) (ι.symm x * t)) ∧
      ‖((j T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re


open Classical in
def sEEofTT (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) :
    E →ₗ⋆[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X :=
  if h : EvalTieT M μ 𝓕 E X G ι t c then (conjHH X G).toLinearMap.comp h.choose_spec.2.choose.toLinearMap else 0

end Formalism.IndefR.AutomorphicEvaluation

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.PublishedAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def AtTauExists (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∀ τ (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) → ∃ x, IsAtTau θ V τ g x

theorem atTauExists_of {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) (V : HSp D) :
    AtTauExists θ V := by
  intro τ g hg
  obtain ⟨x, hx, -⟩ := Formalism.IndefR.Eqv.atTauExUnique_holds (D := D) θ hθ V τ g hg
  exact ⟨x, hx⟩

end Formalism.IndefR.PublishedAut

end
end

