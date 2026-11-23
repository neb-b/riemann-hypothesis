module

public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.IsRealPtO
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.RealPtExHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Fock.DRho Matrix

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isRealPtO_iff {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : RPt D m n) (w : Mx D m n) :
    IsRealPtO θ z w ↔ w = Lb D m n z := by
  have e := Formalism.IndefR.Eqv.eq_thetaC D hθ
  subst e
  constructor
  · rintro ⟨h1, h2⟩
    have hf : ∀ i j, finPart D (w i j) = 0 := fun i j => by
      have := congrFun (congrFun h1 i) j
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact this
    rw [← Lb_sigH w hf]
    congr 1
    funext ρ i j
    have := congrFun (congrFun (h2 ρ) i) j
    simp only [compAt, Matrix.map_apply, Matrix.of_apply] at this
    rw [sigH_apply]
    exact this
  · rintro rfl
    refine ⟨?_, fun τ => compAt_Lb z τ⟩
    ext i j
    rw [Matrix.map_apply, Matrix.zero_apply]
    exact finPart_Lb z i j

theorem realPtEx_holds : RealPtEx D := by
  intro θ m n hθ z
  exact ⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl, fun w hw => (isRealPtO_iff hθ z w).1 hw⟩

end Formalism.IndefR.Mi
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SignsG
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField IsDedekindDomain

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftRes (PP : Formalism.L2.DIV.Pl D.host.E) (x : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E :=
  Function.surjInv Ideal.Quotient.mk_surjective x

def supSum {k : Type} [AddCommMonoid k] {r : ℕ} (x : Matrix (Fin r) (Fin r) k) : k :=
  ∑ i : Fin r, if h : i.1 + 1 < r then x i ⟨i.1 + 1, h⟩ else 0

def psiAt (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (y : D.host.E) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D) (e * incA D (D.host.xi0 * y)))

def SignsAtG {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : Formalism.IndefR.Links.RealDat D A Ks) (F : Formalism.IndefR.Links.Face D A) : Prop :=
  ∀ (e : R.Pg → AE D), (∀ PP : R.Pg, Formalism.L2.NTheta.IsIdemAt (e PP) PP.1) → ∀ u : F.P0,
    D.what₂.embLL ((F.ψ0 u : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : R.Pg, psiAt R.ψ (e PP)
        ((((Ideal.absNorm PP.1.asIdeal : ℕ) : D.host.E))⁻¹ *
          ((liftRes PP.1 (supSum (((R.eG (u : G)) PP : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1)) :
            Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP.1))) : 𝓞 D.host.E) : D.host.E))

end Formalism.IndefR.Mi
end
end

