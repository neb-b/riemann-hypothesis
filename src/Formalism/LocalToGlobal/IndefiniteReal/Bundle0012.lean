module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def crdOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : Crd A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) where
  toR Zs b t := match b with
    | false => (A.fam.R t).toF (A.fam.lvl P0 ψ0) (Zs.Z t)
    | true => (A.fam.R t).toF (A.fam.lvl P1 ψ1) (Zs.Z t)
  toL Zs b j t := match b with
    | false => (A.fam.L j t).toF (A.fam.lvlA P0 ψ0) (Zs.Zl j t)
    | true => (A.fam.L j t).toF (A.fam.lvlA P1 ψ1) (Zs.Zl j t)

end Concrete

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.InjectiveDecompositionAction

variable {D : D7}

def FirstPropositionFrame (D : D7) : Subgroup (AE D)ˣ where
  carrier := {x | (x : AE D) * cA D (x : AE D) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    calc (a : AE D) * b * (cA D a * cA D b) = (a * cA D a) * (b * cA D b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹ : (AE D)ˣ) : AE D) * a = 1 := by simp
    have h2 : cA D ((a⁻¹ : (AE D)ˣ) : AE D) * cA D (a : AE D) = 1 := by rw [← map_mul, h1, map_one]
    calc ((a⁻¹ : (AE D)ˣ) : AE D) * cA D ((a⁻¹ : (AE D)ˣ) : AE D)
        = ((a⁻¹ : (AE D)ˣ) : AE D) * cA D ((a⁻¹ : (AE D)ˣ) : AE D) * ((a : AE D) * cA D (a : AE D)) := by
          rw [ha, mul_one]
      _ = (((a⁻¹ : (AE D)ˣ) : AE D) * a) * (cA D ((a⁻¹ : (AE D)ˣ) : AE D) * cA D (a : AE D)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]

def SuppAtU (D : D7) (e : AE D) (x : (AE D)ˣ) : Prop :=
  (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1

end Formalism.IndefR.InjectiveDecompositionAction

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

namespace Formalism.IndefR.RationalEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev inst : Formalism.MainNotions.S.AutInst := Formalism.L2.SG.InstExistsPf.instOf D

def iota : GA D (D.sp.Y 0) ≃ₜ* (inst D).GA :=
  (Formalism.L2.SG.AdBridge.toHA (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1).symm

theorem iota_symm_isBridge : Formalism.L2.SG.AdBridge.IsBridge (inst D) (iota D).symm :=
  Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1

theorem iota_rat (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iota D g ∈ (inst D).GFset := by
  have hS := Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)
  have hb := Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) hS.1
  have hGF := hS.2.1 _ hb
  have hg : Formalism.L2.SG.AdBridge.toHA (inst D) hS.1 (iota D g) = g :=
    (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).apply_symm_apply g
  rw [← (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).injective.mem_set_image (a := iota D g)
    (s := (inst D).GFset), hGF, hg]
  exact Iff.rfl

end Formalism.IndefR.RationalEmbedding

end
end

