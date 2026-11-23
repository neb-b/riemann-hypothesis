module

public import Formalism.LocalToGlobal.InertKernelTheory.ScalG
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0006
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0005
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDataRec
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgebraicTranslatesAllData
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrame
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTrace
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrob
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDict
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0002
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.AdmissibleEleventhInert
public import Formalism.LocalToGlobal.InertKernelTheory.KernelsIntegralInert

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

theorem linSub_scl {σ R : Type} [Fintype σ] [CommRing R] (c : R) (A : σ → σ → R) (G : MvPowerSeries σ R) :
    Formalism.MainNotions.FormalGroupSystem.linSub (fun x y => c * A x y) G = Formalism.MainNotions.FormalGroupSystem.linSub A (Formalism.L2.KerInert.Rep.sclY c G) := by
  have ha : MvPowerSeries.HasSubst (fun k : σ =>
      (MvPowerSeries.C c * MvPowerSeries.X k : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have hb : MvPowerSeries.HasSubst (fun x : σ =>
      (∑ y, MvPowerSeries.C (A x y) * MvPowerSeries.X y : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  unfold Formalism.MainNotions.FormalGroupSystem.linSub Formalism.L2.KerInert.Rep.sclY
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hb, map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C,
    MvPowerSeries.subst_X hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul]

variable {p : ℕ} [Fact p.Prime]

theorem subBG_eq {X : Sys p} {D : D7} (E : CEmbC X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (fd : FData X D) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (x y : D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) :
    subBG E.toCEmb pos fd j La La' x y = Formalism.L2.KerInert.RepFrame.subGen X E pos fd.frM j La La' x y := by
  unfold subBG Formalism.L2.KerInert.RepFrame.subGen
  split_ifs <;> rfl

theorem ltC_eq (g : GL3Theta.G1 p) (hLT : LTIso g) :
    ltC g hLT = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹ := by
  unfold ltC Formalism.L2.KerInert.BeCob.eLT
  rw [mul_inv, Units.val_inv_eq_inv_val]

theorem twInt_all (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) : Formalism.L2.KerInert.RepFrame.TwInt X E := by
  intro v s w
  rw [Formalism.L2.KerInert.RepFrob.twE_eq, Formalism.L2.KerInert.RepFrob.twT_alg]
  exact Formalism.L2.G.Pend.norm_wToC_le p _


end Formalism.L2.KerInert.KG
