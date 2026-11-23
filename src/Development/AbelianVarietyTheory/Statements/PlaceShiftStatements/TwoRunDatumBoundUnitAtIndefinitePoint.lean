module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem finite_tuples_of_indefiniteSidePoint : Finite p.P.T := by
  have h := p.charW.tup
  refine Finite.of_surjective (fun o : Option p.R.twPl => o.elim p.P.A3.A.μ0 fun w => p.R.mu w) fun t => ?_
  rcases h.mu_used t with rfl | ⟨w, rfl⟩
  · exact ⟨none, rfl⟩
  · by_cases hw : w ∈ p.R.twPl
    · exact ⟨some ⟨w, hw⟩, rfl⟩
    · exact ⟨none, (h.mu_off w hw).symm⟩

theorem twoRunDatum_boundUnit_at_indefinitePoint {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (r : TwoRuns p.T p.P.Gp) {c : OnConst} (O : Obj p c)
    (h : RecAt p Tp r O) (C CH : ℝ) : ErrorConstantMatchesDefinition ((R2 p).num (F2 p) C CH) O C ∧ O.b = L.sc.b := by
  obtain ⟨st, hd⟩ := h.1.depth
  letI := hostAlg D
  have hb : O.b = L.sc.b := by
    unfold OnObj.b OnObj.xe
    rw [hd.x_eq, hd.eps_eq]; rfl
  refine ⟨fun j => ?_, hb⟩
  change C * (L.sc.x ^ L.sc.eps * ((D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.x ^ L.sc.eps + L.Nc)) = C * O.E1u
  unfold OnObj.E1u OnObj.B0
  rw [L_eq, hb, h.1.Nc_eq, hd.f_eq, hd.m_eq]
  unfold OnObj.xe
  rw [hd.x_eq, hd.eps_eq]

end GlobalTheory.BigOn.Check

end
