module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.IrredSt

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.CompSt
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

theorem compSt : CompSt := by
  intro D V H _ _ _ π hπ w W hW
  set ρ := π.comp (embArch D.sp.cm.sig V.gram w) with hρdef
  have hρ : IsUnitaryRep ρ := isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
  let δ : IrrU (GArch D.sp.cm.sig V.gram w) := ⟨W, hW.1.rep, isIrrUnitary_rep hρ hW⟩
  refine ⟨δ, ?_⟩
  show isoPart δ.π ρ ⊤ = ⊤
  set P := isoPart δ.π ρ ⊤ with hPdef
  have hP : IsSubrep ρ P := isSubrep_isoPart

  have hcomm : ∀ g' : GA D V, projArch D.sp.cm.sig V.gram w g' = 1 → ∀ v ∈ P, π g' v ∈ P := by
    intro g' hg' v hv
    have hle : P ≤ P.comap ((π g' : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine isoPart_le (hP.1.preimage (π g').continuous) fun T hT x => ?_
      show π g' (T x) ∈ P
      have hT' : (π g').comp T ∈ homIn δ.π ρ ⊤ := by
        refine mem_homIn_top.2 fun h y => ?_
        have hc : Commute (embArch D.sp.cm.sig V.gram w h) g' := commute_embArch _ _ h hg'
        have e1 : π g' (π (embArch D.sp.cm.sig V.gram w h) (T y)) = π (embArch D.sp.cm.sig V.gram w h) (π g' (T y)) := by
          rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, hc.eq]
        simp only [ContinuousLinearMap.comp_apply]
        rw [(mem_homIn_top.1 hT) h y]
        exact e1
      exact apply_mem_isoPart hT' x
    exact hle hv
  have hinv : IsSubrep π P := by
    refine ⟨hP.1, fun g v hv => ?_⟩
    set x := projArch D.sp.cm.sig V.gram w g
    set g' : GA D V := (embArch D.sp.cm.sig V.gram w x)⁻¹ * g
    have hg' : projArch D.sp.cm.sig V.gram w g' = 1 := by
      simp [g', x, map_mul, map_inv]
    have hg : g = embArch D.sp.cm.sig V.gram w x * g' := by simp [g']
    rw [hg, map_mul, ContinuousLinearMap.mul_apply]
    exact hP.2 x _ (hcomm g' hg' v hv)
  have hne : P ≠ ⊥ := by
    obtain ⟨y, hyW, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.2.1
    intro hbot
    have hsub : W.subtypeL ∈ homIn δ.π ρ ⊤ := mem_homIn_top.2 fun h z => rfl
    have hm : W.subtypeL ⟨y, hyW⟩ ∈ P := apply_mem_isoPart hsub _
    rw [hbot] at hm
    exact hy0 ((Submodule.mem_bot ℂ).1 hm)
  exact (hπ.irred.2 P hinv).resolve_left hne

end MainStatements.Flath2
end

-- bundled from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.CptSt
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

theorem cptSt : CptSt := by
  intro hCT D V μ _ _ H _ _ _ π hπ hm f hf
  have c := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  rw [GlobalTheory.AutMult.mCusp_eq_Rcusp, Ne, GlobalTheory.AutMult.multIn_eq_zero_iff] at hm
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hρ := GlobalTheory.Cusp.isUnitaryRep_Rcusp V μ
  have hb0 : GlobalTheory.AutMult.be T T ≠ 0 := fun e => by
    have h := GlobalTheory.AutMult.be_self_pos hπ hρ hT hT0
    rw [e] at h
    simp at h
  have key : ∀ x, T.adjoint (T x) = GlobalTheory.AutMult.be T T • x := fun x =>
    ext_inner_left ℂ fun y => by
      rw [ContinuousLinearMap.adjoint_inner_right, inner_smul_right (𝕜 := ℂ) (E := H)]
      exact GlobalTheory.AutMult.inner_eq_be hπ hρ hT hT x y
  have hcomm : T ∘L repOp π μ f = GlobalTheory.Cusp.RcuspOp V μ f ∘L T :=
    hπ.unitary.comp_repOp hρ c.1 c.2 T hT.2
  have hR : IsCompactOperator (GlobalTheory.Cusp.RcuspOp V μ f) :=
    GlobalTheory.DiscreteSum.isCompactOperator_of_isHilbertSchmidt (hCT D V μ f hf).isHilbertSchmidt
  have hv : ∀ v, T (repOp π μ f v) = GlobalTheory.Cusp.RcuspOp V μ f (T v) := fun v =>
    DFunLike.congr_fun hcomm v
  have e : ⇑(repOp π μ f) =
      (GlobalTheory.AutMult.be T T)⁻¹ • (⇑T.adjoint ∘ (⇑(GlobalTheory.Cusp.RcuspOp V μ f) ∘ ⇑T)) := funext fun v => by
    show repOp π μ f v = (GlobalTheory.AutMult.be T T)⁻¹ • T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v))
    have k : T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v)) = GlobalTheory.AutMult.be T T • repOp π μ f v :=
      (congrArg T.adjoint (hv v)).symm.trans (key (repOp π μ f v))
    calc repOp π μ f v = (GlobalTheory.AutMult.be T T)⁻¹ • (GlobalTheory.AutMult.be T T • repOp π μ f v) :=
          (inv_smul_smul₀ hb0 _).symm
      _ = (GlobalTheory.AutMult.be T T)⁻¹ • T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v)) := congrArg _ k.symm
  rw [e]
  exact ((hR.comp_clm T).clm_comp T.adjoint).smul (GlobalTheory.AutMult.be T T)⁻¹

end MainStatements.Flath2
end

