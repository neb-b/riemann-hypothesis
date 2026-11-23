module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameOO1FrameValPiIso
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting MeasureTheory

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ClassFrameUnitaryProducts

variable {D : D7} (X : HidaSetting D)

theorem piU_mul_inv_apply (u : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ X.SinfU u) (y : X.Vpi u) :
    X.piU u s (X.piU u s⁻¹ y) = y := by
  have hm := (X.piU_rep u).2.1 s hs s⁻¹ (Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hs)
  rw [mul_inv_cancel, (X.piU_rep u).1] at hm
  show (X.piU u s * X.piU u s⁻¹) y = y
  rw [← hm]
  rfl

theorem frame_alg (u u' : D.what₂.Word) {h h' : X.B.I.Ginf} (hh : h ∈ X.SinfU u) (hh' : h' ∈ X.SinfU u')
    (O V : X.Vpi u' →L[ℂ] X.Vpi u) (c : ℂ)
    (hE : (X.piU u h⁻¹).comp (O.comp (X.piU u' h')) = c • V) :
    O = c • ((X.piU u h).comp (V.comp (X.piU u' h'⁻¹))) := by
  have h1 : O = (X.piU u h).comp (((X.piU u h⁻¹).comp (O.comp (X.piU u' h'))).comp (X.piU u' h'⁻¹)) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, piU_mul_inv_apply X u' hh', piU_mul_inv_apply X u hh]
  rw [h1, hE]
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul]

section Transfer

variable {n r k : ℕ}

def nrm1 (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (wb : Fin k → Fin n → ℂ) :
    Fin k → ℂ :=
  (Formalism.L2.SG.RealObj.Dl (Formalism.L2.SG.RealObj.Zhat ε f f' g) (r + 1))⁻¹ •
    Formalism.L2.SG.RealObj.wCoord ε wb (Formalism.L2.SG.RealObj.xPr (Formalism.L2.SG.RealObj.Zhat ε f f' g) g f')

def nrm2 (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (g gi : Matrix (Fin n) (Fin n) ℂ)
    (wb' : Fin k → Fin n → ℂ) : Fin k → ℂ :=
  (star (Formalism.L2.SG.RealObj.Dl (Formalism.L2.SG.RealObj.Zhat ε f f' g) (r + 1)))⁻¹ •
    Formalism.L2.SG.RealObj.wCoord ε wb' (gi *ᵥ Formalism.L2.SG.RealObj.xUn (Formalism.L2.SG.RealObj.Zhat ε f f' g) f)

theorem isDFrame_transfer (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (g₁ gi₁ g₂ gi₂ : Matrix (Fin n) (Fin n) ℂ)
    (wb wb' : Fin k → Fin n → ℂ) (i0 i0' : Fin k) (h h' : Matrix (Fin k) (Fin k) ℂ)
    (hN1 : nrm1 ε f f' g₁ wb = nrm1 ε f f' g₂ wb) (hN2 : nrm2 ε f f' g₁ gi₁ wb' = nrm2 ε f f' g₂ gi₂ wb')
    (hU : ∀ y₂ : Fin n → ℂ, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) y₂ = 0) →
      (∀ b, Formalism.L2.SG.HidaSetting.hJ ε (g₂ *ᵥ f' b) y₂ = 0) →
        ∃ y₁ : Fin n → ℂ, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) y₁ = 0) ∧
          (∀ b, Formalism.L2.SG.HidaSetting.hJ ε (g₁ *ᵥ f' b) y₁ = 0) ∧
          Formalism.L2.SG.RealObj.wCoord ε wb y₁ = Formalism.L2.SG.RealObj.wCoord ε wb y₂ ∧
          Formalism.L2.SG.RealObj.wCoord ε wb' (gi₁ *ᵥ y₁) = Formalism.L2.SG.RealObj.wCoord ε wb' (gi₂ *ᵥ y₂))
    (hD : Formalism.L2.SG.RealObj.IsDFrame ε f f' g₁ gi₁ wb wb' i0 i0' h h') :
    Formalism.L2.SG.RealObj.IsDFrame ε f f' g₂ gi₂ wb wb' i0 i0' h h' := by
  obtain ⟨hu, hu', h1, h2, h3⟩ := hD
  refine ⟨hu, hu', ?_, ?_, fun y ha hb => ?_⟩
  · have e1 : nrm1 ε f f' g₁ wb = nrm1 ε f f' g₂ wb := hN1
    unfold nrm1 at e1
    rw [← e1]
    exact h1
  · have e2 : nrm2 ε f f' g₁ gi₁ wb' = nrm2 ε f f' g₂ gi₂ wb' := hN2
    unfold nrm2 at e2
    rw [← e2]
    exact h2
  · obtain ⟨y₁, ha1, hb1, hw1, hw⟩ := hU y ha hb
    rw [← hw, ← hw1]
    exact h3 y₁ ha1 hb1

end Transfer

end ClassFrameUnitaryProducts

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def dVal (h h' : X.B.I.Ginf) (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.PairVal.cTerm vR s.toTerm •
    ((X.piU u h).comp ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.toTerm)).comp
      (X.piU u' h'⁻¹)))

def PtValueC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 h h' ∧
      (X.piU u h⁻¹).comp ((chiOO X Y u u' s.1).comp (X.piU u' h')) =
        Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm •
          Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

def VIndepLiftC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ h₁ h₁' h₂ h₂', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 h₁ h₁' →
      Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 h₂ h₂' →
        (X.piU u h₁⁻¹).comp ((chiOO X Y u u' s.1).comp (X.piU u' h₁')) =
          (X.piU u h₂⁻¹).comp ((chiOO X Y u u' s.1).comp (X.piU u' h₂'))

def CommonDFrameC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ h ∈ Formalism.L2.SG.RealObj.HsetU X u, ∃ h' ∈ Formalism.L2.SG.RealObj.HsetU X u', ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      ∀ s : LiftT X Y u u' κ R ρ, s.1.relevant →
        ∃ hs hs', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 hs hs' ∧
          dVal X Y u u' vR i0 i0' νq hs hs' s.1 = ζ • dVal X Y u u' vR i0 i0' νq h h' s.1

def CommonDFrameExactC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ h ∈ Formalism.L2.SG.RealObj.HsetU X u, ∃ h' ∈ Formalism.L2.SG.RealObj.HsetU X u',
      ∀ s : LiftT X Y u u' κ R ρ, s.1.relevant → Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 h h'

def IrrelZeroC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), ¬ s.1.relevant →
    chiOO X Y u u' s.1 = 0 ∧ (Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm = 0 ∨
      Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) = 0)

def PairDFrameC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s₁ s₂ : LiftT X Y u u' κ R ρ),
    s₁.1.relevant → s₂.1.relevant → ∀ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s₁.1.pt.1 h h' →
      Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s₂.1.pt.1 h h'

def ScalarAgreeC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s₁ s₂ : LiftT X Y u u' κ R ρ),
    s₁.1.relevant → s₂.1.relevant → ∀ v,
      ClassFrameUnitaryProducts.nrm1 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v)
          (uMat (s₁.1.pt.1 v)) (X.wfr u v) =
        ClassFrameUnitaryProducts.nrm1 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v)
          (uMat (s₂.1.pt.1 v)) (X.wfr u v) ∧
      ClassFrameUnitaryProducts.nrm2 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v)
          (uMat (s₁.1.pt.1 v)) (uMat ((s₁.1.pt.1 v)⁻¹)) (X.wfr u' v) =
        ClassFrameUnitaryProducts.nrm2 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v)
          (uMat (s₂.1.pt.1 v)) (uMat ((s₂.1.pt.1 v)⁻¹)) (X.wfr u' v) ∧
      ∀ y₂ : Fin X.B.I.n → ℂ, (∀ a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v a) y₂ = 0) →
        (∀ b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat (s₂.1.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b) y₂ = 0) →
          ∃ y₁ : Fin X.B.I.n → ℂ, (∀ a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v a) y₁ = 0) ∧
            (∀ b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat (s₁.1.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b) y₁ = 0) ∧
            Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u v) y₁ = Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u v) y₂ ∧
            Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u' v) (uMat ((s₁.1.pt.1 v)⁻¹) *ᵥ y₁) =
              Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u' v) (uMat ((s₂.1.pt.1 v)⁻¹) *ᵥ y₂)

theorem pairDFrameC_of (hS : ScalarAgreeC X Y u u' κ) : PairDFrameC X Y u u' i0 i0' κ := by
  intro R ρ s₁ s₂ h₁ h₂ h h' hD
  refine ⟨hD.1, hD.2.1, fun v => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hS R ρ s₁ s₂ h₁ h₂ v
  exact ClassFrameUnitaryProducts.isDFrame_transfer _ _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 e3 (hD.2.2 v)

theorem classFrameOO1_one_mem (w : D.what₂.Word) : (1 : X.B.I.Ginf) ∈ Formalism.L2.SG.RealObj.HsetU X w := by
  intro v x _
  simp [uMat]

theorem commonDFrameExactC_of (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hPair : PairDFrameC X Y u u' i0 i0' κ) :
    CommonDFrameExactC X Y u u' i0 i0' κ := by
  intro R ρ
  by_cases hex : ∃ s₀ : LiftT X Y u u' κ R ρ, s₀.1.relevant
  · obtain ⟨s₀, h₀⟩ := hex
    obtain ⟨h, h', hD, -⟩ := hP R ρ s₀ h₀
    exact ⟨h, hD.1, h', hD.2.1, fun s hs => hPair R ρ s₀ s h₀ hs h h' hD⟩
  · exact ⟨1, classFrameOO1_one_mem X u, 1, classFrameOO1_one_mem X u', fun s hs => absurd ⟨s, hs⟩ hex⟩

theorem commonDFrameC_of_exact (hE : CommonDFrameExactC X Y u u' i0 i0' κ) :
    CommonDFrameC X Y u u' vR i0 i0' νq κ := by
  intro R ρ
  obtain ⟨h, hh, h', hh', hs⟩ := hE R ρ
  exact ⟨h, hh, h', hh', 1, by simp, fun s hrel => ⟨h, h', hs s hrel, (one_smul ℂ _).symm⟩⟩

theorem classFrameOO1_liftFrame (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hVL : VIndepLiftC X Y u u' i0 i0' κ)
    (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ) (hrel : s.1.relevant)
    (hs hs' : X.B.I.Ginf) (hD : Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' s.1.pt.1 hs hs') :
    chiOO X Y u u' s.1 = dVal X Y u u' vR i0 i0' νq hs hs' s.1 := by
  obtain ⟨h0, h0', hD0, hEq⟩ := hP R ρ s hrel
  rw [hVL R ρ s hrel h0 h0' hs hs' hD0 hD] at hEq
  exact ClassFrameUnitaryProducts.frame_alg X u u' (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hD.1)
    (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hD.2.1) _ _ _ hEq

theorem classFrameOO1_piIso_coe (w : D.what₂.Word) (g : X.B.I.Ginf) (hg : g ∈ X.SinfU w) :
    ((Formalism.L2.SG.RealObj.InfCut.piIso X w g hg : X.Vpi w ≃ₗᵢ[ℂ] X.Vpi w) : X.Vpi w →L[ℂ] X.Vpi w) = X.piU w g := by
  ext x
  rfl

theorem classFrameOO1_piIso_symm (w : D.what₂.Word) (g : X.B.I.Ginf) (hg : g ∈ X.SinfU w) :
    (((Formalism.L2.SG.RealObj.InfCut.piIso X w g hg).symm : X.Vpi w ≃ₗᵢ[ℂ] X.Vpi w) : X.Vpi w →L[ℂ] X.Vpi w) =
      X.piU w g⁻¹ := by
  rw [← Formalism.L2.SG.RealObj.InfCut.piIso_symm X w g hg]

theorem classFrameOO1_frameVal_piIso (h h' : X.B.I.Ginf) (hh : h ∈ X.SinfU u) (hh' : h' ∈ X.SinfU u')
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    frameVal X Y u u' vR i0 i0' νq (Formalism.L2.SG.RealObj.InfCut.piIso X u h hh)
      (Formalism.L2.SG.RealObj.InfCut.piIso X u' h' hh') s = dVal X Y u u' vR i0 i0' νq h h' s := by
  unfold frameVal dVal
  rw [classFrameOO1_piIso_coe, classFrameOO1_piIso_symm]

theorem commonFrameC_of (hP : PtValueC X Y u u' vR i0 i0' νq κ) (hVL : VIndepLiftC X Y u u' i0 i0' κ)
    (hCD : CommonDFrameC X Y u u' vR i0 i0' νq κ) (hZ : IrrelZeroC X Y u u' vR i0 i0' νq κ) :
    CommonFrameC X Y u u' vR i0 i0' νq κ := by
  intro R ρ
  obtain ⟨h, hh, h', hh', ζ, hζ, hcom⟩ := hCD R ρ
  have hS := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hh
  have hS' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hh'
  refine ⟨Formalism.L2.SG.RealObj.InfCut.piIso X u h hS, Formalism.L2.SG.RealObj.InfCut.piIso X u' h' hS', ζ, hζ,
    fun s A B hAB => ?_⟩
  rw [← hAB, classFrameOO1_frameVal_piIso]
  by_cases hrel : s.1.relevant
  · obtain ⟨hs, hs', hDs, hv⟩ := hcom s hrel
    rw [← hv]
    exact classFrameOO1_liftFrame X Y u u' vR i0 i0' νq κ hP hVL R ρ s hrel hs hs' hDs
  · obtain ⟨h0, hc⟩ := hZ R ρ s hrel
    rw [h0]
    unfold dVal
    rcases hc with hc | hc
    · rw [hc, zero_smul, smul_zero]
    · rw [hc]
      simp

theorem irrelZeroC_of (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    IrrelZeroC X Y u u' vR i0 i0' νq κ := by
  intro R ρ s hrel
  refine ⟨?_, Or.inl (cTerm_irrel X Y u u' vR hAt s.1.toTerm hrel)⟩
  unfold chiOO
  rw [hV R ρ s hrel, smul_zero]

end Formalism.L2.SG.Pf.RowForm
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.LiftRowCohT
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open PI.DCRelEquiv.UnitaryGroupMassFormula (nlam_maps_X nlam_inv nlam_mul mem_orth_iff isom_app gmap_mul' gmap_inv' gmap_one')

namespace LiftRowCohT

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem liftT_map_eq {n : S.V ≃ₗ[E] S.V} {U : Submodule E S.V} (h : ∀ x ∈ U, n x ∈ U) :
    U.map (n : S.V →ₗ[E] S.V) = U :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact h y hy) (LinearEquiv.finrank_map_eq n U)

theorem liftT_map_mul (a b : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) :
    U.map ((a * b : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = (U.map (b : S.V →ₗ[E] S.V)).map (a : S.V →ₗ[E] S.V) := by
  rw [← Submodule.map_comp]
  rfl

theorem liftT_xsp_mapLF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
  simp only [Xsp, mapLF, dite_eq_left hγ, Formalism.MainNotions.S.FlagG.X, mapFlag, Submodule.map_span, ← Set.range_comp]
  rfl

theorem liftT_xsp_eq {T : E} (F : LFlag S r T) : Xsp F = Xflag F r := by
  simp only [Xsp, Xflag, Formalism.MainNotions.S.FlagG.X, Formalism.MainNotions.S.FlagG.Xa]
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

variable {Λ : Submodule (𝓞 E) S.V}

theorem liftT_mem_gmap {n : S.V ≃ₗ[E] S.V} {L : Submodule (𝓞 E) S.V} {v : S.V} :
    n v ∈ Formalism.HermitianLatticesTheory.gmap n L ↔ v ∈ L := by
  constructor
  · rintro ⟨w, hw, h⟩
    have e : w = v := n.injective h
    rw [← e]
    exact hw
  · intro h
    exact ⟨v, h, rfl⟩

theorem liftT_maps {n : S.V ≃ₗ[E] S.V} {L : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap n L = L) {v : S.V}
    (hv : v ∈ L) : n v ∈ L := by
  rw [← h]
  exact liftT_mem_gmap.2 hv

theorem liftT_gmap_inf {n : S.V ≃ₗ[E] S.V} (hn : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) (U : Submodule E S.V) :
    Formalism.HermitianLatticesTheory.gmap n (Λ ⊓ toO S U) = Λ ⊓ toO S (U.map (n : S.V →ₗ[E] S.V)) := by
  ext v
  constructor
  · rintro ⟨w, ⟨hwΛ, hwU⟩, rfl⟩
    exact ⟨liftT_maps hn hwΛ, ⟨w, hwU, rfl⟩⟩
  · rintro ⟨hvΛ, ⟨w, hwU, rfl⟩⟩
    have hw : w ∈ Λ := by
      rw [← hn] at hvΛ
      exact liftT_mem_gmap.1 hvΛ
    exact ⟨w, ⟨hw, hwU⟩, rfl⟩

theorem liftT_iotaCompat {T T' : E} {F : LFlag S r T} {F₁ F₂ F₃ : LFlag S r T'} {β β' n : S.V ≃ₗ[E] S.V} {g : ℕ}
    (hc : IotaCompat Λ F F₁ F₂ β g) (hn : n ∈ NLam Λ F)
    (hX : Xsp F₃ = (Xsp F₂).map (n : S.V →ₗ[E] S.V))
    (hβΛ : ∀ x' ∈ Lrep Λ F₁, β x' ∈ Λ)
    (hβ' : ∀ x' ∈ Lrep Λ F₁, β' x' - n (β x') ∈ XLam Λ F₃) :
    IotaCompat Λ F F₁ F₃ β' g := by
  have hnΛ : Formalism.HermitianLatticesTheory.gmap n Λ = Λ := hn.1.2
  have hK : Formalism.HermitianLatticesTheory.gmap n (NgX Λ g F F₂) = NgX Λ g F F₃ := by
    unfold NgX Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'']
    have h1 := liftT_gmap_inf hnΛ (Xsp F)
    have h2 := liftT_gmap_inf hnΛ (Xsp F₂)
    unfold Formalism.HermitianLatticesTheory.gmap at h1 h2 hnΛ
    unfold XLam
    rw [h1, h2, hnΛ, liftT_map_eq (nlam_maps_X hn), ← hX]
  intro x' hx' l hl
  rw [hc x' hx' l hl]
  have hlΛ : l ∈ Λ := hl.1
  have hbx : β x' ∈ Λ := hβΛ x' hx'
  have hnl : n l - l ∈ NgX Λ g F F₃ := by
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact ⟨Submodule.sub_mem _ (liftT_maps hnΛ hlΛ) hlΛ, hn.2.2 l hl.2⟩
  have hd : β' x' - n (β x') ∈ NgX Λ g F F₃ := Submodule.mem_sup_right (hβ' x' hx')
  have e : l - β' x' = n (l - β x') - ((n l - l) + (β' x' - n (β x'))) := by
    rw [map_sub]
    abel
  rw [e, Submodule.sub_mem_iff_left _ (Submodule.add_mem _ hnl hd), ← hK, liftT_mem_gmap]

end Gen

section Grel

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}

theorem liftT_grel_equiv (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) : Equivalence (GRel X u u' F0 F0' Λ Λ') := by
  constructor
  · intro p
    exact ⟨1, one_mem_NLam _ _, 1, one_mem_NLam _ _, by simp⟩
  · rintro p q ⟨n, hn, n', hn', h⟩
    exact ⟨n⁻¹, nlam_inv hn, n'⁻¹, nlam_inv hn', by rw [h]; group⟩
  · rintro p q r ⟨n, hn, n', hn', h⟩ ⟨m, hm, m', hm', h'⟩
    exact ⟨m * n, nlam_mul hm hn, n' * m', nlam_mul hn' hm', by rw [h', h]; group⟩

theorem liftT_grel_of_mk_eq {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {p q : GCar X u u' F0 F0' Λ Λ'}
    (h : Quot.mk (GRel X u u' F0 F0' Λ Λ') p = Quot.mk _ q) : GRel X u u' F0 F0' Λ Λ' p q :=
  (Equivalence.eqvGen_iff (liftT_grel_equiv Λ Λ')).1 (Quot.eqvGen_exact h)

end Grel

end LiftRowCohT

open LiftRowCohT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

def RatPtNeed : Prop :=
  ∀ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ∃ x : X.B.I.GA, RatLink X x n

def FrameFixNeed : Prop :=
  ∀ (s : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (y : Carrier (PD D s.lam (lf D (X.Fu u)) u')) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    Formalism.L2.SG.DataInst.Elig s.toTerm → Gval (lf D (X.Fu u)) y.1 ≠ 0 →
    IsPair s.lam (lf D (X.Fu u)) s.frame y.1 β (gS D) →
    Lat.s0 s.lam (lf D (X.Fu u)) s.frame y.1 β D.R.k = 1 → IsScalar s.lam (lf D (X.Fu u)) s.frame y.1 β →
      ∃ μ : (VS D).V ≃ₗ[D.host.E] (VS D).V, μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap μ s.lam' = s.lam' ∧
        (∀ x ∈ Xsp (lf D (X.Fu u')), μ x ∈ Xsp (lf D (X.Fu u'))) ∧
        (∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), μ x - x ∈ Xsp (lf D (X.Fu u'))) ∧
        DCRel s.lam (lf D (X.Fu u)) y.1 (mapLF (β * s.lin * μ) (lf D (X.Fu u')))

theorem liftTransNeed_of (hR : RatPtNeed X) (hTR : ToTermRel X u u' (X.Fu u) (X.Fu u'))
    (hF : FrameFixNeed X Y u u') : LiftTransNeed X Y u u' := by
  intro s y β hs hy hP h1 h2
  obtain ⟨μ, hμi, hμΛ, hμX, hμo, hdc⟩ := hF s y β hs hy hP h1 h2
  have hRL : IsRowLat D (X.Fu u) s.lam := (Y.rowsOK u).1 s.lam s.mem
  have hγi : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1
  have hβi : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hP.1.1
  have hβΛ : Formalism.HermitianLatticesTheory.gmap β s.lam = s.lam := hP.1.2
  have hδi : β * s.lin * μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (mul_mem hβi hγi) hμi
  have hδΛ : Formalism.HermitianLatticesTheory.gmap (β * s.lin * μ) s.lam' = s.lam := by
    rw [gmap_mul', gmap_mul', hμΛ, hγΛ, hβΛ]
  have hPD : PD D s.lam (lf D (X.Fu u)) u' (mapLF (β * s.lin * μ) (lf D (X.Fu u'))) :=
    Formalism.L2.SG.Closed.TermStable_holds D u u' (X.Fu u) s.lam hRL y _ hdc
  obtain ⟨x, hx⟩ := hR _ hδi
  let q : GCar X u u' (X.Fu u) (X.Fu u') s.lam s.lam' := ⟨(x, β * s.lin * μ), hx, hδi, hδΛ, hPD⟩
  let s' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') :=
    ⟨s.lam, s.mem, s.lam', s.mem', Quot.mk _ q⟩
  have hrel : GRel X u u' (X.Fu u) (X.Fu u') s.lam s.lam' s'.rep q :=
    liftT_grel_of_mk_eq (Quot.out_eq (Quot.mk (GRel X u u' (X.Fu u) (X.Fu u') s.lam s.lam') q))
  obtain ⟨n, hn, n', hn', hlin⟩ := (liftT_grel_equiv s.lam s.lam').symm hrel
  refine ⟨s', rfl, rfl, ?_, ?_⟩
  · show (⟨s.lam, s.mem, TermDef.mk _ _ _ ⟨s'.frame, s'.rep.2.2.2.2⟩⟩ : Term D u u' (X.Fu u) (Y.what₂ u)) =
      ⟨s.lam, s.mem, TermDef.mk _ _ _ y⟩
    have e1 : TermDef.mk s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') ⟨s'.frame, s'.rep.2.2.2.2⟩ =
        TermDef.mk s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') ⟨_, hPD⟩ :=
      Quot.sound (hTR s.lam s.lam' s'.rep q hrel)
    have e2 : TermDef.mk s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') y =
        TermDef.mk s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') ⟨_, hPD⟩ :=
      Quot.sound hdc
    exact congrArg (Term.mk s.lam s.mem) (e1.trans e2.symm)
  ·
    set A := Xsp (lf D (X.Fu u')) with hA
    have hs'i : s'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s'.rep.2.2.1
    have hlin' : s'.lin = n * (β * s.lin * μ) * n' := hlin
    have hAn' : A.map (n' : (VS D).V →ₗ[D.host.E] (VS D).V) = A := liftT_map_eq (nlam_maps_X hn')
    have hAμ : A.map (μ : (VS D).V →ₗ[D.host.E] (VS D).V) = A := liftT_map_eq hμX
    have hX3 : Xsp s'.frame = ((A.map (s.lin : (VS D).V →ₗ[D.host.E] (VS D).V)).map
        (β : (VS D).V →ₗ[D.host.E] (VS D).V)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      show Xsp (mapLF s'.lin (lf D (X.Fu u'))) = _
      rw [liftT_xsp_mapLF _ hs'i, hlin', liftT_map_mul, liftT_map_mul, hAn', liftT_map_mul, liftT_map_mul, hAμ]
    have hX2 : Xsp y.1 = (A.map (s.lin : (VS D).V →ₗ[D.host.E] (VS D).V)).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      calc
        Xsp y.1 = Xflag y.1 D.R.rS := liftT_xsp_eq _
        _ = (Xflag s.frame D.R.rS).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := (hP.2.1 D.R.rS).symm
        _ = _ := congrArg (Submodule.map _)
          ((liftT_xsp_eq s.frame).symm.trans (liftT_xsp_mapLF s.lin hγi (lf D (X.Fu u'))))
    refine liftT_iotaCompat hP.2.2.2 hn (hX3.trans (congrArg (Submodule.map _) hX2.symm))
      (fun x' hx' => liftT_maps hβΛ hx'.1) ?_
    intro x' hx'
    have hw : s.lin (s.lin⁻¹ x') = x' := s.lin.apply_symm_apply x'
    set w := s.lin⁻¹ x' with hwdef
    have hwΛ : w ∈ s.lam' := by
      have := liftT_mem_gmap (n := s.lin⁻¹) (L := s.lam) (v := x') |>.2 hx'.1
      have hinv : Formalism.HermitianLatticesTheory.gmap s.lin⁻¹ s.lam = s.lam' := by
        rw [← hγΛ, ← gmap_mul', inv_mul_cancel, gmap_one']
      rw [hinv] at this
      exact this
    have hwo : w ∈ orth (VS D) A := by
      rw [mem_orth_iff]
      intro a ha
      have h0 := (mem_orth_iff.1 hx'.2) (s.lin a) (by
        show s.lin a ∈ Xsp (mapLF s.lin (lf D (X.Fu u')))
        rw [liftT_xsp_mapLF _ hγi]
        exact Submodule.mem_map_of_mem ha)
      rw [← hw, isom_app hγi] at h0
      exact h0
    have hn'w : n' w - w ∈ s.lam' ⊓ toO (VS D) A :=
      ⟨Submodule.sub_mem _ (liftT_maps hn'.1.2 hwΛ) hwΛ, hn'.2.2 w hwo⟩
    have hd : μ (n' w) - w ∈ s.lam' ⊓ toO (VS D) A := by
      have e : μ (n' w) - w = μ (n' w - w) + (μ w - w) := by
        rw [map_sub]
        abel
      rw [e]
      exact Submodule.add_mem _ ⟨liftT_maps hμΛ hn'w.1, hμX _ hn'w.2⟩
        ⟨Submodule.sub_mem _ (liftT_maps hμΛ hwΛ) hwΛ, hμo w hwo⟩
    have e : (s'.lin * s.lin⁻¹) x' - n (β x') = n (β (s.lin (μ (n' w) - w))) := by
      rw [map_sub, map_sub, map_sub, hw]
      congr 1
      show s'.lin w = _
      rw [hlin']
      rfl
    rw [e]
    have hγd : s.lin (μ (n' w) - w) ∈ s.lam := by
      rw [← hγΛ]
      exact liftT_mem_gmap.2 hd.1
    refine ⟨liftT_maps hn.1.2 (liftT_maps hβΛ hγd), ?_⟩
    show _ ∈ Xsp s'.frame
    rw [hX3]
    exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hd.2))

theorem liftRowCohC_of_frameFix (hR : RatPtNeed X) (hTR : ToTermRel X u u' (X.Fu u) (X.Fu u'))
    (hF : FrameFixNeed X Y u u') (hD : IotaDictNeed X Y u u') : LiftRowCohC X Y u u' :=
  liftRowCohC_of X Y u u' (liftTransNeed_of X Y u u' hR hTR hF) hD

end Formalism.L2.SG.Pf.RowForm
end
end

