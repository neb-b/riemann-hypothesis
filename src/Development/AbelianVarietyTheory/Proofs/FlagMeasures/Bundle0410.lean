module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLinkConjugateMemIntegralRealPoints
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.CoverAct

theorem ratLink_mem_ROinf : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) → ∃ x : X.B.I.GA, Formalism.L2.SG.TermOp.RatLink X x ((W.δ u)⁻¹ * n * W.δ u) ∧ x.1 ∈ Formalism.L2.SG.TermOp.ROinf s := by
  intro D X Y W u u' s n hn
  obtain ⟨h1, h2⟩ := hn
  have hδ := W.isom u
  have hm1 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam (lf D (X.Fu u)) := by
    rw [← Formalism.L2.SG.TermTieOf.mapL_lf W u] at h1
    exact (Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h1
  have hm2 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam s.frame :=
    (Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h2
  have hiso : (W.δ u)⁻¹ * n * W.δ u ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    mul_mem (mul_mem (inv_mem hδ) h1.1.1) hδ
  have hlin : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hlam : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1
  have hfr : s.frame = Formalism.L2.SG.Saturated.mapL s.lin hlin (lf D (X.Fu u')) := by
    unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
    rw [dite_eq_left hlin]
    rfl
  rw [hfr, ← hlam] at hm2
  have hm3 := (Formalism.L2.SG.Pf.mem_NLam_map s.lin hlin _ _ _).1 hm2
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X _ hiso
  exact ⟨x, hx, x, _, hx, rfl, hm1, hm3⟩

end GlobalTheory.CoverAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalRootCoordinatesEqFrameMatrix
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.LoopVol

open Formalism.L2.SG.HidaSetting

theorem hJ_sum_right' {n m : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) (g : Fin m → ℂ)
    (y : Fin m → Fin n → ℂ) : hJ ε x (∑ i, g i • y i) = ∑ i, g i * hJ ε x (y i) := by
  unfold hJ
  simp only [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem ratCoord_eq_matOn : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ))) (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ)) M → ∀ q : GlobalTheory.LoopV.roots (ptMat w), GlobalTheory.LoopVol.ratCoord X u' w γ s y τ q = M q.1.1 q.1.2 := by
  intro D X u' w γ s y τ M hM q
  unfold GlobalTheory.LoopVol.ratCoord
  rw [hM q.1.2, hJ_sum_right', Fin.sum_univ_castSucc]
  have hfe : ∀ i : Fin D.R.rS, hJ (X.B.I.ε (X.pl.symm τ)) (rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
      (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) (Fin.castSucc i)) = if i = ⟨q.1.1.1, root_fst_lt w q⟩ then 1 else 0 := by
    intro i
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Fin.snoc_castSucc, Complex.ofReal_one, one_pow, inv_one, one_smul]
    exact (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X _ _ _).trans
      (by rw [Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X]; split_ifs <;> simp)
  have hfz : hJ (X.B.I.ε (X.pl.symm τ)) (rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
      (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) (Fin.last _)) = 0 := by
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Fin.snoc_last, Complex.ofReal_one, one_pow, inv_one, one_smul]
    exact (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X _ _ _).trans (by rw [(X.zu_orth u' _).2]; simp)
  simp only [hfe, hfz, mul_ite, mul_one, mul_zero, add_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1

end GlobalTheory.LoopVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealBesselSubgroupActsFrameUpperUnitriangular
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.LoopAct

open scoped Classical

theorem exists_coeff_of_mem_span_image {r n : ℕ} (e : Fin r → Fin n → ℂ) (s : Set (Fin r)) (x : Fin n → ℂ)
    (hx : x ∈ Submodule.span ℂ (e '' s)) : ∃ c : Fin r → ℂ, (∀ b, b ∉ s → c b = 0) ∧ x = ∑ b, c b • e b := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  refine ⟨l, fun b hb => ?_, ?_⟩
  · by_contra h
    exact hb (hl (Finsupp.mem_support_iff.mpr h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro b
    exact zero_smul ℂ (e b)

theorem exists_upUni_of_inS {r n : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : Formalism.L2.SG.HidaSetting.InS e z g) :
    ∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUpUni M ∧
      IsMatOn g (Fin.snoc (α := fun _ => Fin n → ℂ) e z) M := by
  set f : Fin (r + 1) → Fin n → ℂ := Fin.snoc (α := fun _ => Fin n → ℂ) e z with hf

  have hcol : ∀ b : Fin (r + 1), (g - 1) *ᵥ f b ∈ Submodule.span ℂ (e '' {c : Fin r | c.1 < b.1}) := by
    intro b
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simpa [hf, Formalism.L2.SG.HidaSetting.spanLt] using hg.2
    · simpa [hf, Formalism.L2.SG.HidaSetting.spanLt] using hg.1 a
  choose D hD0 hDs using fun b => exists_coeff_of_mem_span_image e _ _ (hcol b)
  refine ⟨fun c b => (if c = b then 1 else 0) + (if h : c.1 < r then D b ⟨c.1, h⟩ else 0), ?_, ?_⟩
  · intro i j
    constructor
    · intro hji
      have hne : i ≠ j := fun h => (lt_irrefl j) (h ▸ hji)
      simp only [hne, if_false, zero_add]
      split_ifs with h
      · apply hD0
        simp only [Set.mem_setOf_eq, not_lt]
        exact le_of_lt hji
      · rfl
    · rintro rfl
      simp only [if_true]
      split_ifs with h
      · rw [hD0 i ⟨i.1, h⟩ (by simp)]
        ring
      · ring
  · intro b
    have hg1 : g *ᵥ f b = (g - 1) *ᵥ f b + f b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    rw [hg1, hDs b]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [add_comm, Fin.sum_univ_castSucc]
    simp [hf]

theorem sinfU_frame_upUni : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : X.B.I.Ginf), y ∈ X.SinfU u → ∀ v : NumberField.InfinitePlace X.B.I.F, ∃ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, IsUpUni M ∧ GlobalTheory.LoopAct.IsMatOn (uMat (y v)) (Formalism.L2.SG.RealObj.frm X u 1 v) M := by
  intro D X u y hy v
  obtain ⟨M, hM, hMat⟩ := exists_upUni_of_inS _ _ _ (hy v)
  refine ⟨M, hM, ?_⟩
  have hfr : Formalism.L2.SG.RealObj.frm X u 1 v = Fin.snoc (α := fun _ => Fin X.B.I.n → ℂ)
      (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Formalism.L2.SG.RealObj.fam]
  rw [hfr]
  exact hMat

end GlobalTheory.LoopAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointRationalIsometryActsFrameMatrix
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.ActQ

theorem snoc_map {α β : Type*} {r : ℕ} (f : α → β) (e : Fin r → α) (z : α) (j : Fin (r + 1)) :
    f (Fin.snoc (α := fun _ => α) e z j) = Fin.snoc (α := fun _ => β) (fun a => f (e a)) (f z) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

end GlobalTheory.ActQ

theorem GlobalTheory.realPoint_ratIsom_isMatOn : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : X.B.I.GA) (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ j, n (frame s.frame j) = ∑ i, A i j • frame s.frame i) → ∀ v : NumberField.InfinitePlace X.B.I.F, GlobalTheory.LoopAct.IsMatOn (uMat (x.1 v)) (fun j => uMat (s.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v j) (A.map (embS D (X.pl v))) := by
  intro D X Y u u' s n x A hR hA v
  obtain ⟨M, -, hM1, -, hM3⟩ := hR
  obtain ⟨M', -, hM1', -, hM3'⟩ := s.rep.2.1
  have hP' : ∀ v, uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (↑M' : Matrix _ _ _).map ⇑(X.B.I.φ v) * X.B.I.P v := hM1'
  have hL' : ∀ y, X.crd (s.lin y) = (↑M' : Matrix _ _ _) *ᵥ X.crd y := hM3'
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hfr : ∀ j, frame s.frame j = s.lin (Fin.snoc (α := fun _ => (VS D).V) X.eX (X.zu u') j) := by
    intro j
    have e1 : s.frame = Formalism.L2.SG.TermOp.mapLF s.lin (lf D (X.Fu u')) := rfl
    rw [e1]
    unfold Formalism.L2.SG.TermOp.mapLF
    rw [dite_eq_left hiso]
    rw [GlobalTheory.ActQ.snoc_map (f := (s.lin : (VS D).V → (VS D).V)), ← X.Fu_e u', ← X.flagZVector u']
    rfl
  have hfrm : ∀ j, Formalism.L2.SG.RealObj.frm X u' 1 v j =
      rv X.B.I v (X.crd (Fin.snoc (α := fun _ => (VS D).V) X.eX (X.zu u') j)) := by
    intro j
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
    rw [GlobalTheory.ActQ.snoc_map (f := fun y => rv X.B.I v (X.crd y))]
    rfl
  have hf : ∀ j, uMat (s.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v j = rv X.B.I v (X.crd (frame s.frame j)) := by
    intro j
    rw [hfrm, hfr, hL', ← Formalism.L2.SG.Pf.Level.rv_mulVec X v, ← hP' v]
  have hsum : ∀ (c : Fin (D.R.rS + 1) → D.host.E) (w : Fin (D.R.rS + 1) → (VS D).V),
      rv X.B.I v (X.crd (∑ i, c i • w i)) = ∑ i, embS D (X.pl v) (c i) • rv X.B.I v (X.crd (w i)) := by
    intro c w
    have hc : X.crd (∑ i, c i • w i) = ∑ i, X.ιE.symm (c i) • X.crd (w i) := by
      funext l
      set_option synthInstance.maxHeartbeats 100000 in
        simp [HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, map_sum, Finset.sum_apply, smul_eq_mul]
    rw [hc]
    unfold rv
    have hv : (fun l => X.B.I.φ v ((∑ i, X.ιE.symm (c i) • X.crd (w i)) l)) =
        ∑ i, embS D (X.pl v) (c i) • fun l => X.B.I.φ v (X.crd (w i) l) := by
      funext l
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Finset.sum_apply, map_sum, X.φ_eq]
    rw [hv, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul]
  intro b
  dsimp only
  rw [hf b, hM1 v, Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3, hA b, hsum]
  simp_rw [hf, Matrix.map_apply]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserHaarRootCoordinatesLeLebesgue
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.LoopVol

theorem pinned_ratCoord_le : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γw sf : X.B.I.Ginf) (μw : MeasureTheory.Measure X.B.I.Ginf), IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw → μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w → D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 → ∀ A : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet A → (μw.map (fun y => sf * y * sf⁻¹)) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro D X u u' w γw sf μw _hH hmap hc A hA
  classical

  let ι : GlobalTheory.LoopV.roots (ptMat w) ≃ Formalism.L2.SG.RealObj.FreeE w :=
    Equiv.subtypeEquivRight (fun p => _root_.GlobalTheory.roots_ptMat_iff D.host.E (D.R.rS + 1) w p.1 p.2)
  let d : GlobalTheory.LoopV.roots (ptMat w) → ℕ := fun q => q.1.2.1 - q.1.1.1
  let S : (NumberField.InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) → (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ) :=
    fun x τ q => (((D.host.rdE : ℝ) : ℂ) ^ d q)⁻¹ * x (X.pl.symm τ) (ι q)
  have hS : Continuous S := by
    refine continuous_pi fun τ => continuous_pi fun q => continuous_const.mul ?_
    exact (continuous_apply _).comp (continuous_apply _)
  have hΦ : Continuous (fun y : X.B.I.Ginf => sf * y * sf⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hst := Formalism.L2.SG.Pf.LoopBPin.stCoord_cont (X := X) u' w γw
  have hrat := ratCoord_cont X u' w γw sf
  have hpre : (fun y : X.B.I.Ginf => sf * y * sf⁻¹) ⁻¹' (ratCoord X u' w γw sf ⁻¹' A) =
      Formalism.L2.SG.RealObj.stCoord X u' w γw ⁻¹' (S ⁻¹' A) := by
    ext y
    simp only [Set.mem_preimage]
    have : ratCoord X u' w γw sf (sf * y * sf⁻¹) = S (Formalism.L2.SG.RealObj.stCoord X u' w γw y) := by
      funext τ q
      exact ratCoord_conj_eq_stCoord D X u' w γw sf y τ q (ι q) rfl
    rw [this]
  have hB : MeasurableSet (S ⁻¹' A) := hS.measurable hA
  rw [Measure.map_apply hΦ.measurable (hrat.measurable hA), hpre,
    ← Measure.map_apply hst.measurable hB, hmap]
  have hrd : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE (D := D)
  have key := _root_.GlobalTheory.CoordScale.measure_preimage_reindex_scale_le D.what₂.Tau (NumberField.InfinitePlace X.B.I.F) (GlobalTheory.LoopV.roots (ptMat w)) (Formalism.L2.SG.RealObj.FreeE w)
    X.pl.symm ι D.host.rdE (D.host.ka / (X.B.g : ℝ) / Real.pi) d hrd hc A hA
  refine le_trans key ?_
  gcongr
  · rw [D.what₂.card_Tau]
  · have hsum : ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ (D.R.rS + 1) ^ 3 := by
      calc ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ ∑ _q : GlobalTheory.LoopV.roots (ptMat w), (D.R.rS + 1) :=
            Finset.sum_le_sum fun q _ => by
              have := q.1.2.2; simp only [d]; omega
        _ = Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) * (D.R.rS + 1) := by simp
        _ ≤ (D.R.rS + 1) ^ 2 * (D.R.rS + 1) := by
            gcongr
            calc Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) ≤ Fintype.card (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :=
                  Fintype.card_subtype_le _
              _ = (D.R.rS + 1) ^ 2 := by simp [sq]
        _ = (D.R.rS + 1) ^ 3 := by ring
    exact hsum

end GlobalTheory.LoopVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TcritLowAlongFamilyGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelGap

private theorem VV_eq_vand_lamSH_of_standingHypotheses (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT : ℝ) (hT : Ties D) (hS : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hL : 1 ≤ Cl * large₂.sc.L)
    (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by

  have hanti : StrictAnti (lamSH D.R (D.hc τ)) := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
  have hd : D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hDs D large₂ C' Cl Cg cb Cu cT CT hT hS hL τ
  have hN : 2 * D.R.rS + D.R.k + 1 = D.R.r := dimS_eq D.R
  have hpos : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hd, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← hN]
  field_simp

theorem tcritLow_along_family_gap :
    Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusBranching.admF5 Fm Cg cb Cu cT CT C0 := by
  intro _ hH _ Cg cb Cu cT CT C0
  refine ⟨40, fun eps Fm _ hCl _ => ?_⟩
  unfold VanishingOnXAndXPlusBranching.admF5 OwnEv
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨hxk, hb⟩ := GlobalTheory.CritLevel.sizes_low _ (Fm.sizes x hx1 i)
  have hL1 : 1 ≤ (Fm.L x i).sc.L := by
    show 1 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps
    exact Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hL : 1 ≤ sCl Fm * (Fm.L x i).sc.L := by nlinarith
  intro h0
  exact GlobalTheory.CritLevel.tcrit_low _ _ _ _ _ _ _ _ _ _ hCl
    (fun τ => VV_eq_vand_lamSH_of_standingHypotheses hH.2.2.2 _ _ _ _ _ _ _ _ _ (Fm.ties x i) h0.1 hL τ) hb hxk h0

end GlobalTheory.CritLevelGap
end

