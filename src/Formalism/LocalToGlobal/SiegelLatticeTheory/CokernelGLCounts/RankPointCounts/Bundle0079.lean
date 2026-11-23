module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0048
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocOpenHolds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0077

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaVLift
section
noncomputable section

namespace Formalism.L2.SG.Pf.LiftCellVolume

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem lemmaVLiftC_of (hRC : Formalism.L2.SG.TermOp.Vanish.RCocompactC) {D : D7} (X : HidaSetting D)
    (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) :
    Formalism.L2.SG.Pf.RowForm.LemmaVLiftC X Y u u' κ := by
  intro R ρ s hs
  exact Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Pf.chiTrivialC_outright Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds hRC Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y s.1 hs

theorem LemmaVLiftC_holds {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) :
    Formalism.L2.SG.Pf.RowForm.LemmaVLiftC X Y u u' κ :=
  lemmaVLiftC_of Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds X Y u u' κ

end Formalism.L2.SG.Pf.LiftCellVolume
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.MassDataPos

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glkC_pos (k g : ℕ) (hg : g.Prime) : 0 < glkC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold glkC
  exact Nat.card_pos

theorem ukC_pos (k g : ℕ) (hg : g.Prime) : 0 < ukC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ukC
  exact Nat.card_pos

theorem ggC_pos (r k g : ℕ) (hg : g.Prime) : 0 < ggC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ggC
  exact Nat.card_pos

theorem nnC_pos (r k g : ℕ) (hg : g.Prime) : 0 < nnC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold nnC
  rw [Nat.card_pos_iff]
  refine ⟨⟨⟨1, ?_⟩⟩, inferInstance⟩
  unfold Formalism.FourierDecayAlt.S3.IsN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [Formalism.DoubleCosetMeasures.IsUpUni, Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32]
       exact ⟨fun i j hij => by simp [Matrix.one_apply, (show j < i from hij).ne'], fun a => by simp [Matrix.one_apply]⟩)
    | (simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)
    | (ext i j; simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)

section Main

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev bk : Formalism.FourierDecayAlt.S3.MassData (TypX X) := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq

def MassDataPosC : Prop := (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos

def LocHaarPosC : Prop :=
  (∀ p, 0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp' p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp' p) ∧
  0 < (X.measG.μGf (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))).toReal ∧
  0 < ((X.measW u).μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < ((X.measW u').μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN'

def CovolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volB

def QuotVolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN'

def RecPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).deg ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0 ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d'

theorem gOf_prime (p : TypX X) : (gOf p).Prime := by
  unfold gOf
  split_ifs
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1

theorem massDataPosC_of (hL : LocHaarPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hCv : CovolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hQv : QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hR : RecPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hP : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hCoo : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1)
    (hκ : 0 < Formalism.L2.SG.MassDataConc.kapN D) (hsd : 0 ≤ sd) (hC : 0 ≤ C) (hTh : 0 < Th) :
    MassDataPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hv, -, -, -, hUo, -, hZZ, hPP, -, hal, -⟩ := hP
  obtain ⟨hloc, hGf, hSf, hSf', hH, hH', hHpp, hHpp', hN, hN'⟩ := hL
  obtain ⟨hG, hHa, hHa', hNa, hNa', hB⟩ := hCv
  obtain ⟨hvH, hvH', hvN, hvN'⟩ := hQv
  obtain ⟨hdeg, hdp, hdp', hr0, hr0', hd, hd'⟩ := hR
  set B := bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hBdef
  have hMp : ∀ p, 0 < B.Mp p := fun p => (hv p.1).1 p.2
  have hU00p : ∀ p, 0 < B.localVolumeAtPlace p := fun p => (hv p.1).2.1
  have hKo : 0 < B.μKo := div_pos hGf (Finset.prod_pos fun p _ => (hloc p).1)
  have hSo : 0 < B.μSo := div_pos hSf (Finset.prod_pos fun p _ => (hloc p).2.2.2.1)
  have hSo' : 0 < B.μSo' := div_pos hSf' (Finset.prod_pos fun p _ => (hloc p).2.2.2.2.1)
  have hU00o : 0 < B.localVolumeArchimedean := hUo
  have hMo : 0 < B.Mo := div_pos (mul_pos hU00o (pow_pos hKo 2)) (mul_pos hSo hSo')
  have hZ : 0 < B.volZZ := hZZ
  have hPPp : 0 < B.volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos fun l _ => (hPP l).2
  have hAl : 0 < B.al := mul_pos (Finset.prod_pos fun p _ => (hv p.1).2.2.2.2) hal
  have hCo : 0 < B.Coo := mul_pos hκ hCoo
  have hMM : 0 < B.MM := mul_pos hMo (Finset.prod_pos fun p _ => hMp p)
  have hμK : 0 < B.μK := mul_pos hKo (Finset.prod_pos fun p _ => (hloc p).1)
  have hAA : 0 < B.AA := div_pos (mul_pos (mul_pos hB hCo) (div_pos hMM hZ)) hμK
  have hn0c : 0 < B.n0c := div_pos hAA hr0
  have hgp : ∀ p, 0 < B.g p := fun p => by
    show (0 : ℝ) < ((gOf p : ℕ) : ℝ)
    exact_mod_cast (gOf_prime X p).pos
  have hglk : ∀ p, 0 < B.glk p := fun p => by
    show (0 : ℝ) < ((glkC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast glkC_pos _ _ (gOf_prime X p)
  have huk : ∀ p, 0 < B.uk p := fun p => by
    show (0 : ℝ) < ((ukC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ukC_pos _ _ (gOf_prime X p)
  have hnn : ∀ p, 0 < B.nn p := fun p => by
    show (0 : ℝ) < ((nnC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast nnC_pos _ _ _ (gOf_prime X p)
  have hgg : ∀ p, 0 < B.gg p := fun p => by
    show (0 : ℝ) < ((ggC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ggC_pos _ _ _ (gOf_prime X p)
  have hδ : 0 ≤ B.δ := by
    show 0 ≤ C * ((D.R.rS : ℝ) + 1) * (C / Th) ^ (Fintype.card (NumberField.InfinitePlace X.B.I.F))
    exact mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg (div_nonneg hC hTh.le) _)
  unfold MassDataPosC Formalism.FourierDecayAlt.S3.MassData.Pos
  exact ⟨fun p => ⟨hgp p, hglk p, huk p, hnn p, hgg p, (hloc p).1, (hloc p).2.1, (hloc p).2.2.1, (hloc p).2.2.2.1,
      (hloc p).2.2.2.2.1, (hloc p).2.2.2.2.2.1, (hloc p).2.2.2.2.2.2, hMp p, hU00p p⟩,
    hKo, hSo, hSo', hMo, hU00o, hH, hH', hHpp, hHpp', hN, hN', hZ, hPPp, hAl, hG, hHa, hHa', hNa, hNa', hB, hvH, hvH',
    hvN, hvN', hCo, hdeg, hdp, hdp', hr0, hr0', hd, hd', hn0c, hsd, hδ⟩

end Main

theorem cooOf_pos {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
  have h := Formalism.L2.SG.RealObj.InfCut.ProductExactness.haar_disintegration_real_holds D X u u' 1 one_pos
  have h' : ∃ C, 0 < C ∧ Formalism.L2.SG.RealObj.Disint X u u' 1 C := h
  unfold Formalism.L2.SG.RealObj.DisintegrationConstant
  rw [dite_eq_left h']
  exact h'.choose_spec.1

theorem quotVolPosC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hK2 : X.LevelSubgroupNormalized) (hV : 0 < X.volK2) :
    QuotVolPosC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hN, hH⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u hK2
  obtain ⟨hN', hH'⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u' hK2
  refine ⟨hH, hH', ?_, ?_⟩
  · show 0 < ((X.muN u) (Y.FN u)).toReal
    exact pos_of_mul_pos_right hN hV.le
  · show 0 < ((X.muN u') (Y.FN u')).toReal
    exact pos_of_mul_pos_right hN' hV.le

end Formalism.L2.SG.Pf.MassDataPos
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed
section
namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

theorem stK_holds {D : D7} (X : HidaSetting D) (p : TypX X) : MassDataIdxSteps.StK X p :=
  MassDataIdxSteps.stK_holds X p

theorem stRed_holds {D : D7} (X : HidaSetting D) (p : TypX X) : MassDataIdxSteps.StRed X p :=
  MassDataIdxSteps.stRed_of_embP X p (MassDataIdxSteps.embP_holds X p)

theorem stImA_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) :
    MassDataIdxSteps.StImA X hb p :=
  MassDataIdxSteps.stImA_of X hb p (MassDataIdxSteps.reduction_image_every_place X hb p)

theorem stImB_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    MassDataIdxSteps.StImB X u p :=
  MassDataIdxSteps.stImB_of_adaptQ X u p (MassDataIdxSteps.stAdaptQ_holds X hb u p)

theorem inIndicesAt_holds :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  local_indices_at_instance

end Formalism.L2.SG.Pf.MassDataX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
section
namespace Formalism.L2.SG.NGCut.NormalCount

theorem NormCountG_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCountG := by
  intro E _ _ _ J m hJ hm S hS
  exact Formalism.L2.SG.NGCut.TorsionTotientBound.card_mul_conj_eq_le_of_fractionalIdeal E J m hJ hm S hS

theorem NormCount_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCount :=
  Formalism.L2.SG.NGCut.NormalInvariants.normCount_of NormCountG_holds

end Formalism.L2.SG.NGCut.NormalCount
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootCoordinatesIndex
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.RootCoordinatesIndex

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau)

abbrev eV (a : Fin D.R.rS) : Fin X.B.I.n → ℂ := rv X.B.I (vOf X τ) (X.eR a)

theorem frS_ne (D : D7) : frS D ≠ 0 := by
  intro h0
  have := Formalism.L2.SG.RealFrameCoordinates.frS_mul_rd D
  rw [h0, zero_mul] at this
  exact zero_ne_one this

theorem Q_e (a : Fin D.R.rS) :
    C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 = frS D ^ (D.R.rS - a.val) • eV τ a :=
  ((C.isT τ).2.2.2 a a rfl).1

theorem Qi_e (a : Fin D.R.rS) :
    C.Qi τ *ᵥ eV τ a = (frS D ^ (D.R.rS - a.val))⁻¹ • Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 := by
  obtain ⟨hQiQ, _, _, _⟩ := C.isT τ
  have h := congrArg (fun x => C.Qi τ *ᵥ x) (Q_e C τ a)
  simp only [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Matrix.mulVec_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (frS_ne D)), one_smul]

theorem Qi_spanLt (a : ℕ) (x : Fin X.B.I.n → ℂ) (hx : x ∈ spanLt (eV (X := X) τ) a) (i : Fin (2 * D.R.rS + D.R.k + 1))
    (hi : a ≤ i.val) : (C.Qi τ *ᵥ x) i = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨b, hb, rfl⟩ := hx'
    rw [Qi_e, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [Formalism.QuantumDeterminants.eI] at this
    simp only [Set.mem_setOf_eq] at hb
    omega
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]

theorem Q_spanLt (a : ℕ) (ha : a ≤ D.R.rS) (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → w i = 0) : C.Q τ *ᵥ w ∈ spanLt (eV (X := X) τ) a := by
  have hw' : w = ∑ i, w i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw', Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : a ≤ i.val
  · rw [hw i hi, zero_smul, Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  · have hir : i.val < D.R.rS := by omega
    have e : i = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨i.val, hir⟩ := Fin.ext rfl
    rw [Matrix.mulVec_smul, e, Q_e]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.val, hir⟩, ?_, rfl⟩))
    simp only [Set.mem_setOf_eq]
    omega

theorem hpk_eI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) (Formalism.QuantumDeterminants.eI k r a) = v (Formalism.QuantumDeterminants.esI k r a) := by
  have hrow : ∀ j, Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) j = if j = Formalism.QuantumDeterminants.esI k r a then 1 else 0 := by
    intro j
    have ha := a.isLt
    have hj := j.isLt
    simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Formalism.QuantumDeterminants.eI, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | omega | (exfalso; omega)
  simp only [Matrix.mulVec, dotProduct, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem hJ_e (a : Fin D.R.rS) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε (vOf X τ)) (eV τ a) y = star ((frS D ^ (D.R.rS - a.val))⁻¹) * (C.Qi τ *ᵥ y) (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have he : eV τ a = (frS D ^ (D.R.rS - a.val))⁻¹ • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1) := by
    rw [Q_e, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (frS_ne D)), one_smul]
  have hy : y = C.Q τ *ᵥ (C.Qi τ *ᵥ y) := by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  conv_lhs => rw [he, hy]
  unfold hJ
  rw [star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH,
    Pi.star_single, star_one, single_dotProduct, one_mul, hpk_eI, smul_eq_mul]

variable {C τ}

theorem inN_iff (z : Fin X.B.I.n → ℂ) (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (C.Qi τ *ᵥ z))
    (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) :
    InN (X.B.I.ε (vOf X τ)) (eV τ) z g ↔ C.Qi τ * g * C.Q τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  obtain ⟨hQiQ, hQQi, hH, _⟩ := C.isT τ
  have hstar_ne : ∀ a : Fin D.R.rS, star ((frS D ^ (D.R.rS - a.val))⁻¹) ≠ 0 := fun a =>
    star_ne_zero.2 (inv_ne_zero (pow_ne_zero _ (frS_ne D)))
  have hcol : ∀ (M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) i j,
      M i j = (M *ᵥ Pi.single j 1) i := fun M i j => by rw [Matrix.mulVec_single_one]; rfl
  constructor
  · rintro ⟨⟨hIe, hIz⟩, hperp⟩
    refine ⟨?_, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩
    ·
      show (C.Qi τ * g * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * g * C.Q τ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
      have hQiQ' : (C.Qi τ)ᴴ * (C.Q τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one]
      rw [← hH]
      calc (C.Qi τ * g * C.Q τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * (C.Qi τ * g * C.Q τ)
          = (C.Q τ)ᴴ * (gᴴ * ((C.Qi τ)ᴴ * (C.Q τ)ᴴ) * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * ((C.Q τ * C.Qi τ) * g)) *
              C.Q τ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQiQ', hQQi, Matrix.mul_one, Matrix.one_mul, hg]
    ·
      rw [hcol (C.Qi τ * g * C.Q τ) i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a)]
      have h1 : (C.Qi τ * g * C.Q τ) *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 =
          Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 +
            frS D ^ (D.R.rS - a.val) • (C.Qi τ *ᵥ ((g - 1) *ᵥ eV τ a)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Q_e, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Qi_e, smul_sub, smul_smul,
          mul_inv_cancel₀ (pow_ne_zero _ (frS_ne D)), one_smul]
        abel
      rw [h1, Pi.add_apply, Pi.smul_apply, Qi_spanLt C τ a.val _ (hIe a) i hai, smul_zero, add_zero, Pi.single_apply]
    ·
      rw [hcol (C.Qi τ * g * C.Q τ) i j]
      have horth : ∀ b : Fin D.R.rS, hJ (X.B.I.ε (vOf X τ)) (eV τ b) (C.Q τ *ᵥ Pi.single j 1) = 0 := by
        intro b
        rw [hJ_e, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Pi.single_apply, if_neg, mul_zero]
        intro h
        have := congrArg Fin.val h
        simp only [Formalism.QuantumDeterminants.esI] at this
        have := b.isLt
        omega
      have h1 : (C.Qi τ * g * C.Q τ) *ᵥ Pi.single j 1 =
          Pi.single j 1 + C.Qi τ *ᵥ ((g - 1) *ᵥ (C.Q τ *ᵥ Pi.single j 1)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
        simp only [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Matrix.mul_assoc]
        abel
      rw [h1, Pi.add_apply, Qi_spanLt C τ D.R.rS _ (hperp _ horth) i hi, add_zero, Pi.single_apply]
  · rintro ⟨_, hce, hcw⟩
    have hg' : g = C.Q τ * (C.Qi τ * g * C.Q τ) * C.Qi τ := by
      simp only [← Matrix.mul_assoc]
      rw [hQQi, Matrix.one_mul, Matrix.mul_assoc, hQQi, Matrix.mul_one]
    set m := C.Qi τ * g * C.Q τ with hm
    have key : ∀ x, (g - 1) *ᵥ x = C.Q τ *ᵥ ((m - 1) *ᵥ (C.Qi τ *ᵥ x)) := by
      intro x
      conv_lhs => rw [hg']
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]

    have hmW : ∀ x : Fin (2 * D.R.rS + D.R.k + 1) → ℂ, (∀ a, x (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0) →
        ∀ i : Fin (2 * D.R.rS + D.R.k + 1), D.R.rS ≤ i.val → ((m - 1) *ᵥ x) i = 0 := by
      intro x hx i hi
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj1 : j.val < D.R.rS
      · have e : j = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨j.val, hj1⟩ := Fin.ext rfl
        have := hce ⟨j.val, hj1⟩ i (by simp only; omega)
        rw [Matrix.sub_apply, e, this, Matrix.one_apply, sub_self, zero_mul]
      · by_cases hj2 : j.val ≤ D.R.rS + D.R.k
        · rw [Matrix.sub_apply, hcw i j (by omega) hj2 hi, Matrix.one_apply, sub_self, zero_mul]
        · have hjr : 2 * D.R.rS + D.R.k - j.val < D.R.rS := by have := j.isLt; omega
          have e : j = Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨2 * D.R.rS + D.R.k - j.val, hjr⟩ := by
            ext; simp only [Formalism.QuantumDeterminants.esI]; have := j.isLt; omega
          rw [e, hx, mul_zero]
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · rw [key, Qi_e, Matrix.mulVec_smul, Matrix.mulVec_smul]
      refine Submodule.smul_mem _ _ (Q_spanLt C τ a.val a.isLt.le _ fun i hi => ?_)
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hcol m i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a), hce a i hi,
        Pi.single_apply, sub_self]
    · rw [key]
      refine Q_spanLt C τ D.R.rS le_rfl _ (hmW _ (fun a => hz _ (Or.inr ?_)))
      simp only [Formalism.QuantumDeterminants.esI]
      have := a.isLt
      omega
    · rw [key]
      refine Q_spanLt C τ D.R.rS le_rfl _ (hmW _ fun a => ?_)
      have h1 := hy a
      rw [hJ_e] at h1
      exact (mul_eq_zero.1 h1).resolve_left (hstar_ne a)

end Formalism.L2.SG.RootCoordinatesIndex

end
end

