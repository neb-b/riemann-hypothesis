module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FamRaise
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0039

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpValAll
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem poincareConstant_pos {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) :
    0 < Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X X u (Y.FN u) := by
  have hv := Formalism.L2.SG.Closed.VolPosC_holds D X Y u (Formalism.L2.SG.Closed.level_subgroup_properties X)
  haveI : Nontrivial (X.Vpi u) := Formalism.L2.SG.Pf.ColDictPf.vpi_nontrivial X u
  have hr : (0 : ℝ) < (Module.finrank ℂ (X.Vpi u) : ℝ) := by exact_mod_cast Module.finrank_pos
  rw [Formalism.L2.SG.Full.Full.poincare_constant_eq]
  exact div_pos (mul_pos hv.1 hv.2) hr

theorem amplitude_lower_bound_real {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hSt : Formalism.MainNotions.S.Cnt.Stand D u u') (hi : ∀ v, i0 v = i0' v) (hNuP : Formalism.L2.SG.RealObj.NuQPin X u u' νq)
    (hVP : Formalism.L2.SG.VolPin.VolumeOddGeneric) (hg3 : ∀ i, 3 ≤ D.host.g i) :
    Formalism.L2.SG.Pf.RowForm.ClassAbs.AmpValLowerC X Y u u'
      (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) i0 i0' νq := by
  have hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hi' : i0' = i0 := funext fun v => (hi v).symm
  subst hi'
  let κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ := fun _ => 0
  have hAtS : ∀ t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w :=
    fun t hG hr => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' t hG hr
  have hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.cell_point_unique_of_term_fun (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  have hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.normRepExists_of (Formalism.L2.SG.Pf.NormRepX.norm_representative_holds D u u' hPH)
      (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  have hLD : Formalism.L2.SG.Pf.RowForm.LiftDecompC X Y u u' κ :=
    Formalism.L2.SG.Pf.RowForm.liftDecompC_of_real (κ := κ) (h := Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of (hAt := hAtS))
  have hFT := Formalism.L2.SG.Pf.formula_transport_of_condition (κ := κ) (hP := hNuP) (hV := hVP) (hg3 := hg3) (hPH := hPH)
    (hRC := Formalism.L2.SG.Pf.RelChar.relCharC_holds) (hLD := hLD) (hAt := Formalism.L2.SG.Pf.LiftedPhaseAgreement.liftAtSomeC_holds X Y u u' κ)
    (hNR := hNR) (hCPU := hCU)
  have hDF : Formalism.L2.SG.Pf.RowForm.DFrameAtS X u u' i0' i0' 1 := Formalism.L2.SG.Pf.Carrier.dual_frame_at_places X u u' 1 i0'
  have hNF := Formalism.L2.SG.Pf.RowForm.normalFormC_all (hAtS := hAtS) (hTP := fun t w h => Formalism.L2.SG.WConst.atPt_totPos t w h)
    (hCU := hCU) (hDF := hDF) (hPT := Formalism.L2.SG.Pf.LiftedPhaseAgreement.phaseTieC_holds (κ := κ) (hP := hPH)) (hFT := hFT)
  refine Formalism.L2.SG.Pf.ampValLowerC_of X Y u u' _ i0' i0' νq κ hNF
    (fun t w h => Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' _ _ t w h) ?_
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := by
    unfold Formalism.L2.SG.HidaSetting.HidaSetting.volK2
    exact ENNReal.toReal_pos hK.2.2.1.ne' hK.2.2.2.ne
  have hc := poincareConstant_pos X Y u
  have hc' := poincareConstant_pos X Y u'
  unfold Formalism.L2.SG.TermOp.scl
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hc hc'))) hV

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

theorem rowsSum_of_formula_volume (hFC : FormulaC) (hVP : Formalism.L2.SG.VolPin.VolumeOddGeneric) : RowsSumC := by
  intro D T u u' i0 i0' νq Lsp κ hne hSt hCT hg3 hk hcong hi hPR hNu hRL
  have hWD : Formalism.L2.SG.WuDecay.WuDecay T.X := hCT.2.2.2.2.1
  have hAbs : (T.Y.tO u u').AbsConv :=
    Formalism.L2.SG.Pf.absConvC_outright D T.X T.Y u u'
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u' (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Pf.fundExistsC_holds D T.X T.Y u u')
      (Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := T.Y) hWD u u')
  have hL := Formalism.L2.SG.Pf.liftOntoC_of (fun D => Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) D T.X T.Y u u'
  have hAF : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u) (T.Y.what₂ u) := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u).A.T_prime.pos (T.X.Fu u) Λ ((T.Y.rowsOK u).1 Λ hΛ)
  have hAF' : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u') (T.Y.what₂ u') := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u').A.T_prime.pos (T.X.Fu u') Λ ((T.Y.rowsOK u').1 Λ hΛ)
  have hLT : Formalism.L2.SG.Pf.LocCP.LocTied D := by
    obtain ⟨_, _, _, _, _, _, _, hL⟩ := hCT.2.2.2.2.2.2.1
    exact hL
  have hnc : 0 < Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p :=
    mul_pos (hFC D T u u' Lsp hLT hSt hcong).1 (tprod_alpD_pos D hk u u')
  exact Formalism.L2.SG.RowsAbsX.rowsSum_of_val _ κ _ i0 i0' (T.Y.FN u) (T.Y.FN u') νq hAbs hL
    (Formalism.L2.SG.Pf.amplitude_lower_bound_real T.X T.Y u u' i0 i0' νq hSt hi hNu hVP hg3) hAF hAF' hnc

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLocS
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx
  Formalism.L2.SG.Pf.AllRowsKpp

variable {D : D7} (X : HidaSetting D)

theorem fr_L (ob : Bool) (j : Fin D.R.r) : fr X ob j ∈ X.B.I.Lf := by
  rcases kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩
  · rw [frame_isotropic]; exact (X.vectorsInLattice.1 a).1
  · cases ob
    · rw [fr_wf]; exact (X.vectorsInLattice.2.2 _).2
    · rw [fr_wt]; exact (X.vectorsInLattice.2.2 _).1
  · rw [frame_anisotropic]; exact X.vectorsInLattice.2.1
  · rw [fr_y]; exact (X.vectorsInLattice.1 _).2

theorem frd_L (ob : Bool) (j : Fin D.R.r) : frd X ob j ∈ X.B.I.Lf := by
  rcases kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩
  · rw [dual_frame_isotropic]; exact (X.vectorsInLattice.1 a).2
  · cases ob
    · rw [frd_wf]; exact (X.vectorsInLattice.2.2 _).1
    · rw [frd_wt]; exact (X.vectorsInLattice.2.2 _).2
  · rw [dual_frame_anisotropic]; exact neg_mem X.vectorsInLattice.2.1
  · rw [frd_y]; exact (X.vectorsInLattice.1 _).1

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)} {p : ℕ}

theorem col (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w)
    {x : X.B.I.Gf} (hx : x ∈ X.K2) (i j : Fin D.R.r)
    (hij : j.1 ≤ i.1 ∨ ((∃ l, i = wI (hrD D) l) ∧ j = zI (hrD D))) :
    CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (if i = j then 1 else 0) := by
  have hc : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := hx.2
  have hci : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x⁻¹ := ((Formalism.L2.SG.Pf.level_subgroup_character_unitary X).2.2.1 x hx).2
  have hgr := gram X ob hg hew hsew
  rcases kind_cases (hrD D) j with ⟨b, rfl⟩ | ⟨l, rfl⟩ | rfl | ⟨b, rfl⟩
  ·
    have hpos : b.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa [xI, wI, yI, zI] using h
      · exact absurd h (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    refine cong_dir hg (frd_L X ob) hgr i (xI (hrD D) b) (S := X.e0 '' {c | c.1 < b.1}) ?_ ?_
    · rintro s ⟨c, hc', rfl⟩
      exact ⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp [xI, wI, yI, zI] at hc' ⊢; omega)⟩
    · rw [frame_isotropic]; exact hc.1 b
  ·
    have hpos : D.R.rS + l.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa [xI, wI, yI, zI] using h
      · exact absurd h (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    ·
      rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩
      · exfalso; simp [xI, wI, yI, zI] at hpos; omega
      · simp [xI, wI, yI, zI] at hpos
        refine cong_dual hg (fr_L X false) hgr (wI (hrD D) l') (wI (hrD D) l)
          (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < (rv l').1}) ?_ ?_
        · rintro s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)
          · exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI] <;> omega)⟩
          · exact ⟨wI (hrD D) (rv c), by rw [frd_wf, rv_rv], ne_val (by simp [xI, wI, yI, zI, rv] at hc' ⊢; omega)⟩
        · rw [frd_wf]; exact hci.2.2 (rv l')
      · refine cong_dual hg (fr_L X false) hgr (zI (hrD D)) (wI (hrD D) l) (S := Set.range X.e0) ?_ ?_
        · rintro s ⟨c, rfl⟩
          exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI] <;> omega)⟩
        · rw [dual_frame_anisotropic, Matrix.mulVec_neg]; exact inMod_neg hci.2.1
      · refine cong_dual hg (fr_L X false) hgr (yI (hrD D) a) (wI (hrD D) l)
          (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_
        · rintro s ⟨c, -, rfl⟩
          exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI] <;> omega)⟩
        · rw [frd_y]; exact hci.1 (rv a)
    ·
      refine cong_dir hg (frd_L X true) hgr i (wI (hrD D) l) (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < l.1}) ?_ ?_
      · rintro s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)
        · exact ⟨xI (hrD D) c, (frame_isotropic X true c).symm, ne_val (by simp [xI, wI, yI, zI]; omega)⟩
        · exact ⟨wI (hrD D) c, (fr_wt X c).symm, ne_val (by simp [xI, wI, yI, zI] at hc' ⊢; omega)⟩
      · rw [fr_wt]; exact hc.2.2 l
  ·
    have hpos : D.R.rS ≤ i.1 := by
      rcases hij with h | ⟨⟨l, rfl⟩, -⟩
      · simp [xI, wI, yI, zI] at h; omega
      · simp [xI, wI, yI, zI]
    refine cong_dir hg (frd_L X ob) hgr i (zI (hrD D)) (S := Set.range X.e0) ?_ ?_
    · rintro s ⟨c, rfl⟩
      exact ⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp [xI, wI, yI, zI]; omega)⟩
    · rw [frame_anisotropic]; exact hc.2.1
  ·
    have hpos : D.R.rS + D.R.k + 1 + b.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa [xI, wI, yI, zI] using h
      · exact absurd h (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩
    · exfalso; simp [xI, wI, yI, zI] at hpos; omega
    · exfalso; simp [xI, wI, yI, zI] at hpos; omega
    · exfalso; simp [xI, wI, yI, zI] at hpos; omega
    · simp [xI, wI, yI, zI] at hpos
      refine cong_dual hg (fr_L X ob) hgr (yI (hrD D) a) (yI (hrD D) b)
        (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_
      · rintro s ⟨c, hc', rfl⟩
        exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI, rv] at hc' ⊢; omega)⟩
      · rw [frd_y]; exact hci.1 (rv a)

theorem shape (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w)
    (hp : p.Prime) (hcard : Nat.card (𝓞 X.B.I.E ⧸ w.asIdeal) = p) (hn : 0 < X.B.I.n)
    {x : X.B.I.Gf} (hx : x ∈ X.K2) {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (N i j)) :
    JPred D.R.k D.R.rS N := by
  refine jPred_of (hrD D) (fun a b hba => ?_) (fun a => ?_) (fun l => ?_)
  · have h := col (p := p) X ob hg hew hsew hx a b (Or.inl (le_of_lt hba))
    rw [if_neg (fun h' => (ne_of_gt hba) h')] at h
    exact congW_unique hp hcard hn (hN a b) h
  · have h := col (p := p) X ob hg hew hsew hx a a (Or.inl le_rfl)
    rw [if_pos rfl] at h
    exact congW_unique hp hcard hn (hN a a) h
  · have h := col (p := p) X ob hg hew hsew hx (wI (hrD D) l) (zI (hrD D)) (Or.inr ⟨⟨l, rfl⟩, rfl⟩)
    rw [if_neg (ne_val (by simp [xI, wI, yI, zI] <;> omega))] at h
    exact congW_unique hp hcard hn (hN _ _) h

end Formalism.L2.SG.Pf.KppLoc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSOf
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SelQ

variable {𝒞 : FamClass} (sel : SSel 𝒞)

variable {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm)

end SelQ

section Closed

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)

theorem cOut_take {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut := by
  unfold FamP.cOut; simp

theorem constant_list_cylinder {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 6 0 = Fm.CYL := by
  unfold FamP.cOut; simp

theorem constant_list_trace {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 13 0 = Fm.CTu := by
  unfold FamP.cOut; simp

end Closed

section Raised

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)
  (yF : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ℝ)

def YFOK : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x), yF Fm hc ≤ x →
    ∀ i : Fm.Ix x, FinX ((sel Fm hc).2 x hx h0 i).Y ∧ Formalism.L2.SG.WuDecay.WuDecay ((sel Fm hc).2 x hx h0 i).X

def yR {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) : ℝ := max (sel Fm hc).1 (yF Fm hc)

theorem h0R {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    (sel Fm hc).1 ≤ x :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans hx.le

theorem hyR {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    yF Fm hc ≤ x :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans hx.le

def AtR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : TermTie (Fm.D x i) :=
  atOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2

def CcR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : ConcAt0 (Fm.D x i) (AtR sel yF hyF Fm hc x hx i) :=
  ccOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem loopRowS_of_raised (hyF : YFOK sel yF) (C1f : List ℝ → ℝ) (C₀f : (List ℝ → ℝ) → List ℝ → ℝ)
    (Yt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut))
    (hRowsF : ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm, ∀ C : ℝ, C₀f aF (Fm.cOut ++ Fm.cMid CH) ≤ C →
      OwnEv Fm fun C' Cl x i => ∀ (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) →
          Formalism.MainNotions.BridgeLemma.RowsND (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsDeg (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C)
    (hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  choose f g hfg using fun p : ℝ × ℝ × ℝ × ℝ =>
    loop_evaluation_threshold_zero Formalism.FourierDecayAlt.P.loop_kernels Formalism.FourierDecayAlt.P.subfamilyAlt Formalism.HermitianLattices.Ext.L3.siegelMassRatio
      (p.1 + 1) (1 / 4) 3 (1 / 2) p.2.1 C0 p.2.2.1 p.2.2.2
  let par : List ℝ → ℝ × ℝ × ℝ × ℝ := fun l => (l.getD 6 0, l.getD 13 0, aF (l.take 16), C₀f aF l)
  obtain ⟨e1, he1, H1⟩ := hRowsF aF
  obtain ⟨e2, he2, H2⟩ := hForm
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  let K4 : TransportedAlt := ⟨0, fun _ => 0, fun _ => 0, fun l => max (f (par l)) (g (par l))⟩
  refine ⟨(K1.sup K2).sup K4, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL12, hL4⟩ := (Fm.large_sup _ _ CH).1 hL
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL12
  intro hc'
  have epar : par (Fm.cOut ++ Fm.cMid CH) = (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) := by
    simp only [par, constant_list_cylinder, constant_list_trace, cOut_take]
  have hthr : ∀ c ∈ Fm.cLast, max (f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)))
      (g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH))) ≤ c := by
    intro c hc0
    have := hL4.2.2.2 c hc0
    simpa only [K4, epar] using this
  have hC' : f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sC' Fm :=
    (le_max_left _ _).trans (hthr _ (by unfold FamP.cLast sC'; simp))
  have hCl : g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sCl Fm := by
    have h := fun c hc => (le_max_right _ _).trans (hthr c hc)
    unfold sCl
    refine le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
      (le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
        (le_min (h _ (by unfold FamP.cLast; simp)) (h _ (by unfold FamP.cLast; simp))))))
  have hE := hfg (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) (Fm.raise (yR sel yF Fm hc')) (C1f Fm.cOut)
    (AtR sel yF hyF Fm hc') (Yt Fm hc') (CcR sel yF hyF Fm hc') (hK1 Fm CH hc hL1 hc') (hK2 Fm CH hc hL2)
  obtain ⟨x0, H⟩ := hE
  refine ⟨max x0 (yR sel yF Fm hc' + 1), fun x hx0 i => ?_⟩
  intro hx h0 u u' hH hCT hA
  have hx' : (Fm.raise (yR sel yF Fm hc')).x1 < x := by
    show max Fm.x1 (yR sel yF Fm hc') < x
    refine max_lt hx ?_
    have := (le_max_right _ _).trans hx0
    linarith
  exact H x ((le_max_left _ _).trans hx0) i hC' hCl hx' u u' hH hCT hA

theorem constant_list_gamma {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := by
  unfold FamP.cOut FamP.cMid; simp


end Raised

end Formalism.L2.SG.LoopsTies
end
end

