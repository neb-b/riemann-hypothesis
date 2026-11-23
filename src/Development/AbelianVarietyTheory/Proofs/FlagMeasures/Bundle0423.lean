module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFramesPrescribedLocalClasses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedCountGluedLatticesEqMassMulLocal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueUnimodularLatticeRepsMoveIsometryFrames
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0387
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermsSameDoubleCosetSameDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0419

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericMassLeHeightPowMulGluedCount
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenMassBound

theorem tri_trans : ∀ (K W : Type) [CommRing K] [AddCommGroup W] [Module K W] (n : ℕ) (f g h : Fin n → W), Tri K f g → Tri K g h → Tri K f h := by
  intro K W _ _ _ n f g h ⟨A, hA, hfg⟩ ⟨B, hB, hgh⟩
  refine ⟨A * B, ⟨fun a b hba => ?_, fun a => ?_⟩, fun b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hca : c < a
    · rw [hA.1 a c hca, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hba (not_lt.1 hca)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h1 | h1
      · rw [hA.1 a c h1, zero_mul]
      · rw [hB.1 c a h1, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [hgh b]
    have e : ∀ c, g c = ∑ a, A a c • f a := hfg
    simp only [e, Finset.smul_sum, smul_smul]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]

theorem mapLF_frame : ∀ (D : D7) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (m : GV D), m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, frame (Formalism.L2.SG.TermOp.mapLF m F) a = m (frame F a)) ∧ (Formalism.L2.SG.TermOp.mapLF m F).zt = m F.zt ∧ (Formalism.L2.SG.TermOp.mapLF m F).fl.z = m F.fl.z := by
  intro D T F m hm
  rw [Formalism.L2.SG.TermOp.mapLF, dif_pos hm]
  refine ⟨fun a => ?_, rfl, rfl⟩
  simp only [frame, Formalism.MainNotions.S.FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp
  · simp

theorem zhat_isom : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') (m : GV D), m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, frame G a = m (frame F a)) → (∀ a, frame G' a = m (frame F' a)) → ZhatL G G' = ZhatL F F' := by
  intro D T T' F G F' G' m hm hG hG'
  funext a b
  have h1 : G.fl.fvec a = m (F.fl.fvec a) := hG a
  have h2 : G'.fl.fvec b = m (F'.fl.fvec b) := hG' b
  simp only [ZhatL, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, h1, h2]
  rw [hm]

theorem zhat_chg : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') (A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Chg (frame F) A (frame G) → Chg (frame F') A' (frame G') → ZhatL G G' = A.transpose.map star * ZhatL F F' * A' := by
  intro D T T' F G F' G' A A' hc hc'
  funext a b
  have h1 : G.fl.fvec a = ∑ c, A c a • F.fl.fvec c := hc a
  have h2 : G'.fl.fvec b = ∑ c, A' c b • F'.fl.fvec c := hc' b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ZhatL, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, h1, h2, map_sum, map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [starRingEnd_apply, RingHom.id_apply]
  ring

theorem cell_chg : ∀ {K : Type} [CommRing K] {r : ℕ} (Z L U : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (w : Point K (r + 1)), IsLoUni L → Uni U → ZhatOM Z = ptMat w → IsInCell (ZhatOM (L * Z * U)) w := by
  intro K _ r Z L U w hL hU hZ
  set s : Fin (r + 1) → K := fun b => (-1 : K) ^ (r - b.val) with hsdef
  have hs : ∀ b, s b * s b = 1 := by
    intro b
    simp only [hsdef, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hZS : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, ZhatOM M = M * Matrix.diagonal s := by
    intro M
    funext a b
    simp [ZhatOM, Matrix.mul_diagonal, hsdef, mul_comm]
  have hDD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal, show (fun i => s i * s i) = fun _ => (1 : K) from funext hs, Matrix.diagonal_one]
  refine ⟨L, Matrix.diagonal s * U * Matrix.diagonal s, hL, fun i j => ⟨fun hji => ?_, fun hij => ?_⟩, ?_⟩
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hU.1 i j hji]
  · subst hij
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, hU.2 i, mul_one]
    exact hs i
  · rw [← hZ, hZS, hZS]
    rw [show L * (Z * Matrix.diagonal s) * (Matrix.diagonal s * U * Matrix.diagonal s) =
      L * Z * (Matrix.diagonal s * Matrix.diagonal s) * U * Matrix.diagonal s by simp only [Matrix.mul_assoc], hDD,
      Matrix.mul_one]

theorem frameN : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (r : ℕ) (Fr : LocNG.FrameD H r), Fr.T ≠ 0 → ∀ (g0 g : Fin (r + 1) → V)
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∃ n ∈ Fr.N, g0 = fun b => n (Fr.f b)) → Uni A → Chg g0 A g →
    ∃ n ∈ Fr.N, g = fun b => n (Fr.f b) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r Fr hT g0 g A hg0 hA hc
  have u := _root_.GlobalTheory.LocOver.UnipOnto.unipotent_onto M hOK H r Fr hT
  obtain ⟨n, hn, rfl⟩ := hg0
  exact u.2.2 g (tri_trans E V (r + 1) _ _ _ (u.2.1 n hn) ⟨A, hA, hc⟩)

theorem genericMass_le_heightPow_mul_glueSum : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), 4 * D.R.rS + 7 ≤ D.R.k → ∀ {K : Type} (Fm : LocFam (zOf Y) K (NuC D)) (γ : PN.Pts D.host.E D.R.rS), 0 < Fm.V0 → (∃ (w : Point D.host.E (D.R.rS + 1)) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Y0 : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep), toPts w = γ ∧ (∃ n ∈ NRat (lf D (X.Fu u)), ∀ a, frame F a = n (frame (lf D (X.Fu u)) a)) ∧ ZhatOM (ZhatL F F') = ptMat w ∧ TotPos (Gval F F') ∧ BaseOK (Tu D u) (Tu D u') F F' Fm.P Fm.d0 ∧ MassLaw F F' Fm.P Fm.d0 Fm.V0 ∧ ∀ p ∈ Fm.P, Fm.ngenL p = (ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p))).toReal ∧ ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t ∧ (locH (zOf Y) p).Zhat t.f t.f' ∈ clsLoc ((zOf Y).M p) (Y0 p)) → 0 < Fm.toL.ngenTot ∧ (∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp) ∧ ∃ (w : Point D.host.E (D.R.rS + 1)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), toPts w = γ ∧ G'.zt = G'.fl.z ∧ TotPos (Gval (lf D (X.Fu u)) G') ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) G')) w ∧ ∀ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s → s.Nonempty ∧ Fm.toL.ngenTot ≤ Fm.toL.Htot ^ (3 * (D.R.rS + 1) ^ 2) * glueSum (lf D (X.Fu u)) G' s := by
  intro D X Y u u' hk K Fm γ hV0 hyp
  obtain ⟨w, F, F', Y0, hw, hFn, hZw, hTP, hBase, hML, hloc⟩ := hyp
  have hBased := hBase.1
  have hRel := hBase.2.1
  have hd0 := hBase.2.2.2.1

  have hOK : ∀ p : PlF D, ((zOf Y).M p).OK := fun p => ((zOf Y).agree p).1
  have hpos : ∀ p ∈ Fm.P, 0 < Fm.ngenL p ∧ ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p)) ≠ ⊤ ∧
      1 ≤ (Fm.FP p).Hp := by
    intro p hp
    obtain ⟨hng, d, t, ht, hc⟩ := hloc p hp
    obtain ⟨g0, g1, -, -⟩ := GlobalTheory.mass_pairingClass_bounds ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS D.R.k (Fm.FP p)
      hk (rank_Vp p) (hRel p) (Fm.R p) (Fm.d0 p) (hd0 p) d t ht (Y0 p) (clsLoc ((zOf Y).M p) (Y0 p)) rfl hc _ rfl
    refine ⟨?_, g1, ?_⟩
    · rw [hng]; exact ENNReal.toReal_pos g0.ne' g1
    · obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := Formalism.MainNotions.KappaEndpoints.ng_factors (hOK p) (hRel p).2.2.1 ht
      unfold LocNG.FPair.Hp
      refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mul_pos (mul_pos a0 b0) c0) ?_ (by norm_num)
      exact mul_le_one₀ (mul_le_one₀ a1 b0.le b1) c0.le c1
  have hTot : 0 < Fm.toL.ngenTot := by
    show 0 < Fm.V0 * ∏ p : {p // p ∈ Fm.P}, Fm.ngenL p.1
    exact mul_pos hV0 (Finset.prod_pos fun p _ => (hpos p.1 p.2).1)
  refine ⟨hTot, fun p hp => (hpos p hp).2.2, ?_⟩

  choose dd tt htt hcls using fun p (hp : p ∈ Fm.P) => (hloc p hp).2
  let f : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p := fun p =>
    if hp : p ∈ Fm.P then (tt p hp).f else scaled (zOf Y) p (frame F)
  let f' : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p := fun p =>
    if hp : p ∈ Fm.P then (tt p hp).f' else scaled (zOf Y) p (frame F')
  have hAf : ∀ p, (Fm.FP p).A.f = scaled (zOf Y) p (frame F) := fun p => (hBased p).1
  have hBf : ∀ p, (Fm.FP p).B.f = scaled (zOf Y) p (frame F') := fun p => (hBased p).2.1
  have hAT : ∀ p, (Fm.FP p).A.T ≠ 0 := fun p => (hRel p).2.2.2.2.2.2.2.1
  have hBT : ∀ p, (Fm.FP p).B.T ≠ 0 := fun p => (hRel p).2.2.2.2.2.2.2.2.2.1
  have htri : ∀ p ∈ Fm.P, Tri (D.s.atP p).Ep (scaled (zOf Y) p (frame F)) (f p) ∧
      Tri (D.s.atP p).Ep (scaled (zOf Y) p (frame F')) (f' p) := by
    intro p hp
    obtain ⟨-, -, ⟨n, hn, hfn, -⟩, ⟨n', hn', hfn', -⟩, -⟩ := htt p hp
    have u1 := _root_.GlobalTheory.LocOver.UnipOnto.unipotent_onto ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).A (hAT p)
    have u2 := _root_.GlobalTheory.LocOver.UnipOnto.unipotent_onto ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).B (hBT p)
    have e1 : f p = (tt p hp).f := dif_pos hp
    have e2 : f' p = (tt p hp).f' := dif_pos hp
    rw [e1, e2, ← hAf p, ← hBf p, hfn, hfn']
    exact ⟨u1.2.1 n hn, u2.2.1 n' hn'⟩
  obtain ⟨G, G'', hStd, hch⟩ := _root_.GlobalTheory.FrameChoice.choose_frames D (zOf Y) u u' F F' Fm.P f f' htri

  have hlocw : ∀ p ∈ Fm.P, ∃ wp : ℝ, 0 < wp ∧ wp ≤ (Fm.FP p).Hp ^ (3 * (D.R.rS + 1) ^ 2) ∧
      ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p)) =
        ENNReal.ofReal wp * locSum G G'' p (Fm.R p) (Fm.d0 p) := by
    intro p hp
    obtain ⟨A, A', hA, hA', hint, hc1, hc2⟩ := hch p hp
    have e1 : f p = (tt p hp).f := dif_pos hp
    have e2 : f' p = (tt p hp).f' := dif_pos hp
    rw [e1] at hc1
    rw [e2] at hc2
    obtain ⟨-, -, ⟨n, hn, hfn, -⟩, ⟨n', hn', hfn', -⟩, -⟩ := htt p hp
    have hN := frameN ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).A (hAT p) _ _ A ⟨n, hn, hfn⟩ hA hc1
    have hN' := frameN ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).B (hBT p) _ _ A' ⟨n', hn', hfn'⟩ hA' hc2
    have hZc := _root_.GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg ((zOf Y).M p) (locH (zOf Y) p) D.R.rS (Y0 p) _ _ _ _ A A' hA hA' hint hc1 hc2 (hcls p hp)
    obtain ⟨wp, h0, h1, h2⟩ := GlobalTheory.T.mass_class_eq_weight_count_alt ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS D.R.k (Fm.FP p) hk
      (rank_Vp p) (hRel p) (Fm.R p) (Fm.d0 p) _ _ hN hN' (Y0 p) (clsLoc ((zOf Y).M p) (Y0 p)) rfl hZc
      ⟨dd p hp, tt p hp, htt p hp, hcls p hp⟩
    exact ⟨wp, h0, h1, h2⟩

  have hTu : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have fc := _root_.GlobalTheory.FlagChange.flag_change D (lf D (X.Fu u)) hTu
  have hTri1 : Tri D.host.E (frame (lf D (X.Fu u))) (frame F) := (fc.2 F).2 hFn
  obtain ⟨m, hm, hGm⟩ := (fc.2 G).1 (tri_trans _ _ _ _ _ _ hTri1 hStd.1)
  have hmI : m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hm.1
  have hmI' : m⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := inv_mem hmI
  obtain ⟨hfr, hzt, hz⟩ := mapLF_frame D G'' m⁻¹ hmI'
  have hG''m : ∀ a, frame G'' a = m (frame (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') a) := by
    intro a
    rw [hfr a]
    exact (DFunLike.congr_fun (mul_inv_cancel m) (frame G'' a)).symm
  have hzt' : (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'').zt = (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'').fl.z := by
    rw [hzt, hz, hStd.2.2.2.1]
  obtain ⟨A, hA, hcA⟩ := hStd.1
  obtain ⟨A', hA', hcA'⟩ := hStd.2.1
  have hZG := zhat_chg D F G F' G'' A A' hcA hcA'
  have hZiso : ZhatL G G'' = ZhatL (lf D (X.Fu u)) (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') :=
    zhat_isom D _ G _ G'' m hmI hGm hG''m
  refine ⟨w, Formalism.L2.SG.TermOp.mapLF m⁻¹ G'', hw, hzt', ?_, ?_, ?_⟩
  · have e : Gval (lf D (X.Fu u)) (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') = Gval G G'' := by
      have h' : Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'').fl = Formalism.MainNotions.S.Zhat G.fl G''.fl :=
        hZiso.symm
      unfold Gval Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
      rw [h']
    rw [e, _root_.GlobalTheory.LocOver.gval_uni_change D F G F' G'' A A' hA hA' hZG]
    exact hTP
  · rw [← hZiso, hZG]
    refine cell_chg _ _ _ w ?_ hA' hZw
    intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · simp [Matrix.map_apply, Matrix.transpose_apply, hA.1 j i hij]
    · subst hij
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.2 i]
  · intro s hs
    obtain ⟨s', hs', hsum⟩ := _root_.GlobalTheory.GlueMove.glue_move D _ _ (lf D (X.Fu u)) G (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') G'' m hmI hGm
      hG''m s hs
    have hcnt := _root_.GlobalTheory.GlueCount.glue_count D (zOf Y) Fm.FP u u' F G F' G'' Fm.P Fm.d0 hk hBase hStd hTP Fm.R Fm.V0 hV0.le hML s' hs'
    choose! wp hwp0 hwpH hwpE using hlocw
    have hglue : glueSum G G'' s' = Fm.V0 * ∏ p ∈ Fm.P, (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal := by
      have hg0 : 0 ≤ glueSum G G'' s' := Finset.sum_nonneg fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _)
      have h := congrArg ENNReal.toReal hcnt
      rwa [ENNReal.toReal_ofReal hg0, ENNReal.toReal_mul, ENNReal.toReal_ofReal hV0.le, ENNReal.toReal_prod] at h
    have hng : ∀ p ∈ Fm.P, Fm.ngenL p = wp p * (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal := by
      intro p hp
      rw [(hloc p hp).1, hwpE p hp, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hwp0 p hp).le]
    have hle : Fm.toL.ngenTot ≤ Fm.toL.Htot ^ (3 * (D.R.rS + 1) ^ 2) *
        glueSum (lf D (X.Fu u)) (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') s := by
      rw [← hsum]
      refine le_of_le_of_eq ?_ (congrArg _ hglue.symm)
      show Fm.V0 * ∏ p : {p // p ∈ Fm.P}, Fm.ngenL p.1 ≤
        (∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp) ^ (3 * (D.R.rS + 1) ^ 2) * _
      rw [← Finset.prod_pow, Finset.prod_coe_sort Fm.P (fun p => Fm.ngenL p),
        Finset.prod_coe_sort Fm.P (fun p => (Fm.FP p).Hp ^ (3 * (D.R.rS + 1) ^ 2)), Finset.prod_congr rfl hng]
      calc Fm.V0 * ∏ p ∈ Fm.P, (wp p * (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal)
          ≤ Fm.V0 * ∏ p ∈ Fm.P, ((Fm.FP p).Hp ^ (3 * (D.R.rS + 1) ^ 2) *
              (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal) := by
            refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)) hV0.le
            · exact mul_nonneg (hwp0 p hp).le ENNReal.toReal_nonneg
            · exact mul_le_mul_of_nonneg_right (hwpH p hp) ENNReal.toReal_nonneg
        _ = _ := by rw [Finset.prod_mul_distrib]; ring
    refine ⟨?_, hle⟩
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp only [glueSum, Finset.sum_empty, mul_zero] at hle
    linarith

end GlobalTheory.GenMassBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermsSameDoubleCosetSameLocalData
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSame

section Gen

variable {K W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ}

theorem tri_refl (f : Fin n → W) : Tri K f f :=
  ⟨1, ⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a⟩,
    fun b => by simp [Matrix.one_apply]⟩

theorem tri_symm {f g : Fin n → W} (h : Tri K f g) : Tri K g f := by
  obtain ⟨A, hA, hc⟩ := h
  have hbt : A.BlockTriangular id := fun i j hij => hA.1 i j hij
  have hu : IsUnit A.det := by
    rw [Matrix.det_of_upperTriangular hbt]; simp [hA.2]
  obtain ⟨i1, i2⟩ := inv_unitri A hA.1 hA.2
  refine ⟨A⁻¹, ⟨i1, i2⟩, fun b => ?_⟩
  have hm := Matrix.mul_nonsing_inv A hu
  have key : ∀ c, (∑ a, A⁻¹ a b * A c a) = (1 : Matrix (Fin n) (Fin n) K) c b := by
    intro c; rw [← hm, Matrix.mul_apply]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  calc f b = ∑ c, (1 : Matrix (Fin n) (Fin n) K) c b • f c := by simp [Matrix.one_apply]
    _ = ∑ c, (∑ a, A⁻¹ a b * A c a) • f c := by simp_rw [key]
    _ = ∑ a, A⁻¹ a b • g a := by
        have e : ∀ a, A⁻¹ a b • g a = ∑ c, (A⁻¹ a b * A c a) • f c := fun a => by
          rw [hc a, Finset.smul_sum]; simp only [smul_smul]
        rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_comm]
        simp only [Finset.sum_smul]

theorem tri_trans {f g h : Fin n → W} (h1 : Tri K f g) (h2 : Tri K g h) : Tri K f h := by
  obtain ⟨A, hA, hc⟩ := h1
  obtain ⟨B, hB, hd⟩ := h2
  refine ⟨A * B, ⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with hca | hca
    · rw [hA.1 a c hca, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hab hca), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2, hB.2, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc | hc
      · rw [hA.1 a c hc, zero_mul]
      · rw [hB.1 c a hc, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [hd b]
    have e1 : ∀ c, B c b • g c = ∑ a, (A a c * B c b) • f a := by
      intro c; rw [hc c, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, mul_comm]
    rw [Finset.sum_congr rfl fun c _ => e1 c, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]

theorem tri_map {f g : Fin n → W} (h : Tri K f g) (φ : W ≃ₗ[K] W) :
    Tri K (fun a => φ (f a)) (fun a => φ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A, hA, fun b => by simp only [hc b, map_sum, map_smul]⟩

theorem span_le_of_tri {f g : Fin n → W} (h : Tri K f g) (j : ℕ) :
    Submodule.span K (g '' {c | c.val < j}) ≤ Submodule.span K (f '' {c | c.val < j}) := by
  obtain ⟨A, hA, hc⟩ := h
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  rw [hc b]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases hab : b < a
  · rw [hA.1 a b hab, zero_smul]; exact Submodule.zero_mem _
  · have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.1 (not_lt.1 hab)
    have hb' : b.val < j := hb
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, lt_of_le_of_lt hab' hb', rfl⟩)

theorem span_eq_of_tri {f g : Fin n → W} (h : Tri K f g) (j : ℕ) :
    Submodule.span K (f '' {c | c.val < j}) = Submodule.span K (g '' {c | c.val < j}) :=
  le_antisymm (span_le_of_tri (tri_symm h) j) (span_le_of_tri h j)

theorem img_cs {r : ℕ} (f : Fin (r + 1) → W) (j : ℕ) (hj : j ≤ r) :
    (fun b : Fin r => f b.castSucc) '' {b | b.val < j} = f '' {c | c.val < j} := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.castSucc, by simpa using hb, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hc' : c.val < j := hc
    exact ⟨⟨c.val, by omega⟩, hc', congrArg f (Fin.ext rfl)⟩

end Gen

section Loc

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem X_eq_span (H : HermSp M V) (f : Fin (r + 1) → V) :
    H.X f = Submodule.span E (f '' {c | c.val < r}) := by
  unfold HermSp.X
  rw [← img_cs f r le_rfl]
  congr 1
  ext x
  simp

theorem X_eq_of_tri (H : HermSp M V) {f g : Fin (r + 1) → V} (h : Tri E f g) : H.X f = H.X g := by
  rw [X_eq_span, X_eq_span, span_eq_of_tri h]

theorem NU_of_tri (H : HermSp M V) {f g : Fin (r + 1) → V} (h : Tri E f g) {u : V ≃ₗ[E] V}
    (hu : u ∈ NU H f) : u ∈ NU H g := by
  obtain ⟨hU, h1, h2⟩ := hu
  have hX := X_eq_of_tri H h
  refine ⟨hU, fun a => ?_, fun v hv => ?_⟩
  · have hsp : Submodule.span E ((fun b : Fin r => g b.castSucc) '' {b | b < a}) =
        Submodule.span E (f '' {c | c.val < a.val}) := by
      rw [show {b : Fin r | b < a} = {b | b.val < a.val} from rfl, img_cs g a.val a.isLt.le,
        span_eq_of_tri h]
    rw [hsp]
    obtain ⟨A, hA, hc⟩ := h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc a.castSucc, map_sum]
    have e : ∑ c, u (A c a.castSucc • f c) - ∑ c, A c a.castSucc • f c =
        ∑ c, A c a.castSucc • (u (f c) - f c) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul, smul_sub]
    rw [e]
    refine Submodule.sum_mem _ fun c _ => ?_
    by_cases hca : a.castSucc < c
    · rw [hA.1 c a.castSucc hca, zero_smul]; exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ ?_
      have hcv : c.val ≤ a.val := by
        have h' := Fin.le_iff_val_le_val.1 (not_lt.1 hca)
        rwa [Fin.coe_castSucc] at h'
      have hcr : c.val < r := lt_of_le_of_lt hcv a.isLt
      have hfc := h1 ⟨c.val, hcr⟩
      have ecs : (⟨c.val, hcr⟩ : Fin r).castSucc = c := Fin.ext rfl
      rw [ecs, show {b : Fin r | b < ⟨c.val, hcr⟩} = {b | b.val < c.val} from rfl,
        img_cs f c.val hcr.le] at hfc
      refine Submodule.span_mono (Set.image_mono fun x hx => ?_) hfc
      have hx' : x.val < c.val := hx
      show x.val < a.val
      omega
  · rw [← hX] at hv ⊢
    exact h2 v hv

theorem cong_congr (H : HermSp M V) (Λ : Submodule M.L.O V) (f : Fin (r + 1) → V)
    {f₁ f₂ : Fin (r + 1) → V} (hX : H.X f₁ = H.X f₂) (x : V) :
    Cong H Λ f f₁ x ↔ Cong H Λ f f₂ x := by
  unfold Cong
  rw [hX]

end Loc

theorem over_same : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → Gval (lf D F0) F₁ ≠ 0 → ∀ n ∈ Formalism.L2.SG.NGData.NRat (lf D F0), ∀ m ∈ Formalism.L2.SG.NGData.NRat F₁, Formalism.HermitianLatticesTheory.gmap (n * m) Λ = Λ → (∀ a, frame F₂ a = (n * m) (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ (n * m) (gS D) → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d, Over P d (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) → Over P d (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) := by
  intro D Z u u' F0 Λ hΛ F₁ F₂ hP₁ hP₂ hG n hn m hm hgm hfr hio p P hP d hd
  have hOK : (Z.M p).OK := (Z.agree p).1
  have hfr' : ∀ a, frame F₂ a = n (m (frame F₁ a)) := fun a => by
    have h := hfr a
    simp only [LinearEquiv.mul_apply] at h
    exact h
  have hG₂ : Gval (lf D F0) F₂ ≠ 0 := by
    have hrel : DCRel (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D F0) F₁
        (⟨F₂.fl, n (m F₁.zt)⟩ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) :=
      ⟨n, ⟨⟨hn.1, (Formalism.L2.SG.Pf.gmap_eq_iff n).2 fun x => by simp⟩, hn.2⟩,
        m, ⟨⟨hm.1, (Formalism.L2.SG.Pf.gmap_eq_iff m).2 fun x => by simp⟩, hm.2⟩, hfr', rfl⟩
    have e := Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel
    exact fun h0 => hG (e.symm.trans h0)
  obtain ⟨hT₁, htri₁⟩ := GlobalTheory.LocOver.locU_isTerm D Z u u' F0 Λ hΛ F₁ hP₁ hG p
  obtain ⟨hT₂, htri₂⟩ := GlobalTheory.LocOver.locU_isTerm D Z u u' F0 Λ hΛ F₂ hP₂ hG₂ p
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1
  have hmI : m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hm.1
  have hnmI : n * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem hnI hmI
  obtain ⟨gn, hgnE, -, -, -, hgnN⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p n hnI
  obtain ⟨gm, hgmE, -, -, -, hgmN⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p m hmI
  obtain ⟨g, -, -, hguniq, hgimg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p (n * m) hnmI
  have hext : Ext p (n * m) (gn * gm) := fun x => by
    show (gn * gm) (baseChange₂ D p x) = baseChange₂ D p ((n * m) x)
    rw [LinearEquiv.mul_apply, hgmE x, hgnE (m x), LinearEquiv.mul_apply]
  have hgeq : gn * gm = g := hguniq _ hext
  have hn' : gn ∈ NU (locH Z p) (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).f := hgnN (lf D F0) hn
  have hm' : gm ∈ NU (locH Z p) (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).f' :=
    NU_of_tri (locH Z p) htri₁ (hgmN F₁ hm)
  have himg : Formalism.MainNotions.S.LocNG.img (gn * gm) (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).abelian₂ =
      (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).abelian₂ := by
    show Formalism.MainNotions.S.LocNG.img (gn * gm) (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ
    rw [hgeq, hgimg Λ, hgm]
  have hsc : scaled Z p (frame F₂) = fun a => (gn * gm) (scaled Z p (frame F₁) a) := by
    funext a
    show frFac Z.δ p a • baseChange₂ D p (frame F₂ a) = (gn * gm) (frFac Z.δ p a • baseChange₂ D p (frame F₁ a))
    rw [LinearEquiv.map_smul, hext, hfr a]
  have htri : Tri (D.s.atP p).Ep (fun b => (gn * gm) ((locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).f' b))
      (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')).f' := by
    have h2 := tri_symm (tri_map htri₁ (gn * gm))
    rw [← hsc] at h2
    exact tri_trans h2 htri₂
  have hX₁ := X_eq_of_tri (locH Z p) htri₁
  have hX₂ := X_eq_of_tri (locH Z p) htri₂
  have hfin : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    rw [finrank_Vp]
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  refine _root_.GlobalTheory.LocOver.SameDC.same_datum (Z.M p) hOK (locH Z p) D.R.rS D.R.k P hfin hP
    (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) hT₁ hT₂
    rfl rfl rfl gn hn' gm hm' himg (tri_refl _) htri ?_ d hd
  intro hs x' hx' x hx hx'p hxp
  have key := _root_.GlobalTheory.IotaLoc.iota_typed D Z u u' F0 Λ hΛ F₁ F₂ hP₁ hP₂ (n * m) hnmI hgm hfr hio p (gn * gm) hext hs
    x' hx' x hx (by rw [hX₁]; exact hx'p) hxp
  rw [cong_congr (locH Z p) _ _ hX₁.symm, cong_congr (locH Z p) _ _ hX₂.symm]
  exact key

end GlobalTheory.LocSame
end
end

