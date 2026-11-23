module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegerPointsCoverRealPointsRootCoordinates

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCompatibilityOfLocalIdentifications
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaLocConv

open Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : D7}

theorem locH_add_right (Z : LocDat D) (p : PlF D) (x y y' : Vp D p) :
    (locH Z p).h x (y + y') = (locH Z p).h x y + (locH Z p).h x y' := by
  rw [(locH Z p).h_herm (y + y') x, (locH Z p).h_add_left, map_add (f := _), ← (locH Z p).h_herm,
    ← (locH Z p).h_herm]

theorem locH_smul_right (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (x y : Vp D p) :
    (locH Z p).h x (c • y) = (Z.M p).L.cj c * (locH Z p).h x y := by
  rw [(locH Z p).h_herm (c • y) x, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm]

theorem baseChange_mem_perp_sup (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) {m : (VS D).V}
    (hm : m ∈ orth (VS D) (Xsp G)) :
    baseChange₂ D p m ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame G))) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hm
  show ∀ y ∈ (locH Z p).X (scaled Z p (frame G)), (locH Z p).h (baseChange₂ D p m) y = 0
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    show (locH Z p).h (baseChange₂ D p m) (frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)) = 0
    rw [locH_smul_right, BwdNP.localForm_baseChange, GlobalTheory.LocExt.frame_castSucc,
      hm (G.fl.e a) (Submodule.subset_span ⟨a, rfl⟩), map_zero, mul_zero]
  | zero =>
    have h2 := locH_add_right Z p (baseChange₂ D p m) 0 0
    rw [add_zero] at h2
    linear_combination -h2
  | add y y' _ _ hy hy' => rw [locH_add_right, hy, hy', add_zero]
  | smul c y _ hy => rw [locH_smul_right, hy, mul_zero]

theorem theta_of_split (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)
    (hs : (Z.M p).split = some g) : Formalism.MainNotions.S.LocNG.theta (Z.M p) = (g.q : (D.s.atP p).Fp) := by
  unfold Formalism.MainNotions.S.LocNG.theta
  rw [hs]

theorem cong_of_mem (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : (VS D).V} (hv : v ∈ NgX Λ (gS D) F F') :
    Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) (baseChange₂ D p v) := by
  obtain ⟨l, hl, ξ, hξ, ξ', hξ', rfl⟩ := IotaBP.NgX_dec hv
  obtain ⟨w, hw, -, -, he, -⟩ := IotaBP.gS_typed Z p g hs
  have hξX : ξ ∈ Xsp F := (Submodule.mem_inf.1 hξ).2
  have hξ'X : ξ' ∈ Xsp F' := (Submodule.mem_inf.1 hξ').2
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • (w • baseChange₂ D p l), ?_,
    baseChange₂ D p ξ, BwdNP.baseChange_mem_localLattice Z (Submodule.mem_inf.1 hξ).1 p, baseChange₂ D p ξ', BwdNP.baseChange_mem_localLattice Z (Submodule.mem_inf.1 hξ').1 p,
    GlobalTheory.LocExt.bcP_Xsp_mem Z p F hξX, GlobalTheory.LocExt.bcP_Xsp_mem Z p F' hξ'X, ?_⟩
  · rw [theta_of_split Z p g hs]
    exact Submodule.subset_span ⟨_, Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p hw (BwdNP.baseChange_mem_localLattice Z hl p), rfl⟩
  · rw [map_add (f := _), map_add (f := _), baseChange_smul₂, he, mul_smul]

theorem mem_localLattice_of_cong (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)
    (hs : (Z.M p).split = some g) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ.FG) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') {w : Vp D p}
    (hw : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) w) :
    w ∈ lattice₂ D Z.M p (NgX Λ (gS D) F F') := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hw
  have hX : ∀ {T₁ : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T₁) {y : Vp D p}, y ∈ lattice₂ D Z.M p Λ →
      y ∈ (locH Z p).X (scaled Z p (frame G)) → y ∈ lattice₂ D Z.M p (XLam Λ G) := by
    intro T₁ G y hy hyX
    have hsp : y ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp G : Set (VS D).V)) := by
      refine Submodule.span_le.2 ?_ hyX
      rintro _ ⟨i, rfl⟩
      show frFac Z.δ p i.castSucc • baseChange₂ D p (frame G i.castSucc) ∈ _
      rw [GlobalTheory.LocExt.frame_castSucc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨G.fl.e i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩)
    have h := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (Xsp G) hΛ
    have h2 : y ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (Xsp G)) : Set (Vp D p)) := by
      rw [h]; exact ⟨hy, hsp⟩
    exact h2
  refine add_mem (add_mem ?_ ?_) ?_
  · rw [theta_of_split Z p g hs] at ha
    unfold Formalism.MainNotions.S.Loc.HermSp.smulLat at ha
    refine (Submodule.span_le.2 ?_) ha
    rintro _ ⟨y, hy, rfl⟩
    exact IotaBP.typed_q_mem Z p g hs F F' hy
  · exact IotaBP.localLattice_mono Z p (le_sup_right.trans le_sup_left) (hX F hb hbX)
  · exact IotaBP.localLattice_mono Z p le_sup_right (hX F' hc hcX)

theorem mem_NgX_of_local (Z : LocDat D) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : (VS D).V} (hv : v ∈ Λ)
    (h : ∀ p : PlF D, (Z.M p).split ≠ none →
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) (baseChange₂ D p v)) :
    v ∈ NgX Λ (gS D) F F' := by
  refine BwdNP.mem_of_bcP Z (IotaBP.isLattice_NgX hΛ F F') fun p => ?_
  match hs : (Z.M p).split with
  | none => exact IotaBP.untyped_mem Z p hs F F' (BwdNP.baseChange_mem_localLattice Z hv p)
  | some g => exact mem_localLattice_of_cong Z p g hs hΛ.toIsLattice.fg F F' (h p (by rw [hs]; exact Option.some_ne_none g))

theorem iotaCompat_of_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t₀ t : TauC Y u u'),
    t.lam = t₀.lam → t.lam' = t₀.lam' →
    (∀ p : PlF D, (Y.M p).split ≠ none → ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ →
      ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam,
      ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam,
      x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X
        (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) →
      x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X
        (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) →
      (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam)
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔
        Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam)
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) →
    IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) := by
  intro D X Y u u' t₀ t hl hl' hloc
  set Z : LocDat D := ⟨Y.δ, Y.M, Y.agree⟩ with hZ
  have hγ0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hβ : t.lin * t₀.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem hγ1 (inv_mem hγ0)
  have hg0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have hg1 : Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' = t₀.lam := by
    have h : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    rw [hl, hl'] at h
    exact h
  have hβΛ : ∀ y ∈ t₀.lam, (t.lin * t₀.lin⁻¹) y ∈ t₀.lam := by
    intro y hy
    rw [← hg0] at hy
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.1 hy
    rw [← hg1]
    refine Submodule.mem_map.2 ⟨y', hy', ?_⟩
    show t.lin y' = t.lin (t₀.lin.symm (t₀.lin y'))
    rw [LinearEquiv.symm_apply_apply]
  have hLat : Submodule.IsFullLattice D.host.E t₀.lam := ((Y.rowsOK u).1 t₀.lam t₀.mem).1.1
  unfold Formalism.MainNotions.S.Lat.IotaCompat
  intro x' hx' l hlr
  have hx'Λ : x' ∈ t₀.lam := (Submodule.mem_inf.1 hx').1
  have hx'o : x' ∈ orth (VS D) (Xsp t₀.frame) := (Submodule.mem_inf.1 hx').2
  have hlΛ : l ∈ t₀.lam := (Submodule.mem_inf.1 hlr).1
  have hlo : l ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := (Submodule.mem_inf.1 hlr).2
  have hβx' : (t.lin * t₀.lin⁻¹) x' ∈ t₀.lam := hβΛ x' hx'Λ
  have key : ∀ p : PlF D, (Z.M p).split ≠ none →
      (Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t₀.frame))
          (baseChange₂ D p (l - x')) ↔
        Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t.frame))
          (baseChange₂ D p (l - (t.lin * t₀.lin⁻¹) x'))) := by
    intro p hp
    obtain ⟨gβ, hext, -⟩ := GlobalTheory.LocExt.ext_isometry D Z p _ hβ
    have h := hloc p hp gβ hext (baseChange₂ D p x') (BwdNP.baseChange_mem_localLattice Z hx'Λ p) (baseChange₂ D p l) (BwdNP.baseChange_mem_localLattice Z hlΛ p)
      (baseChange_mem_perp_sup Z p _ hx'o) (baseChange_mem_perp_sup Z p _ hlo)
    rw [map_sub, map_sub, ← hext x']
    exact h
  constructor
  · intro h1
    refine mem_NgX_of_local Z hLat _ _ (sub_mem hlΛ hβx') fun p hp => ?_
    obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hp
    exact (key p hp).1 (cong_of_mem Z p g hg _ _ h1)
  · intro h2
    refine mem_NgX_of_local Z hLat _ _ (sub_mem hlΛ hx'Λ) fun p hp => ?_
    obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hp
    exact (key p hp).2 (cong_of_mem Z p g hg _ _ h2)

end GlobalTheory.IotaLocConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeLeRootCoordinateCover
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open MeasureTheory in
theorem GlobalTheory.LoopVol.packing_pinned {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (s : TT Y u u')
    {γw g g' : X.B.I.Ginf} {μw : Measure X.B.I.Ginf} (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hdec : s.pt.1 = g * γw * g'⁻¹) (hH : IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw)
    {K B : Set X.B.I.Ginf} (hK : Formalism.L2.SG.LoopTerm.IsFundR s K) (hB : MeasurableSet B)
    (hcov : ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃ q ∈ Formalism.L2.SG.TermOp.ROinf s, q * r ∈ B) :
    (μw.map fun y => g * y * g⁻¹) K ≤ (μw.map fun y => g * y * g⁻¹) B := by
  obtain ⟨-, -, hconc, hinvw⟩ := hH
  obtain ⟨hKm, hKu⟩ := hK
  haveI := Formalism.L2.SG.TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin
  set Γ := Formalism.L2.SG.TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin with hΓ
  set μR := μw.map fun y => g * y * g⁻¹ with hμR
  have hcm : Measurable fun y : X.B.I.Ginf => g * y * g⁻¹ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hRm : MeasurableSet (Formalism.L2.SG.TermOp.Vanish.Rset s) :=
    (Formalism.L2.SG.Pf.rClosedC_holds D X Y u u' s).measurableSet
  have hRc : μR (Formalism.L2.SG.TermOp.Vanish.Rset s)ᶜ = 0 := by
    rw [hμR, Measure.map_apply hcm hRm.compl]
    apply measure_mono_null _ hconc
    intro y hy
    exact fun hySt => hy (Formalism.L2.SG.LoopTerm.stInf_conj hg hg' hdec hySt)
  have hinv : ∀ q ∈ Γ, μR.map (fun x => q * x) = μR := by
    intro q hq
    have hq' := Formalism.L2.SG.LoopTerm.stInf_conj_inv hg hg' hdec (Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset s hq)
    rw [hμR, Measure.map_map (measurable_const_mul q) hcm]
    have e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) =
        (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y) := by
      funext y; simp only [Function.comp]; group
    rw [e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']
  have hpre : ∀ q ∈ Γ, ∀ C, MeasurableSet C → μR ((fun x => q * x) ⁻¹' C) = μR C := by
    intro q hq C hC
    rw [← Measure.map_apply (measurable_const_mul q) hC, hinv q hq]
  have h1 : μR K ≤ ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
    calc μR K = μR (K ∩ Formalism.L2.SG.TermOp.Vanish.Rset s) := (measure_inter_conull hRc).symm
      _ ≤ μR (⋃ q : Γ, K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
          refine measure_mono fun r hr => ?_
          obtain ⟨q, hq, hqr⟩ := hcov r hr.2
          exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩
      _ ≤ _ := measure_iUnion_le _
  have h2 : ∀ q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) =
      μR (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) := by
    intro q
    have hC : MeasurableSet (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) :=
      hB.inter (hKm.preimage (measurable_const_mul _))
    rw [← hpre q q.2 _ hC]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]
    exact and_comm
  have h3 := Formalism.L2.SG.Pf.FormAllPf.decomp μR (Formalism.L2.SG.TermOp.Vanish.Rset s) hRc Γ B K hB hKm hKu
  have h4 : ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) = μR B := by
    rw [h3]
    simp_rw [h2]
    exact (Equiv.inv Γ).tsum_eq (fun q => μR (B ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))
  exact h1.trans_eq h4

theorem GlobalTheory.LoopVol.ka_div_le_one {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (hSt : Formalism.MainNotions.S.Cnt.Stand D u u') :
    D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 := by
  have hrd := GlobalTheory.RealPlaces.one_le_rdE D
  have hg0 := hSt.2.2.2.2.2.2.2.1.two_le
  have hg1 := hSt.2.2.2.2.2.2.2.2.1.two_le
  have h0 : (2 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast hg0
  have h1 : (2 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast hg1
  have hgR : (4 : ℝ) ≤ (X.B.g : ℝ) := by rw [X.g_eq]; push_cast; nlinarith
  have e : D.host.ka / (X.B.g : ℝ) / Real.pi = 2 / (D.host.rdE * X.B.g) := by
    rw [show D.host.ka = Real.pi / (D.host.rdE / 2) from rfl]
    have : (0 : ℝ) < D.host.rdE := by linarith
    have : (0 : ℝ) < (X.B.g : ℝ) := by linarith
    field_simp
  rw [e, div_le_one (by positivity)]
  nlinarith

theorem GlobalTheory.LoopVol.covolume_le_cover : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (μR : MeasureTheory.Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.VolPin.IsPinnedR s w μR → Formalism.L2.SG.LoopTerm.IsFundR s K → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet Ω → (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → μR K ≤ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w μR K hat hPin hK L U hL hU hZ Ω hΩ hcov
  obtain ⟨γw, sf, s', μw, hrep, hsf, hs', hdec, hμwH, hμwS, rfl⟩ := hPin
  obtain ⟨T, hT, hTc⟩ := _root_.GlobalTheory.LoopVol.cover_action Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w γw sf s' hat hrep hsf hs' hdec
    L U hL hU hZ Ω hcov
  have hTΩ : MeasurableSet (T ⁻¹' Ω) := hT.measurable hΩ
  have hBm : MeasurableSet (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
    (GlobalTheory.LoopVol.ratCoord_cont X u' w γw sf).measurable hTΩ
  have hka := GlobalTheory.LoopVol.ka_div_le_one X hH.2.1
  calc (μw.map fun y => sf * y * sf⁻¹) K
      ≤ (μw.map fun y => sf * y * sf⁻¹) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
        GlobalTheory.LoopVol.packing_pinned s hsf hs' hdec hμwH hK hBm hTc
    _ ≤ MeasureTheory.volume (T ⁻¹' Ω) * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) :=
        _root_.GlobalTheory.LoopVol.pinned_ratCoord_le D X u u' w γw sf μw hμwH hμwS hka _ hTΩ
    _ = MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
        rw [hT.measure_preimage hΩ.nullMeasurableSet]

end
end

