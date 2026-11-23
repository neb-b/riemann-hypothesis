module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0074
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolKap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolPrim
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0033
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0038
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0037
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0040
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0096
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0097

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol Formalism.L2.SG.NGAnalytic.MassDataLemmas

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepChoiceDataC_of_leavesG
    (hSW : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
      Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ∧
        Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hTy : OnTied fun D X hb Y u u' X0 ψ =>
      InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
        (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0))
    (hPC : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos)
    (hFV : OnTied fun D X hb Y u u' X0 ψ =>
      FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
        (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)) :
    StepChoiceConstantsC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨Cgs, CTs, -, -, s₀, t₀, hS⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  refine ⟨max s₀ 29, max t₀ 16, fun C' Cl h1 h2 D large₂ X Y u u' hc hb X0 ψ hT => ?_⟩
  obtain ⟨-, -, hrd, -, hg, -⟩ := hS C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u u' hc
  have hGap : Formalism.L2.SG.ConcreteSettingExists.GapHyp D :=
    Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hc.1.1 (le_trans (le_max_right _ _) h2) (le_trans (le_max_right _ _) h1)
  have e := fun {P} (h : OnTied P) => h Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT
  exact ⟨0, 0, 1, X.Fu u, Y.what₂ u, fun _ => 0, pairSys0 u u' (X.Fu u) (Y.what₂ u), fun _ => idx0 D,
    fun _ => idx0 D, fun _ => 0,
    massDataValid_bk_of X hb Y u u' X0 ψ 0 0 1 (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D)
      (fun _ => idx0 D) (fun _ => 0) hc hrd (by linarith) hT (level_s_at_instance X hb Y.hK _ _ u u' X0 _ _)
      (Formalism.L2.SG.Pf.MassDataX.inMassesAt_holds X hb Y.hK _ _ u u' X0 _ _)
      (Formalism.L2.SG.Pf.MassDataX.inColumnsAt_holds X hb Y.hK _ _ u u' X0 _ _)
      (Formalism.L2.SG.Pf.MassDataX.inIndicesAt_holds X hb Y.hK _ _ u u' X0 _ _)
      (volumes_s_at_instance hSW X hb Y.hK _ _ u u' X0 _ _) (kpp_volume_at_instance X hb Y.hK _ _ u u' X0 _ _)
      (e hTy) (e hPC) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
      (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim) (Formalism.L2.SG.LocVolKap.kapX X hb u u')
      (Formalism.L2.SG.Pf.realObj_inNuX X u u' 1) (hInfG D X u u' hGap) (e hPos) (e hFV)⟩

theorem choice_massData (hSW : PI.VolStabS.MassDataS.SWXS)
    (hPC : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1) :
    StepChoiceConstantsC := by
  exact stepChoiceDataC_of_leavesG hSW MassDataX.nTy_holds hPC hInfG (MassDataX.nPos_of hSW hPC) (MassDataX.frameVolAt_of_prodConv hPC)

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXConditions
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Clauses

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem inMass_bCF : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass :=
  inMass_bC X hb hK FdN FdN' u u' X0 _ T sd C Th _ (massH_pos X u).ne'

theorem inMasses_bCF (hX : HypX X hb FdN FdN' u u') :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses := by
  have h := inMassesAt_holds X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX
  exact h

theorem inLevelS_bCF (hX : HypX X hb FdN FdN' u u') :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS := by
  have h := level_s_at_instance X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX
  exact h

theorem inVolumes_bCF (hSW : PI.VolStabS.MassDataS.SWXS) (hX : HypX X hb FdN FdN' u u') (hψ : IsCharAF X.B.I.F ψ)
    (hstd : IsStdChar ψ) (hC : MeasCompatψ X ψ) (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes := by
  have h := inVolumes_of_compat X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    (volumes_s_at_instance hSW X hb hK FdN FdN' u u' X0 _ _) hX ⟨ψ, hψ, hstd, hC⟩ hdet
  exact h

theorem inTyped_bCF (hX : HypX X hb FdN FdN' u u') (hP : ProdConv X u u' ψ) (hL : LocTieX X ψ u) (hL' : LocTieX X ψ u')
    (hTF : TypFacts X u u') (hψ : IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped :=
  inTypedC_loc X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (fun X v => SDL.sdLocX_holds X v) (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) sTypIdx_holds
    hψ hstd hX hP hL hL' hTF

theorem pos_bCF (hSW : PI.VolStabS.MassDataS.SWXS) (hX : HypX X hb FdN FdN' u u') (hP : ProdConv X u u' ψ)
    (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ) (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0)
    (hQ : Formalism.L2.SG.Pf.MassDataPos.QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hsd : 0 ≤ sd) (hC0 : 0 ≤ C) (hTh : 0 < Th) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos := by
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (locHaarPosC_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (covolPosC_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hψ hC hX.1 hdet)
    hQ
    (recPosC_of_dv X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (fun X v => dvPosC_holds X v) hX)
    hP (Formalism.L2.SG.Pf.MassDataPos.cooOf_pos X u u') (Formalism.L2.SG.WConst.kapN_pos (D := D)) hsd hC0 hTh

end Clauses

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OneMemDdPow
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_of_loc (I : Submodule (𝓞 D.host.E) D.host.E) (x : D.host.E)
    (h : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ (t : D.host.E) * x ∈ I) : x ∈ I := by
  let J : Ideal (𝓞 D.host.E) :=
    { carrier := {t | (t : D.host.E) * x ∈ I}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *
        push_cast
        rw [add_mul]
        exact I.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        push_cast
        rw [zero_mul]
        exact I.zero_mem
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq] at *
        have e : (((c • a : 𝓞 D.host.E)) : D.host.E) * x = c • ((a : D.host.E) * x) := by
          rw [smul_eq_mul, Algebra.smul_def]
          push_cast
          ring
        rw [e]
        exact I.smul_mem c ha }
  by_contra hx
  have hJ : J ≠ ⊤ := by
    intro h1
    have h2 : (1 : 𝓞 D.host.E) ∈ J := h1 ▸ Submodule.mem_top
    apply hx
    have h3 : ((1 : 𝓞 D.host.E) : D.host.E) * x ∈ I := h2
    simpa using h3
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.E)
  obtain ⟨t, htP, ht⟩ := h ⟨M, hM.isPrime, hM0⟩
  exact htP (hJM ht)

theorem one_mem_ddPow (k : ℕ) : (1 : D.host.E) ∈ ddS D ^ (-(k : ℤ)) := by
  have hne := Formalism.L2.SG.Pf.StabIntSh.lg_ddS_ne (D := D)
  have h1 : ddS D ^ k ≤ 1 := pow_le_one' FractionalIdeal.coeIdeal_le_one k
  have h2 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ ≤ (ddS D ^ k)⁻¹ :=
    FractionalIdeal.inv_anti_mono (pow_ne_zero k hne) h1
  rw [inv_one] at h2
  rw [_root_.zpow_neg, zpow_natCast]
  exact h2 (FractionalIdeal.mem_one_iff _ |>.2 ⟨1, map_one _⟩)

theorem coef_spanO {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {v : (VS D).V}
    (hv : v ∈ Submodule.span (𝓞 D.host.E) (Set.range F0.e))
    (y : Fin D.R.rS → D.host.E) (hy : v = ∑ a, y a • F0.e a) (a : Fin D.R.rS) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = y a := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  have hyy : y = fun b => (c b : D.host.E) := by
    have h := F0.e_indep
    rw [Fintype.linearIndependent_iff] at h
    funext b
    have := h (fun b => y b - (c b : D.host.E)) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hy]
      rw [← hc]
      simp only [sub_eq_zero]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [algebraMap_smul]) b
    exact sub_eq_zero.1 this
  exact ⟨c a, by rw [hyy]⟩

end Formalism.L2.SG.Pf.ZsVolLat

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxCloseAt
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section CloseAt

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem diag_mul_diag_apply {K : Type*} [CommRing K] {n : ℕ} (a b : Fin n → K) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (Matrix.diagonal a * X * Matrix.diagonal b) i j = a i * X i j * b j := by
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

set_option maxHeartbeats 800000 in
theorem close_at {p : PlF D} (hA : Agree δ M p) (h : ProdE.StP M δ u u' w p) (c : (D.s.atP p).Fp) (hc0 : c ≠ 0)
    (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    ∃ τ : ProdE.MP p, (∀ i j, i < j → τ i j = 0) ∧ (∀ i, τ i i = 1) ∧
      (∀ i j, Formalism.L2.SG.Pf.fσ w j < Formalism.L2.SG.Pf.fσ w i → τ i j = 0) ∧
      ∃ c' : (D.s.atP p).Fp, c' ≠ 0 ∧ c' ∈ 𝒪[(D.s.atP p).Fp] ∧ ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
        EntIn (latS (D.s.atP p) c') (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE - τ) →
        EntIn (latS (D.s.atP p) c) (((h⁻¹ * ProdE.πP M δ u u' w hA g).1.1 : ProdE.MP p) - 1) ∧
          EntIn (latS (D.s.atP p) c) (((h⁻¹ * ProdE.πP M δ u u' w hA g).1.2.unop : ProdE.MP p) - 1) := by
  obtain ⟨ex, ey, d, di, gg, ggi, hexO, heyO, hxx, hyy, hsum, hxy, hd, hg, hlin⟩ := mode_data M δ hA
  obtain ⟨N, Ni, hN, hN', ⟨ν, hν, hNν⟩, hfix⟩ := exists_unit_monomial_stable_of_Y0 M δ u u' w hA
  set σ := Formalism.L2.SG.Pf.fσ w with hσd
  have hσ : ∀ a, σ (σ a) = a := Formalism.L2.SG.Pf.fσ_fσ w
  set h1 : ProdE.GLp p := h.1.1 with hh1d
  set h2 : ProdE.GLp p := h.1.2.unop with hh2d
  obtain ⟨hh1, hh2, hh3⟩ := h.2
  have hh : (h1 : ProdE.MP p) * N * (h2 : ProdE.MP p) = N := hfix _ _ hh1 hh2 hh3
  obtain ⟨hi1, hi2, -⟩ := (h⁻¹).2
  have hΔ : Matrix.diagonal d * Matrix.diagonal di = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hd i
  have hΓ : Matrix.diagonal gg * Matrix.diagonal ggi = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hg i
  have hΓ' : Matrix.diagonal ggi * Matrix.diagonal gg = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact hg i
  obtain ⟨c', hc'0, hc'O, hcl⟩ := close ex ey hexO heyO hxx hyy hsum hxy N Ni (Matrix.diagonal d) (Matrix.diagonal di)
    (Matrix.diagonal gg) (Matrix.diagonal ggi) hN hN' hΔ hΓ hΓ' h1 h2 hh c hc0 hc

  have h1inv : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * (h1 : ProdE.MP p) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2inv : (h2 : ProdE.MP p) * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have rel1 : (h1 : ProdE.MP p) * mono σ ν = mono σ ν * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) := by
    rw [← hNν]
    calc (h1 : ProdE.MP p) * N = (h1 : ProdE.MP p) * N * ((h2 : ProdE.MP p) * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p)) := by
          rw [h2inv, Matrix.mul_one]
      _ = N * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) := by rw [← Matrix.mul_assoc, hh]
  have rel2 : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * mono σ ν = mono σ ν * (h2 : ProdE.MP p) := by
    rw [← hNν]
    calc ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * N
        = ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * ((h1 : ProdE.MP p) * N * (h2 : ProdE.MP p)) := by rw [hh]
      _ = N * (h2 : ProdE.MP p) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1inv, Matrix.one_mul]
  refine ⟨ex • (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) +
      ey • (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi).transpose, ?_, ?_, ?_, c', hc'0, hc'O, ?_⟩
  · intro i j hij
    have a1 : (h1 : ProdE.MP p) i j = 0 := (hh1 i j).1 hij
    have a2 : (h2 : ProdE.MP p) j i = 0 := (hh2 j i).1 hij
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply,
      diag_mul_diag_apply, a1, a2]
    simp
  · intro i
    have a1 : (h1 : ProdE.MP p) i i = 1 := (hh1 i i).2 rfl
    have a2 : (h2 : ProdE.MP p) i i = 1 := (hh2 i i).2 rfl
    have t1 : (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) i i = 1 := by
      rw [diag_mul_diag_apply, a1, mul_one, mul_comm, hd i]
    have t2 : (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi) i i = 1 := by
      rw [diag_mul_diag_apply, a2, mul_one, hg i]
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, t1, t2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one, hsum]
  · intro i j hij
    have e1 : (h1 : ProdE.MP p) i j = 0 :=
      fix_pat hσ ν hν (fun a b hab => (hi2 a b).1 hab) rel1 i j hij
    have e2 : (h2 : ProdE.MP p) j i = 0 := by
      have z : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) (σ j) (σ i) = 0 := (hi1 (σ j) (σ i)).1 hij
      have := fix_entry hσ ν rel2 (σ j) (σ i)
      rw [hσ, hσ, z, zero_mul] at this
      exact (hν (σ j)).mul_right_eq_zero.1 this.symm
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply,
      diag_mul_diag_apply, e1, e2]
    simp
  · intro g hG
    set π := ProdE.πP M δ u u' w hA g with hπd
    set l : ProdE.GLp p := π.1.1 with hld
    set ρ : ProdE.GLp p := π.1.2.unop with hρd
    obtain ⟨hk1, hk2, -⟩ := (h⁻¹ * π).2
    obtain ⟨hπl, hπρ, hπ⟩ := π.2
    have ek1 : ((h⁻¹ * π).1.1 : ProdE.GLp p) = h1⁻¹ * l := rfl
    have ek2 : ((h⁻¹ * π).1.2.unop : ProdE.GLp p) = ρ * h2⁻¹ := rfl
    have hk1' : Formalism.MainNotions.S.IsLoUni (((h1⁻¹ * l : ProdE.GLp p)) : ProdE.MP p) := by rw [← ek1]; exact hk1
    have hk2' : Formalism.MainNotions.S.IsUpUni (((ρ * h2⁻¹ : ProdE.GLp p)) : ProdE.MP p) := by rw [← ek2]; exact hk2
    have hl : ex • ((l : ProdE.GLp p) : ProdE.MP p) =
        ex • (Matrix.diagonal d * ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE *
          Matrix.diagonal di) :=
      (hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).1
    have hρ : ey • ((ρ : ProdE.GLp p) : ProdE.MP p) =
        ey • (Matrix.diagonal ggi * (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map
          (D.s.atP p).ιE).transpose * Matrix.diagonal gg) :=
      (hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).2
    have hlN : ((l : ProdE.GLp p) : ProdE.MP p) * N * ((ρ : ProdE.GLp p) : ProdE.MP p) = N := hfix _ _ hπl hπρ hπ
    have res := hcl l ρ (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE)
      (fun i j hij => by
        rcases lt_or_eq_of_le hij with h' | h'
        · rw [Matrix.sub_apply, (hk1' i j).1 h', Matrix.one_apply_ne (ne_of_lt h'), sub_zero]
        · subst h'
          rw [Matrix.sub_apply, (hk1' i i).2 rfl, Matrix.one_apply_eq, sub_self])
      (fun i j hij => by
        rcases lt_or_eq_of_le hij with h' | h'
        · rw [Matrix.sub_apply, (hk2' i j).1 h', Matrix.one_apply_ne (ne_of_gt h'), sub_zero]
        · subst h'
          rw [Matrix.sub_apply, (hk2' j j).2 rfl, Matrix.one_apply_eq, sub_self])
      hlN hl hρ hG
    rw [ek1, ek2]
    exact res

end CloseAt

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauSecondValue
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

theorem sconj_apply (ρ : MP p) (a b : Fin (D.R.rS + 1)) :
    (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      (-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
  simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem sconj_up {ρ : MP p} (h : IsUpUni ρ) :
    IsUpUni (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [sconj_apply, (h a b).1 hab]; simp
  · subst hab
    rw [sconj_apply, (h a a).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]; simp

theorem tau_second_value (x : GG p) : (((tau p x).2.unop : GLp p) : MP p) =
    Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p := rfl

theorem tau_mem_UP {x : GG p} (hx : x ∈ UP p) : tau p x ∈ UP p :=
  ⟨hx.1, by rw [tau_second_value]; exact sconj_up p hx.2⟩

theorem tau_mem_KP {x : GG p} (hx : x ∈ KP M p) : tau p x ∈ KP M p := by
  refine ⟨hx.1, ?_⟩
  show Formalism.MainNotions.S.TieN.IntUp (M p) (((tau p x).2.unop : GLp p) : MP p)
  rw [tau_second_value]
  obtain ⟨h1, h2, h3⟩ := hx.2
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [sconj_apply, h1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [sconj_apply, h2 a b hab]; simp
  · rw [sconj_apply]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _) (h3 a b))
      (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

def phi (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (Z : MP p) : MP p :=
  Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w

theorem phi_smul (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {x : GG p}
    (hx : x ∈ UP p) (Z : MP p) : phi p δ T T' w (x • Z) = tau p x • phi p δ T T' w Z := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  have hc : ((x.1 : GLp p) : MP p) * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p) =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w := by
    have hu := sconj_up p hx.2
    refine Formalism.L2.SG.Pf.FibQ.corner_fix p (fun a b h => (hx.1 a b).1 h) (fun a => (hx.1 a a).2 rfl)
      (fun a b h => (hu a b).1 h) (fun a => (hu a a).2 rfl) (fun a b h => ?_)
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Matrix.of_apply]
    rw [if_neg h]
  simp only [phi, smul_def, tau_second_value]
  show ((x.1 : GLp p) : MP p) * Z * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w =
    ((x.1 : GLp p) : MP p) * (Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w) *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p)
  rw [Matrix.mul_add, Matrix.add_mul, hc]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), hss, Matrix.one_mul]

theorem phi_inj (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {Z Z' : MP p}
    (h : phi p δ T T' w Z = phi p δ T T' w Z') : Z = Z' := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  unfold phi at h
  have h2 := add_right_cancel h
  calc Z = Z * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]
    _ = Z' * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [h2]
    _ = Z' := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ToPtsInj
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toPts_inj {K : Type} [Zero K] {i : ℕ} (p q : Point K (i + 1)) (h : toPts p = toPts q) : p = q := by
  have key : ∀ r : Point K (i + 1),
      List.ofFn (fun a : Fin (toPts r).1.length =>
        ((toPts r).2 a, (toPts r).1.blocks.get ⟨a.1, a.2⟩)) = r.1 := by
    intro r
    apply List.ext_get
    · simp [toPts, Composition.length]
    · intro n h1 h2
      simp [toPts]
  apply Subtype.ext
  rw [← key p, ← key q, h]

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem at_ptOf (t : TauC Y u u') (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    t.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t.toTerm) := by
  by_cases hex : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant
  · exact Formalism.L2.SG.PairVal.ptOf_spec _ hex
  · exfalso
    have hj : Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.junkPoint D u u' := by
      unfold Formalism.L2.SG.PairVal.ptOf
      rw [dite_eq_right hex]
    have h0 : NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t) = 0 := by
      unfold ptPN
      rw [hj]
      unfold NGPt
      obtain ⟨w0⟩ : Nonempty (InfinitePlace D.host.E) := by
        first | exact inferInstance | infer_instance
      apply Finset.prod_eq_zero (Finset.mem_univ w0)
      rw [GPt_junk]
      first | simp | rw [map_zero, mul_zero]
    linarith

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

