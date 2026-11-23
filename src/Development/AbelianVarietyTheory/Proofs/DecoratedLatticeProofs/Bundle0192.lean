module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
public import Formalism.LocalRingCardinality.HostCls
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComponentParametersContainString
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.LiftParams

theorem param_of_sysParam : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s y, IsEigV R i t h s y → ∀ l : (R.cV i).W →ₗ[ℂ] ℂ, (fun g => l (R.extV i t y g)) ≠ 0 → ∀ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B → GlobalTheory.LFun.IsParamFunV (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (fun g => l (R.extV i t y g)) B := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _hF i t h hh s y hy l hl B hB
  have hC := hG.core
  have h1 := hC.lev.βV i
  unfold IsSDFrame at h1
  obtain ⟨n, hBase⟩ := h1
  have hBase1 : IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1 := by
    simpa only [one_pow] using hBase
  have hfm := Eq.le (hC.models.HV i t).right.left (LinearMap.mem_range_self (R.HV i t).e y)
  have hc := hC.models.cV i
  have hS : ∀ PP : Pl D.host.E, PP ∈ (flag1L (R.datVt i t)).Pg ∨ PP ∈ (flag1L (R.datVt i t)).Q →
      HeightOneSpectrum.under (𝓞 ↥D.host.F) PP ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t :=
    fun _ hPP => GlobalTheory.DownLift.Params.under_mem_badPl R t hPP
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D (Vc D i) (R.βV i) (R.ΛV i) (flag1L (R.datVt i t))
    (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) hBase1 hS).1

  have hfix : ∀ P : Pl D.host.E, GlobalTheory.Hk3.Good R t P → ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ g,
      l ((R.extV i t) y (g * k)) = l ((R.extV i t) y g) := by
    intro P hP k hk g
    have hlo := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) 1 (flag1L (R.datVt i t)) hBase1 P
      (GlobalTheory.DefLiftHecke.one_pow_notMem P 0) (fun PP hPP => hP PP hPP)).1 k hk
    exact congrArg l (GlobalTheory.DefLiftHecke.ext_level (R.cV i) hc hfm hlo.1 hlo.2 g)
  refine ((GlobalTheory.LFun.param_iff_sysParam D (Vc D i) (↑(levG (Vc D i) (R.βV i) (flag1L (R.datVt i t))))
    (levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t))) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) s B hsph).1
    (fun g => l ((R.extV i t) y g)) hl ?_ ?_).2 hB
  · intro v hv k hk g
    have hw0 : ∃ w : HeightOneSpectrum (𝓞 D.host.E), HeightOneSpectrum.under (𝓞 ↥D.host.F) w = v := GlobalTheory.ChainOnto.VacOffS.exists_under v
    obtain ⟨w, hw⟩ := hw0
    have hgood : GlobalTheory.Hk3.Good R t w := (GlobalTheory.DownLift.Params.good_iff R t w).2 (by rw [hw]; exact hv)
    have hm : (GlobalTheory.AdelicU.emb _ (HSpace.gram (Vc D i)) v) k ∈ GlobalTheory.Hk3.hyp (Vc D i) w := (GlobalTheory.HypDict.mem_hyp_iff_embV D v w hw (Vc D i) _).2 ⟨k, hk, rfl⟩
    exact hfix w hgood _ hm g
  · intro P d Rr hR
    have hoff : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) P := by
      obtain ⟨_, _, _, _, hoff, _⟩ := hR
      exact hoff
    have hgood : GlobalTheory.Hk3.Good R t P := (GlobalTheory.Hk3.OpsRowsTuple.offS_badPl_iff R t P).1 hoff
    have hsp : GlobalTheory.Hk3.SphOp (Vc D i) P d Rr :=
      (((GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) 1 (flag1L (R.datVt i t)) hBase1 P
        (GlobalTheory.DefLiftHecke.one_pow_notMem P 0) (fun PP hPP => hgood PP hPP)).2.1 _ d Rr).1 hR).2
    have hlab : GlobalTheory.Hk3.IsLab (Vc D i) P d := ⟨Rr, hsp⟩
    have hK0 := GlobalTheory.SphLabelOps.exists_hyp (Vc D i) P
    obtain ⟨K, hK⟩ := hK0
    have hsp' := hsp
    unfold GlobalTheory.Hk3.SphOp Hecke₂ at hsp'
    obtain ⟨e, f, ϖ, α, _, hpi, hϖ, hϖ2, _, _, _, hα, hdα, _, _⟩ := hsp'
    have r1 := GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi hϖ hϖ2 hα hdα hsp
    have r2 := GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi hϖ hϖ2 hα hdα (GlobalTheory.Hk3.LabDet.sphOp_rep hlab)
    funext g
    have hsum : ∑ γ ∈ Rr, l ((R.extV i t) y (g * γ)) =
        ∑ γ ∈ GlobalTheory.Hk3.rep (Vc D i) P d, l ((R.extV i t) y (g * γ)) := by
      have h0 := r1.sum_eq r2 K.one_mem (fun γ => l ((R.extV i t) y (g * γ)))
        (fun x k hk => by
          simpa only [mul_assoc] using hfix P hgood k (by rw [hK]; exact hk) (g * x))
      simpa only [one_mul] using h0
    have hop : GlobalTheory.Hk3.hkF (Vc D i) P (fun₀ | d => 1) ((R.HV i t).e y) = s P d • (R.HV i t).e y :=
      Eq.trans (Eq.symm (hh P hgood (fun₀ | d => 1) y))
        (Eq.trans (congrArg (⇑(R.HV i t).e) (hy P d hgood hlab)) (map_smul (R.HV i t).e (s P d) y))
    have hext := GlobalTheory.DefLiftHecke.ext_hkF (R.cV i) hc P (fun₀ | d => 1) ((R.HV i t).e y) g
    have hext2 : s P d • (R.cV i).ext ((R.HV i t).e y) g =
        ∑ a ∈ GlobalTheory.Hk3.rep (Vc D i) P d, (R.cV i).ext ((R.HV i t).e y) (g * a) := by
      have h0 := (congrArg (fun z => (R.cV i).ext z g) hop).symm.trans hext
      simpa only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
        one_smul, map_smul, Pi.smul_apply, LinearMap.smul_apply] using h0
    show ∑ γ ∈ Rr, l ((R.extV i t) y (g * γ)) = s P d • l ((R.extV i t) y g)
    refine hsum.trans ?_
    show ∑ γ ∈ GlobalTheory.Hk3.rep (Vc D i) P d, l ((R.cV i).ext ((R.HV i t).e y) (g * γ)) =
      s P d • l ((R.cV i).ext ((R.HV i t).e y) g)
    exact (map_sum l (fun γ => (R.cV i).ext ((R.HV i t).e y) (g * γ)) (GlobalTheory.Hk3.rep (Vc D i) P d)).symm.trans
      ((congrArg l hext2.symm).trans (map_smul l (s P d) _))

end GlobalTheory.LiftParams
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizeInequalitiesNoLevelPrimeColumnNormParameters
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.SizeRowsRec

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare.SizeRows

theorem sizeRowsS_numRec : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word),
    SizeRowsS CY (numDatumOfParameters D L) (codeRec L u) := by
  intro D large₂ CY hR u
  have hnu := _root_.GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem D large₂ CY hR u
  obtain ⟨⟨P⟩, ⟨s2, s3, s4⟩, hg, ⟨s10, -, -, -, s14⟩, ⟨n, hn⟩, -⟩ := hR
  have hDel : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del := by rw [hn, Nat.floor_natCast]
  have hSc : (numDatumOfParameters D large₂).Sc = large₂.Sc := by
    rw [large₂.Sc_eq]
    show (D.R.k : ℝ) * (4 * ((⌊D.s.Del⌋₊ : ℕ) : ℝ)) = _
    rw [← Rat.cast_natCast, ← Rat.cast_natCast (α := ℝ) ⌊D.s.Del⌋₊, hDel]
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm : (0 : ℝ) < D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)
  have hn0 : 0 < D.R.n := D.R.n_pos'
  have hq := D.host.hyp.1.pos
  have hd := D.host.hyp.2.1.pos
  refine ⟨⟨?_, ?_, ?_, s4, ?_⟩, fun i => ⟨?_, hg i⟩, trivial, f_mul_N_le_b P s10, hnu, ?_, ?_, ?_, ?_, ?_⟩
  · exact s2
  · refine log_le_L_of_le_cond P hq ?_
    unfold LevelStarExponents.condE
    exact le_trans (Nat.le_mul_of_pos_left _ D.host.QS_pos) (Nat.le_mul_of_pos_right _ hd)
  · refine log_le_L_of_le_cond P hd ?_
    unfold LevelStarExponents.condE
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos D.host.QS_pos hq)
  · rw [large₂.logDerivative_at_one_eq] at s3
    exact s3
  · obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
    exact h1.trans (h2 i).1
  · intro z i j
    refine (large₂.be_close (tauPl D z) i j).trans ?_
    show large₂.etaSz ≤ (D.R.m : ℝ) * ((⌈LevelStarExponents.h0 large₂⌉₊ : ℕ) : ℝ)
    have h := Nat.le_ceil (LevelStarExponents.h0 large₂)
    calc large₂.etaSz = (D.R.m : ℝ) * LevelStarExponents.h0 large₂ := by unfold LevelStarExponents.h0; field_simp
      _ ≤ _ := by gcongr
  · intro z i
    rw [hSc]
    obtain ⟨h1, h2⟩ := large₂.cloud_v (tauPl D z) i
    exact ⟨by exact_mod_cast h1, h2⟩
  · intro z i h1 h2
    obtain ⟨i, hi⟩ := i
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by simp only at h1; omega⟩
    have hl : l < D.R.k - 2 := by
      have : l + 1 + 1 < D.R.k := h2
      omega
    have e : (numDatumOfParameters D large₂).uW (codeRec large₂ u) z ⟨l + 1, hi⟩ = (D.hcW u (tauPl D z)).u ⟨l + 1, hi⟩ := by
      rw [D.s.u_letter u (tauPl D z) l hl, D.hcW_v]
      unfold NumDatum.uW
      rw [dite_eq_left ⟨h1, h2⟩]
      show _ - _ - (if D.s.letter u ⟨l, hl⟩ = true then ((⌊D.s.Del⌋₊ : ℕ) : ℚ) else 0) = _
      rw [hDel]
      rfl
    rw [hSc, e]
    obtain ⟨a1, a2⟩ := large₂.cloud_u u (tauPl D z) ⟨l + 1, hi⟩ h1 h2
    exact ⟨by exact_mod_cast a1, a2⟩
  · intro t ht
    have h := (large₂.top_u (tauPl D (false, t)) ⟨t, ht⟩ (by omega) (eTau_tauPl (false, t))).2
    have e : (((numDatumOfParameters D large₂).bT t : ℚ) : ℝ) = (large₂.bT ⟨t, ht⟩ : ℝ) := by
      unfold NumDatum.bT
      push_cast
      erw [h]
      ring
    rw [e]
    exact ⟨large₂.bT_ge _, s14 _⟩
  · intro z hz hk2
    have hz' := not_top_of z hz
    rw [hSc]
    refine ⟨P.uk_extreme _ hk2 hz', (large₂.cloud_gap _ (by omega) hz').1, ?_⟩
    have h1 := P.cloud_place_bound _ (by omega) hz'
    have h2 := (large₂.cloud_v (tauPl D z) ⟨0, by omega⟩).2
    push_cast at h1
    show (((D.hc (tauPl D z)).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ _
    linarith

end GlobalTheory.CoreHt.SizeRowsRec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOutsideBoxProductOrthDecSumLattice
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.SumBoxSph

variable {D : D7}

theorem rat_mul_gen {k l m : ℕ} (q : Matrix (Fin k) (Fin l) D.host.E) (p : AF D.host.F) (a : D.host.E)
    (t : Fin l → D.host.E) (z : Fin m → D.host.E) :
    rat q ⬝ (Matrix.of fun i j => (p ⊗ₜ[D.host.F] (a * t i * z j) : AE D) : Mx D l m) =
      (Matrix.of fun i j => (p ⊗ₜ[D.host.F] (a * (q *ᵥ t) i * z j) : AE D) : Mx D k m) := by
  ext i j
  have h : ∀ e y : D.host.E, incA D e * (p ⊗ₜ[D.host.F] y : AE D) = p ⊗ₜ[D.host.F] (e * y) := fun e y => by
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (p ⊗ₜ[D.host.F] y) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  show ∑ r, incA D (q i r) * (p ⊗ₜ[D.host.F] (a * t r * z j) : AE D) = p ⊗ₜ[D.host.F] (a * (∑ r, q i r * t r) * z j)
  rw [Finset.mul_sum, Finset.sum_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [h]
  congr 1
  ring

theorem resT_mem_latO {A B W H : HSp D} (o : OrthDec B W H) {LA : Lat A} {LW : Lat W} {LH : Lat H}
    {P : FinPl D → Prop} {u : WO A B} (hu : u ∈ latO A B LA (sumLatO o LW LH) P) :
    o.resT A u ∈ (latO A W LA LW P).prod (latO A H LA LH P) := by
  have key : latO A B LA (sumLatO o LW LH) P ≤
      ((latO A W LA LW P).prod (latO A H LA LH P)).comap (o.resT A).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨x, hx, x', hx', rfl⟩ := (mem_sumLatO o LW LH t).1 ht
    have e₁ : o.qA *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qA_iA, o.qA_iB, Matrix.one_mulVec,
        Matrix.zero_mulVec, add_zero]
    have e₂ : o.qB *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x' := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qB_iA, o.qB_iB, Matrix.one_mulVec,
        Matrix.zero_mulVec, zero_add]
    refine ⟨AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, x, hx, ?_⟩,
      AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, x', hx', ?_⟩⟩
    · have := rat_mul_gen o.qA (pairA D.host.F 0 α) a (o.iA *ᵥ x + o.iB *ᵥ x') fun j => ∑ k, star (s k) * A.gram k j
      rw [e₁] at this
      exact this
    · have := rat_mul_gen o.qB (pairA D.host.F 0 α) a (o.iA *ᵥ x + o.iB *ᵥ x') fun j => ∑ k, star (s k) * A.gram k j
      rw [e₂] at this
      exact this
  exact key hu

theorem isHalf_mul {k l m : ℕ} {e : AE D} (p : Mx D k l) {u : Mx D l m} (hu : IsHalf e u) : IsHalf e (p ⬝ u) := by
  intro i j
  show e * ∑ r, p i r * u r j = ∑ r, p i r * u r j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [mul_left_comm, hu r j]

theorem isSphOff_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B W H : HSp D) (o : OrthDec B W H) (LA : Lat A) (LW : Lat W) (LH : Lat H) (Sf : Finset (FinPl D)) (Φ : WO A W → ℂ) (Φ' : WO A H → ℂ), IsSphOff ψ A W LA LW Sf Φ → IsSphOff ψ A H LA LH Sf Φ' → IsSphOff ψ A B LA (sumLatO o LW LH) Sf (o.boxT A Φ Φ') := by
  intro D ψ A B W H o LA LW LH Sf Φ Φ' h₁ h₂
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · obtain ⟨hL, hR⟩ := resT_mem_latO o hu
    rw [o.heisO_boxT, map_nsmul, Prod.smul_fst, Prod.smul_snd, h₁.1 _ hL, h₂.1 _ hR]
  · obtain ⟨hL, hR⟩ := resT_mem_latO o hu
    rw [o.heisO_boxT, h₁.2 e he _ hL (isHalf_mul o.pA hh), h₂.2 e he _ hR (isHalf_mul o.pB hh)]

end GlobalTheory.Core.Rk.SumBoxSph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.PlaceProjAt

theorem algebraMap_mem_iff {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (PP : Formalism.L2.DIV.Pl D.host.E) (h : IsProjAt φ PP) (a : 𝓞 D.host.F) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ PP.asIdeal ↔ a ∈ v.asIdeal := by
  have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F a) := by
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  refine (h _).trans ?_
  rw [h1, GlobalTheory.PlaceRed.rdQ_alg, ReciprocityTheory.Aut.adic_valued_algebraMap, HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem under_resCard : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal := by
  intro D v φ PP h
  have hmem := algebraMap_mem_iff φ PP h
  have hv : v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← hmem]
    rfl
  refine ⟨hv, ?_⟩
  refine (GlobalTheory.LFun.SatBoundGL.resCard_completion v).trans ?_
  let f : 𝓞 D.host.F →+* 𝓞 D.host.E ⧸ PP.asIdeal :=
    (Ideal.Quotient.mk PP.asIdeal).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  have hker : RingHom.ker f = v.asIdeal := by
    ext a
    rw [RingHom.mem_ker, ← hmem]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := ReciprocityTheory.Aut.adic_exists_approx v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) (GlobalTheory.PlaceRed.rdQ_int φ x)
    refine ⟨a, ?_⟩
    show Ideal.Quotient.mk PP.asIdeal (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = Ideal.Quotient.mk PP.asIdeal x
    rw [Ideal.Quotient.eq, ← neg_mem_iff, neg_sub]
    refine (h _).2 ?_
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F a) := by
      show algebraMap (𝓞 D.host.E) D.host.E _ = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [show ((x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
        (x : D.host.E) - ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) from
        map_sub (algebraMap (𝓞 D.host.E) D.host.E) _ _, ← GlobalTheory.PlaceRed.rdQh_apply, map_sub, GlobalTheory.PlaceRed.rdQh_apply, GlobalTheory.PlaceRed.rdQh_apply, h1,
      GlobalTheory.PlaceRed.rdQ_alg]
    exact ha
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).toEquiv

end GlobalTheory.PlaceProjAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageCuspFormValueMemFullSphericalHeckeEigenpart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.ValPart

theorem lift_compMultilinearMap {ι : Type*} [Fintype ι] {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module ℂ (Mi i)]
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) (T : (Π i, Mi i) →ₘₗ[ℂ] E) :
    PiTensorProduct.lift (L.compMultilinearMap T) = L ∘ₗ PiTensorProduct.lift T := by
  apply PiTensorProduct.ext
  ext v
  simp

theorem valPart_mem : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ForStage D fun c _ s =>
    ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B →
      ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
        PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
          partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e := by
  intro hCRD D hMet hLev c hc j hj s hs u w B hw hB
  obtain ⟨-, hsphc, hsplit, -, hunif⟩ := _root_.GlobalTheory.ChainOntoSph.level_spherical_off_S D c hc j hj s hs
  obtain ⟨-, hopc, hconjH⟩ := _root_.GlobalTheory.ConjVal.conj_values_hecke hCRD D c hc j hj s hs
  have hlat := (_root_.GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D c hc j hj s hs).2
  obtain ⟨-, -, -, -, hmul, -⟩ := hLev c hc j hj s hs
  have hBV : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (PiLocalization₂.val u w g)) B := (hlat _ B).1 hB
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.ParamEigen.eig_of_param D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsphc B
  have heig : ∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R →
      heckeLin s.V R (PiLocalization₂.val u w) = conj (a P d) • PiLocalization₂.val u w := by
    intro P d R hR
    have h1 := ha _ hBV P d R ((hopc P d R).1 hR)
    rw [hconjH] at h1
    funext g
    have h2 := congrArg (starRingEnd ℂ) (congrFun h1 g)
    simpa [map_mul] using h2
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S
    hunif hc.inf hmul hsplit
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun P d => conj (a P d), ?_⟩
  have hT : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    (mem_multT c.θ s.M _ _ _).1 u.2
  rw [mem_partFull]
  refine ⟨hT, fun P d R hR v => ?_⟩
  obtain ⟨hkeep, -, -⟩ := hops.2.2 P d R hR
  set T := PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) with hTdef
  have hT' : heckeOn s.M R T - conj (a P d) • T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    Submodule.sub_mem _ (hkeep T hT) (Submodule.smul_mem _ _ hT)
  have hmem : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) ∈ s.CC c := by
    show _ ∈ MultT c.θ s.M _ _
    rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact hT'
  let x : s.CC c := ⟨_, hmem⟩
  have hlift : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) =
      heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) - conj (a P d) • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    rw [map_sub, map_smul, heckeOn, postOn]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [lift_compMultilinearMap, hTdef, LinearEquiv.apply_symm_apply]
  have hx : PiLocalization₂.val x w = 0 := by
    show PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) w = 0
    rw [hlift]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [sub_eq_zero]
    exact heig P d R hR
  have hx0 := GlobalTheory.T.thetaChainStage_cuspFormMap_eq_zero_of_value_zero D hMet c hc j hj s hs x w hw0 hx
  have h3 : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) = 0 := congrArg Subtype.val hx0
  have h4 : heckeOn s.M R T - conj (a P d) • T = 0 := by
    have h := congrArg PiTensorProduct.lift.symm h3
    rwa [LinearEquiv.symm_apply_apply, map_zero] at h
  have h5 := congrArg (fun U : MMap s.M => U v) h4
  simp only [sub_apply, smul_apply, zero_apply, sub_eq_zero] at h5
  simpa [heckeOn, postOn_apply] using h5

end GlobalTheory.ChainOnto.ValPart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainOccurringParamsNormHalfRankBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem parBoundW_of_parBound {D : D7} (h : ParBound D) : ParBoundW D := by
  intro c hc j hj s hs u B hu
  exact GlobalTheory.LiftPole.Bounded.mono (h c hc j hj s hs u B hu) (by linarith)

theorem parBoundW (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) (hL : LevFacts D) : ParBoundW D :=
  parBoundW_of_parBound (_root_.GlobalTheory.ChainOnto.parBound_of_rapidDecay hP D hL)

end GlobalTheory.ChainOnto
end

