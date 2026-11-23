module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairBdMulDatBdLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0373
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddings
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0319
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscNResNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0380
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedTermPairsSumLeViaRowsGenusMeans
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowDoubleCosetInnerDataOneRationalClass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0297

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TcritLowOfDsig
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset

namespace GlobalTheory.CritLevelGap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CritLevel

theorem sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

theorem sizes_low {D : D7} (L : SizeData₂ D) (h : SizesAt L) : L.sc.x ≤ D.R.k ∧ Real.sqrt L.sc.b ≤ L.sc.b' := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, -⟩ := h
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  refine ⟨le_trans ?_ hK.1, le_trans hW ?_⟩
  · refine Real.self_le_rpow_of_one_le hx.le ?_
    unfold szTh
    linarith
  · have hn : (1 : ℝ) ≤ D.R.n := by
      have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
      exact_mod_cast this
    refine div_le_self ?_ (one_le_mul_of_one_le_of_one_le hx.le hn)
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity

theorem err_le (D : D7) {δ : ℝ} (hδ : 0 < δ) (h : 8 / Real.log (1 + δ) ≤ D.R.k) :
    Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) - 1 ≤ δ := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hl : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (show D.R.f ≤ D.R.k from D.R.f_le_k)
  have h2 : (D.R.k : ℝ) ^ 2 ≤ 2 ^ D.R.k := by exact_mod_cast sq_le_two_pow D.R.k (by omega)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ D.R.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num
  rw [sub_le_iff_le_add', ← Real.le_log_iff_exp_le (by linarith), e2]
  rw [div_le_iff₀ hl] at h
  calc (D.R.f : ℝ) * (8 / 2 ^ D.R.k) ≤ D.R.k * (8 / (D.R.k : ℝ) ^ 2) := by gcongr
    _ = 8 / D.R.k := by field_simp
    _ ≤ _ := by rw [div_le_iff₀ (by linarith)]; linarith

theorem form_of_ranks (D : D7) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (u : D.what₂.Word) (h3 : UnitaryVolumeMass.stLem3L0 D u) {C0 : ℝ}
    (hD : StandingNumericalData D C0) : UnitaryVolumeMass.FormAt D u := by
  intro F0 he hz what₂ hrows
  obtain ⟨-, -, -, -, -, -, -, -, hT, -⟩ := hD
  have hp := (D.mem u).A.T_prime
  have h3T : 3 ≤ (D.mem u).A.T := by
    have h1 := (hT u).2
    have h2 : 2 * 2 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le
    have h4 : D.host.g 0 * D.host.g 1 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h5 := hp.two_le
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram D.R.k
  have h1 := (hR _ _ _ hst.1).1 hst.2.1 u
  have h2 := (h3 hp h3T (hT u).1 F0 he hz what₂ hrows).1
  have h4 : dimPi (hc := D.hcW) u = ∏ τ, vand (uS D u τ) / ∏ i ∈ range D.R.k, (i.factorial : ℝ) :=
    prod_congr rfl fun τ _ => (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D u τ)).2
  rw [h1, h2, h4]
  change _ * (Cnt.massU D.host.E D.R.k * (Tr D u ^ D.R.k - 1) ^ D.R.f) * _ =
    Cnt.massU D.host.E D.R.k * _ * _ * _
  ring

theorem tcrit_low_of_dsig (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 40 ≤ Cl) (hT : Ties D) (hb' : Real.sqrt large₂.sc.b ≤ large₂.sc.b')
    (hx : large₂.sc.x ≤ D.R.k) : UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hCL : 1 ≤ Cl * large₂.sc.L := by nlinarith
  have hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := fun τ =>
    Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT hH.1 hCL τ
  exact tcrit_low D large₂ C' Cl Cg cb Cu cT CT C0 hCl hVV hb' hx hH

theorem along_family :
    Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) := by
  intro hDs eps Fm Cg cb Cu cT CT C0 A hCl hR h3
  have hM : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := GlobalTheory.MassAtRecord.massRatio_at_record
  have hform : OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
    obtain ⟨x0, h⟩ := hR
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i hH u => ?_⟩
    have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
    exact form_of_ranks _ (h x ((le_max_left _ _).trans hx) i ⟨hH.2.1, hH.1, hH.2.2⟩) u (h3 x hx1 i u) hH.2.1
  refine ⟨fun x i => ?_, ?_, ?_, hform.mono fun _ _ _ _ h u u' hH => h hH.1 u, ⟨0, fun x _ i _ w τ => ?_⟩, hform⟩
  · intro τ w H _ _ z π hπ
    obtain ⟨g, -, hg⟩ := hπ
    exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).1 H _ hg
  · refine AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 ?_ fun δ hδ => ?_
    · obtain ⟨x0, h0⟩ := hR
      refine ⟨x0, fun x hx i hH => ?_⟩
      have h := h0 x hx i
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg0, -, hg1, -, -, -, -, hv, -⟩ := hH.2.1
      have hk : (5 : ℝ) ≤ (Fm.D x i).R.k := by
        have := (Fm.D x i).R.m_add_three_le_k
        have := (Fm.D x i).R.two_le_m
        exact_mod_cast (by omega : 5 ≤ (Fm.D x i).R.k)
      have hb : 1 ≤ (Fm.L x i).sc.b :=
        Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans (Fm.L x i).sc.one_lt_alt.le) _)
      have h1 : (4 : ℝ) ≤ (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 :=
        le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
      exact ratio_ranks _ (hM _) (h hH) (lt_of_lt_of_le one_pos hv) (by exact_mod_cast h1.trans hg0)
        (by exact_mod_cast h1.trans hg1)
    · refine ⟨max (8 / Real.log (1 + δ)) (Fm.x1 + 1), fun x hx i _ => ?_⟩
      have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
      have h1 := (sizes_low _ (Fm.sizes x hx1 i)).1
      rw [Fm.L_x x i hx1] at h1
      exact err_le _ hδ (((le_max_left _ _).trans hx).trans h1)
  · refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h1 := sizes_low _ (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i)
    exact tcrit_low_of_dsig hDs _ _ _ _ _ _ _ _ _ _ hCl (Fm.ties x i) h1.2 h1.1
  · exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).2

end GlobalTheory.CritLevelGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatios
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PairsPf

theorem massC_nonneg {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : 0 ≤ massC Y u := by
  show 0 ≤ ∑ Λ ∈ Y.what₂ u, wRow D (X.Fu u) Λ
  exact Finset.sum_nonneg fun Λ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem datBd_nonneg (K : Type) [Field K] [NumberField K] [StarRing K] (k r : ℕ) (Del Db NT x : ℝ) (hD : 0 ≤ Del)
    (hDb : 0 ≤ Db) (hN : 0 ≤ NT) (hx : 0 ≤ x) : 0 ≤ GlobalTheory.DegAsm.datBd K k r Del Db NT x := by
  unfold GlobalTheory.DegAsm.datBd
  positivity

theorem termPairBoundFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Ch Cp : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2e large₂ CH Ch Cp j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have h1 : 0 ≤ k2Del D j δ := Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have h2 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := Real.rpow_nonneg hb.le _
  have h3 : 0 ≤ k2S D (H1C large₂ CH) j δ := by
    unfold k2S k2sg
    exact Finset.prod_nonneg fun τ _ => le_trans zero_le_one ((Finset.le_fold_max 1).2 (Or.inl le_rfl))
  unfold k2e
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)) (Real.rpow_nonneg h3 _)
private lemma le_mul_sum_sum_of_ofReal_le_ennreal_sum (s s' : Finset ℕ) (f P : ℕ → ℕ → ℝ) (c L : ℝ) (hf : ∀ x x', 0 ≤ f x x')
    (hP : ∀ x x', 0 ≤ P x x') (hc : 0 ≤ c)
    (h : ENNReal.ofReal L ≤ ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x')) :
    L ≤ c * ∑ x ∈ s, ∑ x' ∈ s', P x x' * f x x' := by
  have hnn : ∀ x x', 0 ≤ f x x' * (c * P x x') := fun x x' => mul_nonneg (hf x x') (mul_nonneg hc (hP x x'))
  have e : ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x') =
      ENNReal.ofReal (∑ x ∈ s, ∑ x' ∈ s', f x x' * (c * P x x')) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [ENNReal.ofReal_mul (hf x x')]
  rw [e] at h
  have h' := (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')).1 h
  refine le_trans h' (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

end PairsPf

open PairsPf in
theorem pair_count_bound_of_siegel_mass : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → PairsP := by
  intro hMM hSR
  unfold PairsP
  intro Cg cb Cw cT CT C0 CH hCH

  obtain ⟨Ca, hCa1, hCaH, hCaT⟩ : ∃ Ca : ℝ, 1 ≤ Ca ∧ 2 * (CH + 1) ≤ Ca ∧ CT ≤ Ca :=
    ⟨max 1 (max (2 * (CH + 1)) CT), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨Ch, Cl', hCh, hsum⟩ := GlobalTheory.DegAsm.sum_pairBd_mul_datBd_le Ca hCa1
  refine ⟨Ch, 16, hCh, by norm_num, 1, max 1 Cl', ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hK2 _
  have hStd : GlobalTheory.TypeAsm.Std D large₂ :=
    show ∃ C' Cl Cg cb Cw cT CT C0 : ℝ, Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 from
      ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK2⟩
  have hHost : HostC := _root_.GlobalTheory.TypeAsm.hostC
  have hfD : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := (hHost D large₂ hStd).2.2.2.2.1
  have hCl1 : 1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hClCl : Cl' ≤ Cl := le_trans (le_max_right _ _) hCl
  obtain ⟨hrk, hm, hClm, hm4, hm5, hClk, hlog, hb2, hv1, hvb, hg, hTu⟩ :=
    _root_.GlobalTheory.TypeAsm.pairsPar Ca Cg cb Cw cT CT C0 C' Cl D large₂ hHost hK2 hC' hCl1 hCaT
  have hlb : 0 ≤ (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hClm' : Cl' ≤ (D.R.m : ℝ) := le_trans hClCl hClm
  have hClk' : Cl' * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k :=
    le_trans (mul_le_mul_of_nonneg_right hClCl hlb) hClk

  have hHb : Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f ≤
      large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E) := by
    show large₂.sc.b ^ (2 * (CH + 1) * (D.R.m : ℝ) ^ 2 * D.R.f) ≤ _
    rw [hfD]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr)
  have hHb0 : 0 ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := Real.rpow_nonneg (by linarith) _
  have hNT : NT D u = ((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E := by
    rw [hfD]
    rfl
  have hNT0 : 0 ≤ NT D u := by
    rw [hNT]
    positivity
  have hk2e : ∀ (j : ℕ) (δ : ℕ → D.host.E), k2e large₂ CH Ch 16 j δ =
      k2Del D j δ ^ ((D.R.k : ℝ) / 2) * (large₂.sc.b ^ (Ch * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E)) ^ (Ch * (D.R.rS : ℝ) ^ 4) *
        k2S D (H1C large₂ CH) j δ ^ (16 * (D.R.k : ℝ)) := by
    intro j δ
    rw [hfD]
    rfl
  unfold PairsAt
  intro j' _ j'' _ δ' δ'' S hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [Finset.sum_empty]
    exact mul_nonneg (massC_nonneg Y u) (mul_nonneg (termPairBoundFactor_nonneg large₂ CH Ch 16 j' δ') (termPairBoundFactor_nonneg large₂ CH Ch 16 j'' δ''))
  obtain ⟨hpp, hj1, hj2, hl1, hl2⟩ := hS p hp
  obtain ⟨hr1, hr2, -⟩ := hpp
  have hF := _root_.GlobalTheory.TypeAsm.PairsLab.norms_of_relevant Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost _root_.GlobalTheory.TypeAsm.nfExC_holds _root_.GlobalTheory.TypeAsm.labC _root_.GlobalTheory.TermRow.termC_holds hK2
  obtain ⟨hD1, hDb1, hDle, hDble⟩ := hF p.1 hr1
  obtain ⟨hD1', hDb1', hDle', hDble'⟩ := hF p.2 hr2
  rw [hj1, hl1] at hD1 hDb1 hDle hDble
  rw [hj2, hl2] at hD1' hDb1' hDle' hDble'
  have hS1 : 1 ≤ k2S D (H1C large₂ CH) j' δ' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))
  have hS1' : 1 ≤ k2S D (H1C large₂ CH) j'' δ'' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))

  have hDA := le_trans hDle (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDA' := le_trans hDle' (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDbA := le_trans hDble (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hDbA' := le_trans hDble' (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hbound := hsum D.host.E D.R.k D.R.rS D.R.m (gS D) (Tu D u) large₂.sc.b (k2Del D j' δ') (k2Del D j'' δ'')
    (DbL D j' δ') (DbL D j'' δ'') (k2S D (H1C large₂ CH) j' δ') (k2S D (H1C large₂ CH) j'' δ'') hrk hm hClm' hm4 hm5 hClk'
    hlog hb2 hv1 hvb hg (hTu u).1 (hTu u).2 hS1 hS1' hD1 hD1' hDb1 hDb1' hDA hDA' hDbA hDbA'

  obtain ⟨W, HW, hemb, hrkW, hPD⟩ := _root_.GlobalTheory.TypeAsm.embC D large₂ X u hStd
  have hI := _root_.GlobalTheory.TypeAsm.PairsSum.pairs_sum_le D large₂ X Y u hStd _root_.GlobalTheory.TypeAsm.CompatPf.compatC _root_.GlobalTheory.TypeAsm.perRowC _root_.GlobalTheory.TypeAsm.rowsMean W HW hemb
    (fun s M x x' => _root_.GlobalTheory.TripInv.trip_encard_smul _ _ HW (gS D) D.R.rS x x' s M)
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x')
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _)
    (fun Λ hΛ x x' hx hx' => _root_.GlobalTheory.PairsRow.main hMM hSR hHost _root_.GlobalTheory.TypeAsm.lat0C D large₂ X Y u hStd W HW hemb hrkW hPD Λ hΛ x x' hx hx')
    j' j'' δ' δ'' S hS
  rw [hNT] at hI
  have hstep := le_mul_sum_sum_of_ofReal_le_ennreal_sum _ _
    (fun x x' => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x *
      GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x')
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') (massC Y u) _
    (fun x x' => mul_nonneg (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _))
      (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _)))
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _) (massC_nonneg Y u) hI
  refine le_trans hstep ?_
  rw [hk2e, hk2e]
  exact mul_le_mul_of_nonneg_left hbound (massC_nonneg Y u)

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingGenusWeightsSumToMass
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.SumK

theorem inGen_symm_of {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    (hE : ∀ p, Equivalence (LocNG.Datum.Rel (P := FP p))) {d y y' : Dat Z FP}
    (h : InGen d y) (h' : InGen d y') : InGen y y' := by
  refine ⟨fun p => (hE p).trans ((hE p).symm (h.1 p)) (h'.1 p), ?_⟩
  apply (h.2.union h'.2).subset
  intro p hp
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hp (by rw [hc.1, hc.2])

theorem weights_add_up_to_mass_of
    (hRelEqv : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), Equivalence (LocNG.Datum.Rel (P := FP p)))
    (hInv : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y') :
    ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d := by
  intro D X Y u u' F F' w hw hG Z FP hB hR TS hTS t₀ Λ₀ y₀ d ht₀ hTG₀ hLO₀ hIG₀ K hK ω hω
  subst hK
  obtain ⟨hEq, -, hRel⟩ := GlobalTheory.T.rationalClass_lattices_iff_rationalClass_localFramePairs D X Y u u' F F' w hw hG Z FP hB hR
  have hQ : ∀ y y' : Dat Z FP, (Quot.mk (GRel (Z := Z) (FP := FP) F F') y) = Quot.mk _ y' ↔ GRel F F' y y' :=
    fun y y' => ⟨fun h => hEq.eqvGen_iff.1 (Quot.eqvGen_exact h), Quot.sound⟩
  have hout : ∀ o : Quot (GRel (Z := Z) (FP := FP) F F'), ∀ y, Quot.mk _ y = o → GRel F F' o.out y := by
    intro o y h
    exact (hQ _ _).1 (by rw [h, Quot.out_eq])

  have hex : ∀ κ : {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ},
      ∃ y : Dat Z FP, ∃ t ∈ TS, ∃ Λ : LV D, TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ.1 := by
    rintro ⟨κ, t, ht, Λ, y, h1, h2, h3, h4⟩
    exact ⟨y, t, ht, Λ, h1, h2, h3, h4⟩
  choose yOf hyOf using hex
  set φ := fun κ => (Quot.mk (GRel (Z := Z) (FP := FP) F F') (yOf κ)) with hφ
  have hwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D) (y y' : Dat Z FP), TG F F' t Λ → TG F F' t' Λ' →
      LocOver Λ y → LocOver Λ' y' → key t = key t' → GRel F F' y y' := fun t t' Λ Λ' y y' h1 h2 h3 h4 h5 =>
    ((hRel Λ Λ' y y' h3 h4).1).1 (_root_.GlobalTheory.KeyRel.same_key_lrel D X Y u u' F F' w hw hG t t' Λ Λ' h1 h2 h5)
  have hImg : ∀ κ, InGen d (φ κ).out := by
    intro κ
    obtain ⟨t, -, Λ, h1, h2, h3, -⟩ := hyOf κ
    exact hInv D X Y u u' F F' w hw hG Z FP hB hR Λ d (yOf κ) _ h2 h3 (hEq.symm (hout _ _ rfl))
  unfold massA
  rw [← ENNReal.tsum_fiberwise _ φ]
  refine tsum_congr fun o => ?_
  by_cases ho : InGen d o.out
  · rw [if_pos ho]
    have hIG01 : InGen y₀ o.out := inGen_symm_of (hRelEqv D Z FP) hIG₀ ho
    obtain ⟨Λ₁, hLO₁, hloc⟩ := _root_.GlobalTheory.Unfold.GlueOrbit.glue_local_orbits D X Y u u' F F' w hw hG Z FP hB hR Λ₀ y₀ o.out hLO₀ hIG01
    obtain ⟨t₁, hTG₁⟩ := _root_.GlobalTheory.RowTermReal.exists_term_of_locOver D X Y u u' F F' w hw hG Z FP hB hR Λ₁ o.out hLO₁
    have ht₁ : t₁ ∈ TS := hTS t₀ t₁ Λ₀ Λ₁ hTG₀ hTG₁ hloc ht₀
    obtain ⟨-, hcarry, hwt, hmass⟩ := _root_.GlobalTheory.OrbitCount.orbit_count D X Y u u' F F' w hw hG t₁ Λ₁ hTG₁ _ rfl
    have hRefl : LRel F F' Λ₁ Λ₁ := ((hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).1).2 (hEq.refl _)
    have hStab : stabL F F' Λ₁ = stabY F F' o.out := (hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).2

    have hfib : Subtype.val '' (φ ⁻¹' {o}) =
        {κ | ∃ (t : TauC Y u u') (Λ' : LV D), TG F F' t Λ' ∧ LRel F F' Λ₁ Λ' ∧ key t = κ} := by
      ext κ
      constructor
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨t, -, Λ, h1, h2, -, h4⟩ := hyOf b
        have hb' : φ b = o := hb
        refine ⟨t, Λ, h1, ((hRel Λ₁ Λ o.out (yOf b) hLO₁ h2).1).2 (hout o _ hb'), h4⟩
      · rintro hκ
        obtain ⟨t, hTG, hkey⟩ := hcarry κ hκ
        have htS : t ∈ TS := hTS t₁ t Λ₁ Λ₁ hTG₁ hTG
          (fun p => ⟨1, Subgroup.one_mem _, by
            simp [LocNG.img]⟩) ht₁
        have hmem : κ ∈ {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} :=
          ⟨t, htS, Λ₁, o.out, hTG, hLO₁, ho, hkey⟩
        refine ⟨⟨κ, hmem⟩, ?_, rfl⟩
        show φ ⟨κ, hmem⟩ = o
        obtain ⟨t', -, Λ', h1, h2, -, h4⟩ := hyOf ⟨κ, hmem⟩
        rw [hφ]
        simp only
        rw [← Quot.out_eq o]
        exact Quot.sound (hwd t' t Λ' Λ₁ _ _ h1 hTG h2 hLO₁ (h4.trans hkey.symm))
    have hconst : ∀ b : φ ⁻¹' {o}, ENNReal.ofReal (ω b.1) = ENNReal.ofReal (wt t₁ ^ 2) := by
      intro b
      have hb : b.1.1 ∈ Subtype.val '' (φ ⁻¹' {o}) := ⟨b.1, b.2, rfl⟩
      rw [hfib] at hb
      obtain ⟨t, hTG, hkey⟩ := hcarry _ hb
      rw [hω b.1 t hkey, hwt t Λ₁ hTG hRefl]
    rw [tsum_congr hconst, ENNReal.tsum_set_const, ← Subtype.val_injective.encard_image, hfib, hmass, hStab]
  · rw [if_neg ho]
    refine ENNReal.tsum_eq_zero.2 fun b => (ho ?_).elim
    have hb : φ b.1 = o := b.2
    rw [← hb]
    exact hImg b.1

theorem weights_add_up_to_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d :=
  weights_add_up_to_mass_of GlobalTheory.T.equivalence_complementUnitaryOrbit_localInnerDatum_at_place _root_.GlobalTheory.GenusStab.inGen_of_gRel

end GlobalTheory.Unfold.SumK
end

