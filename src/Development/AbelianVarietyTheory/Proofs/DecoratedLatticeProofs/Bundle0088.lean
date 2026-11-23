module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBound
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory.CritLevelSize

open Formalism.FourierDecayAlt Finset GlobalTheory.CritLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem num_bound_pow (k m r e : ℕ) (B P ae c ka : ℝ) (hm : m = 2 * r + 2) (he : 2 * e + 40 ≤ m) (hk : 5 ≤ k)
    (hB : (k : ℝ) ^ 40 ≤ B) (hP : B ^ m ≤ P) (ha0 : 0 < ae) (ha : ae ≤ B ^ e) (hc : 1 / 8 ≤ c) (hka0 : 0 < ka)
    (hka : ka ≤ 4) : (k : ℝ) ^ (3 * r) ≤ c * (ka ^ (m - 1))⁻¹ * P / ae := by
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have h1 : ka ^ (m - 1) ≤ (k : ℝ) ^ (m - 1) := pow_le_pow_left₀ hka0.le (by linarith) _
  have h2 : (8 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h3 : (k : ℝ) ^ (3 * r) * (k : ℝ) ^ (m - 1) * (k : ℝ) ^ 2 ≤ B ^ (m - e) := by
    rw [← pow_add, ← pow_add]
    calc (k : ℝ) ^ (3 * r + (m - 1) + 2) ≤ (k : ℝ) ^ (40 * (m - e)) := pow_le_pow_right₀ (by linarith) (by omega)
      _ = ((k : ℝ) ^ 40) ^ (m - e) := pow_mul _ _ _
      _ ≤ B ^ (m - e) := pow_le_pow_left₀ (by positivity) hB _
  have h4 : B ^ (m - e) * B ^ e = B ^ m := by rw [← pow_add]; congr 1; omega
  have h5 : (k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae ≤ P :=
    calc (k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae
        ≤ (k : ℝ) ^ (3 * r) * (k : ℝ) ^ (m - 1) * (k : ℝ) ^ 2 * B ^ e := by gcongr
      _ ≤ B ^ (m - e) * B ^ e := by gcongr
      _ ≤ P := h4 ▸ hP
  rw [le_div_iff₀ ha0]
  calc (k : ℝ) ^ (3 * r) * ae = 1 / 8 * (ka ^ (m - 1))⁻¹ * ((k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae) := by
        field_simp
    _ ≤ c * (ka ^ (m - 1))⁻¹ * P := by
        gcongr

theorem le_pow_ceil (b B u cb Cu : ℝ) (hcb : 0 < cb) (hb : 1 ≤ b) (hB : b ^ cb ≤ B) (hu : u ≤ b ^ Cu) :
    u ≤ B ^ ⌈max Cu 0 / cb⌉₊ := by
  have hB1 : 1 ≤ B := le_trans (Real.one_le_rpow hb hcb.le) hB
  have hM : 0 ≤ max Cu 0 / cb := div_nonneg (le_max_right _ _) hcb.le
  calc u ≤ b ^ Cu := hu
    _ ≤ b ^ max Cu 0 := Real.rpow_le_rpow_of_exponent_le hb (le_max_left _ _)
    _ = (b ^ cb) ^ (max Cu 0 / cb) := by
        rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp
    _ ≤ B ^ (max Cu 0 / cb) := Real.rpow_le_rpow (by positivity) hB hM
    _ ≤ B ^ ((⌈max Cu 0 / cb⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (Nat.le_ceil _)
    _ = B ^ ⌈max Cu 0 / cb⌉₊ := Real.rpow_natCast _ _


set_option maxHeartbeats 1600000 in
theorem tcrit_low_of_sizes (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hcb : 0 < cb)
    (hCl : 2 * ((⌈max Cu 0 / cb⌉₊ + 4 : ℕ) : ℝ) + 40 ≤ Cl)
    (hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) :
    UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  rintro ⟨hH, hD, -⟩ u τ
  obtain ⟨-, -, -, -, -, -, hmL, hbD, -, -, -, hg0, -, hg1, -, hbj, -, hu, hv, hDel, hgap, -, -, hClm, -⟩ := hH
  obtain ⟨hvw, -, ha, ha', hl, htop, -⟩ := hD
  set e : ℕ := ⌈max Cu 0 / cb⌉₊ + 4 with he
  have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
  have hCl40 : (40 : ℝ) ≤ Cl := by linarith
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm := GlobalTheory.CritLevel.m_eq D.R
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hmR : (40 : ℝ) ≤ D.R.m := hCl40.trans hClm
  have hme : 2 * e + 40 ≤ D.R.m := by
    have : ((2 * e + 40 : ℕ) : ℝ) ≤ D.R.m := by push_cast; linarith
    exact_mod_cast this
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (by omega) D.R.m_le_f
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  have hlog : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hD1 : (1 : ℝ) ≤ D.s.Del :=
    le_trans (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hf) hL)
      (by linarith)) hDel
  set B := bOne D τ 1 with hBdef
  have hB : (D.R.k : ℝ) ^ 40 ≤ B := by
    refine le_trans ?_ ((le_max_left _ _).trans (hbj τ 1 le_rfl (by omega)).1)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hCl40)
  have hBcb : large₂.sc.b ^ cb ≤ B := (le_max_right _ _).trans (hbj τ 1 le_rfl (by omega)).1
  have hk2 : 3 * (D.R.k : ℝ) ≤ B := by
    refine le_trans ?_ hB
    calc 3 * (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hB1 : 1 ≤ B := by linarith
  have hkD : 0 < (D.R.k : ℝ) * D.s.Del := by positivity
  have hBD : 40 * (D.R.m * D.R.k * D.s.Del) ≤ B :=
    le_trans (mul_le_mul_of_nonneg_right hCl40 (by positivity)) (hbD τ 1 le_rfl (by omega))
  have hBD' : 8 * ((D.R.k : ℝ) * D.s.Del) ≤ B := by nlinarith
  have hg : ∀ j, 1 ≤ j → j < D.R.m → bOne D τ j + 1 ≤ bOne D τ (j + 1) := fun j h1 h2 => by
    have h3 := hgap τ j h1 h2
    have h4 : (1 : ℝ) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hn)) (one_le_pow₀ hf)) hL
    linarith
  have hmono : ∀ j, 1 ≤ j → j ≤ D.R.m → B ≤ bOne D τ j := by
    intro j h1
    induction j, h1 using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j h1 ih => intro h2; linarith [ih (by omega), hg j h1 h2]
  set c := GlobalTheory.CritLevel.cfg D u τ with hc
  have hv1 : c.v 1 = vOne D τ 1 := GlobalTheory.CritLevel.cfg_v D u τ le_rfl (by omega)
  have htp : c.top = true ↔ IsTop D τ := by simp [hc, GlobalTheory.CritLevel.cfg]
  have hOk : c.Ok := by
    refine ⟨show 4 ≤ D.R.k by omega, hm2, hD1, (hvw τ _ (by omega) le_rfl).1, ?_, hB1, hg, ?_, fun h => ?_⟩
    · rw [hv1]; exact (hvw τ 1 le_rfl (by omega)).2
    · rw [hv1]; exact ha u τ
    · have := htop τ (htp.1 h)
      exact ⟨this.2, show bTop D τ ≤ B - 3 by linarith [this.1]⟩
  have hSm : c.Small large₂.sc.b := by
    refine ⟨hb, ?_, fun j h1 h2 => ?_, ?_⟩
    · show 4 * (D.R.m : ℝ) * D.R.k * D.s.Del / B ≤ 1 / 10
      rw [div_le_iff₀ (by linarith)]
      linarith
    · have := (hbj τ j h1 h2).2
      rwa [Real.rpow_two] at this
    · show 2 * (D.R.m : ℝ) * Real.log large₂.sc.b / D.R.k ≤ 1 / 10
      rw [hlog, div_le_iff₀ (by linarith)]
      have h1 : (D.R.m : ℝ) * large₂.sc.L ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := by gcongr; nlinarith
      have h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) := by gcongr
      have h3 : 0 ≤ (D.R.m : ℝ) * large₂.sc.L := by positivity
      linarith
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 2 * Real.pi ≤ gg D := by
    have h1 : (5 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
      le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
    unfold gg
    nlinarith
  have hV : 0 < VV D τ := mul_pos (D.dsig_pos τ) (prod_pos fun i _ => by positivity)
  have hlow := Final.sz_tcritLower c D.R.rS large₂.sc.b (GlobalTheory.CritLevel.letters D u) D.host.ka D.host.rdE (gg D) (VV D τ) hOk hm hSm
    (GlobalTheory.CritLevel.isWord_letters D u) (by linarith) (by rw [hrd]; unfold Host.ka; field_simp) hgg (by
      show (1 - 1 / 2) * Sz.Vand (D.R.k + D.R.m - 1) c.lam ≤ _
      rw [← GlobalTheory.CritLevel.cfg_lam D u τ, ← hVV]
      linarith)
  change _ * gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * _ / _ ≤
    Sz.Tcrit D.R.k D.R.m _ _ _ _ (Sz.Vand D.R.k _) at hlow
  rw [← GlobalTheory.CritLevel.cfg_u D u τ (hl u τ), ← GlobalTheory.CritLevel.tcrit_eq D (by linarith)] at hlow
  have hg0' : 0 < gg D := by linarith
  have hvone := (hvw τ 1 le_rfl (by omega)).1
  have hBe : B ≤ B ^ e := le_self_pow₀ hB1 (by omega)
  have hae : 0 < c.aeff ∧ c.aeff ≤ B ^ e ∧ 0 ≤ c.vthp ∧ c.vthp ≤ 1 := by
    unfold Sz.Cfg.aeff Sz.Cfg.vthp
    by_cases ht : IsTop D τ
    · rw [if_pos (htp.2 ht), if_pos (htp.2 ht)]
      obtain ⟨t1, t2⟩ := htop τ ht
      have ha0 : 0 < uOne D u τ 1 := by linarith [ha u τ]
      have hbp : 0 < bTop D τ := by linarith
      have hu1 : uOne D u τ 1 ≤ B ^ ⌈max Cu 0 / cb⌉₊ := le_pow_ceil _ _ _ _ _ hcb hb hBcb (hu u τ)
      have hpe : B ^ ⌈max Cu 0 / cb⌉₊ * B ≤ B ^ e := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hB1 (by omega)
      refine ⟨div_pos (mul_pos ha0 hbp) hkD, ?_, ?_, ?_⟩
      · show uOne D u τ 1 * bTop D τ / ((D.R.k : ℝ) * D.s.Del) ≤ B ^ e
        refine (div_le_self (by positivity) (by nlinarith)).trans ?_
        calc uOne D u τ 1 * bTop D τ ≤ B ^ ⌈max Cu 0 / cb⌉₊ * B := by gcongr; linarith
          _ ≤ B ^ e := hpe
      · show 0 ≤ 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ
        positivity
      · show 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ ≤ 1
        rw [div_le_one hbp]
        linarith
    · rw [if_neg (fun h => ht (htp.1 h)), if_neg (fun h => ht (htp.1 h)), hv1]
      have h1 := ha u τ
      have h2 := ha' u τ ht
      refine ⟨?_, ?_, le_rfl, zero_le_one⟩
      · show 0 < uOne D u τ 1 - vOne D τ 1
        linarith
      · show uOne D u τ 1 - vOne D τ 1 ≤ B ^ e
        linarith
  have hc1 : 1 / 8 ≤ Sz.cOne c large₂.sc.b := by
    unfold Sz.cOne
    have h1 := Real.add_one_le_exp (-(2 * c.m * Real.log large₂.sc.b / c.k))
    have h2 := hSm.hmu
    rw [le_div_iff₀ (by linarith [hae.2.2.1])]
    linarith [hae.2.2.2]
  have hP : B ^ D.R.m ≤ c.prodb := by
    have := prod_le_prod₀ (s := Icc 1 D.R.m) (f := fun _ => B) (g := bOne D τ) (fun _ _ => by linarith)
      fun j hj => hmono j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2
    rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel] at this
    exact this
  have hka0 : 0 < D.host.ka := div_pos hpi (by linarith)
  have hka : D.host.ka ≤ 4 := (div_le_self hpi.le hv).trans hpi4
  have hnum := num_bound_pow D.R.k D.R.m D.R.rS e B c.prodb c.aeff _ _ hm hme (by omega) hB hP
    hae.1 hae.2.1 hc1 hka0 hka
  rw [Real.rpow_neg hg0'.le, Real.rpow_natCast, le_inv_mul_iff₀ (by positivity)]
  refine le_trans ?_ hlow
  calc gg D ^ D.R.m * (D.R.k : ℝ) ^ (3 * D.R.rS)
      ≤ gg D ^ D.R.m * (Sz.cOne c large₂.sc.b * (D.host.ka ^ (D.R.m - 1))⁻¹ * c.prodb / c.aeff) := by gcongr
    _ = _ := by ring

end GlobalTheory.CritLevelSize

theorem GlobalTheory.CritLevelSize.tcritLow_sizes : ∀ cb Cu : ℝ, 0 < cb → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cT CT C0 : ℝ), thr ≤ Cl → (∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) → UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro cb Cu hcb
  exact ⟨2 * ((⌈max Cu 0 / cb⌉₊ + 4 : ℕ) : ℝ) + 40, fun D large₂ C' Cl Cg cT CT C0 hCl hVV =>
    GlobalTheory.CritLevelSize.tcrit_low_of_sizes D large₂ C' Cl Cg cb Cu cT CT C0 hcb hCl hVV⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormCmExtensionSplitPlaceEqZpow
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.Doubling.AbsSplit

theorem norm_eq_zpow {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a : Fv F v} (ha : a ≠ 0) :
    ‖a‖ = (qV F v : ℝ) ^ (-ordL a) := by
  have h0 : Valued.v a ≠ 0 := (map_ne_zero _).2 ha
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0, ordL, dite_eq_right h0, neg_neg]
  simp [qV, WithZero.toAdd_unzero_eq_log h0]

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {x : L} {y : L'} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

theorem absEv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV E w : ℝ) ^ (-(ordL (toCompl h x.1) + ordL (toCompl h' x.1))) := by
  intro F E _ _ _ _ _ σ hE v w h w' h' hne x
  obtain ⟨τ, hτ, -⟩ := existsUnique_splitPrime_eq hE hne h h'
  obtain ⟨τ', hτ', -⟩ := existsUnique_splitPrime_eq hE hne.symm h' h
  obtain rfl : τ' = τ.comp σ := (eq_or_eq_comp_conj hE τ τ').resolve_left fun e => hne (hτ.symm.trans (e ▸ hτ'))
  have hN : Algebra.norm (Fv F v) x.1 = splitProj τ x.1 * splitProj (τ.comp σ) x.1 := by
    have := congrArg (splitProj τ) (algebraMap_norm_eq hE x.1)
    rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
    exact this
  have hq : qV E w = qV F v := hτ ▸ GlobalTheory.LFun.SplitTie.qV_splitPrime τ
  have e1 : ordL (toCompl h x.1) = ordL (splitProj τ x.1) := ordL_congr (by
    rw [GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, GlobalTheory.LFun.ConjPlace.valued_complMap hE h hτ])
  have e2 : ordL (toCompl h' x.1) = ordL (splitProj (τ.comp σ) x.1) := ordL_congr (by
    rw [GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ', GlobalTheory.LFun.ConjPlace.valued_complMap hE h' hτ'])
  have hq0 : (qV F v : ℝ) ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    unfold qV
    exact_mod_cast (by omega)
  rw [absEv_apply, coe_nnnorm, hN, norm_mul, hq, e1, e2, neg_add, zpow_add₀ hq0,
    norm_eq_zpow v (x.isUnit.map (splitProj τ)).ne_zero, norm_eq_zpow v (x.isUnit.map (splitProj (τ.comp σ))).ne_zero]

end GlobalTheory.Doubling.AbsSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpan
section
open Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.TenInj

noncomputable def tenMap {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) :
    (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × Fin n × Fin n) ℂ)).compLinearMap
    (fun τ => (MvPolynomial.rename (Prod.mk τ)).toLinearMap ∘ₗ j τ))

theorem tenMap_tprod {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (x : ∀ τ, V τ) :
    tenMap j (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  unfold tenMap ten
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rfl

theorem nfAll_zero_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam 0 q = 0 := by
  have h := GlobalTheory.TenTypes.nfAll_smul_left lam 0 0 q
  simpa using h

theorem main : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ι → ℕ) (b : ∀ τ, Module.Basis (Fin (d τ)) ℂ (V τ)), (∀ τ ξ, j τ ξ ∈ delSq ℂ n (lam τ)) → (∀ τ, ∀ p ∈ delSq ℂ n (lam τ), ∃ ξ, j τ ξ = p) → (∀ τ a a', normFock (lam τ) (j τ (b τ a)) (j τ (b τ a')) = if a = a' then 1 else 0) → ∃ Jt : (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, Function.Injective Jt ∧ LinearMap.range Jt = CSpan lam ∧ ∀ x : (∀ τ, V τ), Jt (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  intro ι _ n lam V _ _ j d b hin hon hortho
  refine ⟨tenMap j, ?_, ?_, tenMap_tprod j⟩
  ·
    let B := Basis.piTensorProduct b
    have hB : ∀ i, B i = PiTensorProduct.tprod ℂ (fun τ => b τ (i τ)) := fun i => Basis.piTensorProduct_apply b i
    obtain ⟨hprod, -, -⟩ := GlobalTheory.FockTen.nfAll_ten ι n lam
    have hpair : ∀ i i', nfAll lam (tenMap j (B i)) (tenMap j (B i')) = if i = i' then 1 else 0 := by
      intro i i'
      rw [hB, hB, tenMap_tprod, tenMap_tprod, hprod]
      simp_rw [hortho]
      by_cases h : i = i'
      · subst h; simp
      · rw [if_neg h]
        obtain ⟨τ, hτ⟩ : ∃ τ, i τ ≠ i' τ := by
          by_contra hc; push_neg at hc; exact h (funext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)
    have hcoord : ∀ i' x, nfAll lam (tenMap j x) (tenMap j (B i')) = B.coord i' x := by
      intro i'
      let L : (⨂[ℂ] τ, V τ) →ₗ[ℂ] ℂ :=
        { toFun := fun x => nfAll lam (tenMap j x) (tenMap j (B i'))
          map_add' := fun x y => by rw [map_add (f := _), GlobalTheory.TenTypes.nfAll_add_left]
          map_smul' := fun c x => by rw [map_smul, GlobalTheory.TenTypes.nfAll_smul_left]; rfl }
      have hL : L = B.coord i' := by
        refine B.ext fun i => ?_
        show nfAll lam (tenMap j (B i)) (tenMap j (B i')) = B.coord i' (B i)
        rw [hpair, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      intro x
      exact LinearMap.congr_fun hL x
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine B.ext_elem fun i' => ?_
    rw [map_zero, Finsupp.zero_apply, ← Module.Basis.coord_apply, ← hcoord, hx, nfAll_zero_left]
  ·
    rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    unfold CSpan
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨fun τ => j τ (x τ), fun τ => hin τ _, tenMap_tprod j x⟩
    · rintro ⟨f, hf, rfl⟩
      choose ξ hξ using fun τ => hon τ (f τ) (hf τ)
      refine ⟨PiTensorProduct.tprod ℂ ξ, ⟨ξ, rfl⟩, ?_⟩
      rw [tenMap_tprod]
      congr 1
      funext τ
      exact hξ τ

end GlobalTheory.TenInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupConjugateTransposeMatrixStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_group_conjugate_transpose_matrix : ∀ (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsFrame β I.L → ∃ G : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), ((Formalism.UG.bc (Formalism.L2.Herm.intAf I.F I.E).subtype G : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  first | exact @GlobalTheory.GramFrame.gram_frame_int | exact GlobalTheory.GramFrame.gram_frame_int | (intros; apply GlobalTheory.GramFrame.gram_frame_int <;> assumption)
end

