module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0412
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0030
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpan
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMean
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelPrimesSizeBoundsColumnDimension
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem levelPrime_size : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → C0 * Real.exp 8 ≤ D.R.k → LocalBesselAndTopKernel.FamilyMidVolume D → ∀ u, large₂.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m : ℝ)) := by
  intro hS hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl hCu hC0 hR u
  obtain ⟨hF, hA, -, hk⟩ := pgFrame_at_record hS hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl hCu hC0 hR
  have hcrit := _root_.GlobalTheory.CritLevelUpper.tcrit_le_pow hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl
  obtain ⟨hS0, hData, hC01⟩ := hH
  dsimp only [StandingHypotheses] at hS0
  obtain ⟨-, -, hm4, hfk, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, hv, -, -, -, -, hClm, -⟩ := hS0
  have hwin := (hData.2.2.2.2.2.2.2.2.2.1 u).2

  have hLpos : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hb : 1 < large₂.sc.b := by
    have := Real.add_one_le_exp large₂.sc.L
    show 1 < Real.exp large₂.sc.L
    linarith
  have hbpos : 0 < large₂.sc.b := by linarith
  have hm40 : (40:ℝ) ≤ D.R.m := le_trans hCl hClm
  have hmk : ((D.R.m + 3 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  push_cast at hmk
  have hk40 : (40:ℝ) ≤ D.R.k := by linarith
  have hkpos : (0:ℝ) < D.R.k := by linarith
  have hfpos : (0:ℝ) < D.R.f := by
    have h1 : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_trans h1 hm4)
  have hfk' : (D.R.f:ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hrS : 2 * D.R.rS + 2 = D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    omega

  have hkb : 0 < (D.R.k:ℝ) * large₂.sc.b := mul_pos hkpos hbpos
  have hgg : ((D.R.k:ℝ) * large₂.sc.b) ^ 16 ≤ gg D := by
    show _ ≤ (D.host.g 0 : ℝ) * D.host.g 1
    have h0 : 0 ≤ ((D.R.k:ℝ) * large₂.sc.b) ^ 8 := (pow_pos hkb 8).le
    calc ((D.R.k:ℝ) * large₂.sc.b) ^ 16 = ((D.R.k:ℝ) * large₂.sc.b) ^ 8 * ((D.R.k:ℝ) * large₂.sc.b) ^ 8 := by ring
      _ ≤ _ := mul_le_mul hg1 hg2 h0 (le_trans h0 hg1)
  have hggpos : 0 < gg D := lt_of_lt_of_le (pow_pos hkb 16) hgg

  have hka_pos : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
  have hka_le : D.host.ka ≤ 4 := by
    show Real.pi / D.host.v ≤ 4
    rw [div_le_iff₀ (by linarith)]
    linarith [Real.pi_le_four]
  have hK_pos : 0 < Bridge.kaS D := div_pos hka_pos hggpos
  have hK : Bridge.kaS D * large₂.sc.b ^ 16 ≤ 1 := by
    show D.host.ka / gg D * large₂.sc.b ^ 16 ≤ 1
    rw [div_mul_eq_mul_div, div_le_one hggpos]
    have hk16 : (D.R.k:ℝ) ≤ (D.R.k:ℝ) ^ 16 := le_self_pow₀ (by linarith) (by norm_num)
    have hb16 : 0 ≤ large₂.sc.b ^ 16 := (pow_pos hbpos 16).le
    calc D.host.ka * large₂.sc.b ^ 16 ≤ 4 * large₂.sc.b ^ 16 := mul_le_mul_of_nonneg_right hka_le hb16
      _ ≤ (D.R.k:ℝ) ^ 16 * large₂.sc.b ^ 16 := mul_le_mul_of_nonneg_right (by linarith) hb16
      _ = ((D.R.k:ℝ) * large₂.sc.b) ^ 16 := by ring
      _ ≤ gg D := hgg
  unfold Formalism.L2.SG.RowsConc.TFrameAt at hF
  have hT0 : 0 ≤ Tr D u := Nat.cast_nonneg _
  have hlow : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ Tr D u := by
    have h1 := hF u
    have h2 : (Bridge.kaS D * large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ 1 :=
      pow_le_one₀ (mul_pos hK_pos (pow_pos hbpos 16)).le hK
    rw [mul_pow] at h2
    have hP : 0 ≤ (large₂.sc.b ^ 16) ^ (2 * D.R.rS) := (pow_pos (pow_pos hbpos 16) _).le
    have e : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) * (Tr D u * Bridge.kaS D ^ (2 * D.R.rS)) =
        Tr D u * (Bridge.kaS D ^ (2 * D.R.rS) * (large₂.sc.b ^ 16) ^ (2 * D.R.rS)) := by ring
    linarith [mul_le_mul_of_nonneg_left h1 hP, mul_le_mul_of_nonneg_left h2 hT0]
  refine ⟨le_trans ?_ hlow, ?_⟩
  · rw [← pow_mul, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb.le
    have : ((2 * D.R.rS + 2 : ℕ) : ℝ) = D.R.m := by exact_mod_cast hrS
    push_cast at this ⊢
    linarith
  ·
    by_contra hup
    push Not at hup
    have hbm : 0 < large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := Real.rpow_pos_of_pos hbpos _
    have hTpos : 0 < Tr D u := lt_trans hbm hup
    obtain ⟨q, hq⟩ : ∃ q, q = large₂.sc.b ^ (-(D.R.m:ℝ)) := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := by rw [hq]; exact (Real.rpow_pos_of_pos hbpos _).le
    have hq1 : q ≤ 1 := by
      rw [hq]; exact (Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)).le
    have hq_eq : large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m:ℝ)) = q * large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := by
      rw [hq, ← Real.rpow_add hbpos]; congr 1; ring
    have hgg0 : 0 ≤ gg D := hggpos.le
    have hTc_pos : ∀ τ, 0 < Tcrit D u τ := by
      intro τ
      have h := hk u τ
      have h1 : (0:ℝ) < (D.R.k:ℝ) ^ (3 * D.R.rS) := pow_pos hkpos _
      by_contra hc
      push Not at hc
      have : gg D ^ (-(D.R.m:ℝ)) * Tcrit D u τ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hgg0 _) hc
      linarith
    have hxpos : ∀ τ, 0 < Tcrit D u τ / Tr D u := fun τ => div_pos (hTc_pos τ) hTpos
    have hx : ∀ τ, Tcrit D u τ / Tr D u ≤ q := by
      intro τ
      rw [div_le_iff₀ hTpos]
      calc Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m:ℝ)) := hcrit u τ
        _ = q * large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := hq_eq
        _ ≤ q * Tr D u := mul_le_mul_of_nonneg_left hup.le hq0
    have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
    obtain ⟨τ0⟩ := hTau
    classical
    have hprod : ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k ≤ q ^ D.R.k := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ0)]
      have hrest : ∏ τ ∈ Finset.univ.erase τ0, (Tcrit D u τ / Tr D u) ^ D.R.k ≤ 1 :=
        Finset.prod_le_one₀ (fun τ _ => pow_nonneg (hxpos τ).le _)
          (fun τ _ => pow_le_one₀ (hxpos τ).le (le_trans (hx τ) hq1))
      calc (Tcrit D u τ0 / Tr D u) ^ D.R.k * ∏ τ ∈ Finset.univ.erase τ0, (Tcrit D u τ / Tr D u) ^ D.R.k
          ≤ (Tcrit D u τ0 / Tr D u) ^ D.R.k * 1 :=
            mul_le_mul_of_nonneg_left hrest (pow_nonneg (hxpos τ0).le _)
        _ ≤ q ^ D.R.k := by rw [mul_one]; exact pow_le_pow_left₀ (hxpos τ0).le (hx τ0) _
    have hP0 : 0 < ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k :=
      Finset.prod_pos (fun τ _ => pow_pos (hxpos τ) _)
    unfold UnitaryVolumeMass.cTvA at hA
    obtain ⟨hlo, hhi⟩ := hA u
    have hQ : 0 < D.what₂.Dstar / (D.duS u : ℝ) := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hP0) hlo
    have hd : 0 < (D.duS u : ℝ) := by
      rcases (Nat.cast_nonneg (D.duS u) : (0:ℝ) ≤ _).eq_or_lt with h | h
      · rw [← h, div_zero] at hQ
        exact absurd hQ (lt_irrefl 0)
      · exact h
    have hDs : 0 < D.what₂.Dstar := by
      have := mul_pos hQ hd
      rwa [div_mul_cancel₀ _ hd.ne'] at this
    have hC0pos : 0 < C0 := by linarith

    have hlogG : 0 < Real.log (D.mem u).A.GamP := by
      rw [large₂.Gam_eq u]
      have hL0 : 0 < large₂.sc.L := by linarith
      have hm0 : (0:ℝ) < D.R.m := by linarith
      exact mul_pos (mul_pos (mul_pos large₂.CGam_pos (pow_pos hm0 5)) hfpos) hL0
    have hG0 : (D.mem u).A.GamP ≠ 0 := by
      intro h
      rw [h, Real.log_zero] at hlogG
      exact lt_irrefl 0 hlogG
    have hGabs : 1 < |(D.mem u).A.GamP| := by
      rw [← Real.exp_log_eq_abs hG0]
      have := Real.add_one_le_exp (Real.log (D.mem u).A.GamP)
      linarith
    have hGz : (D.mem u).A.GamP ^ (-2:ℤ) ≤ 1 := by
      rw [zpow_neg, zpow_two]
      apply inv_le_one_of_one_le₀
      rw [← abs_mul_abs_self (D.mem u).A.GamP]
      exact (one_lt_mul_of_lt_of_le hGabs hGabs.le).le
    have hwin' : (D.duS u : ℝ) ≤ 1 * D.what₂.Dstar * C0 :=
      le_trans hwin (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGz hDs.le) hC0pos.le)
    have hinv : 1 / C0 ≤ D.what₂.Dstar / (D.duS u : ℝ) :=
      (div_le_div_iff₀ hC0pos hd).mpr (by linarith)

    have h2pow : (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ 8 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith : (3:ℝ) - D.R.k ≤ 3)
      have h8 : (2:ℝ) ^ (3:ℝ) = 8 := by
        rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      linarith
    have hexp1 : (D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ 8 * D.R.k := by
      calc (D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ (D.R.f:ℝ) * 8 := mul_le_mul_of_nonneg_left h2pow hfpos.le
        _ ≤ 8 * D.R.k := by linarith
    have hqk : q ^ D.R.k = Real.exp (-((D.R.k:ℝ) * large₂.sc.L * D.R.m)) := by
      rw [hq, show large₂.sc.b = Real.exp large₂.sc.L from rfl, ← Real.exp_mul, ← Real.exp_nat_mul]
      congr 1
      ring
    have hLm : (40:ℝ) * D.R.k ≤ (D.R.k:ℝ) * large₂.sc.L * D.R.m := by
      have h40 : (1:ℝ) * 40 ≤ large₂.sc.L * D.R.m := mul_le_mul hLpos.le hm40 (by norm_num) (by linarith)
      rw [mul_assoc]
      linarith [mul_le_mul_of_nonneg_left h40 hkpos.le]
    have hmain : 1 / C0 ≤ Real.exp (-(32 * (D.R.k:ℝ))) := by
      calc 1 / C0 ≤ D.what₂.Dstar / (D.duS u : ℝ) := hinv
        _ ≤ Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k)) * ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k := hhi
        _ ≤ Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k)) * q ^ D.R.k :=
            mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
        _ = Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) - (D.R.k:ℝ) * large₂.sc.L * D.R.m) := by
            rw [hqk, ← Real.exp_add]
            ring_nf
        _ ≤ Real.exp (-(32 * (D.R.k:ℝ))) := Real.exp_le_exp.mpr (by linarith)
    have hC0k : C0 ≤ D.R.k := by
      have h8 := Real.add_one_le_exp 8
      calc C0 = C0 * 1 := (mul_one C0).symm
        _ ≤ C0 * Real.exp 8 := mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
        _ ≤ D.R.k := hC0
    have hkexp : (D.R.k:ℝ) + 1 ≤ Real.exp D.R.k := Real.add_one_le_exp _
    have h31 : Real.exp (-(31 * (D.R.k:ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hsplit : Real.exp (D.R.k:ℝ) * Real.exp (-(32 * (D.R.k:ℝ))) = Real.exp (-(31 * (D.R.k:ℝ))) := by
      rw [← Real.exp_add]
      ring_nf
    have he32 : 0 < Real.exp (-(32 * (D.R.k:ℝ))) := Real.exp_pos _
    have h1C : 1 ≤ C0 * Real.exp (-(32 * (D.R.k:ℝ))) := by
      rw [div_le_iff₀ hC0pos] at hmain
      linarith
    have e : ((D.R.k:ℝ) + 1) * Real.exp (-(32 * (D.R.k:ℝ))) =
        (D.R.k:ℝ) * Real.exp (-(32 * (D.R.k:ℝ))) + Real.exp (-(32 * (D.R.k:ℝ))) := by ring
    linarith [mul_le_mul_of_nonneg_right hC0k he32.le, mul_le_mul_of_nonneg_right hkexp he32.le]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusLocalDataProductLocalWeights
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HL

namespace GlobalTheory.Unfold

private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)

theorem mass_genus_local_weights : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ d0 : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ V1 : ℝ, 0 < V1 ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → {p | d p ≠ d0 p}.Finite → massA F F' d = ENNReal.ofReal (V1 * ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR d0 hd0 hΛ
  obtain ⟨φ, hφi, hφE⟩ := _root_.GlobalTheory.PhiEmbed.phi_embed D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨Λ₀, hLO⟩ := _root_.GlobalTheory.Unfold.GlueOver.exists_locOver D Z FP d0 hd0 hΛ
  have hrk : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    have hm : D.R.m = 2 * D.R.rS + 2 := by
      have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
    rw [finrank_Vp]; unfold Ranks.r; omega
  have hact : ∀ p : PlF D, ∃ act : MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : ↥(FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d :=
    fun p => _root_.GlobalTheory.InnerDatumAct.exists_mulAction (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (hrk p) (hR p)
  choose act hMv hSt using hact
  letI : ∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)) := act
  have hMv' : ∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d' := hMv
  have hSt' : ∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d := hSt
  obtain ⟨hc0, hfin, hdd⟩ := _root_.GlobalTheory.Unfold.LocStab.local_stabilisers D X Y u u' F F' w hw hG Z FP hB hR hMv' hSt' Λ₀ d0 hLO
  have hlat : Submodule.IsLattice D.host.E Λ₀ := hLO.1
  have hfull : Submodule.IsFullLattice D.host.E Λ₀ := by
    obtain ⟨p⟩ := GlobalTheory.PhiEmbed.exists_place D
    obtain ⟨τ, hτ, heq⟩ := hLO.2 p
    apply isFullLattice_of_local_span Z p Λ₀ hlat
    rw [← heq]
    exact (_root_.GlobalTheory.GenMass.Fibre.termLat D Z FP p (d0 p) τ hτ).2
  obtain ⟨V1, hV1, hmain⟩ := _root_.GlobalTheory.HL.mass_restricted_product (fun p => ↥(FP p).UW0) (fun p => LocNG.Datum (FP p))
    (fun p => (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ↥(FlagPairStabilizer F F') φ hφi
    (_root_.GlobalTheory.Unfold.ext_fix_lattice_ae D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hfull)
    (GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀
      (by first | exact hfull | exact hfull.toIsLattice))
    (_root_.GlobalTheory.Unfold.FixFin.conj_aut_finite D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hfull) d0 hc0 hfin
  refine ⟨V1, hV1, fun d hd hfd => ?_⟩
  have h3 := hdd d hd
  rw [_root_.GlobalTheory.Unfold.massA_eq_sum_orbits D X Y u u' F F' w hw hG Z FP hB hR φ hφE hφi hMv' d]
  have hm2 := hmain d (fun p => ⟨(h3 p).1, (h3 p).2.1⟩) hfd
  have e : (∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) = ∏ᶠ p, invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) := finprod_congr fun p => ((h3 p).2.2).symm
  refine hm2.trans ?_
  rw [e]

end GlobalTheory.Unfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanCorankOne

theorem num (a b Mk X Y c₁ c₂ de NT HH l m : ℝ) (j : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hMk : 0 ≤ Mk)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hA : a ≤ Mk * (X * Y)) (hB : b ≤ c₁ * c₂) (hm : Mk * NT ^ j ≤ m) (hde : 1 ≤ de) (hdH : de ≤ HH)
    (hN : 1 ≤ NT) (hNH : NT ≤ HH) (hl : 0 ≤ l) :
    a * b * de ^ j * (de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l)) ≤
      ((de / NT) ^ j * X * (Y * c₁ * c₂ * HH ^ (11 + 3 * l))) * m := by
  have hd0 : 0 ≤ de := by linarith
  have hN0 : 0 < NT := by linarith
  have hH1 : 1 ≤ HH := le_trans hde hdH
  have hH0 : 0 < HH := by linarith
  have hR : de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l) ≤ HH ^ (11 + 3 * l) := by
    have e1 : de ^ (4 + l) ≤ HH ^ (4 + l) := Real.rpow_le_rpow hd0 hdH (by linarith)
    have e2 : NT ^ 2 ≤ HH ^ 2 := pow_le_pow_left₀ hN0.le hNH 2
    have e3 : (de * NT) ^ (2 + l) ≤ (HH * HH) ^ (2 + l) :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul hdH hNH hN0.le hH0.le) (by linarith)
    have e4 : HH ^ (4 + l) * HH ^ 2 * (HH * HH) ^ (2 + l) = HH ^ (10 + 3 * l) := by
      rw [Real.mul_rpow hH0.le hH0.le, ← Real.rpow_natCast HH 2, ← Real.rpow_add hH0,
        ← Real.rpow_add hH0, ← Real.rpow_add hH0]
      congr 1; push_cast; ring
    have e5 : HH ^ (10 + 3 * l) ≤ HH ^ (11 + 3 * l) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    calc _ ≤ HH ^ (4 + l) * HH ^ 2 * (HH * HH) ^ (2 + l) := by
          gcongr
      _ = HH ^ (10 + 3 * l) := e4
      _ ≤ _ := e5
  have hR0 : 0 ≤ de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l) := by positivity
  calc a * b * de ^ j * (de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l))
      ≤ (Mk * (X * Y)) * (c₁ * c₂) * de ^ j * HH ^ (11 + 3 * l) := by gcongr
    _ = ((de / NT) ^ j * X * (Y * c₁ * c₂ * HH ^ (11 + 3 * l))) * (Mk * NT ^ j) := by
        rw [div_pow]; field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.Mass.PrimMeanCorankOne

namespace GlobalTheory.Mass.PrimMeanCorankOne

theorem main : ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), UnitaryVolumeMass.stMassRatio D → Formalism.MainNotions.BridgeLemma₂.PrimitiveMeanCorankOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  intro D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hR
  letI := D.host.cmStar
  intro hyp F0 he hz what₂ hrows de hde HH hdH hNH
  obtain ⟨-, ⟨-, hTp, -, hT3, -, hTs, -⟩, -⟩ := hyp
  unfold Cnt.MeanLe
  rcases what₂.eq_empty_or_nonempty with e | ⟨Λ₀, hΛ₀⟩
  · subst e; simp
  have hΛ₀r := hrows.1 Λ₀ hΛ₀
  have hK : IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨⟨hPD, hrk⟩, hrow⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hint, hcyc⟩ := hrow Λ₀ hΛ₀r
  have hs := (D.sp.X 0).herm
  have hM := (GlobalTheory.Mass.RowPerpMass.main D u F0 he hz hTp hTs Λ₀ hΛ₀r).2
  have hgen := (GlobalTheory.Mass.CyclicGenus.main _ _ _ hK hs (D.sp.X 0).nondeg _ hTp hTs).2
  have hMG := GlobalTheory.MeanGenus.mean_rows_eq_mean_genus D u hTp hT3 hTs F0 he hz what₂ hrows Λ₀ hΛ₀r
  set h := (D.sp.X 0).hT with hh
  obtain ⟨reps, hreps⟩ := (final_massBasic _ _ h hs (GlobalTheory.Mass.GenusOrb.trace_pos_of_PD h hPD) _ hint.1).1
  set N : Submodule (𝓞 D.host.E) (D.sp.X 0).V → ℕ∞ := fun L => (primSp h L (D.R.k - 1) (de ^ 2)).encard with hN
  have hNinv : ∀ γ ∈ isom h, ∀ L, N (gmap γ L) = N L := fun γ hγ L =>
    (GlobalTheory.Mass.PrimMove.main _ _ h hK hs (D.sp.X 0).nondeg ⟨γ, hγ⟩ L ⊥ _ _).2
  have hMG' := hMG reps hreps N hNinv
  have hl : (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
      (Cnt.cntPrim h (Lat.L0X D Λ (lf D F0)) (D.R.k - 1) de : ℝ≥0∞)) =
      ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (Lat.L0X D Λ (lf D F0)) : ℝ≥0∞) := by
    refine Finset.sum_congr rfl fun Λ hΛ => ?_
    rw [(GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD _ (hrow Λ (hrows.1 Λ hΛ)).1).2.2.1]
  generalize Lat.L0X D Λ₀ (lf D F0) = L₀ at *
  obtain ⟨hm1, hm2, hst, -, hsum⟩ := GlobalTheory.Mass.GenusOrb.main _ _ h hK hs hPD L₀ hint.1
  have hr := hsum reps (fun L => (N L : ℝ≥0∞)) hreps (fun g M => by
    change ((N (gmap g.1 M) : ℕ∞) : ℝ≥0∞) = _
    rw [hNinv g.1 g.2 M])
  rw [hl]
  have hf : 1 ≤ D.R.f := by
    have h1 := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.toFrame.ord := rfl
    omega
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  set t : ℕ := Lat.Tu D u ^ D.R.f with ht_def
  have ht : 1 ≤ t := Nat.one_le_pow _ _ hTp.pos
  have hmem : ∀ L ∈ genus h L₀, IsIntLat h L ∧ discN h L = t ^ 2 ∧
      (∃ s : Finset (D.sp.X 0).V, s.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 D.host.E) (s : Set (D.sp.X 0).V)) ∧
      ∀ x ∈ dual h L, ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) • x ∈ L := by
    intro L hL
    obtain ⟨a, ⟨e⟩⟩ := (hgen L₀ L hint hcyc).1 hL
    obtain ⟨b, c⟩ := GlobalTheory.Mass.PrimMeanRow.disc_of_equiv h L _ e
    refine ⟨a, by rw [b, GlobalTheory.Mass.PrimMeanRow.finrank_E, ht_def, ← pow_mul]; ring_nf,
      ((GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD L a).2.2.2.1 1).1 c, ?_⟩
    intro x hx
    have h1 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) • e (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨x, hx⟩))
      rw [← hr, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have h3 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) •
        (Submodule.Quotient.mk ⟨x, hx⟩ : ↥(dual h L) ⧸ L.comap (dual h L).subtype) = 0 :=
      e.injective (by rw [map_smul, h1, map_zero])
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h3
    exact h3
  have hU := GlobalTheory.Mass.StdMass.main _ hK
  have hT0 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have hnorm : Ideal.absNorm (Ideal.span {((Lat.Tu D u : ℕ) : 𝓞 D.host.E)}) = t ^ 2 := by
    rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, RingOfIntegers.rank,
      GlobalTheory.Mass.PrimMeanRow.finrank_E, ht_def, ← pow_mul]
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    ring_nf
  have hP := GlobalTheory.Mass.PrimMeanOne.main GlobalTheory.Mass.MaxFormula.main _ _ h hK hs hPD
    (GlobalTheory.Mass.exists_orthoLattice_of_unimodular _ hK) (D.R.k - 1) (by omega) (by rw [hrk]; omega)
    _ _ _ (hU (D.R.k - 1)).1 (hU (D.R.k - 1)).2.1 _ _ _ (hU 1).1 (hU 1).2.1 de t _ hde ht hT0 hnorm
    (genus h L₀) hst hmem
  have hv : 0 < D.host.v := Formalism.MainNotions.StandardLattice.host_v_pos D
  have hNT1 : 1 ≤ Cnt.NT D u := one_le_pow₀ (by exact_mod_cast hTp.one_le)
  have htNT : ((t : ℕ) : ℝ) = Cnt.NT D u := by
    rw [ht_def, Cnt.NT]; push_cast; rfl
  have hfd : fDeg D.host.E = D.R.f := GlobalTheory.Mass.PrimMeanRow.fDeg_E D
  have hA : Cnt.massU D.host.E (D.R.k - 1) ≤ Cnt.massS D D.R.k *
      ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) :=
    GlobalTheory.MassRatioInvBound.mass_pred_le D hR
  have hB : Cnt.massU D.host.E 1 ≤ (classNumber D.host.E : ℝ) * 2 ^ D.R.f := by
    have e1 := ((hU 1).2.2.2.2 _ (Formalism.HermitianLattices.Ext.L3.stdForm D.host.E 1) (Formalism.HermitianLattices.Ext.L3.stdLat D.host.E 1)
      (Formalism.HermitianLattices.Ext.L3.stdLat_isOrtho D.host.E 1)).1
    have e2 := Formalism.MainNotions.BridgeLemVN.mass_std_one_le hK
    rw [e1, hfd] at e2
    push_cast at e2
    exact e2
  have hbound := num (Cnt.massU D.host.E (D.R.k - 1)) (Cnt.massU D.host.E 1) (Cnt.massS D D.R.k)
    ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f))
    ((2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) (classNumber D.host.E : ℝ) (2 ^ D.R.f)
    de (Cnt.NT D u) HH (Real.logb 2 D.R.f) (mass h L₀) (D.R.k - 1)
    (hU (D.R.k - 1)).2.2.1.le (hU 1).2.2.1.le (hU D.R.k).2.2.1.le (by positivity)
    (by have := GlobalTheory.Mass.PrimMeanRow.one_le_rdE D; positivity) (Nat.cast_nonneg _) (by positivity)
    hA hB hM (by exact_mod_cast hde) hdH hNT1 hNH
    (Real.logb_nonneg one_lt_two (by exact_mod_cast hf))
  have key : (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * ((N (Lat.L0X D Λ (lf D F0)) : ℕ∞) : ℝ≥0∞)) *
      ENNReal.ofReal (mass h L₀) ≤
      ((∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) *
        ENNReal.ofReal (((de : ℝ) / Cnt.NT D u) ^ (D.R.k - 1) *
          (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
          (Formalism.MainNotions.BridgeLemma₂.classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)))) * ENNReal.ofReal (mass h L₀) := by
    rw [hMG', hr, mul_assoc, ← ENNReal.ofReal_mul' hm2.le]
    refine mul_le_mul' le_rfl (hP.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [hfd, htNT]
    unfold Formalism.MainNotions.BridgeLemma₂.classWeightAlt
    exact hbound
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 hm2).ne' ENNReal.ofReal_ne_top).1 key

end GlobalTheory.Mass.PrimMeanCorankOne
end

