module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.FrobeniusPowerCompatibility
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0001
public import Formalism.LocalToGlobal.TieTwRecOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0006
public import Formalism.LocalToGlobal.HilbertRowConditions.AllJoinP
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLabelWeightsOfGreenCuspidalParametrisa

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GaloisRepTowerRestriction
section

end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsomorphismOfFrobeniusTraces
section

end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkIRROfJoinEx
section
noncomputable section

namespace GlobalTheory.Top.Irr

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.ConcNWeight Formalism.L2.GlobalTheoryTheory.AllJoin

theorem tieAdmG_holds (D : D7) : TieAdmG D := fun k =>
  ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩

theorem linkIRR_of_join_ex (eps Cs c : ℝ) (he : 0 < eps) (he1 : eps ≤ 1) (hc : 0 < c) (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
      LabelCountGoodInjective A ∧ AllJoinA A ∧ admLq (Fm.D x i) ∧
        CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧ SizesRec (Fm.D x i) x Fm.ez Cs) :
    LinkIRR Fm := by
  obtain ⟨x0, hx0⟩ := h
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  refine linkIRR_of_allRows eps Cs c he he1 hc Fm ⟨max x0 ((3 / 2 : ℝ) ^ (1 / Fm.ez)), fun x hx i => ?_⟩
  obtain ⟨A, hT, hJ, hL, hC, hS⟩ := hx0 x (le_trans (le_max_left _ _) hx) i
  have hx1 : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x := le_trans (le_max_right _ _) hx
  have hxe : 3 / 2 ≤ x ^ Fm.ez := by
    have hpos : 0 ≤ (3 / 2 : ℝ) ^ (1 / Fm.ez) := by positivity
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (1 / Fm.ez)) ^ Fm.ez := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]
      _ ≤ x ^ Fm.ez := Real.rpow_le_rpow hpos hx1 hez.le
  exact ⟨A, hT, hC, weight_of_join hL (tieAdmG_holds _) (rangeW_of_sizes hS hxe) hJ, hS⟩

end

section
open Formalism.BasicNotions Formalism.MainNotions

theorem sizesRec_at {eps : ℝ} (Fm : FamP eps) {x : ℝ} (hx : Fm.x1 < x) (hx4 : 4 ≤ x) (i : Fm.Ix x) {Cs : ℝ}
    (hCs : 6 ≤ Cs) : Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec (Fm.D x i) x Fm.ez Cs := by
  obtain ⟨hN, -, hK, -, -, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := Fm.sizes x hx i
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hLe : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hε0 : 0 < eps := hLe ▸ (Fm.L x i).sc.eps_pos
  have hε1 : eps < 1 / 52 := hLe ▸ (Fm.L x i).sc.eps_lt
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hLz : (Fm.L x i).sc.ez = Fm.ez := Fm.toFamCore.L_ez x i
  have hz0 : 0 < Fm.ez := div_pos hε0 (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  have hzle : Fm.ez ≤ eps := div_le_self hε0.le Fm.toFamCore.one_le_J
  simp only [SizeN, SizeK, SizeQD, SizeG, szTh, hLx, hLe, hLz] at hN hK hQD hG

  have hf : ((Fm.D x i).R.f : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by simp [Ranks.f]
  have hfk : (Fm.D x i).R.f ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.f_le_k
    simpa [Ranks.f, Ranks.n] using this
  have hmf : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := by
    have := (Fm.D x i).R.m_le_f
    simpa [Ranks.f, Ranks.n] using this
  have hm2 : 2 ≤ (Fm.D x i).R.m := (Fm.D x i).R.two_le_m
  have hrk : (Fm.D x i).R.k ≤ (Fm.D x i).R.r := by unfold Ranks.r; omega
  have hr2k : (Fm.D x i).R.r ≤ 2 * (Fm.D x i).R.k := by unfold Ranks.r; omega

  have h5 : x ^ (9 / 2 + 10 * eps + eps / 100) ≤ x ^ (5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h56 : x ^ (5 : ℝ) ≤ x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h6 : x ^ (6 : ℝ) ≤ x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1 hCs
  have h4 : x ^ (4 : ℝ) ≤ x ^ (9 / 2 + 10 * eps - eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps - eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hx4p : (256 : ℝ) ≤ x ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : (4 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx4 4
    norm_num at this ⊢; linarith
  have hx65 : 2 * x ^ (5 : ℝ) ≤ x ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    have h0 : 0 ≤ x ^ (5 : ℝ) := Real.rpow_nonneg hx0.le _
    have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ x by linarith) h0
    linarith
  have hkx : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) := le_trans hK.2 h5
  have hkl : (256 : ℝ) ≤ (Fm.D x i).R.k := le_trans (le_trans hx4p h4) hK.1
  have hfkR : ((Fm.D x i).R.f : ℝ) ≤ (Fm.D x i).R.k := by exact_mod_cast hfk
  have hmfR : ((Fm.D x i).R.m : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast hmf
  have hr2kR : ((Fm.D x i).R.r : ℝ) ≤ 2 * (Fm.D x i).R.k := by exact_mod_cast hr2k
  have hrkR : ((Fm.D x i).R.k : ℝ) ≤ (Fm.D x i).R.r := by exact_mod_cast hrk

  have hεq : x ^ (Fm.ez / 6) ≤ x ^ (Fm.ez / 5 - Fm.ez / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpos6 : 0 < x ^ (Fm.ez / 6) := Real.rpow_pos_of_pos hx0 _
  have hq : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.q : ℝ) := by
    have hl := hQD.1
    have hq0 : (0 : ℝ) < (Fm.D x i).host.q := by
      rcases Nat.eq_zero_or_pos (Fm.D x i).host.q with h0 | h0
      · rw [h0] at hl; simp at hl; linarith
      · exact_mod_cast h0
    calc Real.exp (x ^ (Fm.ez / 6)) ≤ Real.exp (Real.log (Fm.D x i).host.q) := Real.exp_le_exp.2 hl
      _ = (Fm.D x i).host.q := Real.exp_log hq0
  have hd : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.d : ℝ) := by
    have hl : x ^ (Fm.ez / 6) ≤ Real.log (Fm.D x i).host.d := le_trans hεq hQD.2.2.2.1
    have hd0 : (0 : ℝ) < (Fm.D x i).host.d := by
      rcases Nat.eq_zero_or_pos (Fm.D x i).host.d with h0 | h0
      · rw [h0] at hl; simp at hl; linarith
      · exact_mod_cast h0
    calc Real.exp (x ^ (Fm.ez / 6)) ≤ Real.exp (Real.log (Fm.D x i).host.d) := Real.exp_le_exp.2 hl
      _ = (Fm.D x i).host.d := Real.exp_log hd0
  intro j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hg := (hG j j).1
    have hb : Real.exp (8 * x ^ eps) = (Real.exp (x ^ eps)) ^ 8 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hb0 : 0 ≤ Real.exp (x ^ eps) := (Real.exp_pos _).le
    have hkb : Real.exp (x ^ eps) ≤ ((Fm.D x i).R.k : ℝ) * Real.exp (x ^ eps) := by
      have : (1 : ℝ) ≤ (Fm.D x i).R.k := by linarith
      nlinarith
    have hsc : (Fm.L x i).sc.b = Real.exp (x ^ eps) := by
      rw [show (Fm.L x i).sc.b = Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) from rfl, hLx, hLe]
    rw [hsc] at hg
    have hze : x ^ Fm.ez ≤ x ^ eps := Real.rpow_le_rpow_of_exponent_le hx1 hzle
    refine le_trans (Real.exp_le_exp.2 (by linarith : 8 * x ^ Fm.ez ≤ 8 * x ^ eps)) ?_
    rw [hb]
    exact le_trans (pow_le_pow_left₀ hb0 hkb 8) hg
  ·
    rw [← Real.rpow_two]
    have hn0 : (0 : ℝ) ≤ (Fm.D x i).R.n := Nat.cast_nonneg _
    have hnf : ((Fm.D x i).R.n : ℝ) ≤ (Fm.D x i).R.f := by rw [hf]; linarith
    exact le_trans h2 (le_trans hN.1 hnf)
  · exact le_trans hfkR (le_trans hkx h56)
  · exact le_trans hmfR (le_trans hfkR (le_trans hkx h56))
  ·
    have h256 : 256 ≤ (Fm.D x i).R.k := by exact_mod_cast hkl
    omega
  · have h2k : 2 * ((Fm.D x i).R.k : ℝ) ≤ 2 * x ^ (5 : ℝ) := mul_le_mul_of_nonneg_left hkx (by norm_num)
    exact le_trans hr2kR (le_trans h2k (le_trans hx65 h6))
  · rw [Nat.cast_min]
    exact le_min hq hd

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

end GlobalTheory.Top.Irr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticCmCharacterInjective
section

end

