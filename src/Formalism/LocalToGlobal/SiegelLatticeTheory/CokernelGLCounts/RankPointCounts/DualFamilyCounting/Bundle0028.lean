module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArithG
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcArithG

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem rm_eq (D : D7) : D.R.m = 2 * (D.R.rS + 1) := by
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  show D.R.m = 2 * (D.R.m / 2 - 1 + 1)
  omega

theorem cMass_succ {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (k : ℕ) (hk : 2 ≤ k) :
    Formalism.L2.SG.Pf.Cnt.cMass K F k = Formalism.L2.SG.Pf.Cnt.cMass K F (k - 1) * Formalism.HermitianLatticesTheory.massRatioRightSide K k := by
  unfold Formalism.L2.SG.Pf.Cnt.cMass
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Finset.prod_Icc_succ_top (by omega), Nat.add_sub_cancel, mul_assoc]

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncValueC_of_global (a' Ω ATyp A' AT PT : ℝ)
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (ha : 0 < a') (hATyp : 0 < ATyp) (hA' : 0 < A') (hPT : 0 < PT)
    (hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' * Ω)
    (hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Module.finrank ℚ D.host.F) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Module.finrank ℚ D.host.F *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Module.finrank ℚ D.host.F : ℕ) : ℤ)) *
        |(NumberField.discr D.host.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3))
    (hG1 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      |(NumberField.discr D.host.F : ℝ)| ^ (((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3) *
        ((Lat.gS D : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3) * Module.finrank ℚ D.host.F))
    (hG2 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      ((Lat.gS D : ℕ) : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) * Module.finrank ℚ D.host.F : ℕ) : ℤ)) /
        ATyp)
    (hG3 : Ω = |(NumberField.discr D.host.F : ℝ)| ^
        (-((D.R.r : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)) * A')
    (hG4 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al * ATyp = AT * A')
    (hG5 : AT * ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i = PT)
    (hRM : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
      Formalism.L2.SG.Pf.Cnt.cMass D.host.E D.host.F D.R.k * ((Tw u : ℕ) : ℝ) ^ (D.R.k * Module.finrank ℚ D.host.F) * PT)
    (hV : Formalism.HermitianLatticesTheory.vInv D.host.E =
      |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2)
    (hfE : Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F)
    (hng : ngFac D = ((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F * (D.R.k - 1))) :
    Formalism.L2.SG.Pf.NcAsm.NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by

  set B := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hB
  obtain ⟨hKc, hFc, -⟩ := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D
  set dd : ℝ := |(NumberField.discr D.host.F : ℝ)| with hdd
  set f : ℕ := Module.finrank ℚ D.host.F with hfdef
  set k : ℕ := D.R.k with hkdef
  set s : ℕ := D.R.rS with hsdef
  set gg : ℝ := ((Lat.gS D : ℕ) : ℝ) with hgg
  set TT : ℝ := ((Tw u : ℕ) : ℝ) with hTT
  set Lk : ℝ := ∏ i ∈ Finset.Icc (k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i with hLk
  have hm : D.R.m = 2 * (s + 1) := rm_eq D
  have hk5 : D.R.m + 3 ≤ k := D.R.m_add_three_le_k
  have hk2 : 2 ≤ k := by omega
  have hr : D.R.r = k + 2 * s + 1 := by
    show D.R.k + D.R.m - 1 = k + 2 * s + 1
    omega
  have hf : 0 < f := Module.finrank_pos
  have hdpos : 0 < dd := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.F)
  have hgpos : 0 < gg := by
    have h0 := (D.host.g_prime 0).pos
    have h1' := (D.host.g_prime 1).pos
    rw [hgg]
    unfold Lat.gS
    exact_mod_cast Nat.mul_pos h0 h1'
  have hTpos : 0 < TT := by rw [hTT]; exact_mod_cast (D.mem u).A.T_prime.pos

  obtain ⟨hp, hKo, hSo, hSo', hMo, hU00o, hH, hH', hHpp, hHpp', hN, hN', hZZ, hPP, hal, -⟩ := hP
  have hKp : ∀ p, 0 < B.μKp p := fun p => (hp p).2.2.2.2.2.1
  have hμK : 0 < B.μK := mul_pos hKo (Finset.prod_pos fun p _ => hKp p)

  have hLkpos : 0 < Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k := by
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc k hk2]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc k hk2
  have hLkk : 0 < Lk := by
    apply Finset.prod_pos
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc i hi2]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc i hi2
  have hcm := (Formalism.L2.SG.Pf.Asm.cMass_spec hKc hFc (k - 1) (by omega)).1
  have hIcc : (∏ i ∈ Finset.Icc k D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i) =
      Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k * Lk := by
    have hIo : Finset.Ioc k D.R.r = Finset.Icc (k + 1) D.R.r := by
      ext i; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [Finset.Icc_eq_cons_Ioc (show k ≤ D.R.r by omega), Finset.prod_cons, hLk, hIo]

  have hvI : 2 * Formalism.HermitianLatticesTheory.vInv D.host.E = dd ^ ((1 : ℝ) / f) := by rw [hV]; ring
  have hvIpos : 0 < Formalism.HermitianLatticesTheory.vInv D.host.E := by
    rw [hV]; positivity
  have hpow1 : (dd ^ ((1 : ℝ) / f)) ^ f = dd := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]
    rw [show (1 : ℝ) / f * (f : ℝ) = 1 by field_simp]
    exact Real.rpow_one dd
  have hsq : Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv D.host.E) ^ f) = dd ^ ((1 : ℝ) / 2) := by
    rw [hvI, hpow1, Real.sqrt_eq_rpow]
  have hvk : (Formalism.HermitianLatticesTheory.vInv D.host.E) ^ (k * f) = dd ^ (k : ℝ) / 2 ^ (k * f) := by
    have h2 : Formalism.HermitianLatticesTheory.vInv D.host.E = dd ^ ((1 : ℝ) / f) / 2 := by rw [hV]
    rw [h2, div_pow, pow_mul', hpow1, Real.rpow_natCast]

  set e : ℝ := -(8 * (s : ℝ) ^ 3 + 6 * (s : ℝ) ^ 2 + 6 * k * (s : ℝ) ^ 2 + s) / 3 with he
  set Xe : ℝ := ((s : ℝ) + 1) * (8 * (s : ℝ) ^ 2 + 10 * s + 3) / 3 with hXe
  set e2 : ℝ := (D.R.r : ℝ) * (2 * s + 1) - ((2 * (s : ℝ) + 1) ^ 2) / 2 with he2
  set E1 : ℝ := -((2 * s * (s + 1) * (k - 1) : ℕ) : ℝ) + 1 / 2 - k with hE1
  have hrR : (D.R.r : ℝ) = k + 2 * s + 1 := by rw [hr]; push_cast; ring
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hexp : e = E1 - Xe + e2 := by
    rw [he, hE1, hXe, he2, hrR]
    push_cast
    rw [hk1]
    ring
  have hde : dd ^ e = dd ^ E1 * (dd ^ Xe)⁻¹ * dd ^ e2 := by
    rw [hexp, Real.rpow_add hdpos, Real.rpow_sub hdpos, div_eq_mul_inv]
  have hdE1 : dd ^ E1 = dd ^ ((-((2 * s * (s + 1) * (k - 1) : ℕ) : ℤ) : ℤ) : ℝ) * dd ^ ((1 : ℝ) / 2) *
      (dd ^ (k : ℝ))⁻¹ := by
    rw [hE1, ← Real.rpow_neg hdpos.le, ← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
    congr 1
    push_cast
    ring

  have hgc : gg ^ ((s + 1) * (2 * s + 3) * f) * gg ^ (D.R.m * f * (k - 1)) =
      gg ^ ((s + 1) * (2 * k + 2 * s + 1) * f) := by
    rw [← pow_add]
    congr 1
    rw [hm]
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    ring
  have hgpow : gg ^ (-(((s + 1) * (2 * k + 2 * s + 1) * f : ℕ) : ℤ)) =
      (gg ^ ((s + 1) * (2 * k + 2 * s + 1) * f))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hTpow : TT ^ (-((k * f : ℕ) : ℤ)) = (TT ^ (k * f))⁻¹ := by rw [zpow_neg, zpow_natCast]

  have hal : B.al = AT * A' / ATyp := by rw [eq_div_iff hATyp.ne']; exact hG4
  have hAT : AT = PT / Lk := by rw [eq_div_iff hLkk.ne']; exact hG5
  have hratio : Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E k =
      ((Nat.factorial (k - 1) : ℝ) ^ f * (dd ^ (k : ℝ) / 2 ^ (k * f)) / Real.pi ^ (k * f)) /
        dd ^ ((1 : ℝ) / 2) * Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k := by
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [hfE, hsq, Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc k hk2, mul_pow, ← pow_mul, div_pow, hvk]
    ring
  have hratio_pos : 0 < Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E k := Formalism.HermitianLattices.Ext.L3.massRatio_pos hKc k hk2

  have hKrat : B.μKnat / B.μH' = (B.μKnat / B.μK) * (Ω / a') := by
    have h1 : B.μK / B.μH' = Ω / a' := by
      rw [div_eq_div_iff hH'.ne' ha.ne']
      linarith [hS]
    rw [← h1]
    field_simp
  unfold Formalism.L2.SG.Pf.NcAsm.NcValueC
  rw [← hB]
  calc _ = dd ^ E1 * 2 ^ (k * f) * (Real.pi ^ k / (Nat.factorial (k - 1) : ℝ)) ^ f * TT ^ (-((k * f : ℕ) : ℤ)) *
          A' / ATyp := by
        unfold Formalism.L2.SG.Pf.Cnt.cExpl
        try rw [← hdd]
        try rw [← hfdef]
        try rw [← hkdef]
        try rw [← hsdef]
        rw [hIcc, hRM, cMass_succ k hk2, hratio, hal, hAT, hdE1,
          ← Real.rpow_intCast dd, hTpow, div_pow, ← pow_mul]
        have hpi : 0 < Real.pi := Real.pi_pos
        have hfac : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
        field_simp
    _ = Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat / B.μH' *
          ngFac D := by
        rw [show Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat /
            B.μH' * ngFac D = (Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN') *
            (B.unitLevelVolume / B.volZZ) * (B.μKnat / B.μH') * ngFac D by ring]
        rw [hR, hG1, hKrat, hG2, hG3, hng]
        try rw [← hdd]
        try rw [← hfdef]
        try rw [← hkdef]
        try rw [← hsdef]
        try rw [← hgg]
        try rw [← hTT]
        rw [hde, hgpow, Real.rpow_neg hdpos.le]
        rw [← hgc]
        have hX : 0 < dd ^ Xe := Real.rpow_pos_of_pos hdpos _
        have he2p : 0 < dd ^ e2 := Real.rpow_pos_of_pos hdpos _
        have hgA : 0 < gg ^ ((s + 1) * (2 * s + 3) * f) := pow_pos hgpos _
        have hgC : 0 < gg ^ (D.R.m * f * (k - 1)) := pow_pos hgpos _
        field_simp

end Formalism.L2.SG.Pf.NcArithG
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittGS
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

section GS

variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) K)

theorem exists_aniso (hσ : ∀ z, σ (σ z) = z) (hJ : IsHerm σ J) (h2 : (2 : K) ≠ 0) (u w : Fin n → K)
    (huw : hform σ J u w ≠ 0) : ∃ r t : K, hform σ J (r • u + t • w) (r • u + t • w) ≠ 0 := by
  by_contra H
  push Not at H
  have hexp : ∀ r t : K, hform σ J (r • u + t • w) (r • u + t • w) =
      σ r * r * hform σ J u u + σ r * t * hform σ J u w + σ t * r * hform σ J w u +
        σ t * t * hform σ J w w := by
    intro r t
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
    ring
  set q := hform σ J u w with hq
  set t : K := 2⁻¹ / q with htdef
  have h1 := H 1 0
  have h2' := H 0 1
  have h3 := H 1 t
  rw [hexp, map_one, map_zero] at h1 h2'
  rw [hexp, map_one] at h3
  have ht : t * q = 2⁻¹ := div_mul_cancel₀ _ huw
  have hst : σ t * hform σ J w u = 2⁻¹ := by
    rw [← hform_conj σ J hσ hJ u w, ← hq, ← map_mul, ht, map_inv₀, map_ofNat]
  have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact one_ne_zero (by linear_combination h3 - h1 - (σ t * t) * h2' - ht - hst - hinv : (1 : K) = 0)

end GS

theorem hermDiag : Formalism.L2.SG.Pf.NcS.IntWittPf.HermDiag := by
  intro K _ σ hσ h2 n J hJ a X0 hT
  classical
  have hconj := hform_conj σ J hσ hJ
  let W : Submodule K (Fin n → K) := Submodule.span K (Set.range X0)
  let comb : (Fin a → K) → (Fin n → K) := fun c => ∑ l, c l • X0 l
  have hN : ∀ c : Fin a → K, (∀ j, hform σ J (X0 j) (comb c) = 0) → c = 0 := by
    intro c hc
    refine Matrix.eq_zero_of_mulVec_eq_zero hT ?_
    funext j
    have e : hform σ J (X0 j) (∑ l, c l • X0 l) = 0 := hc j
    rw [hform_sum_right] at e
    simp only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hcW : ∀ c, comb c ∈ W := fun c => W.sum_mem fun l _ => W.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)
  have main : ∀ k ≤ a, ∃ Z : Fin k → Fin n → K, (∀ i, Z i ∈ W) ∧
      (∀ i j, i ≠ j → hform σ J (Z i) (Z j) = 0) ∧ ∀ i, hform σ J (Z i) (Z i) ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨Z, hZW, hZo, hZd⟩ := ih (by omega)
      let f : (Fin a → K) →ₗ[K] (Fin k → K) :=
        { toFun := fun c i => hform σ J (Z i) (comb c)
          map_add' := by
            intro c d
            funext i
            simp only [comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, hform_add_right]
          map_smul' := by
            intro r c
            funext i
            simp only [comb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul, ← Finset.smul_sum,
              hform_smul_right] }
      have hlt : Module.finrank K (Fin k → K) < Module.finrank K (Fin a → K) := by
        simp only [Module.finrank_fin_fun]
        omega
      obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
      have hcZ : ∀ i, hform σ J (Z i) (comb c) = 0 := fun i => congrFun (LinearMap.mem_ker.1 hc) i
      obtain ⟨j, hj⟩ : ∃ j, hform σ J (X0 j) (comb c) ≠ 0 := by
        by_contra H
        push Not at H
        exact hc0 (hN c H)
      let w := X0 j - ∑ i, (hform σ J (Z i) (X0 j) / hform σ J (Z i) (Z i)) • Z i
      have hwZ : ∀ m, hform σ J (Z m) w = 0 := by
        intro m
        simp only [w, hform_sub_right, hform_sum_right]
        rw [Finset.sum_eq_single m]
        · rw [div_mul_cancel₀ _ (hZd m), sub_self]
        · intro i _ him
          rw [hZo m i (Ne.symm him), mul_zero]
        · simp
      have hwc : hform σ J w (comb c) ≠ 0 := by
        simp only [w, hform_sub_left, hform_sum_left]
        rw [Finset.sum_eq_zero, sub_zero]
        · exact hj
        · intro i _
          rw [hcZ i, mul_zero]
      have hwW : w ∈ W := W.sub_mem (Submodule.subset_span ⟨j, rfl⟩) (W.sum_mem fun i _ => W.smul_mem _ (hZW i))
      obtain ⟨r, t, hz⟩ := exists_aniso σ J hσ hJ h2 w (comb c) hwc
      set z := r • w + t • comb c with hzdef
      have hzZ : ∀ m, hform σ J (Z m) z = 0 := by
        intro m
        rw [hzdef, hform_add_right, hform_smul_right, hform_smul_right, hwZ, hcZ, mul_zero, mul_zero, add_zero]
      refine ⟨Fin.snoc Z z, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact W.add_mem (W.smul_mem _ hwW) (W.smul_mem _ (hcW c))
        · rw [Fin.snoc_castSucc]
          exact hZW i
      · intro i j
        refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h; exact absurd rfl h
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc, ← hconj, hzZ, map_zero]
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact hzZ i
        · intro hij
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hZo i j (fun e => hij (by rw [e]))
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact hz
        · rw [Fin.snoc_castSucc]
          exact hZd i
  obtain ⟨Z, hZW, hZo, hZd⟩ := main a le_rfl
  have hex : ∀ i, ∃ c : Fin a → K, ∑ l, c l • X0 l = Z i :=
    fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hZW i)
  choose C hC using hex
  let P : Matrix (Fin a) (Fin a) K := Matrix.of C
  have hPX : ∀ i, ∑ l, P i l • X0 l = Z i := fun i => hC i
  have hdet : P.det ≠ 0 := by
    intro hd
    obtain ⟨c, hc0, hcP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    apply hc0
    funext j
    have e : ∑ i, c i • Z i = 0 := by
      have hl : ∀ l, ∑ i, c i * P i l = 0 := fun l => by
        have := congrFun hcP l
        simpa [vecMul, dotProduct] using this
      simp_rw [← hPX, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hl, zero_smul, Finset.sum_const_zero]
    have h := congrArg (hform σ J (Z j)) e
    rw [hform_sum_right, hform_zero_right, Finset.sum_eq_single j] at h
    · exact (mul_eq_zero.1 h).resolve_right (hZd j)
    · intro i _ hij
      rw [hZo j i (Ne.symm hij), mul_zero]
    · simp
  refine ⟨P, P⁻¹, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.2 hdet), ?_, ?_⟩
  · intro i j hij
    rw [hPX, hPX]
    exact hZo i j hij
  · intro i
    rw [hPX]
    exact hZd i

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end

