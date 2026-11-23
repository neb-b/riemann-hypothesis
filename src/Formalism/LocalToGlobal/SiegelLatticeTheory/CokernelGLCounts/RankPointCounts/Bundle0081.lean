module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0063
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0080
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0057
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocalCountZeroLocalHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocCntUL

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieIdx
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTieIdx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_one_sub_inv_pow_pos (q : ℝ) (hq : 1 < q) (s : Finset ℕ) (hs : ∀ j ∈ s, 1 ≤ j) :
    0 < ∏ j ∈ s, (1 - 1 / q ^ j) :=
  Finset.prod_pos fun j hj => by
    have h1 : 1 < q ^ j := one_lt_pow₀ hq (by have := hs j hj; omega)
    have h2 : 1 / q ^ j < 1 := by rw [div_lt_one (by linarith)]; exact h1
    linarith

theorem cardGL_A (g m : ℕ) [hg : Fact g.Prime] :
    (Nat.card (GL (Fin m) (ZMod g)) : ℝ) = (g : ℝ) ^ (m * m) * ∏ j ∈ Finset.Ioc 0 m, (1 - 1 / (g : ℝ) ^ j) := by
  have hq0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.out.ne_zero
  rw [Matrix.card_GL_field, ZMod.card, Nat.cast_prod]
  have hterm : ∀ i : Fin m, (((g ^ m - g ^ (i : ℕ) : ℕ)) : ℝ) = (g : ℝ) ^ m * (1 - 1 / (g : ℝ) ^ (m - i)) := by
    intro i
    rw [Nat.cast_sub (Nat.pow_le_pow_right hg.out.pos i.2.le), Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one,
      mul_one_div, div_eq_mul_inv, ← pow_sub₀ _ hq0 (Nat.sub_le m i), Nat.sub_sub_self i.2.le]
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun i => 1 - 1 / (g : ℝ) ^ (m - i)) m]
  have h1 : ∏ i ∈ Finset.range m, (1 - 1 / (g : ℝ) ^ (m - i)) =
      ∏ i ∈ Finset.range m, (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) (m - 1 - i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    show _ = 1 - 1 / (g : ℝ) ^ (m - 1 - i + 1)
    rw [show m - 1 - i + 1 = m - i by omega]
  rw [h1, Finset.prod_range_reflect (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) m, Finset.range_eq_Ico,
    Finset.prod_Ico_add' (fun j => 1 - 1 / (g : ℝ) ^ j) 0 m 1]
  have h2 : Finset.Ico (0 + 1) (m + 1) = Finset.Ioc 0 m := by ext; simp; omega
  rw [h2]

theorem idx_arith (g r k : ℕ) (hg : g.Prime) :
    (glkC k g : ℝ) * (nnC r k g : ℝ) / (ggC r k g : ℝ) =
      (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) /
        ∏ i ∈ Finset.Icc (k + 1) (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ i) := by
  have : Fact g.Prime := ⟨hg⟩
  have hq : (1 : ℝ) < g := by exact_mod_cast hg.one_lt
  have hq0 : (g : ℝ) ≠ 0 := by linarith
  have hc : Fintype.card (Formalism.FourierDecayAlt.S3.Idx r k) = 2 * r + k + 1 := by
    simp only [Formalism.FourierDecayAlt.S3.Idx, Formalism.FourierDecayAlt.S3.Mid, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  have hG : (ggC r k g : ℝ) = (Nat.card (GL (Fin (2 * r + k + 1)) (ZMod g)) : ℝ) := by
    unfold ggC
    exact_mod_cast Nat.card_congr
      (Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod g) (ZMod g) (Fintype.equivFinOfCardEq hc)).toMulEquiv)
  have hN : (nnC r k g : ℝ) = (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
    unfold nnC
    rw [MassDataIdxStIm.card_isN, ZMod.card]
    push_cast
    try rfl
  unfold glkC
  rw [hG, hN, cardGL_A, cardGL_A]
  have hIcc : Finset.Icc (k + 1) (2 * r + k + 1) = Finset.Ioc k (2 * r + k + 1) := by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, ← Finset.prod_Ioc_consecutive _ (Nat.zero_le k) (by omega : k ≤ 2 * r + k + 1)]
  have hA : 0 < ∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => (Finset.mem_Ioc.1 hj).1)
  have hB : 0 < ∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => by have := (Finset.mem_Ioc.1 hj).1; omega)
  have hpow : (g : ℝ) ^ (k * k) * (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) /
      (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) = (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) := by
    rw [← pow_add, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hq0]
    congr 1
    rcases r with _ | s
    · simp; ring
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  rw [← hpow]
  generalize (∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j)) = A at hA ⊢
  generalize (∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j)) = B at hB ⊢
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hgn : (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  try ring

variable {D : D7} (X : HidaSetting D)

theorem ratio_eq (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal / (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ) / (ggC D.R.rS D.R.k (gOf p) : ℝ) := by
  obtain ⟨j, hj, hj0, hμj, hB0, hBt⟩ := MassDataIdxSteps.measB_of X MassDataIdxSteps.haarIdx MassDataIdxSteps.redIdx u p
    (MassDataIdxSteps.stTop X p) (Formalism.L2.SG.Pf.MassDataX.stK_holds X p) (Formalism.L2.SG.Pf.MassDataX.stRed_holds X p)
    (Formalism.L2.SG.Pf.MassDataX.stImB_holds X hb u p)
  have h1 : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (j : ℝ) * (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal := by
    rw [hμj, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hpos : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
  rw [h1, ← hj]
  rcases eq_or_ne (j : ℝ) 0 with h0 | h0
  · simp [h0]
  · rw [mul_comm (j : ℝ) (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal, mul_comm (j : ℝ),
      div_mul_eq_div_div, div_self hpos, div_mul_eq_div_div, div_self hj0]

theorem gAt_eq (p : TypX X) : gAt X p.1 = gOf p := by
  unfold gAt gOf
  split_ifs <;> rfl

theorem aP_typed (u : D.what₂.Word) (p : TypX X) :
    aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) =
      ∏ i ∈ Finset.Icc (D.R.k + 1) (2 * D.R.rS + D.R.k + 1), (1 - 1 / (gOf p : ℝ) ^ i) := by
  obtain ⟨hN, hη⟩ := Formalism.L2.SG.Pf.gSplitX_holds X p
  have hT := Formalism.L2.SG.Pf.AlTieFD.T_not_mem X u p
  unfold aP
  rw [if_neg (by unfold Tw; exact hT), X.n_eq, ← Formalism.MainNotions.S.dimS_eq D.R, hη, hN, gAt_eq X p]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem indexTypC_holds (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro p
  refine (ratio_eq X hb u p).trans ?_
  rw [idx_arith (gOf p) D.R.rS D.R.k (MassDataIdxSteps.gOf_prime X p), aP_typed X u p, gAt_eq X p]

end Formalism.L2.SG.Pf.AlTieIdx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
section
namespace Formalism.L2.SG.Pf

theorem formRelC_holds : Formalism.L2.SG.Pf.FormRel.FormRelC :=
  formRelC_of (fun D X Y u u' => Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of X Y u u'
    (Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')) Formalism.L2.SG.Pf.RelChar.relCharC_holds

theorem formNGC_holds : Formalism.L2.SG.NGVanish.FormNGC := formNGC_of_rel formRelC_holds

theorem formGC_holds : Formalism.L2.SG.Pf.MainEqVanish.FormGC := formGC_of_rel formRelC_holds

end Formalism.L2.SG.Pf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameActOne
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem frameAct_one {n : ℕ} (f : Fin n → (VS D).V) (b : Fin n) : frameAct f 1 b = f b := by
  simp [frameAct, Matrix.one_apply]

theorem sgnP_mem (p : PlF D) (b : Fin (D.R.rS + 1)) : TermLoc.sgnP D p b ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  refine ⟨Polynomial.X ^ 2 - 1, by monicity!, ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
  rw [pow_two, TermLoc.localSign_sq, sub_self]


set_option maxHeartbeats 1000000 in
theorem btAdm : BtAdm Zd u u' F0 what₂ := by
  intro hC γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, _⟩ := hs
  refine ⟨fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, fun b => ?_⟩
  intro P hgP
  rw [frameAct_one]
  haveI := P.isPrime
  set x : (VS D).V := frame (liftF F'₂) b - frame (lf D F0) b with hx
  obtain ⟨p, hpdef⟩ : ∃ p : PlF D, p = Formalism.L2.SG.Pf.LocalDenominators.plOf P.asIdeal P.isMaximal := ⟨_, rfl⟩
  have hPp : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal := by rw [hpdef]; rfl
  have hty : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) :=
    (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P hPp).1 hgP
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 ((D.s_split p).2 hty)
  have hag := (Zd.agree p).2.2.2.2.2
  obtain ⟨g', hMs⟩ : ∃ g', (Zd.M p).split = some g' := by
    cases hm : (Zd.M p).split with
    | none => rw [hm, hsg] at hag; exact hag.elim
    | some g' => exact ⟨g', rfl⟩
  have hadm := ((hloc p).1.1.2.2.2.2.2 g' hMs).2.2 b

  have hrow := hC.2.1.1 γ.lam γ.mem
  have hgP' : ∀ P' : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      P'.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P'.asIdeal :=
    fun P' hP' => (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P' hP').2 hty
  obtain ⟨-, w, hw, hw1⟩ := Formalism.L2.SG.Pf.BBTie.bt_typed_frFac Zd (Formalism.L2.SG.Pf.locEqC_holds D Zd)
    (Formalism.L2.SG.Pf.locDiffC_holds D Zd) p F0 γ.lam hrow.2.1.1.fg hrow.2.2 hrow.2.1.2.2.2 hgP' b
  have hO := (Zd.agree p).2.2.2.1
  have hsg' : TermLoc.sgnP' D p b = TermLoc.sgnP D p b := by
    show (match (D.s.atP p).split with | some _ => TermLoc.sgnP D p b | none => (-1) ^ (D.R.rS - b.val)) = _
    rw [hsg]
  set c : (D.s.atP p).Ep := TermLoc.sgnP D p b * frFac Zd.δ p b with hc
  have hdiff : locF' Zd p F'₂ b - (tLoc Zd p γ).f b = c • baseChange₂ D p x := by
    show (TermLoc.sgnP' D p b * frFac Zd.δ p b) • baseChange₂ D p (frame F'₂ b) -
      (TermLoc.sgnP D p b * frFac Zd.δ p b) • baseChange₂ D p (frame (lf D F0) b) = _
    rw [hsg', hx, map_sub, smul_sub]
    rfl
  have hinv : (TermLoc.sgnP D p b * w) * c = 1 := by
    rw [hc, mul_mul_mul_comm, TermLoc.localSign_sq, hw1, one_mul]
  have hinvO : TermLoc.sgnP D p b * w ∈ (Zd.M p).L.O := by
    rw [hO]; exact (D.s.atP p).O.mul_mem (sgnP_mem p b) (by rw [← hO]; exact hw)

  have h1 : baseChange₂ D p x ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g'.q : (D.s.atP p).Fp))
      (lattice₂ D Zd.M p Λ₂) := by
    have : baseChange₂ D p x = (TermLoc.sgnP D p b * w) • (locF' Zd p F'₂ b - (tLoc Zd p γ).f b) := by
      rw [hdiff, smul_smul, hinv, one_smul]
    rw [this]
    exact Submodule.smul_mem _ ⟨_, hinvO⟩ hadm

  have hqg := Formalism.L2.SG.Pf.Cnt.DualityBasisChange.q_gS_inv_mem Zd.agree p hMs
  have h2 : (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ₂ := by
    have key : ∀ v ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g'.q : (D.s.atP p).Fp))
        (lattice₂ D Zd.M p Λ₂), (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • v ∈ lattice₂ D Zd.M p Λ₂ := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨y, hy, rfl⟩ := hv
        rw [smul_smul]
        exact (lattice₂ D Zd.M p Λ₂).smul_mem ⟨_, hqg⟩ hy
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add a c _ _ ha hc => rw [smul_add]; exact Submodule.add_mem _ ha hc
      | smul o v _ hv =>
        have e : (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • (o • v) =
            o • ((D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • v) := by
          show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
          rw [smul_smul, smul_smul, mul_comm]
        rw [e]; exact Submodule.smul_mem _ _ hv
    exact key _ h1
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have := Formalism.L2.SG.Pf.Cnt.DualityBasisChange.gS_ne (D := D); exact_mod_cast this
  have h3 : baseChange₂ D p ((((gS D : ℕ) : D.host.E))⁻¹ • x) ∈ lattice₂ D Zd.M p Λ₂ := by
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact h2
  haveI := p.isPrime
  letI := hlat
  have h4 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ₂) (by infer_instance) _).1 h3
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ₂ _).1 h4
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, fun h => ht (by rw [← hPp]; exact h), ?_⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x =
      ((gS D : ℕ) : 𝓞 D.host.E) • (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • ((((gS D : ℕ) : D.host.E))⁻¹ • x)) := by
    rw [Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.oE_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ₂
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) htx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameZEqLinZu
section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 800000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem frame_fvec (t : TauC Y u u') (b : Fin (D.R.rS + 1)) : t.frame.fl.fvec b = t.lin ((X.Fu u').fvec b) := by
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  show (mapLF t.lin (lf D (X.Fu u'))).fl.fvec b = _
  rw [mapLF_fl hγ, fvec_mapFlag]

theorem frame_z_eq_lin_zu (t : TauC Y u u') : t.frame.fl.z = t.lin (X.Fu u').z := by
  have := frame_fvec Y t (Fin.last _)
  simpa [FlagG.fvec, Fin.snoc_last] using this

theorem mem_frameX (t : TauC Y u u') (x : (VS D).V) : x ∈ t.frame.fl.X ↔ t.lin.symm x ∈ (X.Fu u').X :=
  CorankRelation.mem_Xsp_mapLF t.lin t.rep.2.2.1 (lf D (X.Fu u')) x

theorem omp_terms (t1 t2 : TauC Y u u') (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u'))) (he : t2.lin = σ * t1.lin * s') :
    omp (X.Fu u) t2.frame.fl = σ (omp (X.Fu u) t1.frame.fl) ∧
    Dl (X.Fu u) t2.frame.fl (D.R.rS + 1) = Dl (X.Fu u) t1.frame.fl (D.R.rS + 1) ∧
    omp t2.frame.fl (X.Fu u) = σ (omp t1.frame.fl (X.Fu u)) ∧
    Dl t2.frame.fl (X.Fu u) (D.R.rS + 1) = Dl t1.frame.fl (X.Fu u) (D.R.rS + 1) := by
  have hσ' := SRat_inv (lf D (X.Fu u)) hσ
  obtain ⟨hσi, -, -⟩ := hσ
  obtain ⟨hσi', hσf', hσz'⟩ := hσ'
  obtain ⟨-, hsf, hsz⟩ := hs'
  have hγ1 : t1.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t1.rep.2.2.1
  have hγ2 : σ * t1.lin * s' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := he ▸ t2.rep.2.2.1
  obtain ⟨o1, o2, o3, o4⟩ := omp_coset (X.Fu u) (X.Fu u') σ t1.lin s' hσi hσi' hγ1 hγ2 hσf' hσz' hsf hsz
  have hF1 : t1.frame.fl = mapFlag t1.lin hγ1 (X.Fu u') := mapLF_fl hγ1 (lf D (X.Fu u'))
  have hF2 : ∀ b, t2.frame.fl.fvec b = (mapFlag (σ * t1.lin * s') hγ2 (X.Fu u')).fvec b := fun b => by
    rw [frame_fvec, fvec_mapFlag, he]
  have hrefl : ∀ b, (X.Fu u).fvec b = (X.Fu u).fvec b := fun b => rfl
  obtain ⟨k1, k2⟩ := omp_congr (F := X.Fu u) (G := X.Fu u) hrefl hF2
  obtain ⟨k3, k4⟩ := omp_congr (F := t2.frame.fl) (G := mapFlag (σ * t1.lin * s') hγ2 (X.Fu u')) hF2 hrefl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact k1.trans (o1.trans (congrArg (fun G => σ (omp (X.Fu u) G)) hF1.symm))
  · refine ((det_eq_Dl _ _).symm.trans ?_).trans (det_eq_Dl _ _)
    exact (congrArg Matrix.det k2).trans (o2.trans (congrArg (fun G => (Zhat (X.Fu u) G).det) hF1.symm))
  · exact k3.trans (o3.trans (congrArg (fun G => σ (omp G (X.Fu u))) hF1.symm))
  · refine ((det_eq_Dl _ _).symm.trans ?_).trans (det_eq_Dl _ _)
    exact (congrArg Matrix.det k4).trans (o4.trans (congrArg (fun G => (Zhat G (X.Fu u)).det) hF1.symm))

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsotropicSpanOrthogonalAnisotropicVector
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem hsw' (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem fvec_cs {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (i : Fin D.R.rS) : F.fvec i.castSucc = F.e i := by
  simp [FlagG.fvec]

theorem fvec_last {T : D.host.E} (F : FlagG (VS D) D.R.rS T) : F.fvec (Fin.last D.R.rS) = F.z := by
  simp [FlagG.fvec]

theorem hff {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (F.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [fvec_last, F.z_norm, if_pos ⟨rfl, rfl⟩]
    | cast j =>
      rw [fvec_last, fvec_cs, if_neg (fun h => Fin.castSucc_ne_last j h.2), hsw', F.z_orth, star_zero]
  | cast i =>
    rw [if_neg (fun h => Fin.castSucc_ne_last i h.1)]
    induction b using Fin.lastCases with
    | last => rw [fvec_cs, fvec_last, F.z_orth]
    | cast j => rw [fvec_cs, fvec_cs, F.e_iso]

theorem iso_X {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x y : (VS D).V} (hx : x ∈ F.X) (hy : y ∈ F.X) :
    (VS D).hT x y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply, F.e_iso]

theorem isotropicSpan_orthogonal_anisotropicVector {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ F.X) :
    (VS D).hT x F.z = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply, F.z_orth]

theorem z_orth_X {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ F.X) :
    (VS D).hT F.z x = 0 := by
  rw [hsw', isotropicSpan_orthogonal_anisotropicVector F hx, star_zero]

theorem Xplus_eq {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    F.Xplus = Submodule.span D.host.E (Set.range F.fvec) := by
  apply le_antisymm
  · apply sup_le
    · rw [FlagG.X, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.castSucc, fvec_cs F i⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨Fin.last _, fvec_last F⟩
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    induction a using Fin.lastCases with
    | last => rw [fvec_last]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    | cast i => rw [fvec_cs]; exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRecPos
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem massH_pos {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    0 < massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) := by
  classical
  have hC := Formalism.L2.SG.Pf.MassDataX.classFinite_holds X u
  have hS := MassDataMassesW.stabFinite_of Formalism.L2.SG.Pf.MassDataX.hinfCompact_holds
    Formalism.L2.SG.Pf.MassDataX.kCompactOpen_holds X u
  show 0 < massCl (MassDataMassesW.GamH X u) (MassDataMassesW.KH X u)
  unfold massCl
  haveI := hC
  letI : Fintype (DoubleCoset.Quotient (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (MassDataMassesW.GamH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (MassDataMassesW.KH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))) :=
    Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  apply Finset.sum_pos
  · intro c _
    haveI := hS (Quotient.out c)
    apply inv_pos.mpr
    exact_mod_cast Nat.card_pos
  · exact Finset.univ_nonempty_iff.mpr ⟨Quot.mk _ 1⟩

theorem finrank_Vpi_pos {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : 0 < Module.finrank ℂ (X.Vpi u) := by
  classical
  have hx : ∀ v, ∃ y : X.Vloc u v, y ≠ 0 := fun v => by
    haveI := (X.piLoc_type u v).1
    exact exists_ne 0
  choose x hx using hx
  have hne : X.tensU u x ≠ 0 := by
    intro h0
    have h := X.tensU_inner u x x
    rw [h0, inner_zero_left] at h
    exact (Finset.prod_ne_zero_iff.mpr fun v _ => inner_self_ne_zero.mpr (hx v)) h.symm
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ModSideUL
section
namespace Formalism.L2.SG.LsDatumA

theorem modSide0L : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n false) :=
  Formalism.L2.SG.LocalCountModules.localCountZeroLocal_holds

theorem modSideUL : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n false) :=
  Formalism.L2.SG.LocalCountModules.localCountUnitLocal_holds

end Formalism.L2.SG.LsDatumA
end

