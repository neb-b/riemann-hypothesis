module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0019
public import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0010
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0017
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LvlDimCondition
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem preF_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : preF (p := p) (r := r) G j jp ≠ 0 := by
  classical
  obtain ⟨s, hs1, hs2⟩ := Formalism.GM.M.good_pre (p := p) (r := r) G j jp
  have hpre : Formalism.GM.M.pre (p := p) (r := r) G j jp ≠ 0 := by
    intro h0
    rw [h0, zero_sub] at hs2
    have hmem : s ∈ (-(monomial s (1 : ℚ_[p]))).support := by
      rw [support_neg, support_monomial, if_neg one_ne_zero]
      exact Finset.mem_singleton_self s
    exact (hs2 s hmem).2 hs1
  have e : preF (p := p) (r := r) G j jp =
      Formalism.GM.M.pre (p := p) (r := r) G j jp * monomial (Formalism.GM.M.zmS G) 1 := by
    rw [← Formalism.GM.M.zmon_eq]
    unfold preF Formalism.GM.M.pre
    ring
  rw [e]
  exact mul_ne_zero hpre (by rw [Ne, monomial_eq_zero]; exact one_ne_zero)

theorem den_Y (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∀ y ∈ Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr, ∃ c : ℤ_[p], c ≠ 0 ∧
      ((c : ℚ_[p]) • y) ∈ Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr := by
  intro y hy
  obtain ⟨k, hk⟩ := Formalism.GM.TM.exists_pow_smul_intPol (p := p) y
  refine ⟨(p : ℤ_[p]) ^ k, pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero), ?_⟩
  have e : (((p : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k := by push_cast; rfl
  rw [e]
  refine ⟨Submodule.smul_mem _ _ hy, ?_, hk⟩
  exact Submodule.smul_mem _ _ ((inf_le_left : Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr ≤ _) hy)

theorem xiMons_free (n : ℕ) : ∀ β ∈ xiMons (r := r) G n, ∀ x, β (Formalism.GM.M.chainEmb N r G.T.t x) = 0 := by
  intro β hβ x
  by_contra h
  have hmem : Formalism.GM.M.chainEmb N r G.T.t x ∈ β.support := Finsupp.mem_support_iff.2 h
  obtain ⟨c, hc⟩ := (xiMons_spec G n β hβ).1 _ hmem
  simp only [Formalism.GM.M.chainEmb, Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hc
  exact Fin.castSucc_ne_last _ hc.1

theorem xiMons_mem (n : ℕ) : ∀ β ∈ xiMons (r := r) G n, (monomial β (1 : ℚ_[p])) ∈ Formalism.GM.M.XiPolZ p N r G.T.t n := by
  classical
  intro β hβ
  obtain ⟨h1, h2, -⟩ := xiMons_spec G n β hβ
  refine ⟨?_, Formalism.GM.M.intPol_monomial' β⟩
  show monomial β (1 : ℚ_[p]) ∈ MvPolynomial.restrictSupport ℚ_[p] _
  rw [MvPolynomial.mem_restrictSupport_iff, support_monomial, if_neg one_ne_zero]
  intro m hm
  rw [Finset.coe_singleton, Set.mem_singleton_iff] at hm
  subst hm
  exact ⟨h1, h2⟩

end Gen

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

set_option maxHeartbeats 800000 in
theorem lvlDimCondition : RestLvlDim C0 CE1 CE2 X := by
  classical
  intro aTop _ aPlus _ b _ x hx
  have hL : (gB C0 CE1 CE2 X aTop aPlus b).LevelOK x.1 x.2 := by
    unfold lv levels at hx
    exact (Finset.mem_filter.1 hx).2
  have hfd : FiniteDimensional ℚ_[X.p]
      (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2)) := by
    have h1 := span_SSZ_fin C0 CE1 CE2 X aTop aPlus b
    have hle : Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2) ≤
        Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :=
      Submodule.span_le.2 fun y hy => Submodule.subset_span
        (Formalism.GM.M.gens_mem_SSZ (p := X.p) (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) x.1 x.2 hL y hy)
    exact Submodule.finiteDimensional_of_le hle
  exact lvlDim_gen (gB C0 CE1 CE2 X aTop aPlus b) x.1 x.2 (preF_ne_zero _ _ _) (den_Y _ _ _) hfd
    (xiMons_free _ _) (xiMons_mem _ _)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ThresholdsMonoNormalized
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem thresholds_mono_normalized {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 1 ≤ C0 → 2 ≤ CYb → 0 ≤ CD → 1 ≤ Cb → 0 ≤ CE1 → 0 ≤ CE2 →
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : TransportedAlt P) : TransportedAlt Q := by
  unfold Formalism.MainNotions.flipOneThree.TransportedAlt at hP ⊢
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨max T0 1, lt_max_of_lt_left hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 (le_trans (le_max_left _ _) hC0)
  refine ⟨T1, hT1, fun CE1 CE2 hE1 hE2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 hE1 hE2
  refine ⟨max T2 2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb hY hde hk hD hb => ?_⟩
  have hT2' : T2 ≤ max T2 2 := le_max_left _ _
  have h2' : (2 : ℝ) ≤ max T2 2 := le_max_right _ _
  have h1' : (1 : ℝ) ≤ max T0 1 := le_max_right _ _
  exact h C0 CYb Cde Ck CD Cb CE1 CE2 Cc (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
    (h2 CYb Cde Ck CD Cb (hT2'.trans hY) (hT2'.trans hde) (hT2'.trans hk) (hT2'.trans hD) (hT2'.trans hb))

def RestOpen4 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestPlusA C0 CE1 CE2 X CM ∧ RestPlusB C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpen4E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen4 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem openE_of_open4 (D : Formalism.BasicNotions.D7) (h : RestOpen4E D) : RestOpenE D := by
  obtain ⟨CM, hCM, hTM⟩ := restTM_closed
  exact thresholds_mono_normalized (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hC0 hY hD hb h1 h2 hP Ckap Cs =>
    ⟨CM, by linarith, fun X hA hH => by
      obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
      have hY0 : (0 : ℝ) < X.L.Y := by linarith [hH.1.1]
      exact ⟨block_bound_of_dual_families C0 CE1 CE2 X (block_valuation_over_Zp_holds C0 CE1 CE2 X (by linarith) h1 h2 hH) a,
        restPlus_of CM hY0 b (restRankL_proved C0 CE1 CE2 X) c,
        hTM D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hY hb hD hC0 h1 h2 hH, d⟩⟩) h

theorem closed_of_open_directions (D : Formalism.BasicNotions.D7) (h : RestOpen4E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_conditions D (openE_of_open4 D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

