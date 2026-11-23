module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0004
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0005
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Mathlib
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLt
public import Formalism.SharpRestriction.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def DlSize {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps

theorem numsL_wtsL_fam {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) :
    ∃ Cn₀ : ℝ, ∀ Cn ≥ Cn₀, ∀ cL ≥ (3 : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ WtsL (Fm.D x i) (Fm.L x i) Cn :=
  flipTwoThree.nums_wts_of_tuSize Fm hT hDl

theorem factDGam_mono {D : D7} {C C' : ℝ} (h : FactDGam D C) (hC : C ≤ C') : FactDGam D C' := by
  intro u
  refine (h u).trans ?_
  have h1 : (0 : ℝ) ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by
    have : ((D.R.f : ℝ) * D.R.N D.R.m) = ((D.R.f * D.R.N D.R.m : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact Real.log_natCast_nonneg _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) h1
  have := mul_le_mul_of_nonneg_right hC h2
  simp only [mul_assoc] at this ⊢
  exact this

theorem slopes_family_of_column_values {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (h5 : flipTwoThree.ConclusionF5 Fm)
    (h6 : flipTwoThree.ConclusionF6 Fm) (hCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) :
    LocalQuadraticParts.SlopesFamily Fm := by
  obtain ⟨Cn, hN⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨x1, hCV⟩ := hCV
  refine family_orderBound_of_fifth_sixth Fm Cn 3 h5 h6 (by norm_num) ⟨max x0 x1, fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e1 : x ≥ x1 := le_trans (le_max_right _ _) hx
  exact ⟨by linarith [flipTwoThree.two_le_rdE (Fm.D x i).host], (hN x e0 i).1, (hN x e0 i).2, hCV x e1 i⟩

theorem family_levelPrime_summary_simple {eps : ℝ} (Fm : FamP eps) (C C1 : ℝ) (hC1 : 0 ≤ C1)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, product_first_zeroth_parts.Conclusion2 (Fm.D x i) u) ∧ (∀ u, product_first_zeroth_parts.Conclusion5 (Fm.D x i) u C) ∧
      LevelPrimeSizeBounds (Fm.D x i) (Fm.L x i) C1 ∧ ∀ u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨x0, hE⟩ := hE
  refine family_levelPrime_summary Fm C C1 hC1 ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e1 : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx)
  obtain ⟨a, b, c, d⟩ := hE x e0 i
  exact ⟨a, b, locSpan _, lenAtT _ _ (Fm.ex x e1 i).lat.atT, c, d⟩

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSab
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G

variable {D : D7} {L : SizeData₂ D}

theorem four_orbit_conditions_of_proof {X : Inst D L} {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Formalism.MainNotions.OrbitPlaces.Ent D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {sp C : ℝ} (h : Formalism.MainNotions.OrbitPlaces.Conclusion₂ D L X K Dx T E lev Xe ce sp C) :
    Formalism.MainNotions.WeilJacquetShalikaLaw.OrbitsWithoutOperator D L X K Dx T lev Xe ce sp ∧ Formalism.MainNotions.WeilJacquetShalikaLaw.MediumInertPrimeLengthBound D L K Dx T lev Xe ce sp ∧
      Formalism.MainNotions.WeilJacquetShalikaLaw.LossAtDiscriminant D L K Dx T lev Xe ce sp ∧ Formalism.MainNotions.WeilJacquetShalikaLaw.IsotypicPartsInternalDirectSum D Dx T sp := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSv
section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section Ab

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

theorem cc_ph : PowerSeries.constantCoeff g.ph = 0 := by
  rw [Formalism.MainNotions.GL3Theta.G1.ph.eq_1, map_neg, neg_eq_zero]
  show Formalism.MainNotions.GL3Theta.logMv _ 0 = 0
  rw [Formalism.MainNotions.GL3Theta.logMv.eq_1]
  simp

theorem be_ab (i0 : K0 p →+* ℂ_[p]) (be : MvPowerSeries (Fin 2) (K0 p)) (ep : ℂ_[p]) (hep : ep ≠ 0)
    (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    (n : Fin 2 →₀ ℕ) (hn : coeff n be ≠ 0) : 1 ≤ n 0 ∧ 1 ≤ n 1 := by
  classical
  set c : ℂ_[p] := ep⁻¹ with hc
  set ψ : PowerSeries ℂ_[p] :=
    PowerSeries.subst (PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) g.ex) g.ph with hψ
  have hcX : PowerSeries.constantCoeff (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) = 0 := by simp
  have hE : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) g.ex) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hcX _ hex
  have hψ0 : PowerSeries.coeff 0 ψ = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.constantCoeff_subst_eq_zero hE _ (cc_ph g)
  have key : ∀ z : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff z = 0 →
      g.phAt (g.pt (C c * z)) = PowerSeries.subst z ψ := by
    intro z hz
    have hz' := PowerSeries.HasSubst.of_constantCoeff_zero hz
    rw [hψ, PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hE) hz',
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hcX) hz',
      PowerSeries.subst_mul hz', PowerSeries.subst_C, PowerSeries.subst_X hz']
    rfl
  have h0 : ∀ i : Fin 2, constantCoeff (C c * X i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by intro i; simp
  have hB : map i0 be = PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ψ -
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ψ -
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ψ := by
    have h := be_at g i0 be ep hex be_tie (cc_pt g hex (h0 0)) (cc_pt g hex (h0 1))
    rw [lg_pt g hex hinv (h0 0), lg_pt g hex hinv (h0 1)] at h
    have e : (![C ep * (C c * X 0), C ep * (C c * X 1)] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]) = X := by
      funext s
      fin_cases s
      · show C ep * (C c * X 0) = X 0
        rw [← mul_assoc, ← map_mul, hc, mul_inv_cancel₀ hep, map_one, one_mul]
      · show C ep * (C c * X 1) = X 1
        rw [← mul_assoc, ← map_mul, hc, mul_inv_cancel₀ hep, map_one, one_mul]
    rw [e, subst_self] at h
    have h' : map i0 be = g.be (g.pt (C c * X 0)) (g.pt (C c * X 1)) := h
    rw [h']
    unfold G1.be G1.add
    rw [lg_pt g hex hinv (h0 0), lg_pt g hex hinv (h0 1), ← mul_add, key _ (by simp), key _ (by simp),
      key _ (by simp)]
  have hco : i0 (coeff n be) = ((n 0 + n 1).choose (n 0) : ℂ_[p]) * PowerSeries.coeff (n 0 + n 1) ψ -
      (if n = Finsupp.single 0 (n 0) then PowerSeries.coeff (n 0) ψ else 0) -
      (if n = Finsupp.single 1 (n 1) then PowerSeries.coeff (n 1) ψ else 0) := by
    rw [← coeff_map, hB, map_sub, map_sub, PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_single,
      PowerSeries.coeff_subst_single]
  by_contra hcon
  apply hn
  apply i0.injective
  rw [map_zero, hco]
  have hcase : n 0 = 0 ∨ n 1 = 0 := by
    by_contra h
    push Not at h
    exact hcon ⟨Nat.one_le_iff_ne_zero.2 h.1, Nat.one_le_iff_ne_zero.2 h.2⟩
  rcases hcase with h | h
  · have e1 : n = Finsupp.single 1 (n 1) := by
      ext i
      fin_cases i
      · simp [h]
      · simp
    rw [if_pos e1, h, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul]
    split_ifs with h2
    · have : n 1 = 0 := by rw [h2]; simp
      rw [this, hψ0]; ring
    · ring
  · have e1 : n = Finsupp.single 0 (n 0) := by
      ext i
      fin_cases i
      · simp
      · simp [h]
    rw [if_pos e1, h, add_zero, Nat.choose_self, Nat.cast_one, one_mul]
    split_ifs with h2
    · have : n 0 = 0 := by rw [h2]; simp
      rw [this, hψ0]; ring
    · ring

end Ab

variable {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSx
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem sumFE_atG_le {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) (i : Fin 2) (w : D.what₂.places.Pl)
    (hwi : D.what₂.places.resChar w = D.host.g i) (u : D.what₂.Word) (hw : D.what₂.places.resChar w ≠ (D.mem u).A.T) :
    ∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w) ≤
      -(∑ j ∈ Formalism.MainNotions.LiftErrorLocal.lifts D, vNN Xe i u j w) - C1 * Formalism.MainNotions.LiftErrorLocal.errC D L := by
  have hg : D.what₂.places.resChar w ∈ L.gTypes := by
    rw [hwi]
    unfold SizeData₂.gTypes
    fin_cases i <;> simp
  have hFj : ∀ j ∈ SizeData₂.lifts D, L.F j w = FTypeG D j := by
    intro j hj
    rw [hF j hj w]
    exact if_pos hg
  have hEj : ∀ j ∈ SizeData₂.lifts D, L.E u j w = vDG D u w + EatG L Xe ce i u j w := by
    intro j hj
    rw [hE.edef u j hj w]
    unfold Eval vDG
    dsimp only
    rw [if_neg hw]
    fin_cases i
    · have h0 : D.what₂.places.resChar w = D.host.g 0 := hwi
      rw [if_pos h0]
      rfl
    · have h1 : D.what₂.places.resChar w = D.host.g 1 := hwi
      rw [if_neg (by rw [h1]; exact D.host.g_ne.symm), if_pos h1]
      rfl
  have hvD : 0 ≤ vDG D u w := Nat.cast_nonneg _
  set A : ℝ := (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) with hA
  set B : ℝ := (D.R.f : ℝ) * (Nm D * (Nm D + D.R.t) + (D.R.m : ℝ) ^ 2 * L.etaSz) with hB
  have hη := L.etaSz_pos.le
  have hN0 : 0 ≤ Nm D := by unfold Nm; positivity
  have ht : (D.R.t : ℝ) ≤ Nm D := by
    have h1 : D.R.t + 1 ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_left _ (by have := D.R.two_le_m; omega)
    have h2 : D.R.t ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    unfold Nm
    exact_mod_cast h2
  have hA0 : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hη))
  have hBA : B ≤ 2 * A := by
    have h3 : Nm D * (Nm D + D.R.t) + (D.R.m : ℝ) ^ 2 * L.etaSz ≤ 2 * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) := by
      nlinarith [mul_le_mul_of_nonneg_left ht hN0, mul_nonneg (sq_nonneg (D.R.m : ℝ)) hη]
    have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg D.R.f : (0 : ℝ) ≤ (D.R.f : ℝ))
    rw [hA, hB]
    linarith
  have hcard : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by
    unfold SizeData₂.lifts
    simp
  have hsum : ∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w) =
      -(∑ j ∈ SizeData₂.lifts D, vNN Xe i u j w) - (D.R.m : ℝ) * (ce.g * A) - (D.R.m : ℝ) * vDG D u w := by
    have : ∀ j ∈ SizeData₂.lifts D, L.F j w - L.E u j w = -vNN Xe i u j w - (ce.g * A + vDG D u w) := by
      intro j hj
      rw [hFj j hj, hEj j hj]
      unfold EatG
      rw [hA]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul,
      hcard]
    ring
  have hEr : Formalism.MainNotions.LiftErrorLocal.errC D L = (D.R.m : ℝ) * B := by
    unfold Formalism.MainNotions.LiftErrorLocal.errC
    rw [hB]
    unfold Nm
    ring
  have hl : Formalism.MainNotions.LiftErrorLocal.lifts D = SizeData₂.lifts D := rfl
  rw [hEr, hl, hsum]
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have h1 : C1 * ((D.R.m : ℝ) * B) ≤ (D.R.m : ℝ) * (ce.g * A) := by
    have h5 : C1 * ((D.R.m : ℝ) * B) ≤ C1 * ((D.R.m : ℝ) * (2 * A)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBA hm0) hC1
    have h6 : (2 * C1) * ((D.R.m : ℝ) * A) ≤ ce.g * ((D.R.m : ℝ) * A) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg hm0 hA0)
    nlinarith
  have h2 : 0 ≤ (D.R.m : ℝ) * vDG D u w := mul_nonneg hm0 hvD
  linarith

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
section
noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.BasicNotions

theorem finrank_F_eq (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  exact D.host.der.finrank_F

theorem splitsF_g (D : D7) (i : Fin 2) : StandardLattice.SplitsF D (D.host.g i) := by
  have h := splits_sub D.host.F (D.host.g i) D.host.E (D.host.g_prime i) (D.nd.g_split i)
  rw [finrank_F_eq] at h
  exact h

theorem idxColTie_holds (D : D7) : IdxColTie D := idxColTie_of D (splitsF_g D)

theorem idxRowTie_holds (D : D7) : IdxRowTie D := idxRowTie_of D (splitsF_g D)

end Formalism.MainNotions.J

end
end

