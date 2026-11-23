module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0030
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0027
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0018
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0008
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0024

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnEndo
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem endo_curve (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    ∃ neg : S → S, C.IsEndoCurve (A.shortW (ι L.g₂) (ι L.g₃)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ))) (fun P : S => ι (L.derivWeierstrassP (P : ℂ)) / 2)
      (ι α) := by
  obtain ⟨neg, hneg, hinv, -, hid⟩ := F.endoZInstance L α S hα hst hS
  have hb2 : (A.shortW (ι L.g₂) (ι L.g₃)).b₂ = 0 := by
    simp [A.shortW, WeierstrassCurve.b₂]
  have hnegeq : ∀ P : S, (neg P : ℂ) = -(P : ℂ) + ((⟨_, hneg P⟩ : L.lattice) : ℂ) := by
    intro P
    simp
  refine ⟨neg, ?_, hinv, ?_, ?_⟩
  · intro P
    have h := L.derivWeierstrassP_sq (P : ℂ) (hS.1 P P.2).2
    have h' := congrArg ι h
    simp only [map_pow, map_sub, map_mul, map_ofNat] at h'
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [A.shortW]
    linear_combination (1 / 4 : ℂ_[l]) * h'
  · intro P
    constructor
    · show ι (L.weierstrassP (neg P : ℂ)) = _
      rw [hnegeq P, L.weierstrassP_add_coe, L.weierstrassP_neg]
    · show ι (L.derivWeierstrassP (neg P : ℂ)) / 2 = _
      rw [hnegeq P, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_neg]
      simp [WeierstrassCurve.Affine.negY, A.shortW, neg_div]
  · have h := congrArg (PowerSeries.map (ι : ℂ →+* ℂ_[l])) hid
    rw [wp_bridge]
    simp only [C.wTr, hb2, zero_div, add_zero, map_zero]
    simp only [← trans_bridge l L ι _ (hS.1 _ (Subtype.coe_prop _)).2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_add (f := _), map_sum, map_sub, PowerSeries.map_C, map_pow] at h
    have hr : PowerSeries.map (ι : ℂ →+* ℂ_[l]) (PowerSeries.rescale α (F.pSeries L))
        = PowerSeries.rescale (ι α) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L)) := by
      ext n
      simp [PowerSeries.coeff_rescale]
    rw [hr] at h
    simpa using h

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgIsoU
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem exists_powerSeries_square_formula {K : Type} [Field K] [CharZero K] (R : Subring K) (M a ph G : PowerSeries K)
    (c : ℕ) (m : K) (ha : constantCoeff a = 0) (hph : constantCoeff ph = 0)
    (hc : (c : K) + 1 = m)
    (hiso : M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c) =
      G * X ^ (2 * (c + 1)) * C.mvExp (-((2 * ((c : K) + 1)) • ph)))
    (hcong : C.Cong R a (m • ph)) :
    ∃ U : PowerSeries K, constantCoeff U = 1 ∧ C.IntPS R U ∧ M ^ 2 = X ^ 2 * U * G := by
  obtain ⟨h0, h1, hadd, -⟩ := C.mvExpLaws K Unit
  obtain ⟨-, hLadd, -⟩ := C.lGSubgroup K R Unit
  have hD : C.LG R ((a - m • ph) + (a - m • ph)) := hLadd _ _ hcong hcong
  have ha' : MvPowerSeries.constantCoeff a = 0 := ha
  have hph' : MvPowerSeries.constantCoeff ph = 0 := hph
  have c1 : MvPowerSeries.constantCoeff (-((2 : K) • a)) = 0 := by
    rw [map_neg, MvPowerSeries.smul_eq_C_mul, map_mul, ha', mul_zero, neg_zero]
  have c2 : MvPowerSeries.constantCoeff ((2 : K) • a) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, ha', mul_zero]
  have c3 : MvPowerSeries.constantCoeff (-((2 * ((c : K) + 1)) • ph)) = 0 := by
    rw [map_neg, MvPowerSeries.smul_eq_C_mul, map_mul, hph', mul_zero, neg_zero]
  refine ⟨C.mvExp ((a - m • ph) + (a - m • ph)), h1 _ hD.1, fun n => hD.2 _, ?_⟩
  have e1 : C.mvExp (-((2 : K) • a)) * C.mvExp ((2 : K) • a) = 1 := by
    rw [← hadd _ _ c1 c2, neg_add_cancel, h0]
  have e2 : C.mvExp (-((2 * ((c : K) + 1)) • ph)) * C.mvExp ((2 : K) • a)
      = C.mvExp ((a - m • ph) + (a - m • ph)) := by
    rw [← hadd _ _ c3 c2, hc]
    congr 1
    rw [mul_smul, two_smul, two_smul]
    abel
  have hX : (X : PowerSeries K) ^ (2 * c) ≠ 0 := pow_ne_zero _ X_ne_zero
  apply mul_right_cancel₀ hX
  calc M ^ 2 * X ^ (2 * c)
      = (M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c)) * C.mvExp ((2 : K) • a) := by
        rw [show M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c) * C.mvExp ((2 : K) • a)
          = M ^ 2 * X ^ (2 * c) * (C.mvExp (-((2 : K) • a)) * C.mvExp ((2 : K) • a)) by ring,
          e1, mul_one]
    _ = G * X ^ (2 * (c + 1)) *
          (C.mvExp (-((2 * ((c : K) + 1)) • ph)) * C.mvExp ((2 : K) • a)) := by
        rw [hiso]; ring
    _ = X ^ 2 * C.mvExp ((a - m • ph) + (a - m • ph)) * G * X ^ (2 * c) := by
        rw [e2]; ring

theorem sq_formula (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (n : ℕ) (hn : 0 < n) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) :
    ∃ U : PowerSeries ℂ_[l], constantCoeff U = 1 ∧ IntegralPS U ∧
      ((uSer g2 g3).subst (C (n : ℂ_[l]) * lgS g2 g3)) ^ 2 =
        X ^ 2 * U * (C ((n : ℂ_[l]) ^ 2) *
          ∏ P ∈ S, (A.xS (A.shortW g2 g3) - C (ι (L.weierstrassP P)) * X ^ 2)) := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have : ¬ l ∣ 2 := fun hd => hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
    exact_mod_cast norm_natCast_Cl_of_not_dvd l this
  have h2R : (2 : ℂ_[l])⁻¹ ∈ unitBall ℂ_[l] := by
    change ‖(2 : ℂ_[l])⁻¹‖ ≤ 1
    rw [norm_inv, h2, inv_one]
  have h4 : ‖(4 : ℂ_[l])‖ = 1 := by
    have : (4 : ℂ_[l]) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  set W := A.shortW g2 g3 with hW
  have hco : C.CoeffIn (unitBall ℂ_[l]) W := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (unitBall ℂ_[l]).zero_mem
    · exact (unitBall ℂ_[l]).zero_mem
    · exact (unitBall ℂ_[l]).zero_mem
    · change ‖-g2 / 4‖ ≤ 1
      rw [norm_div, norm_neg, h4, div_one]; exact hM.n2
    · change ‖-g3 / 4‖ ≤ 1
      rw [norm_div, norm_neg, h4, div_one]; exact hM.n3
  have hb2 : W.b₂ / 12 = 0 := by
    rw [(A.shortInv ℂ_[l] g2 g3).1, zero_div]
  obtain ⟨hLP, hXW, -, hFG, -⟩ := C.curveFrame ℂ_[l] (unitBall ℂ_[l]) W hco
  set s2 : ℂ_[l] := ι (F.s2 L) with hs2
  set ph := B.phO s2 (A.wpReg W) (A.logSer W) with hph
  have hPh : C.IsPh (A.wpReg W) s2 (A.logSer W) ph :=
    (C.phOIsPh ℂ_[l] (A.wpReg W) (A.logSer W) s2 hLP.1 hLP.2.1).2
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hst : F.MulStable L (n : ℂ) := by
    intro ω hω
    have := L.lattice.nsmul_mem hω n
    rwa [nsmul_eq_mul] at this
  have hIF := iso_formula l L ι (n : ℂ) S hn0 hst hS
  rw [← hM.eq2, ← hM.eq3, map_natCast] at hIF
  have hcard : ((Fintype.card S : ℕ) : ℂ_[l]) + 1 = (n : ℂ_[l]) * (n : ℂ_[l]) := by
    have h := F.kerRepsCard L (n : ℂ) S hn0 hst hS
    rw [Complex.normSq_natCast] at h
    have h' : S.card + 1 = n * n := by exact_mod_cast h
    rw [Fintype.card_coe]
    exact_mod_cast h'
  have hU := C.isogenyU ℂ_[l] (A.wpReg W) s2 (A.logSer W) (A.expSer W) ph (A.xS W) (W.b₂ / 12) S
    (fun P : S => ι (L.weierstrassP (P : ℂ))) (n : ℂ_[l]) hLP hPh hXW
    (by simpa only [hb2, add_zero] using hIF)
  have hFr : C.Frame (unitBall ℂ_[l]) (A.logSer W) (A.expSer W) ph := ⟨hLP, hFG, hPh.1⟩
  have hN := phNorm_int (unitBall ℂ_[l]) (A.logSer W) (A.expSer W) ph hFr
    (G.weierstrass_biadditive_mod_equiv ℂ_[l] W hco h2 s2) (G.curveNegNorm ℂ_[l] (unitBall ℂ_[l]) W hco h2R s2) h2R (n : ℤ)
  rw [Int.cast_natCast] at hN
  have hMul : (uSer g2 g3).subst (C (n : ℂ_[l]) * lgS g2 g3)
      = C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l]) := by
    rw [lgS_eq_logSer, A.uSerEq ℂ_[l] g2 g3]; rfl
  have hM0 : constantCoeff (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) = 0 := by
    rw [← hMul]; exact mult_const g2 g3 _
  have ha : constantCoeff (PowerSeries.subst (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) ph) = 0 :=
    constantCoeff_subst_eq_zero hM0 _ hPh.1
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_powerSeries_square_formula (unitBall ℂ_[l])
    (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l]))
    (PowerSeries.subst (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) ph) ph
    (C ((n : ℂ_[l]) ^ 2) * ∏ P : S, (A.xS W - C (ι (L.weierstrassP (P : ℂ))) * X ^ 2))
    (Fintype.card S) ((n : ℂ_[l]) * (n : ℂ_[l])) ha hPh.1 hcard
    (by rw [hU]; ring) hN
  refine ⟨U, hU1, hU2, ?_⟩
  rw [hMul, hU3, Finset.prod_coe_sort S
    (fun P => A.xS W - C (ι (L.weierstrassP P)) * X ^ 2)]

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKur
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

variable (l : ℕ) [Fact l.Prime]

theorem red_norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := norm_l_Cl l

theorem red_norm_natCast {n : ℕ} (h : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 :=
  norm_natCast_Cl_of_not_dvd l h

theorem kur_val {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) : ∃ m : ℤ, ‖x‖ = (l : ℝ) ^ m := by
  obtain ⟨y, hy, hd⟩ := kur_approx l hx ‖x‖ (norm_pos_iff.2 h0)
  have h2 : ‖x‖ = ‖y‖ :=
    norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hd (le_max_left _ _))
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact h0 (norm_eq_zero.1 h2)
  obtain ⟨m, a, -, b, -, ha, hb, e⟩ := kmu_shape l hy hy0
  refine ⟨-m, ?_⟩
  rw [h2, e, norm_mul, norm_div, ha, hb, div_one, mul_one, norm_zpow, norm_l_Cl, inv_zpow, zpow_neg]

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKurOmega
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem redOmegaK_quad (d m : ℕ) (hm : d + 1 = 4 * m) : omegaK d ^ 2 - omegaK d + (m : ℂ) = 0 := by
  have hs : (((Real.sqrt d : ℝ) : ℂ)) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hm' : (d : ℂ) + 1 = 4 * (m : ℂ) := by exact_mod_cast hm
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold omegaK
  have : ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) ^ 2 - (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2
      + (m : ℂ) = (Complex.I ^ 2 * (((Real.sqrt d : ℝ) : ℂ)) ^ 2 - 1 + 4 * (m : ℂ)) / 4 := by ring
  rw [this, hI, hs, ← hm']
  ring

theorem omega_mem_kur (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (l : ℕ) [Fact l.Prime] (hld : ¬ l ∣ d)
    (ι : ℂ ≃+* ℂ_[l]) : ι (omegaK d) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  set w : ℂ_[l] := ι (omegaK d) with hw
  have hq : w ^ 2 - w + (m : ℂ_[l]) = 0 := by
    have := congrArg ι (redOmegaK_quad d m hm)
    simpa using this
  have hm1 : ‖(m : ℂ_[l])‖ ≤ 1 := by
    rw [norm_natCast_Cl]
    exact Padic.norm_int_le_one (m : ℤ)
  have hd1 : ‖(d : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd l hld
  have hw1 : ‖w‖ ≤ 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have h1 : ‖w - 1‖ = ‖w‖ := by
      have hne : ‖w‖ ≠ ‖(-1 : ℂ_[l])‖ := by rw [norm_neg, norm_one]; exact hgt.ne'
      rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_one]
      exact max_eq_left hgt.le
    have h2 : w * (w - 1) = -(m : ℂ_[l]) := by linear_combination hq
    have h3 : ‖w‖ * ‖w‖ ≤ 1 := by
      have := congrArg norm h2
      rw [norm_mul, h1, norm_neg] at this
      rw [this]; exact hm1
    nlinarith
  have hder : ‖2 * w - 1‖ = 1 := by
    have h2 : (2 * w - 1) ^ 2 = -(d : ℂ_[l]) := by
      have hm' : (d : ℂ_[l]) + 1 = 4 * (m : ℂ_[l]) := by exact_mod_cast hm
      linear_combination 4 * hq + hm'
    have h3 : ‖2 * w - 1‖ ^ 2 = 1 := by rw [← norm_pow, h2, norm_neg, hd1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h3
  have hco : ∀ i, (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l]) : Polynomial ℂ_[l]).coeff i =
      (if i = 2 then 1 else 0) - (if 1 = i then 1 else 0) + (if i = 0 then (m : ℂ_[l]) else 0) := fun i => by
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_X]
  refine hensel_mem l (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l])) ?_ ?_ w hw1 ?_ ?_
  · intro i
    rw [hco]
    refine (MaximalUnramifiedExtension l).add_mem ((MaximalUnramifiedExtension l).sub_mem ?_ ?_) ?_
    · split_ifs
      · exact (MaximalUnramifiedExtension l).one_mem
      · exact (MaximalUnramifiedExtension l).zero_mem
    · split_ifs
      · exact (MaximalUnramifiedExtension l).one_mem
      · exact (MaximalUnramifiedExtension l).zero_mem
    · split_ifs
      · exact natCast_mem (MaximalUnramifiedExtension l) m
      · exact (MaximalUnramifiedExtension l).zero_mem
  · intro i
    rw [hco]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((norm_sub_le_max_Cl l _ _).trans (max_le ?_ ?_)) ?_)
    · split_ifs <;> simp
    · split_ifs <;> simp
    · split_ifs
      · exact hm1
      · simp
  · simpa using hq
  · have hd : (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l]) : Polynomial ℂ_[l]).derivative.eval w
        = 2 * w - 1 := by
      simp
      left; norm_num
    rw [hd, hder]

end ReciprocityTheory.ChartRestriction.L1
end
end

