module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReduced
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.IdealLattice

open scoped MatrixGroups UpperHalfPlane

theorem wK_mul_mem (D : D7) (c : Ideal (𝓞 D.host.K)) (x : ℂ) :
    ∀ z ∈ lamOf D c x, ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * z ∈ lamOf D c x := by
  intro z hz
  obtain ⟨o, ho⟩ := (GlobalTheory.MomDict.inOK_iff D ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2)).1
    ⟨0, 1, by simp [GlobalTheory.MomOne.wK]⟩
  obtain ⟨a, ha, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D c x z).1 hz
  refine (GlobalTheory.CurveLattice.mem_lamOf D c x _).2 ⟨o * a, c.mul_mem_left o ha, ?_⟩
  rw [ho]; simp; ring

theorem exists_reduced {Λ : AddSubgroup ℂ} {b : ℂ} {τ₀ : ℍ} (hb : b ≠ 0)
    (h : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, b * (m * (τ₀ : ℂ) + n) = z) :
    ∃ ω₁ : ℂ, ∃ τ : ℍ, ω₁ ≠ 0 ∧ τ ∈ ModularGroup.fd ∧ JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ τ := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ₀
  set A : ℤ := g 0 0 with hA
  set B : ℤ := g 0 1 with hB
  set C : ℤ := g 1 0 with hC
  set E : ℤ := g 1 1 with hE
  have hdet : A * E - B * C = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hdetC : (A : ℂ) * E - B * C = 1 := by exact_mod_cast hdet
  have hco : ((g • τ₀ : ℍ) : ℂ) = (A * τ₀ + B) / (C * τ₀ + E) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [A, B, C, E]
  have hden : (C * (τ₀ : ℂ) + E) ≠ 0 := by
    intro h0
    have := (g • τ₀).im_pos
    rw [← UpperHalfPlane.coe_im, hco, h0, div_zero] at this
    simp at this
  refine ⟨b * (C * τ₀ + E), g • τ₀, mul_ne_zero hb hden, hg, fun z => ?_⟩
  rw [h, hco]
  have key : ∀ m n : ℂ, (C * (τ₀ : ℂ) + E) * (m + n * ((A * τ₀ + B) / (C * τ₀ + E))) =
      m * (C * τ₀ + E) + n * (A * τ₀ + B) := fun m n => by
    field_simp
  constructor
  · rintro ⟨M, N, rfl⟩
    refine ⟨N * A - M * B, M * E - N * C, ?_⟩
    rw [mul_assoc, key]
    push_cast
    linear_combination (-b * (M * (τ₀ : ℂ) + N)) * hdetC
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * C + n * A, m * E + n * B, ?_⟩
    rw [mul_assoc, key]
    push_cast
    ring

theorem main : ∀ (D : D7) (c : Ideal (𝓞 D.host.K)), c ≠ ⊥ → ∀ x : ℂ, x ≠ 0 →
    (∀ z ∈ lamOf D c x, ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * z ∈ lamOf D c x) ∧
    ∃ ω₁ τ : ℂ, ω₁ ≠ 0 ∧ 0 < τ.im ∧ JacobiThetaHalfCharacteristic.IsPeriodLattice (lamOf D c x) ω₁ τ ∧
      1 / 2 ≤ τ.im ∧ 2 * τ.im ≤ Real.sqrt D.host.d := by
  intro D c hc x hx
  have hst := wK_mul_mem D c x
  refine ⟨hst, ?_⟩
  obtain ⟨a, τ₀, ha, -, hlat⟩ := GlobalTheory.CurveLattice.exists_tau D c hc
  obtain ⟨ω₁, τ, hω, hfd, hper⟩ := exists_reduced (Λ := lamOf D c x) (b := x * a) (τ₀ := τ₀)
    (mul_ne_zero hx ha) (hlat x)
  have him : 0 < (τ : ℂ).im := τ.im_pos
  have him' : 0 < τ.im := τ.im_pos
  have hci : (τ : ℂ).im = τ.im := rfl
  refine ⟨ω₁, τ, hω, him, hper, ?_, ?_⟩
  · have h1 := hfd.1
    have h2 := hfd.2
    rw [Complex.normSq_apply] at h1
    have hre : ((τ : ℂ).re) ^ 2 ≤ 1 / 4 := by
      have := abs_le.1 h2
      simp only [UpperHalfPlane.re] at this
      nlinarith [this.1, this.2]
    nlinarith
  · have hmem : ω₁ ∈ lamOf D c x := (hper ω₁).2 ⟨1, 0, by simp⟩
    obtain ⟨m, n, hmn⟩ := (hper _).1 (hst ω₁ hmem)
    have hw : (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = (m : ℂ) + n * τ := by
      have := hmn
      rw [mul_comm] at this
      exact mul_left_cancel₀ hω (by rw [← this])
    have him2 := congrArg Complex.im hw
    simp at him2
    have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    have hn : (0 : ℝ) < n := by
      by_contra hn
      have hn' : (n : ℝ) ≤ 0 := le_of_not_gt hn
      nlinarith
    have hn1 : (1 : ℝ) ≤ n := by
      have : (0 : ℤ) < n := by exact_mod_cast hn
      exact_mod_cast this
    rw [hci]
    nlinarith

end GlobalTheory.IdealLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceRowWeightRatioAndLastCloudLeTwiceF
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rpow_mul_X'_le_b (eps c : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    s.x ^ c * s.X' ≤ s.b ∧ s.x ^ 10 ≤ s.X' := by
  obtain ⟨x0, h0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps c 1 1 0 (by positivity)
    (by linarith) one_pos
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) 10 0 1 0 le_rfl
    (by linarith) one_pos
  refine ⟨max x0 x1, fun s hs hx => ?_⟩
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have h2 := h0 s.x ((le_max_left _ _).trans hx)
  have h3 := h1 s.x ((le_max_right _ _).trans hx)
  rw [← hs] at h2 h3
  simp only [pow_zero, one_mul, mul_one, zero_mul, add_zero] at h2 h3
  constructor
  · rw [Real.rpow_def_of_pos hx0, Scale.X', Scale.b, Scale.L, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · have e : s.x ^ 10 = Real.exp (10 * Real.log s.x) := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
    rw [e, Scale.X']
    exact Real.exp_le_exp.2 h3

theorem szRow_size_ratio : SzRow (fun C D L => (∀ j j' τ τ', 1 ≤ j → j ≤ D.R.m → 1 ≤ j' → j' ≤ D.R.m → wj D j τ ≤ L.sc.X'' D.R.n * wj D j' τ') ∧ (∀ τ (hm : 0 < D.R.m), (D.hc τ).b ⟨D.R.m - 1, by omega⟩ ≤ 2 * (D.hc τ).b ⟨0, hm⟩)) := by
  intro eps he he' C hC
  obtain ⟨CN, x1, hLa⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, hx2'⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps 1 (2 * C.GK.La * CN ^ 2) 2 (by linarith)
  have hK : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  refine ⟨0, fun cD _ => ⟨0, fun ch hch => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := rpow_mul_X'_le_b eps (ch + 9) he
  refine ⟨max (max x0 x1) (max x2 2), fun D L hs hx hV => ?_⟩
  have hxa : x0 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxb : x1 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxc : x2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2 : 2 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hxp : 0 < L.sc.x := by linarith
  obtain ⟨⟨hn0, hn⟩, hm, -⟩ := rankVal_crude L.sc D.R hx2 hV.ranks
  obtain ⟨hb, hX⟩ := hx0 L.sc hs hxa
  have hLa1 : L.LaG ≤ L.sc.x := by
    have h1 := ((hLa L.sc hs hxb).2.2 C.GK hK).2
    have h2 := hx2' L.sc.x hxc
    rw [Real.rpow_one, ← hs] at h2
    rw [hV.La_eq]
    refine h1.trans (le_trans (le_of_eq ?_) h2)
    ring
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 0 < D.R.n := by exact_mod_cast hn0
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k :=
    le_trans (Real.one_le_rpow hx1 (by have := L.sc.eps_pos; linarith)) hV.ranks.2.2.1.1
  have hX0 : 0 < L.sc.X' := Real.exp_pos _
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have eb' : L.sc.b' = L.sc.x * (L.sc.b / L.sc.X') := by rw [Scale.b', Scale.a]; ring
  have ew : L.sc.w'' D.R.n = (L.sc.b / L.sc.X') / D.R.n := by
    rw [Scale.w'', Scale.b', Scale.a]; field_simp
  have hq0 : 0 < L.sc.b / L.sc.X' := div_pos hb0 hX0
  have hb'0 : 0 < L.sc.b' := by rw [eb']; positivity
  have hw0 : 0 < L.sc.w'' D.R.n := by rw [ew]; positivity
  have hwb' : L.sc.w'' D.R.n ≤ L.sc.b' := by
    rw [ew, eb']
    exact (div_le_self hq0.le hn1).trans (le_mul_of_one_le_left hq0.le hx1)
  have h8 : (8 : ℝ) ≤ L.sc.x ^ 3 := by
    have : (2 : ℝ) ^ 3 ≤ L.sc.x ^ 3 := by gcongr
    linarith
  have h6 : (1 : ℝ) ≤ L.sc.x ^ 6 := one_le_pow₀ hx1
  have hb'b : 8 * (L.sc.x ^ 6 * L.sc.b') ≤ L.sc.b := by
    have h1 : L.sc.x ^ 10 * (L.sc.b / L.sc.X') ≤ L.sc.X' * (L.sc.b / L.sc.X') := by gcongr
    have h2 : L.sc.X' * (L.sc.b / L.sc.X') = L.sc.b := by field_simp
    rw [eb']
    calc 8 * (L.sc.x ^ 6 * (L.sc.x * (L.sc.b / L.sc.X')))
        ≤ L.sc.x ^ 3 * (L.sc.x ^ 6 * (L.sc.x * (L.sc.b / L.sc.X'))) := by gcongr
      _ = L.sc.x ^ 10 * (L.sc.b / L.sc.X') := by ring
      _ ≤ L.sc.b := h1.trans h2.le
  have hb'6 : L.sc.b' ≤ L.sc.x ^ 6 * L.sc.b' := le_mul_of_one_le_left hb'0.le h6
  have heta : L.etaSz + 1 ≤ L.sc.w'' D.R.n := by
    have hy : 1 ≤ L.sc.x ^ ch := Real.one_le_rpow hx1 hch
    have h1 : (⌈L.sc.x ^ ch⌉₊ : ℝ) ≤ 2 * L.sc.x ^ ch := by
      have := (Nat.ceil_lt_add_one (a := L.sc.x ^ ch) (by linarith)).le
      linarith
    have h2 : L.etaSz ≤ L.sc.x ^ 2 * (2 * (2 * L.sc.x ^ ch)) := by
      rw [hV.eta_eq, h0v]
      push_cast
      gcongr
    have h3 : 1 ≤ L.sc.x ^ 2 * L.sc.x ^ ch := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) hy
    have h4 : L.sc.x ^ (ch + 9) = L.sc.x ^ 3 * (L.sc.x ^ 2 * L.sc.x ^ ch) * L.sc.x ^ 4 := by
      rw [Real.rpow_add hxp, show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [ew, le_div_iff₀ hn0, le_div_iff₀ hX0]
    refine le_trans ?_ hb
    rw [h4]
    have h5 : L.etaSz + 1 ≤ 8 * (L.sc.x ^ 2 * L.sc.x ^ ch) := by linarith
    have h7 : 8 * (L.sc.x ^ 2 * L.sc.x ^ ch) ≤ L.sc.x ^ 3 * (L.sc.x ^ 2 * L.sc.x ^ ch) := by gcongr
    have h9 := h5.trans h7
    have := L.etaSz_pos
    gcongr
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + 2 * (L.sc.x ^ 6 * L.sc.b') := by
    intro t
    refine (hV.bT_le t).trans ?_
    have d1 : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by have := L.sc.eps_pos; linarith)
    have d0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hxp.le _
    have e1 : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 (show L.sc.eps ≤ 1 by have := L.sc.eps_lt; linarith)
      rwa [Real.rpow_one] at this
    have e0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hxp.le _
    have h1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
        2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' / (D.R.k : ℝ) := by gcongr
    have h2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' / (D.R.k : ℝ) ≤
        2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' :=
      div_le_self (by positivity) hk1
    have h3 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' ≤
        2 * L.sc.x ^ 4 * 1 * L.sc.x * L.sc.x * L.sc.b' := by gcongr
    have h4 : 2 * L.sc.x ^ 4 * 1 * L.sc.x * L.sc.x * L.sc.b' = 2 * (L.sc.x ^ 6 * L.sc.b') := by ring
    linarith
  have hd0 : 0 ≤ L.sc.b' / L.sc.x := by positivity
  have hd1 : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1
  have hwin : ∀ j τ, 1 ≤ j → j ≤ D.R.m → L.sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b := by
    intro j τ hj hj'
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at h1
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
      obtain ⟨a1, a2⟩ := L.win_top j hj hj' τ ⟨t, htT⟩ hteq.symm
      have h2 := L.bT_ge ⟨t, htT⟩
      have h3 := hbT ⟨t, htT⟩
      constructor <;> linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · obtain ⟨a1, a2⟩ := L.win_thick j hj hj' τ h2
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := L.win_thin j hj hj' τ ⟨(D.eTau τ).2, h1, h2⟩
        constructor <;> linarith
  refine ⟨fun j j' τ τ' a1 a2 a3 a4 => ?_, fun τ hm0 => ?_⟩
  · have hXX : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b := by
      rw [Scale.X'', div_mul_cancel₀ _ hw0.ne', Scale.a]
    have hXX0 : 0 ≤ L.sc.X'' D.R.n := by
      rw [Scale.X'', Scale.a]; positivity
    calc wj D j τ ≤ 2 * L.sc.b := (hwin j τ a1 a2).2
      _ ≤ L.sc.x * L.sc.b := by gcongr
      _ = L.sc.X'' D.R.n * L.sc.w'' D.R.n := hXX.symm
      _ ≤ L.sc.X'' D.R.n * wj D j' τ' := by gcongr; exact (hwin j' τ' a3 a4).1
  · obtain ⟨-, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
    have hb1 : L.sc.w'' D.R.n ≤ (b1 τ : ℝ) := by
      by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
      · classical
        unfold Host.topPlaces at h1
        obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
        rw [htop τ ⟨t, htT⟩ hteq.symm]
        have h2 := L.bT_ge ⟨t, htT⟩
        have h3 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by
          exact_mod_cast Int.floor_nonneg.2 hd0
        push_cast
        linarith
      · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
        · have h3 := Int.le_ceil L.sc.b
          have h4 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (hthick τ h2).1
          linarith
        · rw [hthin τ ⟨(D.eTau τ).2, h1, h2⟩]
          exact Int.le_ceil _
    have h1 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz := by
      rw [hV.eta_eq]
      gcongr
      omega
    rw [(hbj τ _).1, (hbj τ _).1, ← Rat.cast_le (K := ℝ)]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_zero,
      zero_mul, add_zero]
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemExtLatOfMemLocP
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.ExtLatMatrix

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L}


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in
theorem _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP (h : ∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1)
    {a : ℕ} (M : Submodule (𝓞 K) (Fin a → K)) (x : Fin a → K) (hx : x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) :
    (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M := by
  obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M x).1 hx
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have hs' : s = 0 := by exact_mod_cast h0
    rw [hs']
    exact w.asIdeal.zero_mem
  have hval : w.valuation K ((s : K)⁻¹) ≤ 1 := by
    rw [map_inv₀]
    have h1 : w.valuation K (s : K) = 1 := by
      rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs
    rw [h1, inv_one]
  have hint : σ ((s : K)⁻¹) ∈ v.integer := (h _).2 hval
  have hmem : (fun i => σ ((s • x) i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M :=
    Submodule.subset_span ⟨s • x, hsx, rfl⟩
  have hsm := Submodule.smul_mem _ (⟨σ ((s : K)⁻¹), hint⟩ : v.integer) hmem
  convert hsm using 1
  funext i
  change σ (x i) = σ ((s : K)⁻¹) * σ ((s : K) * x i)
  rw [← map_mul, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in
theorem _root_.GlobalTheory.ExtLatMatrix.extLat_matrix_integral : ∀ (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (L Γ : Type) [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (σ : K →+* L), (∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) →
    (∀ (a : ℕ) (M : Submodule (𝓞 K) (Fin a → K)), ∀ x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M,
      (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) ∧
    ∀ (a b : ℕ) (M : Submodule (𝓞 K) (Fin a → K)) (MW : Submodule (𝓞 K) (Fin b → K))
      (B : GL (Fin a) K) (BW : GL (Fin b) K), _root_.Formalism.L2.DIV.IsBasisAt w M B → _root_.Formalism.L2.DIV.IsBasisAt w MW BW →
      ∀ ap : Matrix (Fin a) (Fin b) L,
        (∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW, ap *ᵥ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) →
        ∀ i j, v ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ * ap *
          (BW : Matrix (Fin b) (Fin b) K).map σ) i j) ≤ 1 := by
  intro K _ _ w L Γ _ _ v σ h
  refine ⟨fun a M x hx => _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h M x hx, ?_⟩
  intro a b M MW B BW hB hBW ap hap i j
  have hunit : ∀ t : 𝓞 K, t ∉ w.asIdeal → v (σ ((t : K)⁻¹)) ≤ 1 := by
    intro t ht
    refine (h _).2 ?_
    rw [map_inv₀]
    have h1 : w.valuation K (t : K) = 1 := by
      rw [show (t : K) = algebraMap (𝓞 K) K t from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w t).2 ht
    rw [h1, inv_one]
  have hint : ∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M, ∀ k,
      v (((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ y) k) ≤ 1 := by
    intro y hy
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      have hm' : m ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.colLat B) := by
        unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
        rw [← hB]
        exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hm
      obtain ⟨t, ht, htm⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal _ m).1 hm'
      unfold _root_.Formalism.L2.DIV.colLat at htm
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 htm
      have ht0 : (t : K) ≠ 0 := by
        intro h0
        apply ht
        have ht' : t = 0 := by exact_mod_cast h0
        rw [ht']
        exact w.asIdeal.zero_mem
      have hBc : (B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K)) = (t : K) • m := by
        funext r
        have hr := congrFun hc r
        simp only [Finset.sum_apply, Pi.smul_apply] at hr
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
        rw [← Algebra.smul_def] at *
        convert hr using 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [Algebra.smul_def, mul_comm]
          try rfl
      have hBm : ((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m =
          (t : K)⁻¹ • fun k => (c k : K) := by
        have e : m = (t : K)⁻¹ • ((B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K))) := by
          rw [hBc, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
        simp
      intro k
      have e : ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ (fun i => σ (m i))) k =
          σ ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m) k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e, hBm, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]
      refine mul_le_one' (hunit t ht) ((h _).2 ?_)
      exact HeightOneSpectrum.valuation_le_one w (c k)
    | zero => simp
    | add y z _ _ hy hz =>
      intro k
      rw [Matrix.mulVec_add, Pi.add_apply]
      exact v.map_add_le (hy k) (hz k)
    | smul c y _ hy =>
      intro k
      rw [Matrix.mulVec_smul, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
      exact mul_le_one' c.2 (hy k)
  have hcol : (fun k => σ ((BW : Matrix (Fin b) (Fin b) K) k j)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW := by
    refine _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h MW _ ?_
    unfold _root_.Formalism.L2.DIV.IsBasisAt at hBW
    rw [hBW]
    exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have key := hint _ (hap _ hcol) i
  convert key using 2
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.ExtLatMatrix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowDelTOGap
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_Del_TO_gap : SzRow (fun C D L => ((((TOv L.sc : ℕ) : ℝ)) ^ 2 ≤ ((D.s.Del : ℚ) : ℝ)) ∧ ((((TOv L.sc : ℕ) : ℝ) + (D.R.f * D.R.r.choose 2 : ℕ) + 2) * (((TOv L.sc : ℕ) : ℝ) + (D.R.f * D.R.r.choose 2 : ℕ) + 2 + 2 * (D.R.N D.R.m : ℝ)) ≤ ((D.s.Del : ℚ) : ℝ))) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps he he'
  refine ⟨805, fun cD hcD => ⟨0, fun ch _ => ⟨max x0 35, fun D L hs hx hV => ?_⟩⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hDY, -, -, -, -, hN, -⟩ :=
    hx0 L.sc D.R hs (le_trans (le_max_left _ _) hx) hV.ranks
  have hx35 : (35 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ L.sc.x := by linarith
  have hxp : (0 : ℝ) < L.sc.x := by linarith
  set y : ℝ := L.sc.x ^ (402 : ℝ) with hy
  have hy1 : (1 : ℝ) ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have h377 : L.sc.x ^ (377 : ℝ) ≤ y := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h12 : L.sc.x ^ (12 : ℝ) ≤ y := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hT : ((TOv L.sc : ℕ) : ℝ) ≤ y + 1 := by
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hxp.le (377 : ℝ))
    unfold TOv
    linarith
  have hDel : 35 * y ^ 2 ≤ ((D.s.Del : ℚ) : ℝ) := by
    rw [hV.Del_eq]
    have h1 : L.sc.x ^ cD ≤ ((Delv L.sc cD : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : L.sc.x ^ (805 : ℝ) ≤ L.sc.x ^ cD := Real.rpow_le_rpow_of_exponent_le hx1 hcD
    have h3 : L.sc.x ^ (805 : ℝ) = L.sc.x * y ^ 2 := by
      rw [hy, show (805 : ℝ) = 1 + (402 + 402) by norm_num, Real.rpow_add hxp, Real.rpow_add hxp,
        Real.rpow_one, sq]
    have h4 : 35 * y ^ 2 ≤ L.sc.x * y ^ 2 := mul_le_mul_of_nonneg_right hx35 (sq_nonneg _)
    rw [Rat.cast_natCast]
    exact h4.trans (h3.symm.le.trans (h2.trans h1))
  have hT0 : (0 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have : ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ (2 * y) ^ 2 := pow_le_pow_left₀ hT0 (by linarith) 2
    nlinarith
  · refine le_trans ?_ hDel
    calc _ ≤ (5 * y) * (7 * y) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = 35 * y ^ 2 := by ring

end GlobalTheory.EX
end

