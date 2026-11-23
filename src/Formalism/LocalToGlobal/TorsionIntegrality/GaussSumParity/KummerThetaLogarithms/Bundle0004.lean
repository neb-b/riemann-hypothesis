module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementF
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NormLeInvOfLtOne
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KernelFromKOne
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
section
noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension cW wpNum wpDen uSer)

theorem lubin_tate_log_is_artin_hasse : LtLogIsLgF := by
  intro K _ l hl
  ext n
  unfold Formalism.L2.Th1.CM.ltLog lgF
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have h1 : 1 < l ^ 2 := by nlinarith
  split_ifs with h
  · have hs := Nat.find_spec h
    rw [Finset.sum_eq_single (Nat.find h)]
    · rw [if_pos hs]
    · intro j _ hj
      rw [if_neg]
      intro hj'
      exact hj (Nat.pow_right_injective h1 (hj'.symm.trans hs))
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_range]
      have h2 : Nat.find h < (l ^ 2) ^ Nat.find h := Nat.lt_pow_self h1
      exact Nat.lt_succ_of_lt (lt_of_lt_of_eq h2 hs.symm)
  · symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro hj
    exact h ⟨j, hj⟩

namespace FAux

section Maps

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem cW_eq (g2 g3 : K) (k : ℕ) :
    cW g2 g3 k =
      if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
      if 4 ≤ k then
        3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
          ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
      else 0 := by
  unfold cW
  rw [Nat.strongRecOn_eq]
  split_ifs <;> rfl

theorem cW_map (g2 g3 : K) (k : ℕ) : φ (cW g2 g3 k) = cW (φ g2) (φ g3) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_eq, cW_eq (φ g2) (φ g3) k]
    split_ifs with h2 h3 h4
    · rw [map_div₀, map_ofNat]
    · rw [map_div₀, map_ofNat]
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_div₀, map_add, map_sub, map_natCast, map_one, map_ofNat, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.isLt
      rw [ih (m.val + 2) (by omega), ih (k - (m.val + 2)) (by omega)]
    · exact map_zero φ

theorem wpNum_map (g2 g3 : K) : PowerSeries.map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold wpNum
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs
  · exact map_one φ
  · exact cW_map φ g2 g3 _
  · exact map_zero φ

theorem wpDen_map (g2 g3 : K) : PowerSeries.map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold wpDen
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs
  · exact map_one φ
  · rw [map_mul, map_neg, map_sub, map_natCast, map_one, cW_map]
  · exact map_zero φ

theorem cc_wpDen (g2 g3 : K) : PowerSeries.constantCoeff (wpDen g2 g3) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold wpDen
  rw [PowerSeries.coeff_mk, if_pos rfl]

variable [CharZero K] [CharZero K']

theorem uSer_map (g2 g3 : K) : PowerSeries.map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by
  unfold uSer
  rw [map_mul, map_mul, PowerSeries.map_X,
    Formalism.L2.Th1.B.Map.map_inv' φ (by rw [cc_wpDen]; exact one_ne_zero), wpNum_map, wpDen_map]

theorem cc_arg {l : ℕ} (hl : 2 ≤ l) (ε : K) :
    PowerSeries.constantCoeff (PowerSeries.C ε * lgF K l) = 0 := by
  rw [map_mul, Pair.cc_lgF hl, mul_zero]

theorem thetaS_map {l : ℕ} (hl : 2 ≤ l) (g2 g3 ε : K) :
    PowerSeries.map φ (thetaS l g2 g3 ε) = thetaS l (φ g2) (φ g3) (φ ε) := by
  unfold thetaS
  rw [Formalism.L2.Th1.B.Map.map_psubst' φ (cc_arg hl ε), uSer_map, map_mul, PowerSeries.map_C,
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF]

theorem cc_phFF {l : ℕ} (hl : 2 ≤ l) (g2 g3 s2 ε : K) :
    PowerSeries.constantCoeff (phFF l g2 g3 s2 ε) = 0 := by
  have h1 : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.C ε * lgF K l)
      (Formalism.L2.Th1.B.sigS (Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW g2 g3)))) = 0 :=
    Pair.cc_ps (τ := Unit) (cc_arg hl ε) (Formalism.L2.Th1.B.Map.cc_sigS _)
  have h2 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU (lgF K l) - 1) = 0 := by
    rw [map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hl, sub_self]
  have h3 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU (lgF K l))) = 0 :=
    Pair.cc_ps (τ := Unit) h2 PowerSeries.constantCoeff_log
  unfold phFF
  rw [map_sub, map_add (f := _), map_neg, map_mul, map_pow, h1, h3, cc_arg hl ε]
  simp

end Maps

section Field

variable (l : ℕ) [hl : Fact l.Prime]

theorem norm_coe (x : MaximalUnramifiedExtension l) : ‖(MaximalUnramifiedExtension l).subtype x‖ = ‖x‖ := rfl

theorem model (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) (dK : ℕ) (L : PeriodPair)
    (hsq : Squarefree dK) (h4 : dK % 4 = 3) (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (h5 : 5 ≤ l)
    (hd : ¬ l ∣ dK) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (ι : ℂ ≃+* ℂ_[l]) :
    ∃ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
      (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) := by
  obtain ⟨g2, g3, hg⟩ := h2 dK L hsq h4 hcm l h5 hd ι
  obtain ⟨ε, hε, hε1, hc⟩ := h3 dK L hsq h4 hcm l h5 hd hin ι g2 g3 hg
  refine ⟨⟨g2, hg.1⟩, ⟨g3, hg.2.1⟩, ⟨ε, hε⟩, hg, hε1, fun n => ?_⟩
  have hm := thetaS_map (MaximalUnramifiedExtension l).subtype (l := l) (by omega) ⟨g2, hg.1⟩ ⟨g3, hg.2.1⟩ ⟨ε, hε⟩
  have hn := (hc n).2
  rw [lubin_tate_log_is_artin_hasse ℂ_[l] l (by omega)] at hn
  rw [← norm_coe, ← PowerSeries.coeff_map, hm]
  exact hn

theorem ffs (hF1 : CurveExponentCoboundaryCocycle) (g2 g3 ε : MaximalUnramifiedExtension l) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1)
    (hε : ‖ε‖ = 1) (hth : ∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1)
    (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (hF : IsLawOfLog l F) (s2 : MaximalUnramifiedExtension l)
    (hN : ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) :
    F1 F (cob F (phFF l g2 g3 s2 ε)) ∧ F2 l σ (cob F (phFF l g2 g3 s2 ε)) ∧
      Simeq (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * phFF l g2 g3 s2 ε)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l)))
          (cob F (phFF l g2 g3 s2 ε))) := by
  have h1 := hF1 (MaximalUnramifiedExtension l) l hσ.1 hσ.2.1 hσ.2.2.1 F hF g2 g3 s2 ε hg2 hg3 hε hth
  have h2 := second_level_of_norm_holds (MaximalUnramifiedExtension l) l σ hσ F hF _ (cc_phFF hσ.1.two_le g2 g3 s2 ε) h1 hN
  exact ⟨h1, h2.1, h2.2.2⟩

theorem exists_root2 : ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  refine kurRoots l (l ^ 2 - 1) (by omega) fun hd => ?_
  have h2 : l ∣ l ^ 2 := dvd_pow_self l two_ne_zero
  have h3 : l ∣ 1 := by
    have := (Nat.dvd_sub h2 hd)
    rwa [Nat.sub_sub_self h1.le] at this
  exact hl.out.one_lt.ne' (Nat.dvd_one.1 h3)

end Field

end FAux

theorem complex_multiplication_field_data : FieldDataCM := by
  intro l _ h5
  obtain ⟨σ, hσ, -⟩ := kurFrob l (by omega)
  refine ⟨σ, hσ, (Formalism.InvariantFactorPaths.G7.Top.lawExists (MaximalUnramifiedExtension l) l hσ.1 hσ.2.2.1).1, ?_⟩
  intro d _ hd
  have hl2 := hσ.1.two_le
  have hd0 : d ≠ 0 := NeZero.ne d
  have h1 : 1 < l ^ d := Nat.one_lt_pow hd0 hσ.1.one_lt
  obtain ⟨ζ, hζ⟩ := kurRoots l (l ^ d - 1) (by omega) (fun hdv => by
    have h2 : l ∣ l ^ d := dvd_pow_self l hd0
    have h3 : l ∣ 1 := by
      have := (Nat.dvd_sub h2 hdv)
      rwa [Nat.sub_sub_self h1.le] at this
    exact hσ.1.one_lt.ne' (Nat.dvd_one.1 h3))
  obtain ⟨om, oms, h1, h2⟩ := trDualExists (MaximalUnramifiedExtension l) l d σ hσ hd ζ hζ
  exact ⟨ζ, om, oms, hζ, h1, h2⟩

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.GramMatrixExists
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)

namespace OrbitCoverLemmas

end OrbitCoverLemmas

namespace OrbitCoverLemmas

def blk {K : Type} [Field K] (lam : K) (k x : Bool) : K :=
  if x = false then (if k = false then 1 else lam) else (if k = false then 2⁻¹ else -lam * 2⁻¹)

theorem blk_gram {K : Type} [Field K] (σ : K →+* K) (lam : K) (h2 : (2 : K) ≠ 0)
    (h : lam * σ lam = -1) (x x' : Bool) :
    ∑ k, blk lam k x * σ (blk lam k x') = if x ≠ x' then 1 else 0 := by
  have s2 : σ 2 = 2 := map_ofNat σ 2
  cases x <;> cases x' <;> simp [blk, map_inv₀, s2]
  · linear_combination h
  · field_simp; linear_combination -h
  · field_simp; linear_combination -h
  · field_simp; linear_combination h

theorem lam_spec {K : Type} [Field K] (σ : K →+* K) (m : ℕ) (hm : 0 < m) (ζ : K)
    (hζ : IsPrimitiveRoot ζ ((2 * m + 1) ^ 2 - 1)) (hσ : σ ζ = ζ ^ (2 * m + 1)) :
    (ζ ^ m) * σ (ζ ^ m) = -1 := by
  have e : (2 * m + 1) ^ 2 - 1 = (m * (2 * m + 2)) * 2 := by
    have : (2 * m + 1) ^ 2 = (m * (2 * m + 2)) * 2 + 1 := by ring
    omega
  have hp : IsPrimitiveRoot (ζ ^ (m * (2 * m + 2))) 2 := by
    have := hζ.pow_of_dvd (p := m * (2 * m + 2)) (by positivity) (by rw [e]; exact Dvd.intro _ rfl)
    rwa [e, Nat.mul_div_cancel_left _ (by positivity)] at this
  have := hp.eq_neg_one_of_two_right
  rw [map_pow, hσ, ← this]; ring

theorem norm_two {K : Type} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (h : ‖((2 * m + 1 : ℕ) : K)‖ < 1) : ‖(2 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one K 2
    simpa using this
  refine le_antisymm h2 ?_
  by_contra hlt
  rw [not_le] at hlt
  have hm : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  have e : (1 : K) = ((2 * m + 1 : ℕ) : K) + -(2 * (m : K)) := by push_cast; ring
  have h1 : ‖(1 : K)‖ < 1 := by
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h ?_)
    rw [norm_neg, norm_mul]
    calc ‖(2 : K)‖ * ‖(m : K)‖ ≤ ‖(2 : K)‖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  rw [norm_one] at h1
  exact lt_irrefl _ h1

end OrbitCoverLemmas

theorem gram_matrix_exists : GramExists := by
  intro K _ _ _ l σ hU hζ E _ _
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨hp, hl2, hnl, -, -⟩ := id hU
  obtain ⟨m, rfl⟩ : ∃ m, l = 2 * m + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hm : 0 < m := by omega
  have hσζ : σ ζ = ζ ^ (2 * m + 1) := teichSigma K _ 2 σ hU (by norm_num) ζ hζ.pow_eq_one
  have hN0 : (2 * m + 1) ^ 2 - 1 ≠ 0 := by
    have : 1 < (2 * m + 1) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have nζ : ‖ζ‖ = 1 := FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσζ, map_pow, hσζ, ← pow_mul, ← sq]
    have e : (2 * m + 1) ^ 2 = ((2 * m + 1) ^ 2 - 1) + 1 := by omega
    rw [e, pow_succ, hζ.pow_eq_one, one_mul]
  have hlam := OrbitCoverLemmas.lam_spec σ m hm ζ hζ hσζ
  have n2 : ‖(2 : K)‖ = 1 := by
    refine OrbitCoverLemmas.norm_two m ?_
    rw [hnl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have nlam : ‖ζ ^ m‖ = 1 := by rw [norm_pow, nζ, one_pow]
  have s2 : σ 2 = 2 := map_ofNat σ 2
  have hblk : ∀ k x : Bool, ‖OrbitCoverLemmas.blk (ζ ^ m) k x‖ ≤ 1 ∧
      σ (σ (OrbitCoverLemmas.blk (ζ ^ m) k x)) = OrbitCoverLemmas.blk (ζ ^ m) k x := by
    intro k x
    cases k <;> cases x <;> simp [OrbitCoverLemmas.blk, nlam, hσσ, n2, s2, map_inv₀]
  refine ⟨fun k x => if k.2 = x.2 then OrbitCoverLemmas.blk (ζ ^ m) k.1 x.1 else 0, fun k x => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hblk _ _
    · simp
  · rintro ⟨b, e⟩ ⟨b', e'⟩
    rw [Fintype.sum_prod_type]
    dsimp only
    by_cases h : e = e'
    · subst h
      have h3 : ∀ k : Bool, ∑ y : E, (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b else 0) *
          σ (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b' else 0) =
          OrbitCoverLemmas.blk (ζ ^ m) k b * σ (OrbitCoverLemmas.blk (ζ ^ m) k b') := by
        intro k
        rw [Finset.sum_eq_single e]
        · simp
        · intro y _ hy
          simp [hy]
        · simp
      simp only [h3]
      rw [OrbitCoverLemmas.blk_gram σ _ h2 hlam]
      simp
    · rw [if_neg (fun h' => h h'.2)]
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y = e
      · have : ¬ y = e' := fun h' => h (hy ▸ h')
        simp [this]
      · simp [hy]

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NonVac
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D.ChainWitness

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Integral Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog Simeq Gser BetaHyp)

theorem fieldWitness (hF : KurFrob) (hR : KurRoots) (hC : KurComplete) (hT : TrDualExists)
    (hB : FOfBetaHyp) (l : ℕ) [Fact l.Prime] (hl : 2 < l) (ν : ℕ) [NeZero ν] :
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ ∧ CompleteSpace (MaximalUnramifiedExtension l) ∧
      (∀ a, ‖(MaximalUnramifiedExtension l).subtype a‖ = ‖a‖) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧
      2 ≤ 2 * ν ∧ Even (2 * ν) ∧
      (∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l])) ∧
      (∃ om oms : Fin ν → MaximalUnramifiedExtension l, OwOK (2 * ν) σ om oms ∧ TrDual (2 * ν) σ om oms) ∧
      ∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F ∧
        ∃ be : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), F1 F be ∧ F2 l σ be ∧ ¬ Simeq be 0 := by
  obtain ⟨σ, hσ, -⟩ := hF l hl
  have hl1 : 1 < l := by omega
  have hnd : ∀ k : ℕ, 0 < k → 0 < l ^ k - 1 ∧ ¬ l ∣ l ^ k - 1 := by
    intro k hk
    have h1 : 1 < l ^ k := Nat.one_lt_pow hk.ne' hl1
    refine ⟨by omega, fun hdv => ?_⟩
    have h2 : l ∣ l ^ k := dvd_pow_self l hk.ne'
    have h3 : l ∣ 1 := by
      have := (Nat.dvd_sub h2 hdv)
      rwa [Nat.sub_sub_self h1.le] at this
    exact absurd (Nat.le_of_dvd one_pos h3) (by omega)
  have hν : 0 < ν := Nat.pos_of_ne_zero (NeZero.ne ν)
  obtain ⟨ζ2, hζ2⟩ := hR l (l ^ 2 - 1) (hnd 2 (by norm_num)).1 (hnd 2 (by norm_num)).2
  obtain ⟨ζd, hζd⟩ := hR l (l ^ (2 * ν) - 1) (hnd _ (by omega)).1 (hnd _ (by omega)).2
  have hdual := hT (MaximalUnramifiedExtension l) l (2 * ν) σ hσ (even_two_mul ν) ζd hζd
  rw [Nat.mul_div_cancel_left ν two_pos] at hdual
  obtain ⟨F, hFl⟩ := (Formalism.InvariantFactorPaths.G7.Top.lawExists (MaximalUnramifiedExtension l) l hσ.1 hσ.2.2.1).1
  have h1 : σ (σ (1 : MaximalUnramifiedExtension l)) = 1 := by simp
  have hbeta := Formalism.InvariantFactorPaths.G7.Top.gcIsBeta (MaximalUnramifiedExtension l) l σ hσ F hFl 1 (by simp) h1
  have hFF := hB (MaximalUnramifiedExtension l) l σ hσ ⟨ζ2, hζ2⟩ F hFl _ hbeta
  refine ⟨σ, hσ, hC l, fun _ => rfl, ⟨ζ2, hζ2⟩, ⟨ζd, hζd⟩, by omega, even_two_mul ν, ?_, hdual,
    F, hFl, _, hFF.1, hFF.2, ?_⟩
  · exact IsAlgClosed.exists_pow_nat_eq _ (hnd 2 (by norm_num)).1
  · intro h0
    have hz : (Gser l (0 : MaximalUnramifiedExtension l) (σ 0)) = 0 := by simp [Gser]
    have := Formalism.InvariantFactorPaths.G7.Top.gcUnique (MaximalUnramifiedExtension l) l σ hσ 1 0 h1 (by simp) (by rw [hz]; exact h0)
    exact one_ne_zero this

theorem fullWitness (hF : KurFrob) (hR : KurRoots) (hC : KurComplete) (hT : TrDualExists)
    (hB : FOfBetaHyp) (l : ℕ) [Fact l.Prime] (hl : 2 < l) (ν r0 r1 : ℕ) [NeZero ν] :
    ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin ν → MaximalUnramifiedExtension l)
      (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) ℂ_[l]) (ph : PowerSeries (MaximalUnramifiedExtension l)),
      UnrOK (MaximalUnramifiedExtension l) l σ ∧ CompleteSpace (MaximalUnramifiedExtension l) ∧ (∀ a, ‖(MaximalUnramifiedExtension l).subtype a‖ = ‖a‖) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧ 2 ≤ 2 * ν ∧ Even (2 * ν) ∧
      (∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l])) ∧
      OwOK (2 * ν) σ om oms ∧ TrDual (2 * ν) σ om oms ∧ IsLawOfLog l F ∧ F1 F be ∧ F2 l σ be ∧
      ¬ Simeq be 0 ∧ Integral U0 ∧ MvPowerSeries.constantCoeff Φ = 0 ∧
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be)) ∧
      Simeq (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be) := by
  obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7, h8, ⟨om, oms, h9, h10⟩, F, h11, be, h12, h13, h14⟩ :=
    fieldWitness hF hR hC hT hB l hl ν
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    have := h12.1 0 (Or.inl rfl)
    simpa using this
  refine ⟨σ, F, be, om, oms, 1, sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be),
    PowerSeries.C ((2 : MaximalUnramifiedExtension l)⁻¹) *
      MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [MvPowerSeries.coeff_one]
    split_ifs <;> simp
  · unfold sumE
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_eq_zero
    intro e _
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; simp)) (by intro i; simp)
      (by rw [MvPowerSeries.constantCoeff_map, hbe0, map_zero])
  · exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[l] _).1 _
  · have : MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * (PowerSeries.C ((2 : MaximalUnramifiedExtension l)⁻¹) *
        MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be) =
        MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be := by
      rw [← mul_assoc]
      have h2 : (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) : MvPowerSeries Unit (MaximalUnramifiedExtension l)) *
          PowerSeries.C ((2 : MaximalUnramifiedExtension l)⁻¹) = 1 := by
        change (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) : MvPowerSeries Unit (MaximalUnramifiedExtension l)) *
          MvPowerSeries.C ((2 : MaximalUnramifiedExtension l)⁻¹) = 1
        rw [← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
      rw [h2, one_mul]
    rw [this]
    exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules (MaximalUnramifiedExtension l) _).1 _

end Formalism.L2.Th1.D.ChainWitness

namespace Formalism.L2.Th1.D

theorem chain_nonvacuous : ChainNonVacuous := fun l _ hl ν r0 r1 _ =>
  ChainWitness.fullWitness kurFrob kurRoots kurComplete trDualExists fOfBetaHyp l hl ν r0 r1

end Formalism.L2.Th1.D
end
end

