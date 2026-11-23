module

public import Mathlib
public import GroundTheory.LocalFields.UpperNumbering
public import GroundTheory.LocalFields.LubinTateTowerMaps
public import GroundTheory.LocalFields.SeparableClosure
public import GroundTheory.LocalFields.Bundle0014

@[expose] public section

-- bundled from GroundTheory.LocalFields.ConductorTransport
section
noncomputable section

open ValuativeRel IsDiscreteValuationRing

namespace GroundTheory.LocalField

section Transport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L₁ : Type*} [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [Algebra K L₁] [ValuativeExtension K L₁] [FiniteDimensional K L₁]
  {L₂ : Type*} [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [Algebra K L₂] [ValuativeExtension K L₂] [FiniteDimensional K L₂]

def integerAlgEquivOfAlgEquiv (e : L₁ ≃ₐ[K] L₂) : 𝒪[L₁] ≃ₐ[𝒪[K]] 𝒪[L₂] :=
  AlgEquiv.ofAlgHom (integerAlgHom e.toAlgHom) (integerAlgHom e.symm.toAlgHom)
    (AlgHom.ext fun x => Subtype.ext (e.apply_symm_apply (x : L₂)))
    (AlgHom.ext fun x => Subtype.ext (e.symm_apply_apply (x : L₁)))


omit [IsNonarchimedeanLocalField K] in
theorem addVal_ringEquiv {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (φ : R ≃+* S) (x : R) :
    addVal S (φ x) = addVal R x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have hϖ' : Irreducible (φ ϖ) := (MulEquiv.irreducible_iff (f := (φ : R ≃* S))).mpr hϖ
  rw [map_mul, map_pow, addVal_def' u hϖ n]
  exact addVal_def' (Units.map (φ : R →* S) u) hϖ' n

theorem lowerIndex_autCongr (e : L₁ ≃ₐ[K] L₂) (σ : L₁ ≃ₐ[K] L₁) :
    lowerIndex K L₂ (e.autCongr σ) = lowerIndex K L₁ σ := by
  set φ := integerAlgEquivOfAlgEquiv e
  rw [lowerIndex, lowerIndex, ← φ.toEquiv.iInf_comp]
  refine iInf_congr fun x => ?_
  have h : integerAlgEquiv K L₂ (e.autCongr σ) (φ x) - φ x = φ (integerAlgEquiv K L₁ σ x - x) := by
    apply Subtype.ext
    change (e.autCongr σ) (e (x : L₁)) - e (x : L₁) = e (σ (x : L₁) - (x : L₁))
    simp [AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [h]
  exact addVal_ringEquiv (φ : 𝒪[L₁] ≃+* 𝒪[L₂]) _

theorem map_lowerRamificationGroup_autCongr (e : L₁ ≃ₐ[K] L₂) (i : ℤ) :
    (lowerRamificationGroup K L₁ i).map (e.autCongr : (L₁ ≃ₐ[K] L₁) →* (L₂ ≃ₐ[K] L₂)) =
      lowerRamificationGroup K L₂ i := by
  ext τ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [mem_lowerRamificationGroup_iff_lowerIndex] at hσ ⊢
    show _ ≤ lowerIndex K L₂ (e.autCongr σ)
    rw [lowerIndex_autCongr]
    exact hσ
  · intro hτ
    refine ⟨e.autCongr.symm τ, ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [mem_lowerRamificationGroup_iff_lowerIndex] at hτ ⊢
    rw [← lowerIndex_autCongr e, MulEquiv.apply_symm_apply]
    exact hτ

theorem map_lowerRamificationGroupReal_autCongr (e : L₁ ≃ₐ[K] L₂) (t : ℝ) :
    (lowerRamificationGroupReal K L₁ t).map (e.autCongr : (L₁ ≃ₐ[K] L₁) →* (L₂ ≃ₐ[K] L₂)) =
      lowerRamificationGroupReal K L₂ t :=
  map_lowerRamificationGroup_autCongr e _

theorem herbrandPhi_eq_of_algEquiv (e : L₁ ≃ₐ[K] L₂) (u : ℝ) :
    herbrandPhi K L₂ u = herbrandPhi K L₁ u := by
  rcases le_or_gt (-1) u with hu | hu
  · rw [herbrandPhi_eq_sum_lowerIndex hu, herbrandPhi_eq_sum_lowerIndex hu]
    have hcard : Nat.card (lowerRamificationGroup K L₂ 0) = Nat.card (lowerRamificationGroup K L₁ 0) := by
      rw [← map_lowerRamificationGroup_autCongr e 0]
      exact Subgroup.card_map_of_injective e.autCongr.injective
    rw [hcard, ← Fintype.sum_equiv e.autCongr.toEquiv
      (fun σ => enatMin (lowerIndex K L₁ σ) (u + 1))
      (fun τ => enatMin (lowerIndex K L₂ τ) (u + 1))
      (fun σ => by
        show _ = enatMin (lowerIndex K L₂ (e.autCongr σ)) (u + 1)
        rw [lowerIndex_autCongr])]
  · rw [herbrandPhi_of_nonpos (by linarith), herbrandPhi_of_nonpos (by linarith)]

theorem herbrandPsi_eq_of_algEquiv (e : L₁ ≃ₐ[K] L₂) (v : ℝ) :
    herbrandPsi K L₂ v = herbrandPsi K L₁ v := by
  rw [herbrandPsi_eq_iff, herbrandPhi_eq_of_algEquiv e, herbrandPhi_herbrandPsi]

theorem map_upperRamificationGroup_autCongr (e : L₁ ≃ₐ[K] L₂) (v : ℝ) :
    (upperRamificationGroup K L₁ v).map (e.autCongr : (L₁ ≃ₐ[K] L₁) →* (L₂ ≃ₐ[K] L₂)) =
      upperRamificationGroup K L₂ v := by
  rw [upperRamificationGroup, upperRamificationGroup, herbrandPsi_eq_of_algEquiv e,
    map_lowerRamificationGroupReal_autCongr]

theorem upperRamificationGroup_eq_bot_of_ramificationIndex_eq_one [IsGalois K L₁]
    (he : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L₁))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1) {v : ℝ} (hv : -1 < v) : upperRamificationGroup K L₁ v = ⊥ := by
  have h0 : lowerRamificationGroup K L₁ 0 = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [card_lowerRamificationGroup_zero, he])
  rw [eq_bot_iff, ← h0, upperRamificationGroup, lowerRamificationGroupReal]
  apply lowerRamificationGroup_antitone
  have h1 : -1 < herbrandPsi K L₁ v := by
    rw [← herbrandPsi_of_nonpos (K := K) (L := L₁) (show (-1 : ℝ) ≤ 0 by norm_num)]
    exact herbrandPsi_strictMono hv
  exact Int.le_ceil_iff.mpr (by push_cast; linarith)

end Transport

section Restrict

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  {L M : IntermediateField K Ω} [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L]
  [IsGalois K M]

theorem map_upperRamificationGroup_restrictAut (h : L ≤ M) (v : ℝ) :
    (upperRamificationGroup K M v).map (restrictAut h) = upperRamificationGroup K L v := by
  set R := IntermediateField.restrict h
  let e : L ≃ₐ[K] R := IntermediateField.restrictAlgEquiv h
  have : IsGalois K R := IsGalois.of_algEquiv e
  have hH := map_upperRamificationGroup (K := K) (L := M) R v
  have hT := map_upperRamificationGroup_autCongr e.symm v
  have key : ∀ y : R, ((e.symm y : L) : Ω) = ((y : M) : Ω) := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rfl
  have hcomp : (e.symm.autCongr : (R ≃ₐ[K] R) →* (L ≃ₐ[K] L)).comp
      (AlgEquiv.restrictNormalHom R) = restrictAut h := by
    ext σ x
    rw [restrictAut_apply]
    show ((e.symm ((σ.restrictNormal R) (e x)) : L) : Ω) = _
    rw [key]
    have h1 := AlgEquiv.restrictNormal_commutes σ R (e x)
    have h2 : (algebraMap R M (σ.restrictNormal R (e x)) : M) = ((σ.restrictNormal R (e x) : R) : M) :=
      rfl
    rw [← h2, h1]
    rfl
  rw [← hT, ← hH, Subgroup.map_map, hcomp]

end Restrict

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalZetaIntegral
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Laurent



theorem differentiable_qpow : Differentiable ℂ fun s : ℂ => (residueCard K : ℂ) ^ (-s) :=
  differentiable_neg.const_cpow (Or.inl residueCard_ne_zero_complex)

end Laurent

section Sums


omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem hasSum_int_of_shift {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {a : ℤ → E}
    (M : ℤ) (h : ∀ k, k < M → a k = 0) {x : E} (hx : HasSum (fun n : ℕ => a (M + n)) x) :
    HasSum a x := by
  have hinj : Function.Injective (fun n : ℕ => M + (n : ℤ)) := fun m n hmn => by
    simpa using hmn
  refine (hinj.hasSum_iff fun k hk => h k ?_).mp hx
  by_contra hle
  push Not at hle
  exact hk ⟨(k - M).toNat, by simp only; omega⟩

end Sums

section LFactor

variable (χ : Kˣ →* ℂˣ)


open Classical in
def localLFactor (s : ℂ) : ℂ :=
  if IsUnramifiedChar χ then (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
  else 1

variable {χ}

theorem localLFactor_of_isUnramified (h : IsUnramifiedChar χ) (s : ℂ) :
    localLFactor χ s = (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ := by
  simp [localLFactor, h]

theorem localLFactor_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localLFactor χ s = 1 := by
  simp [localLFactor, h]

variable (hχ : Continuous χ)
include hχ

theorem norm_quasiChar_unifUnit :
    ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ = (residueCard K : ℝ) ^ (-quasiCharExponent χ) := by
  rw [norm_quasiChar_apply hχ, modulus_of_ne_zero (unifUnit K).ne_zero, ord_unifUnit,
    NNReal.coe_zpow, NNReal.coe_natCast, ← Real.rpow_intCast,
    ← Real.rpow_mul residueCard_pos_real.le]
  congr 1
  push_cast
  ring

theorem norm_quasiChar_unifUnit_mul_qpow_lt_one {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, norm_quasiChar_unifUnit hχ, norm_qpow, ← Real.rpow_add residueCard_pos_real]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_residueCard) (by linarith)

theorem one_sub_quasiChar_unifUnit_mul_qpow_ne_zero {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  rw [← sub_eq_zero.mp h, norm_one] at this
  exact lt_irrefl _ this

theorem localLFactor_ne_zero {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    localLFactor χ s ≠ 0 := by
  by_cases h : IsUnramifiedChar χ
  · rw [localLFactor_of_isUnramified h]
    exact inv_ne_zero (one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hχ hs)
  · rw [localLFactor_of_not_isUnramified h]
    exact one_ne_zero

theorem norm_quasiChar_mul_modulus_cpow (u : Kˣ) (s : ℂ) :
    ‖((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s‖ =
      ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ ^ ord (u : K) := by
  have hχu : ‖((χ u : ℂˣ) : ℂ)‖ = ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ ^ ord (u : K) := by
    have e := congrArg (fun v => ‖((χ v : ℂˣ) : ℂ)‖) (eq_unifUnit_zpow_mul u)
    rw [e, map_mul, Units.val_mul, norm_mul,
      norm_quasiChar_apply_eq_one hχ (unifUnit_zpow_neg_mul_mem u), mul_one, map_zpow,
      Units.val_zpow_eq_zpow_val, norm_zpow]
  rw [norm_mul, hχu, modulus_cpow_eq_zpow, norm_zpow, ← mul_zpow, ← norm_mul]

end LFactor

section ZetaNonvanishing₂

variable [MeasurableSpace K] [BorelSpace K]

def localZeta (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ u, f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s ∂multHaar K

variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}

omit [MeasurableSpace K] [BorelSpace K] in
theorem continuous_localZeta_integrand (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) (s : ℂ) :
    Continuous fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s := by
  refine ((hf.1.continuous.comp Units.continuous_val).mul (Units.continuous_val.comp hχ)).mul ?_
  refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)

theorem integrable_localZeta (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    Integrable (fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s)
      (multHaar K) := by
  obtain ⟨-, M, -, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  set ρ := ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ with hρ
  have hρ1 : ρ < 1 := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  have hρ0 : 0 < ρ := norm_pos_iff.mpr (mul_ne_zero (χ _).ne_zero (qpow_ne_zero s))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨(continuous_localZeta_integrand hf hχ s).aestronglyMeasurable, ?_⟩
  let a : ℤ → ℝ := fun k => if M ≤ k then C * ρ ^ k else 0
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    simp only [a]
    split_ifs
    · exact mul_nonneg hC0 (zpow_nonneg hρ0.le _)
    · exact le_rfl
  have hsum : HasSum a (C * ρ ^ M * (1 - ρ)⁻¹) := by
    refine hasSum_int_of_shift M (fun k hk => by simp [a, not_le.mpr hk]) ?_
    have e : (fun n : ℕ => a (M + n)) = fun n : ℕ => C * ρ ^ M * ρ ^ n := by
      funext n
      simp only [a, le_add_iff_nonneg_right, Nat.cast_nonneg, if_true]
      rw [zpow_add₀ hρ0.ne', zpow_natCast, mul_assoc]
    rw [e]
    exact (hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have hbound : ∀ u : Kˣ,
      ‖f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s‖ₑ ≤
        ENNReal.ofReal (a (ord (u : K))) := by
    intro u
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc, norm_mul, norm_quasiChar_mul_modulus_cpow hχ]
    simp only [a]
    split_ifs with hk
    · exact mul_le_mul_of_nonneg_right (hC _) (zpow_nonneg hρ0.le _)
    · have : f u = 0 := by
        by_contra h0
        exact hk ((mem_valBall_iff_le_ord u.ne_zero).mp (hM _ h0))
      rw [this, norm_zero, zero_mul]
  refine (lintegral_multHaar_le_tsum _ (fun k => ENNReal.ofReal (a k)) hbound).trans_lt ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hsum.summable]
  exact ENNReal.ofReal_lt_top


open scoped Classical in
theorem localZeta_eq_sum (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {M N : ℤ} (hMN : M ≤ N)
    (hM : ∀ x, f x ≠ 0 → x ∈ valBall K M) (hN : ∀ x ∈ valBall K N, f x = f 0) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    localZeta f χ s =
      ∑ k ∈ Finset.Ico M N, (∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K) *
          ((residueCard K : ℂ) ^ (-s)) ^ k +
        if IsUnramifiedChar χ then
          f 0 * (((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N *
            (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
        else 0 := by
  set T := (residueCard K : ℂ) ^ (-s) with hT
  set α := ((χ (unifUnit K) : ℂˣ) : ℂ) with hα
  let Z : ℤ → ℂ := fun k => ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K
  have hsum := hasSum_setIntegral_ordShell (integrable_localZeta hf hχ hs)
  have hterm : ∀ k, ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ s ∂multHaar K = Z k * T ^ k := by
    intro k
    simp only [Z]
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_
    rw [modulus_cpow_eq_zpow, mem_ordShell.mp hu]
  simp only [hterm] at hsum
  have hlow : ∀ k, k < M → Z k = 0 := by
    intro k hk
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    have : f u = 0 := by
      by_contra h0
      have := (mem_valBall_iff_le_ord u.ne_zero).mp (hM _ h0)
      rw [mem_ordShell.mp hu] at this
      omega
    rw [this, zero_mul]
  have hhigh : ∀ k, N ≤ k → Z k = f 0 * (if IsUnramifiedChar χ then α ^ k else 0) := by
    intro k hk
    rw [← setIntegral_ordShell_quasiChar hχ k, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_
    rw [hN u ((mem_valBall_iff_le_ord u.ne_zero).mpr (by rw [mem_ordShell.mp hu]; exact hk))]
  have hαT : ‖α * T‖ < 1 := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  have hαT0 : α * T ≠ 0 := mul_ne_zero (χ _).ne_zero (qpow_ne_zero s)
  have h1 : HasSum (fun k => if k < N then Z k * T ^ k else 0)
      (∑ k ∈ Finset.Ico M N, Z k * T ^ k) := by
    have : HasSum (fun k => if k < N then Z k * T ^ k else 0)
        (∑ k ∈ Finset.Ico M N, if k < N then Z k * T ^ k else 0) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
        rcases hk with hk | hk
        · simp [hlow k hk]
        · simp [not_lt.mpr hk])
    convert this using 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_Ico.mp hk).2]
  have h2 : HasSum (fun k => if k < N then 0 else Z k * T ^ k)
      (if IsUnramifiedChar χ then f 0 * (α * T) ^ N * (1 - α * T)⁻¹ else 0) := by
    by_cases hu : IsUnramifiedChar χ
    · rw [if_pos hu]
      refine hasSum_int_of_shift N (fun k hk => by simp [hk]) ?_
      have e : (fun n : ℕ => if N + (n : ℤ) < N then 0 else Z (N + n) * T ^ (N + (n : ℤ))) =
          fun n : ℕ => f 0 * (α * T) ^ N * (α * T) ^ n := by
        funext n
        rw [if_neg (by omega), hhigh _ (by omega), if_pos hu, mul_assoc, ← mul_zpow,
          zpow_add₀ hαT0, zpow_natCast, mul_assoc]
      rw [e]
      exact (hasSum_geometric_of_norm_lt_one hαT).mul_left _
    · rw [if_neg hu]
      convert hasSum_zero with k
      split_ifs with hk
      · rfl
      · rw [hhigh k (not_lt.mp hk), if_neg hu, mul_zero, zero_mul]
  have h12 := h1.add h2
  have e : (fun k => (if k < N then Z k * T ^ k else 0) + (if k < N then 0 else Z k * T ^ k)) =
      fun k => Z k * T ^ k := by
    funext k
    split_ifs <;> simp
  rw [e] at h12
  exact hsum.unique h12



end ZetaNonvanishing₂

end GroundTheory.LocalField
end
end

