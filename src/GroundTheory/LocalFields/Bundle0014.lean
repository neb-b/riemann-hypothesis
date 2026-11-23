module

public import Mathlib
public import GroundTheory.LocalFields.LubinTateReciprocity.Descent
public import GroundTheory.LocalFields.LocalZetaShell

@[expose] public section

-- bundled from GroundTheory.LocalFields.ConductorFormalGroup
section
noncomputable section

open MvPowerSeries ValuativeRel

namespace GroundTheory.LocalField

section Coeff

variable {R : Type*} [CommRing R] (F : FormalGroup R)

theorem coeff_formalGroup_Xzero (j : ℕ) :
    PowerSeries.coeff j F.Xzero = coeff (Finsupp.single 0 j) F.toPowerSeries := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (Finsupp.single 0 j)]
  · simp [PowerSeries.coeff_X_pow]
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · simp [hd₁, PowerSeries.coeff_X_pow]
      intro h
      exact absurd (by ext i; fin_cases i <;> simp [h, hd₁]) hd
    · simp [hd₁]
  · exact HasSubst.X_zero

theorem exists_sub_X_eq_X_mul :
    ∃ G : MvPowerSeries (Fin 2) R, constantCoeff G = 1 ∧ F.toPowerSeries - X 0 = X 1 * G := by
  have hdvd : (X 1 : MvPowerSeries (Fin 2) R) ∣ F.toPowerSeries - X 0 := by
    rw [X_dvd_iff]
    intro m hm
    have hm' : m = Finsupp.single 0 (m 0) := by
      ext i; fin_cases i <;> simp [hm]
    rw [map_sub, hm', ← coeff_formalGroup_Xzero, F.Xzero_eq_X, PowerSeries.coeff_X, coeff_X]
    by_cases h : m 0 = 1
    · simp [h]
    · have : Finsupp.single (0 : Fin 2) (m 0) ≠ Finsupp.single 0 1 := by
        intro e; exact h (by simpa using congrArg (fun d => d 0) e)
      simp [h, this]
  obtain ⟨G, hG⟩ := hdvd
  refine ⟨G, ?_, hG⟩
  have h := congrArg (coeff (Finsupp.single 1 1)) hG
  rw [map_sub, F.lin_coeff_Y, coeff_X, if_neg (by
    intro e; simpa using congrArg (fun d => d 1) e)] at h
  have e := coeff_add_monomial_mul (m := Finsupp.single (1 : Fin 2) 1) (n := 0) (φ := G) (1 : R)
  rw [add_zero, one_mul, ← X_def] at e
  rw [e, sub_zero] at h
  rw [← coeff_zero_eq_constantCoeff_apply, ← h]

end Coeff

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [IsValuativeTopology Ω]
  [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem psEval_one {σ : Type*} (x : σ → Ω) : psEval (1 : MvPowerSeries σ 𝒪[K]) x = 1 := by
  classical
  rw [psEval, tsum_eq_single 0]
  · simp [psTerm]
  · intro d hd
    simp [psTerm, coeff_one, hd]

theorem valuation_psEval_sub_left (F : FormalGroup 𝒪[K]) {a b : Ω} (ha : valuation Ω a < 1)
    (hb : valuation Ω b < 1) :
    valuation Ω (psEval F.toPowerSeries ![a, b] - a) = valuation Ω b := by
  obtain ⟨G, hG1, hG⟩ := exists_sub_X_eq_X_mul F
  have hx : ∀ i, valuation Ω ((![a, b] : Fin 2 → Ω) i) < 1 := by
    intro i; fin_cases i
    exacts [ha, hb]
  have h1 : psEval F.toPowerSeries ![a, b] - a = b * psEval G ![a, b] := by
    have e : F.toPowerSeries = X 0 + X 1 * G := by rw [← hG]; ring
    rw [e, psEval_add' _ _ _ hx, psEval_mul' _ _ _ hx, psEval_X, psEval_X]
    simp
  have h2 : valuation Ω (psEval G ![a, b]) = 1 := by
    have hG' : G = 1 + (G - 1) := by ring
    have hc : constantCoeff (G - 1) = 0 := by simp [hG1]
    rw [hG', psEval_add' _ _ _ hx, psEval_one]
    exact Valuation.map_one_add_of_lt _ (valuation_psEval_lt_one' hc _ hx)
  rw [h1, map_mul, h2, mul_one]

end Valuation

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalZetaChar
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Decomposition

theorem unifUnit_zpow_neg_mul_mem (u : Kˣ) :
    unifUnit K ^ (-ord (u : K)) * u ∈ unitFiltrationUnits K 0 := by
  rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_unifUnit_zpow]
  ring

theorem eq_unifUnit_zpow_mul (u : Kˣ) :
    u = unifUnit K ^ ord (u : K) * (unifUnit K ^ (-ord (u : K)) * u) := by
  rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

theorem isCompact_unitFiltrationUnits_zero :
    IsCompact (unitFiltrationUnits K 0 : Set Kˣ) := by
  have hS : IsCompact ((valBall K 0 : Set K) \ valBall K 1) :=
    (isCompact_valBall 0).diff (isOpen_valBall 1)
  have heq : (unitFiltrationUnits K 0 : Set Kˣ) =
      Units.val ⁻¹' ((valBall K 0 : Set K) \ valBall K 1) := by
    rw [← ordShell_zero]
    ext u
    simp only [mem_ordShell, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      mem_valBall_iff_le_ord u.ne_zero]
    omega
  rw [heq]
  refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS ?_
  rintro x ⟨-, hx⟩
  have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
  exact ⟨Units.mk0 x hx0, rfl⟩

end Decomposition

section QuasiCharacter

variable (χ : Kˣ →* ℂˣ)

def IsUnramifiedChar : Prop := unitFiltrationUnits K 0 ≤ χ.ker

def quasiCharConductor : ℕ := sInf {n : ℕ | unitFiltrationUnits K n ≤ χ.ker}

def quasiCharExponent : ℝ := -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖

variable {χ}

theorem isUnramifiedChar_iff : IsUnramifiedChar χ ↔ ∀ u : Kˣ, ord (u : K) = 0 → χ u = 1 := by
  refine ⟨fun h u hu => h (mem_unitFiltrationUnits_zero_iff_ord.mpr hu), fun h u hu => ?_⟩
  exact h u (mem_unitFiltrationUnits_zero_iff_ord.mp hu)

theorem quasiChar_apply_of_isUnramified (h : IsUnramifiedChar χ) (u : Kˣ) :
    χ u = χ (unifUnit K) ^ ord (u : K) := by
  conv_lhs => rw [eq_unifUnit_zpow_mul u]
  rw [map_mul, MonoidHom.mem_ker.mp (h (unifUnit_zpow_neg_mul_mem u)), mul_one, map_zpow]

theorem quasiChar_apply_eq_of_isUnramified (h : IsUnramifiedChar χ) {π : Kˣ}
    (hπ : ord (π : K) = 1) : χ π = χ (unifUnit K) := by
  rw [quasiChar_apply_of_isUnramified h, hπ, zpow_one]

variable (hχ : Continuous χ)
include hχ

theorem exists_unitFiltrationUnits_le_ker : ∃ n, unitFiltrationUnits K n ≤ χ.ker := by
  refine exists_unitFiltrationUnits_le (GroundTheory.Global.isOpen_ker_of_noSmallSubgroups (fun W hW => ?_)
    GroundTheory.Global.Complex.units_noSmallSubgroups χ hχ)
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp hW
  exact ⟨⟨unitFiltrationUnits K n, isOpen_unitFiltrationUnits n⟩, hn⟩

theorem unitFiltrationUnits_quasiCharConductor_le_ker :
    unitFiltrationUnits K (quasiCharConductor χ) ≤ χ.ker :=
  Nat.sInf_mem (show {n : ℕ | unitFiltrationUnits K n ≤ χ.ker}.Nonempty from
    exists_unitFiltrationUnits_le_ker hχ)

theorem quasiCharConductor_eq_zero_iff : quasiCharConductor χ = 0 ↔ IsUnramifiedChar χ := by
  constructor
  · intro h
    have := unitFiltrationUnits_quasiCharConductor_le_ker hχ
    rwa [h] at this
  · intro h
    exact Nat.eq_zero_of_le_zero (Nat.sInf_le h)

theorem exists_apply_ne_one_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) :
    ∃ v ∈ unitFiltrationUnits K (quasiCharConductor χ - 1), χ v ≠ 1 := by
  have hc : quasiCharConductor χ ≠ 0 := mt (quasiCharConductor_eq_zero_iff hχ).mp h
  have hlt : quasiCharConductor χ - 1 < quasiCharConductor χ := by omega
  have hnot := Nat.notMem_of_lt_sInf hlt
  by_contra hcon
  push_neg at hcon
  exact hnot fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)

omit hχ in
theorem quasiCharConductor_pos (hχ : Continuous χ) (h : ¬ IsUnramifiedChar χ) :
    0 < quasiCharConductor χ :=
  Nat.pos_of_ne_zero (mt (quasiCharConductor_eq_zero_iff hχ).mp h)

theorem norm_quasiChar_apply_eq_one {u : Kˣ} (hu : u ∈ unitFiltrationUnits K 0) :
    ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  have hcont : Continuous fun v : Kˣ => ‖((χ v : ℂˣ) : ℂ)‖ :=
    (Units.continuous_val.comp hχ).norm
  obtain ⟨C, hC⟩ := isCompact_unitFiltrationUnits_zero.exists_bound_of_continuousOn
    hcont.continuousOn
  have key : ∀ v ∈ unitFiltrationUnits K 0, ‖((χ v : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro v hv
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop C).exists
    have := hC (v ^ n) (pow_mem hv n)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), map_pow, Units.val_pow_eq_pow_val,
      norm_pow] at this
    linarith
  have h1 := key u hu
  have h2 := key u⁻¹ (inv_mem hu)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ u : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ u).ne_zero
  have : 1 ≤ ‖((χ u : ℂˣ) : ℂ)‖ := by rwa [inv_le_one₀ hpos] at h2
  linarith

theorem norm_quasiChar_apply (u : Kˣ) :
    ‖((χ u : ℂˣ) : ℂ)‖ = (modulus (u : K) : ℝ) ^ quasiCharExponent χ := by
  have hq := residueCard_pos_real (K := K)
  have hq1 : (residueCard K : ℝ) ≠ 1 := by exact_mod_cast (one_lt_residueCard (K := K)).ne'
  have hr : 0 < ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ _).ne_zero
  conv_lhs => rw [eq_unifUnit_zpow_mul u]
  rw [map_mul, Units.val_mul, norm_mul,
    norm_quasiChar_apply_eq_one hχ (unifUnit_zpow_neg_mul_mem u), mul_one, map_zpow,
    Units.val_zpow_eq_zpow_val, norm_zpow, modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow,
    NNReal.coe_natCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le,
    quasiCharExponent]
  rw [show ((-ord (u : K) : ℤ) : ℝ) * -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ =
      Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ * (ord (u : K) : ℝ) by push_cast; ring,
    Real.rpow_mul hq.le, Real.rpow_logb hq hq1 hr]

omit hχ in
theorem continuous_quasiChar_inv (hχ : Continuous χ) : Continuous (χ⁻¹ : Kˣ →* ℂˣ) := by
  have : ((χ⁻¹ : Kˣ →* ℂˣ) : Kˣ → ℂˣ) = fun u => (χ u)⁻¹ := by
    funext u
    rfl
  rw [this]
  exact hχ.inv


omit hχ in
theorem quasiCharExponent_inv : quasiCharExponent χ⁻¹ = -quasiCharExponent χ := by
  simp only [quasiCharExponent, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv,
    Real.logb_inv, neg_neg]

end QuasiCharacter

section ShellIntegral

variable [MeasurableSpace K] [BorelSpace K] {χ : Kˣ →* ℂˣ}


open scoped Classical in
theorem setIntegral_ordShell_quasiChar (hχ : Continuous χ) (k : ℤ) :
    ∫ u in ordShell K k, ((χ u : ℂˣ) : ℂ) ∂multHaar K =
      if IsUnramifiedChar χ then ((χ (unifUnit K) : ℂˣ) : ℂ) ^ k else 0 := by
  have hk : ord ((unifUnit K ^ k : Kˣ) : K) + 0 = k := by rw [ord_unifUnit_zpow, add_zero]
  have e := setIntegral_ordShell_mul (fun u : Kˣ => ((χ u : ℂˣ) : ℂ)) (unifUnit K ^ k) 0
  rw [hk] at e
  rw [e]
  simp only [map_mul, Units.val_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  rw [integral_const_mul]
  split_ifs with h
  · have hone : ∀ u ∈ ordShell K 0, ((χ u : ℂˣ) : ℂ) = 1 := fun u hu => by
      rw [(isUnramifiedChar_iff.mp h) u hu, Units.val_one]
    rw [setIntegral_congr_fun (measurableSet_ordShell 0) hone, setIntegral_const,
      measureReal_def, multHaar_ordShell, ENNReal.toReal_one, one_smul, mul_one]
  · obtain ⟨v, hv, hv1⟩ : ∃ v ∈ unitFiltrationUnits K 0, χ v ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact h fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)
    rw [setIntegral_ordShell_eq_zero (fun u => ((χ u : ℂˣ) : ℂ))
      (mem_unitFiltrationUnits_zero_iff_ord.mp hv) (a := ((χ v : ℂˣ) : ℂ))
      (fun h1 => hv1 (Units.val_eq_one.mp h1)) 0 (fun u _ => by simp), mul_zero]

end ShellIntegral

end GroundTheory.LocalField
end
end

