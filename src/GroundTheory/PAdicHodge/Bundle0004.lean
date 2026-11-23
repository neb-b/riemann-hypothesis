module

public import Mathlib
public import GroundTheory.LocalFields.SeparableClosure
public import GroundTheory.PAdicHodge.NormalizedTraceTower
public import GroundTheory.PAdicHodge.NormalizedTraceClosure
public import GroundTheory.PAdicHodge.CyclotomicTower
public import GroundTheory.PAdicHodge.PerfectoidField
public import GroundTheory.PAdicHodge.TiltValuation
public import GroundTheory.PAdicHodge.TiltField
public import GroundTheory.PAdicHodge.KerTheta
public import GroundTheory.PAdicHodge.TiltMap

@[expose] public section

-- bundled from GroundTheory.PAdicHodge.FieldOfNormsTower
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology

section Nrm

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

def nrm (x : Ω) : ℝ :=
  letI := normedField K
  spectralNorm K Ω x

variable {K}

theorem nrm_nonneg (x : Ω) : 0 ≤ nrm K x := by
  letI := algebraicNormedField K Ω
  change 0 ≤ ‖x‖
  exact norm_nonneg x

@[simp]
theorem nrm_zero : nrm K (0 : Ω) = 0 := by
  letI := algebraicNormedField K Ω
  change ‖(0 : Ω)‖ = 0
  exact norm_zero

@[simp]
theorem nrm_one : nrm K (1 : Ω) = 1 := by
  letI := algebraicNormedField K Ω
  change ‖(1 : Ω)‖ = 1
  exact norm_one

theorem nrm_mul (x y : Ω) : nrm K (x * y) = nrm K x * nrm K y := by
  letI := algebraicNormedField K Ω
  change ‖x * y‖ = ‖x‖ * ‖y‖
  exact norm_mul x y

theorem nrm_pow (x : Ω) (n : ℕ) : nrm K (x ^ n) = nrm K x ^ n := by
  letI := algebraicNormedField K Ω
  change ‖x ^ n‖ = ‖x‖ ^ n
  exact norm_pow x n

@[simp]
theorem nrm_neg (x : Ω) : nrm K (-x) = nrm K x := by
  letI := algebraicNormedField K Ω
  change ‖-x‖ = ‖x‖
  exact norm_neg x

theorem nrm_pos {x : Ω} : 0 < nrm K x ↔ x ≠ 0 := by
  letI := algebraicNormedField K Ω
  change 0 < ‖x‖ ↔ x ≠ 0
  exact norm_pos_iff

theorem nrm_inv (x : Ω) : nrm K x⁻¹ = (nrm K x)⁻¹ := by
  letI := algebraicNormedField K Ω
  change ‖x⁻¹‖ = ‖x‖⁻¹
  exact norm_inv x

theorem nrm_div (x y : Ω) : nrm K (x / y) = nrm K x / nrm K y := by
  letI := algebraicNormedField K Ω
  change ‖x / y‖ = ‖x‖ / ‖y‖
  exact norm_div x y

theorem nrm_add_le_max (x y : Ω) : nrm K (x + y) ≤ max (nrm K x) (nrm K y) := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖x + y‖ ≤ max ‖x‖ ‖y‖
  exact IsUltrametricDist.norm_add_le_max x y

theorem nrm_add_le_of_le {x y : Ω} {r : ℝ} (hx : nrm K x ≤ r) (hy : nrm K y ≤ r) :
    nrm K (x + y) ≤ r :=
  (nrm_add_le_max x y).trans (max_le hx hy)

theorem nrm_sum_le {ι : Type*} {s : Finset ι} {f : ι → Ω} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, nrm K (f i) ≤ C) : nrm K (∑ i ∈ s, f i) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact nrm_add_le_of_le (h j (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

theorem nrm_natCast_le_one (n : ℕ) : nrm K (n : Ω) ≤ 1 := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖(n : Ω)‖ ≤ 1
  exact IsUltrametricDist.norm_natCast_le_one Ω n

theorem nrm_algEquiv (σ : Ω ≃ₐ[K] Ω) (x : Ω) : nrm K (σ x) = nrm K x := by
  letI := normedField K
  exact (spectralNorm_eq_of_equiv σ x).symm


variable [ValuativeRel Ω] [ValuativeExtension K Ω]

theorem nrm_le_nrm_iff (x y : Ω) : nrm K x ≤ nrm K y ↔ x ≤ᵥ y :=
  (vle_iff_spectralNorm_le (K := K) x y).symm

variable [TopologicalSpace Ω] [IsValuativeTopology Ω]


end Nrm

section Estimates

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

variable {p : ℕ}

end Estimates

section Tower

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)

structure NormTower where

  E : ℕ → IntermediateField K Ω
  mono : Monotone E
  finiteDimensional : ∀ n, FiniteDimensional K (E n)

  T : ℕ → Finset Gal(Ω/K)
  fix : ∀ n, ∀ σ ∈ T n, ∀ x ∈ E n, σ x = x
  prod_mem : ∀ n, ∀ y ∈ E (n + 1), (∏ σ ∈ T n, σ y) ∈ E n

  k : ℕ → ℕ
  card_alt : ∀ n, (T n).card = p ^ k n
  frequently_ne_zero : ∀ n, ∃ m, n ≤ m ∧ k m ≠ 0

  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  step : ∀ n, ∀ σ ∈ T n, ∀ x ∈ E (n + 1), nrm K (σ x - x) ≤ c * nrm K x
  prime : p.Prime
  nrm_p_lt_one : nrm K (p : Ω) < 1

  value : ℕ → ℝ
  value_pos : ∀ n, 0 < value n
  value_lt_one : ∀ n, value n < 1
  exists_value : ∀ n, ∃ π ∈ E n, nrm K π = value n
  value_zpow : ∀ n, ∀ y ∈ E n, y ≠ 0 → ∃ j : ℤ, nrm K y = value n ^ j
  value_succ : ∀ n, value (n + 1) ^ (p ^ k n) = value n

namespace NormTower

variable {K Ω p} (t : NormTower K Ω p)

end NormTower

end Tower

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.TateNormalizedTrace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Module Set

noncomputable section

variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]

def tateTrace (n : ℕ) : PadicAlgCl p → PadicAlgCl p := normTrace (cyclotomicLayer K n)

theorem tateTrace_add (n : ℕ) (y z : PadicAlgCl p) :
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  normTrace_add _ y z

theorem tateTrace_mem (n : ℕ) (y : PadicAlgCl p) : tateTrace K n y ∈ cyclotomicLayer K n :=
  normTrace_mem _ y

theorem tateTrace_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTrace K n a = a :=
  normTrace_of_mem _ ha

theorem tateTrace_mul_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n)
    (y : PadicAlgCl p) : tateTrace K n (a * y) = a * tateTrace K n y :=
  normTrace_mul_of_mem _ ha y

theorem tateTrace_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    tateTrace K n (σ y) = σ (tateTrace K n y) :=
  normTrace_cyclotomicLayer_gal K σ n y

theorem tateTrace_tateTrace_of_le {n n' : ℕ} (h : n ≤ n') (y : PadicAlgCl p) :
    tateTrace K n (tateTrace K n' y) = tateTrace K n y :=
  normTrace_normTrace_of_le (cyclotomicLayer_mono K h) y

theorem exists_norm_tateTrace_le_of_stableIndex_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, stableIndex K ≤ n → ∀ x ∈ cyclotomicLimit K,
      ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  refine ⟨p * ∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro n hn x hx
  obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hx
  have hm' : x ∈ cyclotomicLayer K (max m n) := cyclotomicLayer_mono K (le_max_left m n) hm
  refine norm_normTrace_cyclotomicLayer_le K (Nat.cast_nonneg p) ?_ hn (le_max_right m n) hm'
  intro n' m' hn' hnm' y hy
  exact norm_normTrace_cycl_le
    (le_trans (by norm_num) ((two_le_stableIndex K).trans hn')) hnm' hy

theorem exists_norm_tateTrace_le_on_layer (n N : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ cyclotomicLayer K N, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  let S : Submodule ℚ_[p] (PadicAlgCl p) := (cyclotomicLayer K N).toSubalgebra.toSubmodule
  haveI : FiniteDimensional ℚ_[p] S :=
    inferInstanceAs (FiniteDimensional ℚ_[p] (cyclotomicLayer K N))
  let f : S →ₗ[ℚ_[p]] PadicAlgCl p :=
    ((normTraceₗ (cyclotomicLayer K n)).restrictScalars ℚ_[p]).comp S.subtype
  let f' := LinearMap.toContinuousLinearMap f
  refine ⟨‖f'‖, ContinuousLinearMap.opNorm_nonneg f', fun x hx => ?_⟩
  have := f'.le_opNorm ⟨x, hx⟩
  exact this

theorem exists_norm_tateTrace_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, ∀ x ∈ cyclotomicLimit K, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_tateTrace_le_of_stableIndex_le K
  choose c' hc'0 hc' using fun n => exists_norm_tateTrace_le_on_layer K n (stableIndex K)
  refine ⟨c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n), by
    have : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
    positivity, ?_⟩
  intro n x hx
  have hs : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
  by_cases hn : stableIndex K ≤ n
  · calc ‖tateTrace K n x‖ ≤ c * ‖x‖ := hc n hn x hx
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        nlinarith [mul_nonneg (mul_nonneg hc0 hs) (norm_nonneg x)]
  · push_neg at hn
    have hle : c' n ≤ ∑ n ∈ Finset.range (stableIndex K), c' n :=
      Finset.single_le_sum (fun n _ => hc'0 n) (Finset.mem_range.2 hn)
    rw [← tateTrace_tateTrace_of_le K hn.le x]
    calc ‖tateTrace K n (tateTrace K (stableIndex K) x)‖
        ≤ c' n * ‖tateTrace K (stableIndex K) x‖ := hc' n _ (tateTrace_mem K _ x)
      _ ≤ c' n * (c * ‖x‖) := mul_le_mul_of_nonneg_left (hc _ le_rfl x hx) (hc'0 n)
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        have := norm_nonneg x
        nlinarith [mul_nonneg hc0 this]

def tateBound : ℝ := Classical.choose (exists_norm_tateTrace_le K)

theorem tateBound_nonneg : 0 ≤ tateBound K := (Classical.choose_spec (exists_norm_tateTrace_le K)).1

theorem norm_tateTrace_le (n : ℕ) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    ‖tateTrace K n x‖ ≤ tateBound K * ‖x‖ :=
  (Classical.choose_spec (exists_norm_tateTrace_le K)).2 n x hx

section Completion

def cyclotomicCompletion : Set ℂ_[p] := closureInCp (cyclotomicLimit K)

def tateTraceHat (n : ℕ) : ℂ_[p] → ℂ_[p] := extendToClosure (cyclotomicLimit K) (tateTrace K n)

variable {K}

theorem tateTrace_add_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K, ∀ z ∈ cyclotomicLimit K,
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  fun y _ z _ => tateTrace_add K n y z

theorem norm_tateTrace_le_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K,
    ‖tateTrace K n y‖ ≤ tateBound K * ‖y‖ :=
  fun _ hy => norm_tateTrace_le K n hy

theorem norm_tateTraceHat_le (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    ‖tateTraceHat K n x‖ ≤ tateBound K * ‖x‖ :=
  norm_extendToClosure_le (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx

theorem tateTraceHat_add (n : ℕ) {x x' : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K)
    (hx' : x' ∈ cyclotomicCompletion K) :
    tateTraceHat K n (x + x') = tateTraceHat K n x + tateTraceHat K n x' :=
  (extendToClosure_add (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx hx').2

theorem tateTraceHat_mem (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n x ∈
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (cyclotomicLayer K n : Set (PadicAlgCl p)) :=
  extendToClosure_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (fun y _ => tateTrace_mem K n y) hx

theorem tateTraceHat_coe_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTraceHat K n (a : ℂ_[p]) = a :=
  extendToClosure_coe_of_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha => tateTrace_of_mem K ha) ha

theorem tateTraceHat_mul {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * tateTraceHat K n x :=
  extendToClosure_mul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha y _ => tateTrace_mul_of_mem K ha y) ha hx

theorem gal_mem_cyclotomicLimit (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLimit K) : σ y ∈ cyclotomicLimit K :=
  map_mem_cyclotomicLimit K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) hy

theorem smul_mem_cyclotomicCompletion (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : σ • x ∈ cyclotomicCompletion K :=
  smul_mem_closureInCp σ (fun _ hy => gal_mem_cyclotomicLimit σ hy) hx

theorem tateTraceHat_smul (n : ℕ) (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : tateTraceHat K n (σ • x) = σ • tateTraceHat K n x :=
  extendToClosure_smul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) σ
    (fun _ hy => gal_mem_cyclotomicLimit σ hy) (fun y _ => tateTrace_gal K σ n y) hx

end Completion

section Gamma

variable {K}

end Gamma

end

end GroundTheory.PAdicHodge
end

-- bundled from GroundTheory.PAdicHodge.TiltAlgebra
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Functor

variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M] [IsUltrametricDist M]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]
omit [IsUltrametricDist K] [IsUltrametricDist L] [IsUltrametricDist M] in
theorem norm_comp_eq {φ : K →+* L} (hφ : ∀ x, ‖φ x‖ = ‖x‖) {ψ : L →+* M}
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (x : K) : ‖(ψ.comp φ) x‖ = ‖x‖ := by
  rw [RingHom.comp_apply, hψ, hφ]

variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (ψ : L →+* M) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)

theorem preTiltMap_comp :
    preTiltMap (p := p) (ψ.comp φ) (norm_comp_eq hφ hψ) =
      (preTiltMap (p := p) ψ hψ).comp (preTiltMap (p := p) φ hφ) := by
  refine RingHom.ext fun x => Perfection.ext fun n => ?_
  rw [RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, coeff_preTiltMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (Perfection.coeff (ModP (normInteger K) p) p n x)
  rw [← ha, modPMap_mk, modPMap_mk, modPMap_mk]
  rfl

end Functor

section Density

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]


end Density

section Algebra

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

end Algebra

section IntermediateField

variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]

end IntermediateField

section TiltIntermediate

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

variable (F : IntermediateField K C) [IsPerfectoidField F p]




end TiltIntermediate

end GroundTheory.PAdicHodge
end
end

