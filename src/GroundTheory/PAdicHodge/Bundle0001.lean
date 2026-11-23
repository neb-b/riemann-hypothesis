module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.PAdicHodge.LogPowSeries
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

theorem X_dvd_one_add_X_pow_sub_one {R : Type*} [CommRing R] (q : ℕ) :
    (Polynomial.X : Polynomial R) ∣ (1 + Polynomial.X) ^ q - 1 := by
  have h := sub_dvd_pow_sub_pow (1 + Polynomial.X : Polynomial R) 1 q
  rwa [one_pow, add_sub_cancel_left] at h

theorem coeff_one_add_X_pow_sub_one_pow_of_lt {R : Type*} [CommRing R] (q : ℕ) {m n : ℕ}
    (h : m < n) : (((1 + Polynomial.X : Polynomial R) ^ q - 1) ^ n).coeff m = 0 := by
  obtain ⟨g, hg⟩ := pow_dvd_pow_of_dvd (X_dvd_one_add_X_pow_sub_one (R := R) q) n
  rw [hg, Polynomial.coeff_X_pow_mul', if_neg (not_le.2 h)]

theorem one_add_X_mul_mk_neg_one_pow :
    (1 + X : ℚ⟦X⟧) * mk (fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add (f := _)]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one, if_neg n.succ_ne_zero]
    simp [pow_succ]

theorem hasSubst_one_add_X_pow_sub_one (q : ℕ) : HasSubst ((1 + X : ℚ⟦X⟧) ^ q - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

theorem PowerSeries.log_subst_one_add_X_pow_sub_one (q : ℕ) :
    (log ℚ).subst ((1 + X : ℚ⟦X⟧) ^ q - 1) = (q : ℚ⟦X⟧) * log ℚ := by
  set U : ℚ⟦X⟧ := (1 + X) ^ q - 1 with hU
  have hs : HasSubst U := hasSubst_one_add_X_pow_sub_one q
  set G : ℚ⟦X⟧ := mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)
  have hG : (1 + U) * G.subst U = 1 := by
    have h := congrArg (substAlgHom (R := ℚ) hs) one_add_X_mul_mk_neg_one_pow
    rw [map_mul, map_add (f := _), map_one] at h
    simp only [coe_substAlgHom] at h
    rwa [subst_X hs] at h
  have h1U : 1 + U = (1 + X) ^ q := by rw [hU]; ring
  apply derivative.ext
  · have hd : d⁄dX ((log ℚ).subst U) = d⁄dX ((q : ℚ⟦X⟧) * log ℚ) := by
      have hunit : IsUnit (1 + X : ℚ⟦X⟧) := by
        rw [isUnit_iff_constantCoeff]; simp
      apply hunit.mul_left_cancel
      rw [derivative_subst hs, deriv_log, Derivation.leibniz, deriv_log]
      rcases q with _ | q
      · simp [hU]
      · have hdU : d⁄dX U = ((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q := by
          rw [hU, map_sub, derivative_pow, Derivation.map_one_eq_zero, sub_zero, map_add (f := _),
            Derivation.map_one_eq_zero, derivative_X, zero_add, mul_one, Nat.add_sub_cancel]
        rw [hdU]
        have hc : d⁄dX ((q + 1 : ℕ) : ℚ⟦X⟧) = 0 := by
          rw [← map_natCast (C (R := ℚ)), derivative_C]
        rw [hc, smul_zero, add_zero, smul_eq_mul]
        calc (1 + X) * (G.subst U * (((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q))
            = ((q + 1 : ℕ) : ℚ⟦X⟧) * ((1 + X) ^ (q + 1) * G.subst U) := by ring
          _ = ((q + 1 : ℕ) : ℚ⟦X⟧) := by rw [← h1U, hG, mul_one]
          _ = (1 + X) * (((q + 1 : ℕ) : ℚ⟦X⟧) * G) := by
            rw [mul_left_comm, one_add_X_mul_mk_neg_one_pow, mul_one]
    exact hd
  · have h0 : constantCoeff U = 0 := by simp [hU]
    have h1 : constantCoeff ((log ℚ).subst U) = 0 :=
      constantCoeff_subst_eq_zero h0 _ constantCoeff_log
    rw [h1]
    simp

theorem one_add_X_pow_sub_one_eq_coe (q : ℕ) :
    ((1 + X : ℚ⟦X⟧) ^ q - 1) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1 : Polynomial ℚ) : ℚ⟦X⟧) := by
  simp

theorem sum_coeff_one_add_X_pow_sub_one_pow (q : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m = (-1) ^ (m - 1) * q / m := by
  have h := congrArg (coeff m) (PowerSeries.log_subst_one_add_X_pow_sub_one q)
  rw [coeff_subst' (hasSubst_one_add_X_pow_sub_one q), one_add_X_pow_sub_one_eq_coe] at h
  simp only [← Polynomial.coe_pow, Polynomial.coeff_coe, smul_eq_mul] at h
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc 1 m) ?_] at h
  · have hr : coeff m ((q : ℚ⟦X⟧) * log ℚ) = q * ((-1) ^ (m - 1) / m) := by
      rw [show (q : ℚ⟦X⟧) = C (q : ℚ) from (map_natCast C q).symm, coeff_C_mul, coeff_log,
        if_neg (by omega), Algebra.algebraMap_self, RingHom.id_apply]
      congr 2
      rw [show m + 1 = (m - 1) + 2 by omega, pow_add]; simp
    rw [hr] at h
    rw [show (-1 : ℚ) ^ (m - 1) * q / m = q * ((-1) ^ (m - 1) / m) by ring, ← h]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
    rw [coeff_log, if_neg hn1, Algebra.algebraMap_self, RingHom.id_apply,
      show n + 1 = (n - 1) + 2 by omega, pow_add]
    simp
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    rcases Nat.lt_or_ge n 1 with h1 | h1
    · obtain rfl : n = 0 := by omega
      simp at hn
    · have hlt : m < n := by omega
      rw [coeff_one_add_X_pow_sub_one_pow_of_lt q hlt, mul_zero] at hn
      exact hn rfl

theorem log_pow_coeff_int (q m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (n - 1) *
      ((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m * ((m.factorial / n : ℕ) : ℤ) =
      (-1) ^ (m - 1) * q * (m - 1).factorial := by
  apply Int.cast_injective (α := ℚ)
  have hcoe : ∀ n : ℕ, (((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m : ℚ) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := fun n => by
    rw [← eq_intCast (Int.castRingHom ℚ), ← Polynomial.coeff_map]
    simp [Polynomial.map_pow]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, hcoe]
  have hdiv : ∀ n ∈ Finset.Icc 1 m, (((m.factorial / n : ℕ) : ℚ)) = m.factorial / n := fun n hn => by
    have h1 := (Finset.mem_Icc.1 hn)
    rw [Nat.cast_div (Nat.dvd_factorial (by omega) h1.2) (by exact_mod_cast (show n ≠ 0 by omega))]
  rw [Finset.sum_congr rfl fun n hn => by rw [hdiv n hn]]
  have hfac : (m.factorial : ℚ) = m * (m - 1).factorial := by
    rw [← Nat.cast_mul, ← Nat.mul_factorial_pred (by omega)]
  calc ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) *
        ((((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m) * (m.factorial / n)
      = m.factorial * ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
        (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ = (-1) ^ (m - 1) * q * (m - 1).factorial := by
        rw [sum_coeff_one_add_X_pow_sub_one_pow q hm, hfac]
        field_simp

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.RobbaSeries
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology

namespace Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

def ConvergesAt (a : ℤ → K) (ρ : ℝ) : Prop :=
  Tendsto (fun n : ℤ => ‖a n‖ * ρ ^ n) cofinite (𝓝 0)

def gaussNorm (a : ℤ → K) (ρ : ℝ) : ℝ := ⨆ n, ‖a n‖ * ρ ^ n

def domSet (a : ℤ → K) (ρ : ℝ) : Set ℤ := {n | ‖a n‖ * ρ ^ n = gaussNorm a ρ}

def lowIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sInf (domSet a ρ)

def highIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sSup (domSet a ρ)

variable {a b c : ℤ → K} {ρ : ℝ}

section Basic

theorem ConvergesAt.bddAbove (h : ConvergesAt a ρ) :
    BddAbove (Set.range fun n : ℤ => ‖a n‖ * ρ ^ n) :=
  h.bddAbove_range_of_cofinite

theorem ConvergesAt.le_gaussNorm (h : ConvergesAt a ρ) (n : ℤ) :
    ‖a n‖ * ρ ^ n ≤ gaussNorm a ρ :=
  le_ciSup h.bddAbove n

theorem gaussNorm_le {C : ℝ} (h : ∀ n, ‖a n‖ * ρ ^ n ≤ C) : gaussNorm a ρ ≤ C :=
  ciSup_le h

theorem gaussNorm_nonneg (hρ : 0 < ρ) : 0 ≤ gaussNorm a ρ :=
  Real.iSup_nonneg fun n => by positivity

theorem ConvergesAt.finite_le (h : ConvergesAt a ρ) {ε : ℝ} (hε : 0 < ε) :
    {n | ε ≤ ‖a n‖ * ρ ^ n}.Finite := by
  have := Filter.eventually_cofinite.1 (h.eventually (gt_mem_nhds hε))
  simpa only [not_lt] using this

end Basic

section Product

variable [CompleteSpace K]

end Product

section Dominant

section Attained

variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha

theorem ConvergesAt.exists_eq_gaussNorm : ∃ n, ‖a n‖ * ρ ^ n = gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have hε : 0 < ‖a n0‖ * ρ ^ n0 := by have := norm_pos_iff.2 hn0; positivity
  set S := (h.finite_le hε).toFinset
  have hn0S : n0 ∈ S := by simp [S]
  obtain ⟨m, hmS, hm⟩ := S.exists_max_image (fun n => ‖a n‖ * ρ ^ n) ⟨n0, hn0S⟩
  refine ⟨m, le_antisymm (h.le_gaussNorm m) (gaussNorm_le fun n => ?_)⟩
  by_cases hn : n ∈ S
  · exact hm n hn
  · simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hn
    exact hn.le.trans (hm n0 hn0S)

theorem gaussNorm_pos : 0 < gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have := norm_pos_iff.2 hn0
  exact lt_of_lt_of_le (by positivity) (h.le_gaussNorm n0)

theorem domSet_finite : (domSet a ρ).Finite :=
  (h.finite_le (gaussNorm_pos hρ h ha)).subset fun n hn => le_of_eq (Eq.symm hn)

theorem domSet_nonempty : (domSet a ρ).Nonempty :=
  h.exists_eq_gaussNorm hρ ha

theorem lowIndex_mem : lowIndex a ρ ∈ domSet a ρ :=
  Int.csInf_mem (domSet_nonempty hρ h ha) (domSet_finite hρ h ha).bddBelow

theorem highIndex_mem : highIndex a ρ ∈ domSet a ρ :=
  Int.csSup_mem (domSet_nonempty hρ h ha) (domSet_finite hρ h ha).bddAbove

theorem lowIndex_le {n : ℤ} (hn : n ∈ domSet a ρ) : lowIndex a ρ ≤ n :=
  csInf_le (domSet_finite hρ h ha).bddBelow hn

theorem le_highIndex {n : ℤ} (hn : n ∈ domSet a ρ) : n ≤ highIndex a ρ :=
  le_csSup (domSet_finite hρ h ha).bddAbove hn

theorem weight_lt_of_lt_lowIndex {n : ℤ} (hn : n < lowIndex a ρ) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ :=
  lt_of_le_of_ne (h.le_gaussNorm n) fun heq => absurd (lowIndex_le hρ h ha heq) (not_le.2 hn)

theorem weight_lt_of_highIndex_lt {n : ℤ} (hn : highIndex a ρ < n) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ :=
  lt_of_le_of_ne (h.le_gaussNorm n) fun heq => absurd (le_highIndex hρ h ha heq) (not_le.2 hn)

theorem ne_zero_of_mem_domSet {n : ℤ} (hn : n ∈ domSet a ρ) : a n ≠ 0 := by
  intro h0
  have := gaussNorm_pos hρ h ha
  simp only [domSet, Set.mem_setOf_eq, h0, norm_zero, zero_mul] at hn
  linarith

end Attained

section Multiplicative

variable [CompleteSpace K]

variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0

end Multiplicative

end Dominant

end Laurent

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.SemilinearResidue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Polynomial Module Finset

namespace SemilinearResidue

section Poly

variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]


omit [CharP k p] in
include hp in
theorem two_le_pow {e : ℕ} (he : 0 < e) : 2 ≤ p ^ e :=
  calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos he

variable {e : ℕ}

end Poly

section Vec

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem linearIndependent_of_notMem_span (v : ℕ → V) : ∀ m : ℕ,
    (∀ j < m, v j ∉ Submodule.span k (Set.range (fun i : Fin j => v i))) →
      LinearIndependent k (fun i : Fin m => v i) := by
  intro m
  induction m with
  | zero => exact fun _ => linearIndependent_empty_type
  | succ m ih =>
    intro h
    exact linearIndependent_finSucc'.mpr
      ⟨ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h m (Nat.lt_succ_self m)⟩


variable (k) in
theorem exists_rel [FiniteDimensional k V] (v : ℕ → V) :
    ∃ m, (∃ c : ℕ → k, v m = ∑ i ∈ range m, c i • v i) ∧
      LinearIndependent k (fun i : Fin m => v i) := by
  classical
  let P : ℕ → Prop := fun j => v j ∈ Submodule.span k (Set.range (fun i : Fin j => v i))
  have hex : ∃ j, P j := by
    by_contra hcon
    push Not at hcon
    have li := linearIndependent_of_notMem_span v (finrank k V + 1) (fun j _ => hcon j)
    have := li.fintype_card_le_finrank
    simp at this
  refine ⟨Nat.find hex, ?_, linearIndependent_of_notMem_span v _ (fun j hj => Nat.find_min hex hj)⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (Nat.find_spec hex)
  refine ⟨fun i => if h : i < Nat.find hex then c ⟨i, h⟩ else 0, ?_⟩
  rw [← hc, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [i.2]

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}


end Vec

end SemilinearResidue

end GroundTheory.PAdicHodge
end

-- bundled from GroundTheory.PAdicHodge.SenTateCharQp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]

theorem norm_eq_one_of_compactSpace (η : G →* ℚ_[p]ˣ) (hη : Continuous η) (σ : G) :
    ‖((η σ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
  set f : G → ℝ := fun τ => ‖((η τ : ℚ_[p]ˣ) : ℚ_[p])‖ with hf
  have hcont : Continuous f := (Units.continuous_val.comp hη).norm
  obtain ⟨τ₀, -, hτ₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hbound : ∀ τ, f τ ≤ f τ₀ := fun τ => hτ₀ (Set.mem_univ τ)
  have hpow : ∀ τ : G, ∀ n : ℕ, f (τ ^ n) = f τ ^ n := by
    intro τ n
    simp only [hf, map_pow, Units.val_pow_eq_pow_val, norm_pow]
  have hle : ∀ τ, f τ ≤ 1 := by
    intro τ
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop (f τ₀) |>.exists
    have := hbound (τ ^ n)
    rw [hpow] at this
    linarith
  have hmul : f σ * f σ⁻¹ = 1 := by
    simp only [hf, map_inv, ← norm_mul, Units.val_inv_eq_inv_val]
    rw [mul_inv_cancel₀ (Units.ne_zero _), norm_one]
  have h0 : 0 ≤ f σ⁻¹ := norm_nonneg _
  apply le_antisymm (hle σ)
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt (hle σ⁻¹)
  linarith

theorem exists_continuous_units_padicInt_lift (η : G →* ℚ_[p]ˣ) (hη : Continuous η) :
    ∃ η' : G →* ℤ_[p]ˣ, Continuous η' ∧ ∀ σ, (((η' σ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = η σ := by
  have h1 := norm_eq_one_of_compactSpace η hη
  let η' : G →* ℤ_[p]ˣ :=
    { toFun := fun σ => PadicInt.mkUnits (h1 σ)
      map_one' := by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, map_one]
        rfl
      map_mul' := fun σ τ => by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq,
          PadicInt.mkUnits_eq, map_mul, Units.val_mul] }
  refine ⟨η', ?_, fun σ => PadicInt.mkUnits_eq (h1 σ)⟩
  have hval : Continuous fun σ => ((η σ : ℚ_[p]ˣ) : ℚ_[p]) := Units.continuous_val.comp hη
  have hinv : Continuous fun σ => (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) :=
    Units.continuous_val.comp (continuous_inv.comp hη)
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun σ => (⟨((η σ : ℚ_[p]ˣ) : ℚ_[p]), (h1 σ).le⟩ : ℤ_[p])
    exact hval.subtype_mk _
  · have hn : ∀ σ, ‖(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := fun σ => by
      rw [← map_inv]; exact (h1 σ⁻¹).le
    have e : (fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) =
        fun σ => (⟨(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), hn σ⟩ : ℤ_[p]) := by
      funext σ
      apply PadicInt.ext
      rw [← map_inv η' σ]
      show ((PadicInt.mkUnits (h1 σ⁻¹) : ℤ_[p]) : ℚ_[p]) = (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])
      rw [PadicInt.mkUnits_eq, map_inv]
    change Continuous fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    rw [e]
    exact hinv.subtype_mk _

end SenTateChar

end GroundTheory.PAdicHodge
end
end

