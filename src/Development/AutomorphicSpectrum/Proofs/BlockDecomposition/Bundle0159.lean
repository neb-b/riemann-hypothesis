module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0039
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import GroundTheory.PAdicHodge.BStPeriod
public import GroundTheory.PAdicHodge.KerTheta
public import GroundTheory.PAdicHodge.TiltValuation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPairUnitaryTransitive
section
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry

open GlobalTheory.CompanionTheory.SW.QuasiRefl

section Form

variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}

theorem hform_add_fst (x x' y : Fin N → A) :
    hform τ H (x + x') y = hform τ H x y + hform τ H x' y := by
  have h : (τ ∘ (x + x')) = τ ∘ x + τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, add_dotProduct]

theorem hform_add_snd (x y y' : Fin N → A) :
    hform τ H x (y + y') = hform τ H x y + hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_add, dotProduct_add]

theorem hform_sub_fst (x x' y : Fin N → A) :
    hform τ H (x - x') y = hform τ H x y - hform τ H x' y := by
  have h : (τ ∘ (x - x')) = τ ∘ x - τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, sub_dotProduct]

theorem hform_sub_snd (x y y' : Fin N → A) :
    hform τ H x (y - y') = hform τ H x y - hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_sub, dotProduct_sub]

theorem hform_unitary {g : GL (Fin N) A} (hg : g ∈ UJ τ H) (x y : Fin N → A) :
    hform τ H ((g : Matrix (Fin N) (Fin N) A) *ᵥ x) ((g : Matrix (Fin N) (Fin N) A) *ᵥ y) =
      hform τ H x y := by
  rw [hform_mulVec']
  have hg' : cT τ (g : Matrix (Fin N) (Fin N) A) * H * (g : Matrix (Fin N) (Fin N) A) = H := hg
  rw [hg']

theorem carry (hτ : ∀ y, τ (τ y) = y)
    (hcar : ∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1)
    (hH : ∀ i j, τ (H j i) = H i j) (x y : Fin N → A)
    (hxy : hform τ H x x = hform τ H y y) (hβ : IsUnit (hform τ H x x)) :
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ x = y ∧
      ∀ z, hform τ H x z = 0 → hform τ H y z = 0 → (g : Matrix (Fin N) (Fin N) A) *ᵥ z = z := by
  have hfix : τ (hform τ H x x) = hform τ H x x := hform_conj_symm hτ hH x x
  obtain ⟨ε, z, hε, hz⟩ := hcar (hform τ H y x) (hform τ H x x) hβ hfix
  exact exists_unitary_carry A τ hτ N H hH x y ε hxy hβ hε ⟨⟨_, z, hz, (mul_comm z _).trans hz⟩, rfl⟩

theorem exists_hyperbolic_partner (hτ : ∀ y, τ (τ y) = y) (h2 : IsUnit (2 : A))
    {Hi : Matrix (Fin N) (Fin N) A} (hHi : H * Hi = 1) (hH : ∀ i j, τ (H j i) = H i j)
    (y a : Fin N → A) (hyy : hform τ H y y = 0) (hay : ∑ k, a k * y k = 1) :
    ∃ y₁ : Fin N → A, hform τ H y₁ y₁ = 0 ∧ hform τ H y y₁ = 1 := by
  have hyw : hform τ H y (Hi *ᵥ (τ ∘ a)) = 1 := by
    rw [hform_eq_dot, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]
    have h : (τ ∘ y) ⬝ᵥ (τ ∘ a) = τ (∑ k, a k * y k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Function.comp_apply, map_sum, map_mul]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    rw [h, hay, map_one]
  have hwy : hform τ H (Hi *ᵥ (τ ∘ a)) y = 1 := by
    rw [← hform_conj_symm hτ hH y (Hi *ᵥ (τ ∘ a)), hyw, map_one]
  have hww : τ (hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := hform_conj_symm hτ hH _ _
  have ht2 : 2 * (↑h2.unit⁻¹ : A) = 1 := h2.mul_val_inv
  have hτt : τ (↑h2.unit⁻¹ : A) = ↑h2.unit⁻¹ := by
    have h1 : τ (↑h2.unit⁻¹ : A) * 2 = 1 := by
      have h := congrArg τ ht2
      rw [map_mul, map_one, map_ofNat] at h
      rw [mul_comm]
      exact h
    calc τ (↑h2.unit⁻¹ : A) = τ (↑h2.unit⁻¹ : A) * (2 * ↑h2.unit⁻¹) := by rw [ht2, mul_one]
      _ = (τ (↑h2.unit⁻¹ : A) * 2) * ↑h2.unit⁻¹ := by ring
      _ = ↑h2.unit⁻¹ := by rw [h1, one_mul]
  have hτc : τ ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      (↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := by
    rw [map_mul, hτt, hww]
  refine ⟨Hi *ᵥ (τ ∘ a) - ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) • y, ?_, ?_⟩
  · rw [hform_sub_left, hform_sub_right, hform_sub_right, hyy, hwy, hyw, hτc]
    linear_combination (-1 : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) * ht2
  · rw [hform_sub_right, hyw, hyy, mul_zero, sub_zero]

end Form

theorem exists_unitary_carry_primitive :
    ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) →
    (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) →
    ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) →
    ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 →
    hform τ H y y = 0 → ∑ k, a k * y k = 1 →
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  intro A _ τ hτ h2 hcar N H Hi hHi hH e f y a hee hff hef hyy hay
  obtain ⟨y₁, hy₁, hyy₁⟩ := exists_hyperbolic_partner hτ h2 hHi hH y a hyy hay
  have hfe : hform τ H f e = 1 := by rw [← hform_conj_symm hτ hH e f, hef, map_one]
  have hy₁y : hform τ H y₁ y = 1 := by rw [← hform_conj_symm hτ hH y y₁, hyy₁, map_one]
  have hx1 : hform τ H (e + f) (e + f) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    norm_num
  have hy1 : hform τ H (y + y₁) (y + y₁) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    norm_num
  obtain ⟨g₁, hg₁, hg₁x, -⟩ := carry hτ hcar hH (e + f) (y + y₁) (by rw [hx1, hy1]) (by rw [hx1]; exact h2)
  have hvv : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) = -2 := by
    rw [hform_unitary hg₁, hform_sub_fst, hform_sub_snd, hform_sub_snd, hee, hef, hfe, hff]
    ring
  have hyy' : hform τ H (y - y₁) (y - y₁) = -2 := by
    rw [hform_sub_fst, hform_sub_snd, hform_sub_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have h2' : IsUnit (-2 : A) := h2.neg
  obtain ⟨g₂, hg₂, hg₂v, hfix⟩ := carry hτ hcar hH ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y - y₁)
    (by rw [hvv, hyy']) (by rw [hvv]; exact h2')
  have hperp1 : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y + y₁) = 0 := by
    rw [← hg₁x, hform_unitary hg₁, hform_sub_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    ring
  have hperp2 : hform τ H (y - y₁) (y + y₁) = 0 := by
    rw [hform_sub_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have hfix' := hfix (y + y₁) hperp1 hperp2
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  have hsum : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e + f) = y + y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁x, hfix']
  have hdiff : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e - f) = y - y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₂v]
  have key : (2 : A) • (((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ e) = (2 : A) • y := by
    have h : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ ((e + f) + (e - f)) = (y + y₁) + (y - y₁) := by
      rw [Matrix.mulVec_add, hsum, hdiff]
    have he : (e + f) + (e - f) = (2 : A) • e := by
      rw [two_smul]
      abel
    have hy : (y + y₁) + (y - y₁) = (2 : A) • y := by
      rw [two_smul]
      abel
    rw [he, Matrix.mulVec_smul, hy] at h
    exact h
  have h3 := congrArg (fun z => (↑h2.unit⁻¹ : A) • z) key
  simp only [smul_smul, h2.val_inv_mul, one_smul] at h3
  exact h3

end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFacts
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltFacts

variable (l : ℕ) [Fact l.Prime]

theorem isDomain_ob : IsDomain (CrystallineSemistableComparison.Ob l) :=
  IsPerfectoidField.isDomain_preTilt (K := ℂ_[l]) l

theorem norm_pFlat_eq : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ = ‖(l : ℂ_[l])‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]

theorem norm_pFlat_pos : 0 < ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ := by
  rw [norm_pFlat_eq]
  exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem norm_pFlat_lt_one : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ < 1 := by
  rw [norm_pFlat_eq]
  exact IsPerfectoidField.norm_natCast_lt_one

theorem rt_pow (k : ℕ) : CrystallineSemistableComparison.D.rt l k ^ l ^ k = pFlat l := by
  have h := (iterateFrobeniusEquiv (CrystallineSemistableComparison.Ob l) l k).apply_symm_apply (pFlat l)
  rwa [iterateFrobeniusEquiv_def] at h

theorem exists_dvd_pFlat_pow (a : CrystallineSemistableComparison.Ob l) (ha : a ≠ 0) : ∃ M : ℕ, a ∣ pFlat l ^ M := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 ha) (norm_pFlat_lt_one l)
  refine ⟨M, preTilt_dvd_iff_norm_le.2 ?_⟩
  rw [norm_pow]
  exact hM.le

theorem exists_rt_dvd (a : CrystallineSemistableComparison.Ob l) (ha : ¬ IsUnit a) : ∃ k : ℕ, CrystallineSemistableComparison.D.rt l k ∣ a := by
  have hlt : ‖a‖ < 1 := by
    refine lt_of_le_of_ne (preTilt_norm_le_one a) fun h => ha ?_
    exact (IsPerfectoidField.isUnit_iff_norm_untilt l).2 (by rwa [preTilt_norm_def] at h)
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pFlat_pos l) hlt
  have hnl : n ≤ l ^ n := (Nat.lt_pow_self hl).le
  refine ⟨n, preTilt_dvd_iff_norm_le.2 ?_⟩
  have h1 : ‖a‖ ^ l ^ n ≤ ‖CrystallineSemistableComparison.D.rt l n‖ ^ l ^ n := by
    rw [← norm_pow (CrystallineSemistableComparison.D.rt l n), rt_pow]
    exact (pow_le_pow_of_le_one (norm_nonneg _) hlt.le hnl).trans hn.le
  exact le_of_pow_le_pow_left₀ (pow_ne_zero _ (by omega)) (norm_nonneg _) h1

theorem obFacts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := by
  intro l _
  haveI := isDomain_ob l
  refine ⟨inferInstance, ?_, exists_dvd_pFlat_pow l, exists_rt_dvd l⟩
  refine (ValuationRing.iff_dvd_total).2 ⟨fun a b => ?_⟩
  rcases le_total ‖a‖ ‖b‖ with h | h
  · exact Or.inr (preTilt_dvd_iff_norm_le.2 h)
  · exact Or.inl (preTilt_dvd_iff_norm_le.2 h)

end GlobalTheory.CompanionTheory.TiltFacts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeDpowClosedOfHyp
section
open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatDP

variable {B : Type} [CommRing B] [Algebra ℚ B]

theorem inv_fact_smul_add_pow_mem (S : Subring B) {z w : B}
    (hz : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • z ^ k ∈ S) (hw : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • w ^ k ∈ S)
    (k : ℕ) : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k ∈ S := by
  have e : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k =
      ∑ i ∈ Finset.range (k + 1), (((i.factorial : ℚ))⁻¹ • z ^ i) * ((((k - i).factorial : ℚ))⁻¹ • w ^ (k - i)) := by
    rw [add_pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hc : ((k.choose i : ℕ) : B) = ((k.choose i : ℕ) : ℚ) • (1 : B) := by
      rw [Algebra.smul_def, mul_one, map_natCast]
    rw [hc, mul_smul_comm, mul_one, smul_smul, smul_mul_smul_comm, Nat.cast_choose ℚ hik]
    congr 1
    have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have h2 : (i.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
    have h3 : ((k - i).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k - i).factorial_ne_zero
    field_simp
  rw [e]
  exact S.sum_mem fun i _ => S.mul_mem (hz i) (hw _)

variable {W : Type} [CommRing W] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem inv_fact_smul_dpE_pow (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • Lat.dpE f ξ l M j ^ k =
      ((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j) := by
  have hU : ((k.uniformBell j : ℕ) : ℚ) * (j.factorial : ℚ) ^ k * (k.factorial : ℚ) = ((k * j).factorial : ℚ) := by
    exact_mod_cast Nat.uniformBell_mul_eq k hj
  have hc : ((k.uniformBell j : ℕ) : B) = ((k.uniformBell j : ℕ) : ℚ) • (1 : B) := by
    rw [Algebra.smul_def, mul_one, map_natCast]
  have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 j.factorial_ne_zero
  have h3 : ((k * j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k * j).factorial_ne_zero
  rw [Lat.dpE, Lat.dpE, smul_pow, ← pow_mul, smul_smul, hc, smul_mul_assoc, one_mul, smul_smul, mul_comm j k]
  congr 1
  have h4 : (j.factorial : ℚ) ^ k ≠ 0 := pow_ne_zero _ h2
  rw [eq_mul_inv_iff_mul_eq₀ h3, ← hU, inv_pow]
  field_simp

theorem inv_fact_smul_term_mem (c : W) (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k ∈ Lat.sub f ξ l M := by
  have e : ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k =
      f c ^ k * (((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j)) := by
    rw [mul_pow, ← mul_smul_comm, inv_fact_smul_dpE_pow f ξ l M j k hj]
  rw [e]
  have hf : f c ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inl ⟨c, rfl⟩)
  have hd : Lat.dpE f ξ l M (k * j) ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  exact mul_mem (pow_mem hf _) (mul_mem (natCast_mem _ _) hd)

theorem inv_fact_smul_sum_mem {n : ℕ} (c : Fin n → W) (s : Finset (Fin n)) (k : ℕ) :
    ((k.factorial : ℚ))⁻¹ • (∑ i ∈ s, f (c i) * Lat.dpE f ξ l M (i + 1)) ^ k ∈ Lat.sub f ξ l M := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · simpa using (Lat.sub f ξ l M).one_mem
    · simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inv_fact_smul_add_pow_mem _ (fun k => inv_fact_smul_term_mem f ξ l M _ _ k (Nat.succ_ne_zero _)) ih k

theorem dpClosed {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ)
    (h : Lat.Hyp f ξ l m) : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ) := by
  intro x hx k
  obtain ⟨n, c, e⟩ := (_root_.GlobalTheory.CompanionTheory.LatIdeal.mem_I f ξ l M m h x).1 hx
  refine ⟨⟨_, inv_fact_smul_sum_mem f ξ l M c Finset.univ k⟩, ?_⟩
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hx, e, Ring.inverse_eq_inv']
  rfl

end GlobalTheory.CompanionTheory.LatDP
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationFg
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatFG

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dpE_eq (i : ℕ) : Lat.dpE f ξ l M i =
    (((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ i := by
  simp only [Lat.dpE, Lat.η, smul_pow, mul_smul]

theorem dpE_mem {k i : ℕ} (h : k ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ k} := by
  rw [dpE_eq, Ideal.mem_span_singleton']
  refine ⟨(((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ (i - k), ?_⟩
  rw [smul_mul_assoc, ← pow_add, Nat.sub_add_cancel h]

variable {f ξ} in
theorem dpE_eq_zero {m : ℕ} (hn : f ξ ^ m = 0) {i : ℕ} (h : m ≤ i) : Lat.dpE f ξ l M i = 0 := by
  rw [dpE_eq, pow_eq_zero_of_le h hn, smul_zero]

theorem mul_dpE {l : ℕ} (hl : l ≠ 0) (j : ℕ) :
    f ξ * Lat.dpE f ξ l M j = ((l ^ M * (j + 1) : ℕ) : B) * Lat.dpE f ξ l M (j + 1) := by
  have hl' : ((l : ℚ) ^ M) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl)
  have h : f ξ = ((l : ℚ) ^ M) • Lat.η f ξ l M := by
    simp only [Lat.η, smul_smul, mul_inv_cancel₀ hl', one_smul]
  have hnat : ((l ^ M * (j + 1) : ℕ) : B) = ((l : ℚ) ^ M * ((j : ℚ) + 1)) • (1 : B) := by
    rw [Algebra.smul_def, mul_one, ← map_natCast (algebraMap ℚ B)]; push_cast; rfl
  simp only [Lat.dpE]
  generalize Lat.η f ξ l M = e at h
  rw [h, hnat]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, pow_succ']
  congr 1
  rw [Nat.factorial_succ]
  have h1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((j.factorial : ℚ)) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  push_cast
  field_simp

variable {f ξ l M} in
theorem sum_single {m : ℕ} (hn : f ξ ^ m = 0) (k : ℕ) (a : W) :
    ∑ i ∈ Finset.range m, f ((Pi.single k a : ℕ → W) i) * Lat.dpE f ξ l M i = f a * Lat.dpE f ξ l M k := by
  by_cases hk : k < m
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_range.2 hk) h
  · rw [dpE_eq_zero l M hn (not_lt.1 hk), mul_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i ≠ k := by
      have := Finset.mem_range.1 hi
      omega
    simp [Pi.single_eq_of_ne this]

variable {f ξ l} in
theorem l_ne {m : ℕ} (h : Lat.Hyp f ξ l m) : l ≠ 0 := by
  rintro rfl
  exact h.l0 (by simp)


variable {f ξ l} in
theorem dvd_of_mem {m : ℕ} (h : Lat.Hyp f ξ l m) {j : ℕ} (hj : j < m) {a : W}
    (hmem : f a * Lat.dpE f ξ l M j ∈ Ideal.span {f ξ ^ (j + 1)}) : ξ ∣ a := by
  have hl' : ((l : ℚ) ^ M)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (l_ne h)))
  have h2 : ((j.factorial : ℚ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast j.factorial_ne_zero)
  have hu : (((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) ≠ 0 := mul_ne_zero h2 (pow_ne_zero _ hl')
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [dpE_eq] at hb
  generalize (((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) = u at hb hu
  refine h.gr j hj a (u⁻¹ • b) ?_
  rw [mul_smul_comm, mul_comm (f ξ ^ (j + 1)), hb, mul_smul_comm, smul_smul, inv_mul_cancel₀ hu, one_smul]


variable {f ξ l} in
theorem exists_coeff {m : ℕ} (h : Lat.Hyp f ξ l m) {x : B} (hx : x ∈ Lat.sub f ξ l M) {r : ℕ}
    (hr : x ∈ Ideal.span {f ξ ^ r}) (j : ℕ) (hj : j ≤ r) :
    ∃ c : ℕ → W, (∀ i < j, c i = 0) ∧ x = ∑ i ∈ Finset.range m, f (c i) * Lat.dpE f ξ l M i := by
  induction j with
  | zero =>
    obtain ⟨n, c, hc⟩ := (_root_.GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff f ξ l M x).1 hx
    refine ⟨fun i => if hi : i < n then c ⟨i, hi⟩ else 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    set g : ℕ → B := fun i => f (if hi : i < n then c ⟨i, hi⟩ else 0) * Lat.dpE f ξ l M i with hg
    have h1 : x = ∑ i ∈ Finset.range n, g i := by
      rw [hc, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hg]
    have h2 : ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range (max n m), g i :=
      Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun i _ hi => by
        have : ¬ i < n := by simpa using hi
        simp [hg, this]
    have h3 : ∑ i ∈ Finset.range m, g i = ∑ i ∈ Finset.range (max n m), g i :=
      Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun i _ hi => by
        have : m ≤ i := by simpa using hi
        simp [hg, dpE_eq_zero l M h.nil this]
    rw [h1, h2, ← h3]
  | succ j ih =>
    obtain ⟨c, hc, hxc⟩ := ih (by omega)
    set c' : ℕ → W := c - Pi.single j (c j) with hc'
    have hsum : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i =
        x - f (c j) * Lat.dpE f ξ l M j := by
      rw [← sum_single h.nil j (c j), hxc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc', Pi.sub_apply, map_sub, sub_mul]
    have hz : ∀ i ≤ j, c' i = 0 := by
      intro i hi
      rcases hi.lt_or_eq with hi | rfl
      · rw [hc', Pi.sub_apply, hc i hi, Pi.single_eq_of_ne hi.ne, sub_zero]
      · rw [hc', Pi.sub_apply, Pi.single_eq_same, sub_self]
    have hrest : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)} := by
      refine Ideal.sum_mem _ fun i _ => ?_
      by_cases hi : i ≤ j
      · rw [hz i hi, map_zero, zero_mul]
        exact Ideal.zero_mem _
      · exact Ideal.mul_mem_left _ _ (dpE_mem f ξ l M (by omega))
    have hx1 : x ∈ Ideal.span {f ξ ^ (j + 1)} :=
      (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hj)) hr
    have hterm : f (c j) * Lat.dpE f ξ l M j ∈ Ideal.span {f ξ ^ (j + 1)} := by
      have := Ideal.sub_mem _ hx1 hrest
      rwa [hsum, sub_sub_cancel] at this
    obtain ⟨e, he⟩ : ∃ e : W, f (c j) * Lat.dpE f ξ l M j = f e * Lat.dpE f ξ l M (j + 1) := by
      by_cases hjm : j < m
      · obtain ⟨d, hd⟩ := dvd_of_mem M h hjm hterm
        refine ⟨d * ((l ^ M * (j + 1) : ℕ) : W), ?_⟩
        rw [hd, map_mul, map_mul, map_natCast, mul_comm (f ξ), mul_assoc, mul_dpE f ξ M (l_ne h), mul_assoc]
      · refine ⟨0, ?_⟩
        rw [dpE_eq_zero l M h.nil (not_lt.1 hjm), map_zero, zero_mul, mul_zero]
    refine ⟨c' + Pi.single (j + 1) e, fun i hi => ?_, ?_⟩
    · rw [Pi.add_apply, hz i (by omega), Pi.single_eq_of_ne (by omega), add_zero]
    · simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      rw [hsum, sum_single h.nil, ← he, sub_add_cancel]

end

theorem dividedPowerFiltration_fg : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ,
      (pdP (Lat.γ f ξ l M hc) r).FG := by
  intro W B _ _ _ f ξ l M m h hc r
  have key : pdP (Lat.γ f ξ l M hc) r =
      Ideal.span (Lat.dpA f ξ l M '' (↑(Finset.Ico r m) : Set ℕ)) := by
    rw [_root_.GlobalTheory.CompanionTheory.LatPdpEq.dividedPowerFiltration_eq f ξ l M m h hc r]
    apply le_antisymm
    · intro x hx
      have hxs : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := x.2
      obtain ⟨c, hc0, hxc⟩ := exists_coeff M h hxs (Ideal.mem_comap.1 hx) r le_rfl
      have hx' : x = ∑ i ∈ Finset.range m, Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i := by
        apply Lat.ι_injective f ξ l M
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hxc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, Lat.ι_ofW, Lat.ι_dpA]
      rw [hx']
      refine Ideal.sum_mem _ fun i hi => ?_
      by_cases hir : i < r
      · rw [hc0 i hir, map_zero, zero_mul]
        exact Ideal.zero_mem _
      · refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, ?_, rfl⟩)
        simp only [Finset.coe_Ico, Set.mem_Ico]
        exact ⟨not_lt.1 hir, Finset.mem_range.1 hi⟩
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi
      exact Ideal.mem_comap.2 (dpE_mem f ξ l M hi.1)
  rw [key]
  exact Submodule.fg_span ((Finset.finite_toSet _).image _)

end GlobalTheory.CompanionTheory.LatFG
end

