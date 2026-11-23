module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicitySuccEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemIntegralDifferentialSubmodule
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

theorem derivation_prod_erase {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq ι] (D : Derivation R A A) (f : ι → A) (S : Finset ι) :
    D (∏ s ∈ S, f s) = ∑ i ∈ S, (∏ s ∈ S.erase i, f s) * D (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hai : a ≠ i := by rintro rfl; exact ha hi
    rw [Finset.erase_insert_of_ne hai,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)), mul_assoc]

theorem pderiv_prod_pow {R τ σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ]
    (u : σ → MvPowerSeries τ R) (a : σ → ℕ) (j : τ) :
    pderiv j (∏ s, u s ^ a s) =
      ∑ i, a i • ((∏ s ∈ Finset.univ.erase i, u s ^ a s) * (u i ^ (a i - 1) * pderiv j (u i))) := by
  rw [derivation_prod_erase]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_pow, nsmul_eq_mul, mul_assoc, mul_left_comm]

theorem subst_mem_quasiInt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, u i ∈ intBy p k τ 1) → f ∈ quasiInt p k σ → subst u f ∈ quasiInt p k τ := by
  intro p _ k _ _ _ σ τ _ u f hu0 hu hf
  classical
  have : Fintype σ := Fintype.ofFinite σ
  set φ := algebraMap (WittVector p k) (Fr p k) with hφ
  have ha : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hlift : ∀ i, ∃ v : MvPowerSeries τ (WittVector p k), MvPowerSeries.map φ v = u i := by
    intro i
    have hui : ∀ α, ∃ w : WittVector p k, coeff α (u i) = φ (1 * w) := hu i
    let w0 : MvPowerSeries τ (WittVector p k) := fun α => (hui α).choose
    refine ⟨w0, ?_⟩
    ext α
    rw [coeff_map, (hui α).choose_spec, one_mul]
    rfl
  choose v hv using hlift
  intro γ j
  rw [coeff_subst ha]
  have hP : ∀ α : σ →₀ ℕ, (α.prod fun s e => u s ^ e) =
      MvPowerSeries.map φ (∏ s, v s ^ α s) := by
    intro α
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
    exact Finset.prod_congr rfl fun s _ => by rw [map_pow, hv]
  have hterm : ∀ α : σ →₀ ℕ,
      (γ j : Fr p k) * (coeff α f • coeff γ (α.prod fun s e => u s ^ e)) ∈ φ.range := by
    intro α
    rw [hP, coeff_map, smul_eq_mul]
    by_cases hγ : γ j = 0
    · rw [hγ, Nat.cast_zero, zero_mul]; exact zero_mem _
    have hle : Finsupp.single j 1 ≤ γ := by
      intro t
      by_cases ht : t = j
      · subst ht; simp only [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_apply, if_neg (Ne.symm ht)]; exact Nat.zero_le _
    set δ := γ - Finsupp.single j 1 with hδ
    have hδγ : δ + Finsupp.single j 1 = γ := tsub_add_cancel_of_le hle
    have hδj : (δ j : Fr p k) + 1 = γ j := by
      rw [← hδγ, Finsupp.add_apply, Finsupp.single_eq_same]; push_cast; rfl
    have key := coeff_pderiv (R := WittVector p k) (i := j) (∏ s, v s ^ α s) δ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hδγ, pderiv_prod_pow, map_sum] at key
    have hk : (γ j : Fr p k) * φ (coeff γ (∏ s, v s ^ α s)) =
        φ (∑ i, coeff δ (α i • ((∏ s ∈ Finset.univ.erase i, v s ^ α s) *
          (v i ^ (α i - 1) * pderiv j (v i))))) := by
      rw [key, map_mul, map_add (f := _), map_natCast, map_one, ← hδj]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_left_comm, hk, map_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    obtain ⟨w, hw⟩ := (hf : ∀ (α : σ →₀ ℕ) (i : σ), ∃ w : WittVector p k,
      (α i : Fr p k) * coeff α f = φ w) α i
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, ← mul_assoc, mul_comm (coeff α f), hw, ← map_mul]
    exact ⟨_, rfl⟩
  have hfin := coeff_subst_finite ha f γ
  rw [finsum_eq_sum _ hfin, Finset.mul_sum]
  have hmem : (γ j : Fr p k) * ∑ α ∈ hfin.toFinset, coeff α f • coeff γ (α.prod fun s e => u s ^ e)
      ∈ φ.range := by
    rw [Finset.mul_sum]; exact Subring.sum_mem _ fun α _ => hterm α
  rw [← Finset.mul_sum]
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw.symm⟩

end Katz

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferential
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_sub_eq_p_mul_of_constantCoeff_eq {x y : WittVector p k}
    (h : WittVector.constantCoeff x = WittVector.constantCoeff y) : ∃ z, x - y = p * z := by
  by_cases hxy : x - y = 0
  · exact ⟨0, by rw [hxy, mul_zero]⟩
  obtain ⟨m, z, hz, hxyz⟩ := WittVector.exists_eq_pow_p_mul (x - y) hxy
  rcases m with _ | m
  · exfalso; apply hz
    have h1 := congrArg WittVector.constantCoeff hxyz
    rw [map_sub, h, sub_self, pow_zero, one_mul] at h1
    exact h1.symm
  · exact ⟨p ^ m * z, by rw [hxyz, pow_succ]; ring⟩

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem prod_sub_prod_divisible_lemma_2 {σ τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k)
    (U V : σ → MvPowerSeries τ (WittVector p k)) (e : σ → ℕ) (S : Finset σ)
    (h : ∀ i ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (U i ^ e i - V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (∏ i ∈ S, U i ^ e i - ∏ i ∈ S, V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i S hi ih =>
    obtain ⟨Y1, hY1⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨Y2, hY2⟩ := h i (Finset.mem_insert_self i S)
    refine ⟨U i ^ e i * Y1 + Y2 * ∏ j ∈ S, V j ^ e j, ?_⟩
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    simp only [Algebra.smul_def, map_sub, map_mul, map_add (f := _), map_pow, map_prod] at hY1 hY2 ⊢
    linear_combination
      (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i)) ^ e i * hY1 +
      (∏ j ∈ S, (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V j)) ^ e j) * hY2

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_choose_mul_p_pow_mul_eq_p_mul (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∃ t : WittVector p k, c * ((n.choose j : _root_.GlobalTheory.Katz.Fr p k) * (p : _root_.GlobalTheory.Katz.Fr p k) ^ j) =
      algebraMap (WittVector p k) _ (p * t) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨e, j', hj', hjeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : j ≠ 0) p hp.ne_one
  have hj'0 : j' ≠ 0 := by rintro rfl; simp at hj'
  have hej : e < j := by
    have h1 : p ^ e ≤ j := by rw [hjeq]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj'0)
    exact lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h1
  obtain ⟨q, rfl⟩ : ∃ q, j = q + e + 1 := ⟨j - e - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hunit : IsUnit (j' : WittVector p k) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have h2 : (j' : WittVector p k).coeff 0 = (j' : k) :=
      map_natCast (WittVector.constantCoeff (p := p) (R := k)) j'
    rw [h2]
    exact (CharP.cast_eq_zero_iff k p j').not.2 hj'
  obtain ⟨s, hs⟩ := hunit.exists_right_inv
  refine ⟨m * (n'.choose (q + e) : WittVector p k) * (p : WittVector p k) ^ q * s, ?_⟩
  set ι := algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)
  have hs' : (j' : _root_.GlobalTheory.Katz.Fr p k) * ι s = 1 := by
    rw [← map_natCast ι, ← map_mul, hs, map_one]
  have hjK : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) = (p : _root_.GlobalTheory.Katz.Fr p k) ^ e * j' := by
    rw [hjeq]; push_cast; ring
  have hchoose : ((n' + 1).choose (q + e + 1) : _root_.GlobalTheory.Katz.Fr p k) * ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) =
      ((n' + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) := by
    have := Nat.add_one_mul_choose_eq n' (q + e)
    rw [← Nat.cast_mul, ← Nat.cast_mul, this]
  have hj0 : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) ≠ 0 := by
    rw [hjK]
    have hinj : Function.Injective ι := IsFractionRing.injective _ _
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 (WittVector.p_nonzero p k)
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 hunit.ne_zero
  apply mul_right_cancel₀ hj0
  simp only [map_mul, map_pow, map_natCast]
  linear_combination (c * (p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1)) * hchoose +
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k)) * hc -
    ((p : _root_.GlobalTheory.Katz.Fr p k) * ι m * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) *
      (p : _root_.GlobalTheory.Katz.Fr p k) ^ q * ι s) * hjK -
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) * ι m) * hs'

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_algebraMap_smul' {τ : Type} (a : WittVector p k) (Y : MvPowerSeries τ (WittVector p k)) :
    MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (a • Y) =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a •
        MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  ext β
  simp only [MvPowerSeries.coeff_map, map_smul, smul_eq_mul, map_mul]

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_add_p_mul_pow_sub_pow_eq_p_smul {τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (V H : MvPowerSeries τ (WittVector p k)) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      ((V + (p : MvPowerSeries τ (WittVector p k)) * H) ^ n - V ^ n) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
    mul_one, add_sub_cancel_right, map_sum, Finset.smul_sum]
  have key : ∀ j ∈ Finset.range n, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨t, ht⟩ := exists_choose_mul_p_pow_mul_eq_p_mul c m hc (n - j) (by omega) (by omega)
    rw [Nat.choose_symm (by omega)] at ht
    refine ⟨t • (V ^ j * H ^ (n - j)), ?_⟩
    have e1 : V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k)) =
        ((n.choose j * p ^ (n - j) : ℕ) : WittVector p k) • (V ^ j * H ^ (n - j)) := by
      rw [Algebra.smul_def, map_natCast]; push_cast; ring
    rw [e1, map_algebraMap_smul', map_algebraMap_smul', smul_smul, smul_smul, map_natCast]
    congr 1
    rw [← map_mul, ← ht]; push_cast; ring
  have hsum : ∀ S : Finset ℕ, (∀ j ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) →
      ∃ Y, ∑ j ∈ S, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro S hS
    classical
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j S hj ih =>
      obtain ⟨Y1, hY1⟩ := ih fun i hi => hS i (Finset.mem_insert_of_mem hi)
      obtain ⟨Y2, hY2⟩ := hS j (Finset.mem_insert_self j S)
      exact ⟨Y2 + Y1, by rw [Finset.sum_insert hj, hY1, hY2, map_add (f := _), smul_add]⟩
  exact hsum _ key


open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
theorem _root_.GlobalTheory.Katz.subst_sub_subst_mem_intBy : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries (τ) (_root_.GlobalTheory.Katz.Fr p k)) (w : σ → MvPowerSeries τ k) (f : MvPowerSeries (σ) (_root_.GlobalTheory.Katz.Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, _root_.GlobalTheory.Katz.Red p (u i) (w i)) → (∀ i, _root_.GlobalTheory.Katz.Red p (v i) (w i)) → f ∈ _root_.GlobalTheory.Katz.quasiInt p k σ → subst u f - subst v f ∈ _root_.GlobalTheory.Katz.intBy p k τ p := by
  intro p _ k _ _ _ σ τ _ u v w f hu0 hv0 hu hv hf
  classical
  choose a ha using fun i β => hu i β
  choose b hb using fun i β => hv i β
  choose hh hhh using fun i β =>
    exists_sub_eq_p_mul_of_constantCoeff_eq ((ha i β).2.trans (hb i β).2.symm)
  let U : σ → MvPowerSeries τ (WittVector p k) := fun i β => a i β
  let V : σ → MvPowerSeries τ (WittVector p k) := fun i β => b i β
  let Hs : σ → MvPowerSeries τ (WittVector p k) := fun i β => hh i β
  have hUV : ∀ i, U i = V i + (p : MvPowerSeries τ (WittVector p k)) * Hs i := by
    intro i; refine MvPowerSeries.ext fun β => ?_
    have e : (p : MvPowerSeries τ (WittVector p k)) * Hs i = (p : WittVector p k) • Hs i := by
      rw [Algebra.smul_def, map_natCast]
    rw [e, map_add (f := _), map_smul, smul_eq_mul]
    show a i β = b i β + p * hh i β
    rw [← hhh]; ring
  have huM : u = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (ha i β).1
  have hvM : v = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (hb i β).1
  have hf' : ∀ (α : σ →₀ ℕ) (i : σ), ∃ m, ((α i : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * MvPowerSeries.coeff α f =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) m := hf
  have hsu := MvPowerSeries.hasSubst_of_constantCoeff_zero hu0
  have hsv := MvPowerSeries.hasSubst_of_constantCoeff_zero hv0
  unfold _root_.GlobalTheory.Katz.intBy
  refine fun β => ?_
  rw [map_sub, MvPowerSeries.coeff_subst hsu, MvPowerSeries.coeff_subst hsv,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hsu f β)
      (MvPowerSeries.coeff_subst_finite hsv f β)]
  refine finsum_induction (fun x => ∃ w, x = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) (p * w))
    ⟨0, by simp⟩ (fun x y ⟨w1, h1⟩ ⟨w2, h2⟩ => ⟨w1 + w2, by rw [h1, h2, mul_add, map_add (f := _)]⟩) fun α => ?_
  obtain ⟨Y, hY⟩ := prod_sub_prod_divisible_lemma_2 (MvPowerSeries.coeff α f) U V α α.support fun i _ => by
    obtain ⟨mi, hmi⟩ := hf' α i
    rw [hUV i]
    exact map_add_p_mul_pow_sub_pow_eq_p_smul _ mi hmi (V i) (Hs i)
  refine ⟨MvPowerSeries.coeff β Y, ?_⟩
  rw [huM, hvM]
  simp only [Finsupp.prod, ← map_pow, ← map_prod]
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← map_sub, ← smul_eq_mul, ← map_smul, hY,
    map_smul, MvPowerSeries.coeff_map, smul_eq_mul, map_mul]

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgeGlobalOneFormsEqZeroIff
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem wsum_eq_zero_iff : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (n : ℕ) (u v : Fin n → Glob1 F), wsum F u v = 0 ↔ ∀ l l' : Glob1 F →ₗ[R] R, ∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k)) = 0 := by
  intro R _ C _ F hfr hH n u v
  constructor
  · intro hw l l'
    obtain ⟨δ, -, hδ⟩ := _root_.GlobalTheory.AbCoh.exists_vectorField_of_functional R C F hfr hH l
    obtain ⟨δ', -, hδ'⟩ := _root_.GlobalTheory.AbCoh.exists_vectorField_of_functional R C F hfr hH l'
    have key : ∀ T, algebraMap R (F.obj T) (∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k))) = 0 := by
      intro T
      have h0 := congrArg (exteriorPower.pairingDual (F.obj T) Ω[F.obj T⁄R] 2
        (exteriorPower.ιMulti (F.obj T) 2 ![δ T, δ' T])) (congrFun hw T)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [wsum, map_sum, wedge_eq_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti,
        Matrix.det_fin_two, map_zero, Pi.zero_apply] at h0
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons, hδ, hδ'] at h0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sub, map_mul, map_mul]
      ring
    obtain ⟨r, -, huniq⟩ := hH 0 (map_zero _)
    have h1 := huniq _ (fun T => by rw [key T]; rfl)
    have h2 := huniq 0 (fun T => by rw [map_zero]; rfl)
    rw [h1, h2]
  · intro h
    obtain ⟨m, ⟨Φ⟩⟩ := hfr
    obtain ⟨L, -, hL⟩ := _root_.GlobalTheory.AbCoh.frame_coord R C F hH m Φ
    funext T
    have hexp : ∀ w : Glob1 F, w.1 T = ∑ i, L i w • (Φ.w i).1 T := by
      intro w
      conv_lhs => rw [hL w]
      simp [Submodule.coe_sum, Finset.sum_apply]
    let x : Fin m → Fin m → Om R (F.obj T) 2 := fun i j => wedge R _ ((Φ.w i).1 T) ((Φ.w j).1 T)
    let c : Fin m → Fin m → R := fun i j => ∑ k, L i (u k) * L j (v k)
    have hc : ∀ i j, c i j = c j i := by
      intro i j
      have := h (L i) (L j)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c, this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hsum : wsum F u v T = ∑ i, ∑ j, c i j • x i j := by
      have hu : ∀ k, (u k).1 T = ∑ i, L i (u k) • (Φ.w i).1 T := fun k => hexp _
      have hv : ∀ k, (v k).1 T = ∑ i, L i (v k) • (Φ.w i).1 T := fun k => hexp _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [wsum, hu, hv, map_sum, LinearMap.sum_apply, wedge_smul_left, wedge_smul_right, c, x,
        Finset.sum_smul, mul_smul]
      conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [Pi.zero_apply, hsum, ← Finset.sum_product' (f := fun i j => c i j • x i j)]
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ _
      simp only [Prod.swap_prod_mk, x]
      rw [hc j i, wedge_swap ((Φ.w j).1 T), smul_neg, add_neg_cancel]
    · rintro ⟨i, j⟩ _ hne heq
      apply hne
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [x]
    · simp
    · simp

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_deformation_affine_sections : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by
  first | exact @GlobalTheory.AbCoh.preα_surjective_and_ker | exact GlobalTheory.AbCoh.preα_surjective_and_ker | (intros; apply GlobalTheory.AbCoh.preα_surjective_and_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmCocycleApplyFinsetSum
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem symmCocycle_swap {A B : Type} [AddCommGroup A] [AddCommGroup B] (γ : A → A → B)
    (hs : ∀ x y, γ x y = γ y x) (hc : ∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0)
    (a b c e : A) :
    γ (a + b) (c + e) + γ a b + γ c e = γ (a + c) (b + e) + γ a c + γ b e := by
  have h1 := hc (a + b) c e
  have h2 := hc a b c
  have h3 := hc (a + c) b e
  have h4 := hc a c b
  rw [add_right_comm a c b] at h3
  rw [add_comm c b, hs c b] at h4
  rw [← sub_eq_zero]
  calc _ = ((γ c e - γ (a + b + c) e + γ (a + b) (c + e) - γ (a + b) c)
        - (γ b c - γ (a + b) c + γ a (b + c) - γ a b))
        - ((γ b e - γ (a + b + c) e + γ (a + c) (b + e) - γ (a + c) b)
        - (γ b c - γ (a + c) b + γ a (b + c) - γ a c)) := by abel
    _ = 0 := by rw [h1, h2, h3, h4]; simp

theorem symmCocycle_sum : ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] (γ : A → A → B), (∀ x y, γ x y = γ y x) → (∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0) → γ 0 0 = 0 → ∀ (d : ℕ) (x y : Fin d → A), γ (∑ m, x m) (∑ m, y m) = ∑ m, γ (x m) (y m) + ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) - (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) - ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) := by
  intro A B _ _ γ hs hc h0 d
  induction d with
  | zero => intro x y; simp [h0]
  | succ d ih =>
    intro x y
    have ih' := ih (fun j => x (Fin.castSucc j)) (fun j => y (Fin.castSucc j))
    simp only [Finset.sum_filter] at ih' ⊢
    simp only [Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last,
      if_true, lt_irrefl, if_false, add_zero] at ih' ⊢
    have hl : ∀ i : Fin d, ¬ (Fin.last d < i.castSucc) := fun i => not_lt.mpr (Fin.castSucc_lt_last i).le
    simp only [hl, if_false, add_zero] at ih' ⊢
    have k := symmCocycle_swap γ hs hc (∑ m : Fin d, x m.castSucc) (x (Fin.last d)) (∑ m : Fin d, y m.castSucc) (y (Fin.last d))
    rw [ih'] at k
    rw [Finset.sum_add_distrib]
    rw [← sub_eq_zero] at k ⊢
    rw [← k]
    abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicitySuccEqStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_succ_eq : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (ρ k : ℕ), ρ + k + 2 ≤ r → nPos ψ τ ρ k = nPos ψ τ (ρ + 1) k := by
  first | exact @GlobalTheory.FinGL.RootExchange.nPos_succ | exact GlobalTheory.FinGL.RootExchange.nPos_succ | (intros; apply GlobalTheory.FinGL.RootExchange.nPos_succ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLocalizationEtaleNbhdEqUnitMulPowStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.kummer_divisor_step) | (exact GlobalTheory.EtC.kummer_divisor_step) | (intros; apply GlobalTheory.EtC.kummer_divisor_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VirtualCharacterCosetNormOneSingleStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.virtualCharacter_coset_normOne_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧ ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  first | (exact @GlobalTheory.Shin.virt_coset_norm_one_single) | (exact GlobalTheory.Shin.virt_coset_norm_one_single) | (intros; apply GlobalTheory.Shin.virt_coset_norm_one_single <;> assumption)
end

