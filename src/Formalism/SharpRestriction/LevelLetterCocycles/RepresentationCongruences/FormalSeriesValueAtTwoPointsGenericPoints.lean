module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvdCoeffsOfMemSpanDistinguished
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

namespace ContPA

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

private lemma isUnit_natCast_sp_complex_sections {l m : ℕ} (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hc : Nat.Coprime l m) : IsUnit (m : O) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  by_contra hm
  have hm' : (m : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hm)
  have hne : (1 : O) ∉ IsLocalRing.maximalIdeal O :=
    (Ideal.ne_top_iff_one _).mp (inferInstance : (IsLocalRing.maximalIdeal O).IsMaximal).ne_top
  apply hne
  have h1 : (a : O) * (l : O) + (b : O) * (m : O) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → O) hab
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hm')

theorem natCast_unit_mul {l : ℕ} [hp : Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    {n : ℕ} (hn : n ≠ 0) : ∃ v : Oˣ, (n : O) = v * (l : O) ^ padicValNat l n := by
  obtain ⟨m, hm⟩ := (fun {p n : ℕ} => _root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)) (p := l) (n := n)
  have hnd : ¬ l ∣ m := by
    rintro ⟨c, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := l) hn
    exact ⟨c, by rw [pow_succ, mul_assoc]; simpa only [Nat.padicValNat_def] using hm⟩
  have hu := isUnit_natCast_sp_complex_sections hl ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd)
  refine ⟨hu.unit, ?_⟩
  have hc : (n : O) = (l : O) ^ padicValNat l n * (m : O) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → O) hm
  rw [hc, IsUnit.unit_spec, mul_comm]

theorem natCast_ne_zero' {l : ℕ} [Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hl0 : (l : O) ≠ 0) {n : ℕ} (hn : n ≠ 0) : (n : O) ≠ 0 := by
  obtain ⟨v, hv⟩ := natCast_unit_mul hl hn
  rw [hv]
  exact mul_ne_zero v.ne_zero (pow_ne_zero _ hl0)

theorem addVal_l {l : ℕ} (hl0 : (l : O) ≠ 0) :
    IsDiscreteValuationRing.addVal O (l : O) = ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℕ∞) := by
  exact (ENat.coe_toNat ((IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hl0)).symm

theorem addVal_natCast {l : ℕ} [Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hl0 : (l : O) ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    IsDiscreteValuationRing.addVal O (n : O) =
      (((IsDiscreteValuationRing.addVal O (l : O)).toNat * padicValNat l n : ℕ) : ℕ∞) := by
  obtain ⟨v, hv⟩ := natCast_unit_mul hl hn
  rw [hv, AddValuation.map_mul, AddValuation.map_pow, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k := ⟨_, addVal_l hl0⟩
  rw [hk, ENat.toNat_coe, nsmul_eq_mul]
  push_cast
  ring

theorem l_unit_mul {ϖ : O} (hϖ : Irreducible ϖ) {l : ℕ} (hl0 : (l : O) ≠ 0) :
    ∃ v : Oˣ, (l : O) = v * ϖ ^ (IsDiscreteValuationRing.addVal O (l : O)).toNat := by
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨v, ?_⟩
  rw [IsDiscreteValuationRing.addVal_def _ v hϖ n hv, ENat.toNat_coe]
  exact hv

private lemma order_unit_mul_X_pow_lemma_3 {K : Type*} [Field K] {w : K⟦X⟧} (hw : IsUnit w) (n : ℕ) :
    (w * X ^ n).order = (n : ℕ∞) := by
  have hw0 : w.order = 0 := by
    obtain ⟨u, rfl⟩ := hw
    have h := congrArg PowerSeries.order u.mul_inv
    rw [PowerSeries.order_mul, PowerSeries.order_one] at h
    have h2 : PowerSeries.order (u : K⟦X⟧) ≤ 0 := by
      rw [← h]; exact le_self_add
    exact le_antisymm h2 (by simp)
  rw [PowerSeries.order_mul, hw0, PowerSeries.order_X_pow, zero_add]

theorem dist_of_map_eq {f : O⟦X⟧} {w : (IsLocalRing.ResidueField O)⟦X⟧} (hw : IsUnit w) (n : ℕ)
    (h : f.map (IsLocalRing.residue O) = w * X ^ n) : IsDist f ∧ wdeg f = n := by
  have hord : (f.map (IsLocalRing.residue O)).order = n := by
    rw [h]; exact order_unit_mul_X_pow_lemma_3 hw n
  refine ⟨?_, ?_⟩
  · unfold IsDist
    intro h0
    rw [h0, PowerSeries.order_zero] at hord
    exact ENat.top_ne_coe n hord
  · unfold wdeg
    rw [hord]
    rfl

theorem dist_X_pow (n : ℕ) : IsDist ((X : O⟦X⟧) ^ n) ∧ wdeg ((X : O⟦X⟧) ^ n) = n := dist_of_map_eq isUnit_one n (by simp)

section P1
variable {l : ℕ} [hlp : Fact l.Prime] {p1 e u : O⟦X⟧}

theorem residue_map_p1_eq (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hp : p1 = C (l : O) * e + u * X ^ l) :
    p1.map (IsLocalRing.residue O) = u.map (IsLocalRing.residue O) * X ^ l := by
  have h0 : IsLocalRing.residue O (l : O) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hl
  have h0' : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]; exact h0
  have h0'' : ((l : ℕ) : (IsLocalRing.ResidueField O)⟦X⟧) = 0 := by
    rw [← map_natCast (C : IsLocalRing.ResidueField O →+* (IsLocalRing.ResidueField O)⟦X⟧) l, h0', map_zero]
  rw [hp]
  simp [h0, h0', h0'']

theorem addVal_coef (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) {a i : ℕ} (hi : i ≤ a) :
    IsDiscreteValuationRing.addVal O ((a.choose i : O) * (l : O) ^ (a - i)) =
      (((IsDiscreteValuationRing.addVal O (l : O)).toNat * (a - i + padicValNat l (a.choose i)) : ℕ) : ℕ∞) := by
  have hc : a.choose i ≠ 0 := (Nat.choose_pos hi).ne'
  rw [AddValuation.map_mul, addVal_natCast hl hl0 hc, AddValuation.map_pow]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k := ⟨_, addVal_l hl0⟩
  rw [hk, ENat.toNat_coe, nsmul_eq_mul]
  push_cast
  ring

theorem coef_ne_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) {a i : ℕ} (hi : i ≤ a) :
    (a.choose i : O) * (l : O) ^ (a - i) ≠ 0 := mul_ne_zero (natCast_ne_zero' hl hl0 (Nat.choose_pos hi).ne') (pow_ne_zero _ hl0)

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

theorem content_p1_pow_X_pow_eq_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (y b : ℕ) (hlt : b < l * y) :
    cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ b) = 0 := by
  refine le_antisymm ?_ (by simp)
  unfold cont
  refine iSup₂_le fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exfalso
    obtain ⟨a', c', hac⟩ := Ideal.mem_span_pair.mp hk
    have hϖ0 : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr
      ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
    have hm := congrArg (PowerSeries.map (IsLocalRing.residue O)) hac
    simp only [map_add (f := _), map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero,
      zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm
    have e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y =
        PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y) := by ring
    rw [e1] at hm
    have ho := congrArg PowerSeries.order hm
    rw [PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow] at ho
    have h2 : ((l * y : ℕ) : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + ((l * y : ℕ) : ℕ∞) :=
      le_add_self
    rw [ho] at h2
    have h3 : l * y ≤ b := by exact_mod_cast h2
    omega

theorem content_X_pow_p1_pow_eq_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (B y : ℕ) (hlt : l * y < B) :
    cont ϖ ((X : O⟦X⟧) ^ B) (p1 ^ y) = 0 := by
  refine le_antisymm ?_ (by simp)
  unfold cont
  refine iSup₂_le fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exfalso
    obtain ⟨a', c', hac⟩ := Ideal.mem_span_pair.mp hk
    have hϖ0 : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr
      ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
    have hm := congrArg (PowerSeries.map (IsLocalRing.residue O)) hac
    simp only [map_add (f := _), map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero,
      zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm
    have e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y =
        PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y) := by ring
    rw [e1] at hm
    have ho := congrArg PowerSeries.order hm
    rw [PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow] at ho
    have h2 : (B : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + (B : ℕ∞) :=
      le_add_self
    rw [ho] at h2
    have h3 : B ≤ l * y := by exact_mod_cast h2
    omega



end P1

end ContPA

end Formalism.MainNotions.N.FrobeniusPowerSeries
