module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffSubstBinomSeries
section
noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.C

variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem binom_zero (z : K) : binom z 0 = 1 := by simp [binom]

theorem binom_succ (z : K) (n : ℕ) : ((n : K) + 1) * binom z (n + 1) = (z - n) * binom z n := by
  unfold binom
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  have h0 : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have h1 : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

theorem binom_pascal (z : K) (k : ℕ) :
    binom (z + 1) (k + 1) = binom z (k + 1) + binom z k := by
  unfold binom
  rw [Finset.prod_range_succ' (fun i : ℕ => z + 1 - (i : K)),
    Finset.prod_range_succ (fun i : ℕ => z - (i : K)), Nat.factorial_succ]
  have h0 : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h1 : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have e : ∏ i ∈ range k, (z + 1 - ((i + 1 : ℕ) : K)) = ∏ i ∈ range k, (z - (i : K)) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  rw [e]
  push_cast
  field_simp
  ring

theorem binom_zero_succ (k : ℕ) : binom (0 : K) (k + 1) = 0 := by
  unfold binom
  rw [Finset.prod_range_succ']
  simp

def binomSeries (z : K) : PowerSeries K := PowerSeries.mk (binom z)

theorem binomSeries_ode (z : K) :
    (1 + PowerSeries.X) * PowerSeries.derivative (R := K) (binomSeries z) = z • binomSeries z := by
  ext n
  rw [add_mul, one_mul, map_add (f := _), PowerSeries.coeff_derivative, PowerSeries.coeff_smul]
  cases n with
  | zero =>
    have h := binom_succ z 0
    simp only [binomSeries, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul, smul_eq_mul]
    push_cast at h ⊢
    linear_combination h
  | succ n =>
    have h := binom_succ z (n + 1)
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    simp only [binomSeries, PowerSeries.coeff_mk, smul_eq_mul]
    push_cast at h ⊢
    linear_combination h

theorem constantCoeff_subst_binomSeries (z : K) {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst g (binomSeries z)) = 1 := by
  have h := IntegralMvPolynomialLemmas.coeff_subst_congr (g := binomSeries z) (h := PowerSeries.C (1 : K)) hg 0
    (fun k hk => by
      have : k = 0 := by simpa using hk
      subst this
      simp [binomSeries, binom_zero])
  rw [PowerSeries.subst_C] at h
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp

theorem subst_binomSeries_eq_mvExp (z : K) {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (mvExp f - 1) (binomSeries z) = mvExp (z • f) := by
  have hg : MvPowerSeries.constantCoeff (mvExp f - 1) = 0 := by
    rw [map_sub, constantCoeff_mvExp hf, map_one, sub_self]
  have hs : PowerSeries.HasSubst (mvExp f - 1) := hasSubst_of_cc hg
  have hzf : MvPowerSeries.constantCoeff (z • f) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]
  have hnzf : MvPowerSeries.constantCoeff (-(z • f)) = 0 := by rw [map_neg, hzf, neg_zero]
  set B := PowerSeries.subst (mvExp f - 1) (binomSeries z) with hB
  have hode : mvExp f * PowerSeries.subst (mvExp f - 1) (PowerSeries.derivative (R := K) (binomSeries z))
      = z • B := by
    have h := congrArg (PowerSeries.subst (mvExp f - 1)) (binomSeries_ode z)
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_add hs, PowerSeries.subst_X hs,
      PowerSeries.subst_smul hs, ← PowerSeries.coe_substAlgHom hs, map_one,
      PowerSeries.coe_substAlgHom hs] at h
    rw [hB, ← h]
    ring
  have hd : ∀ i, MvPowerSeries.pderiv (R := K) i B =
      MvPowerSeries.C z * MvPowerSeries.pderiv (R := K) i f * B := by
    intro i
    apply (isUnit_mvExp hf).mul_left_cancel
    rw [hB, IntegralMvPolynomialLemmas.pderiv_subst _ hg, ← mul_assoc, hode, map_sub, MvPowerSeries.pderiv_one, sub_zero,
      pderiv_mvExp hf, MvPowerSeries.smul_eq_C_mul]
    ring
  have key : B * mvExp (-(z • f)) = 1 := by
    refine MvPowerSeries.pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, pderiv_mvExp hnzf, hd, map_neg, MvPowerSeries.smul_eq_C_mul,
        Derivation.leibniz, MvPowerSeries.pderiv_C, MvPowerSeries.pderiv_one]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, constantCoeff_mvExp hnzf, hB, constantCoeff_subst_binomSeries z hg, map_one,
        mul_one]
  calc B = B * (mvExp (-(z • f)) * mvExp (z • f)) := by rw [mvExp_neg hzf, mul_one]
    _ = mvExp (z • f) := by rw [← mul_assoc, key, one_mul]

theorem expIntegralBinomial' : LGBinom := by
  intro K _ _ R σ z hz f hf
  refine ⟨by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf.1, mul_zero], ?_⟩
  rw [← subst_binomSeries_eq_mvExp z hf.1]
  refine IntegralMvPolynomialLemmas.intMv_subst (fun n => ?_) ⟨?_, fun n => ?_⟩
  · rw [binomSeries, PowerSeries.coeff_mk]
    exact hz n
  · rw [map_sub, constantCoeff_mvExp hf.1, map_one, sub_self]
  · rw [map_sub]
    exact R.sub_mem (hf.2 n) (IntegralMvPolynomialLemmas.intMv_one n)

theorem intBinomialScalar' : IntBinomScalar := by
  intro K _ _ R n k
  induction k generalizing n with
  | zero => rw [binom_zero]; exact R.one_mem
  | succ k ih =>
    induction n using Int.induction_on with
    | zero => rw [Int.cast_zero, binom_zero_succ]; exact R.zero_mem
    | succ m hm =>
      have h := binom_pascal ((m : ℤ) : K) k
      have e : (((m : ℤ) + 1 : ℤ) : K) = ((m : ℤ) : K) + 1 := by push_cast; ring
      rw [e, h]
      exact R.add_mem hm (ih _)
    | pred m hm =>
      have h := binom_pascal (((-(m : ℤ) - 1 : ℤ)) : K) k
      have e : (((-(m : ℤ) - 1 : ℤ)) : K) + 1 = ((-(m : ℤ) : ℤ) : K) := by push_cast; ring
      rw [e] at h
      have h2 : binom (((-(m : ℤ) - 1 : ℤ)) : K) (k + 1) =
          binom ((-(m : ℤ) : ℤ) : K) (k + 1) - binom (((-(m : ℤ) - 1 : ℤ)) : K) k := by
        rw [h]; ring
      rw [h2]
      exact R.sub_mem hm (ih _)

end Formalism.L2.Th1.C
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideA
section
noncomputable section
open scoped BigOperators
open PowerSeries

namespace Formalism.L2.Th1.C

namespace USideA

section Int

variable {K : Type} [Field K] {R : Subring K}

theorem intPS_add {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f + g) := fun n => by
  rw [map_add (f := _)]
  exact R.add_mem (hf n) (hg n)

theorem intPS_sub {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f - g) := fun n => by
  rw [map_sub]
  exact R.sub_mem (hf n) (hg n)

theorem intPS_mul {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f * g) := fun n => by
  rw [PowerSeries.coeff_mul]
  exact R.sum_mem (fun p _ => R.mul_mem (hf _) (hg _))

theorem intPS_C {c : K} (hc : c ∈ R) : IntPS R (PowerSeries.C c) := fun n => by
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact hc
  · exact R.zero_mem

theorem intPS_X_pow (k : ℕ) : IntPS R (PowerSeries.X ^ k : PowerSeries K) := fun n => by
  rw [PowerSeries.coeff_X_pow]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem intPS_X : IntPS R (PowerSeries.X : PowerSeries K) := by
  simpa using (intPS_X_pow 1 : IntPS R (PowerSeries.X ^ 1 : PowerSeries K))

theorem intPS_sum {ι : Type} (s : Finset ι) {F : ι → PowerSeries K} (hF : ∀ i ∈ s, IntPS R (F i)) :
    IntPS R (∑ i ∈ s, F i) := fun n => by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact R.sum_mem (fun i hi => hF i hi n)

theorem intPS_of_mul_eq_one {U V : PowerSeries K} (hU : IntPS R U)
    (hU0 : PowerSeries.constantCoeff U = 1) (hUV : U * V = 1) : IntPS R V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := congrArg (PowerSeries.coeff n) hUV
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at h
    have hmem0 : ((0, n) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    rw [← Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal n)
      (fun p : ℕ × ℕ => PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V)
      hmem0] at h
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0, one_mul] at h
    have hrest : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
        PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V) ∈ R := by
      refine R.sum_mem (fun p hp => R.mul_mem (hU _) (ih _ ?_))
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
      by_contra hle
      apply hne
      obtain ⟨a, b⟩ := p
      simp only [Prod.mk.injEq] at hmem hle ⊢
      refine ⟨?_, ?_⟩ <;> omega
    have h' : PowerSeries.coeff n V = (if n = 0 then 1 else 0) -
        ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
          PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V := by
      linear_combination h
    rw [h']
    refine R.sub_mem ?_ hrest
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem

end Int

section Log

variable {K : Type} [Field K]

theorem hs_of {a : PowerSeries K} (h : PowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a :=
  PowerSeries.HasSubst.of_constantCoeff_zero h

theorem cc_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.constantCoeff (mulBy l linv al) = 0 := by
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr h.2.2.1
  have ha : PowerSeries.HasSubst (PowerSeries.C al * l) := hs_of (by simp [h.1])
  unfold mulBy
  rw [hq, ← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X ha, map_mul, map_mul, h.1, mul_zero, zero_mul]

theorem subst_mulBy_l {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.subst (mulBy l linv al) l = PowerSeries.C al * l := by
  have ha : PowerSeries.HasSubst (PowerSeries.C al * l) := hs_of (by simp [h.1])
  have hlinv : PowerSeries.HasSubst linv := hs_of h.2.2.1
  unfold mulBy
  rw [← PowerSeries.subst_comp_subst_apply hlinv ha, h.2.2.2.2, PowerSeries.subst_X ha]

theorem subst_rescale {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) (g : PowerSeries K) :
    PowerSeries.subst l (PowerSeries.rescale al g) =
      PowerSeries.subst (mulBy l linv al) (PowerSeries.subst l g) := by
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hm : PowerSeries.HasSubst (mulBy l linv al) := hs_of (cc_mulBy h al)
  have hX : PowerSeries.HasSubst (PowerSeries.C al * PowerSeries.X : PowerSeries K) := hs_of (by simp)
  have hC : PowerSeries.subst l (PowerSeries.C al) = PowerSeries.C al := PowerSeries.subst_C al
  rw [PowerSeries.subst_comp_subst_apply hl hm, subst_mulBy_l h, PowerSeries.rescale_eq_subst,
    PowerSeries.smul_eq_C_mul, PowerSeries.subst_comp_subst_apply hX hl,
    ← PowerSeries.coe_substAlgHom hl, map_mul, PowerSeries.coe_substAlgHom, hC,
    PowerSeries.subst_X hl]

theorem l_ne_zero {l linv : PowerSeries K} (h : IsLogPair l linv) : l ≠ 0 := by
  intro h0
  have h1 := h.2.1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem subst_C' (a : PowerSeries K) (c : K) :
    PowerSeries.subst a (PowerSeries.C c) = PowerSeries.C c :=
  PowerSeries.subst_C c

theorem subst_wpShift_zero {a : PowerSeries K} (ha : PowerSeries.HasSubst a) (e : PowerSeries K) :
    PowerSeries.subst a (wpShift e 0) = 1 + a ^ 2 * PowerSeries.subst a e := by
  unfold wpShift
  rw [← PowerSeries.coe_substAlgHom ha]
  simp only [map_add (f := _), map_one, map_mul, map_pow, map_sub, map_zero, sub_zero,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]

end Log

end USideA

open USideA

theorem veluXOfSigma' : VeluXFromZ := by
  intro K _ _ e l linv A c0 ι _ neg xP w xs al h hXW hE hw
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hm : PowerSeries.HasSubst (mulBy l linv al) := hs_of (cc_mulBy h al)
  have hal : PowerSeries.HasSubst (PowerSeries.C al * l) := hs_of (by simp [h.1])
  have F0 : (A + PowerSeries.C c0 * PowerSeries.X ^ 2) * l ^ 2 =
      PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e 0) := hXW
  have F1 := F0
  rw [subst_wpShift_zero hl] at F1
  have F2 := congrArg (PowerSeries.subst (mulBy l linv al)) F0
  rw [← PowerSeries.coe_substAlgHom hm] at F2
  simp only [map_add (f := _), map_mul, map_pow, PowerSeries.coe_substAlgHom] at F2
  rw [subst_C', PowerSeries.subst_X hm, subst_mulBy_l h, PowerSeries.subst_comp_subst_apply hl hm,
    subst_mulBy_l h, subst_wpShift_zero hal] at F2
  have hZr : PowerSeries.subst (PowerSeries.C al * l) e = PowerSeries.subst l (PowerSeries.rescale al e) := by
    rw [subst_rescale h, PowerSeries.subst_comp_subst_apply hl hm, subst_mulBy_l h]
  have F3 := congrArg (PowerSeries.subst l) hE.2.2
  rw [← PowerSeries.coe_substAlgHom hl] at F3
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_mul, map_sum, map_sub, PowerSeries.coe_substAlgHom] at F3
  simp only [subst_C'] at F3
  simp only [hw, ← hZr, map_pow, map_add (f := _)] at F3
  have hsum : ∑ P, (xs P + PowerSeries.C c0 - (PowerSeries.C (xP P) + PowerSeries.C c0)) =
      ∑ P, (xs P - PowerSeries.C (xP P)) := Finset.sum_congr rfl (fun P _ => by ring)
  rw [hsum] at F3
  unfold veluXs
  simp only [map_pow, map_mul, map_sub, map_one]
  have key : l ^ 2 * (PowerSeries.C al ^ 2 * PowerSeries.subst (mulBy l linv al) A * PowerSeries.X ^ 2 -
      mulBy l linv al ^ 2 * (A + PowerSeries.X ^ 2 * (∑ P, (xs P - PowerSeries.C (xP P)) -
        (PowerSeries.C al ^ 2 - 1) * PowerSeries.C c0))) = 0 := by
    linear_combination PowerSeries.X ^ 2 * F2 + mulBy l linv al ^ 2 * PowerSeries.X ^ 2 * l ^ 2 * F3 -
      mulBy l linv al ^ 2 * F1
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 (l_ne_zero h)))

end Formalism.L2.Th1.C
end
end

