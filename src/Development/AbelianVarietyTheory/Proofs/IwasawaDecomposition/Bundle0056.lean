module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddMulDerivativeTrunc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogAdd

open Polynomial

theorem one_add_mul_derivative_trunc {R : Type} [CommRing R] (n : ℕ) (u : R[X]) (hu : u ^ n = 0) :
    (1 + u) * derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (n.factorial : R[X]) * derivative u := by
  have h1 : derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-u) ^ k) * ((n.factorial : R[X]) * derivative u) := by
    rw [derivative_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hd : (k + 1) ∣ n.factorial :=
      Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.1 hk)
    have hc : ((n.factorial / (k + 1) : ℕ) : R[X]) * ((k : R[X]) + 1) = (n.factorial : R[X]) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → R[X]) (Nat.div_mul_cancel hd)
    have hs : derivative ((-1 : R[X]) ^ k) = 0 := by
      rcases neg_one_pow_eq_or R[X] k with h | h <;> simp [h]
    rw [derivative_mul, derivative_mul, hs, derivative_natCast, derivative_pow_succ, ← hc, neg_pow u]
    simp only [map_add (f := _), map_natCast, map_one]
    ring
  have h2 : (1 + u) * ∑ k ∈ Finset.range n, (-u) ^ k = 1 := by
    have := mul_neg_geom_sum (-u) n
    rw [sub_neg_eq_add, neg_pow u, hu, mul_zero, sub_zero] at this
    exact this
  rw [h1, ← mul_assoc, h2, one_mul]

theorem trunc_add {R : Type} [CommRing R] (hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R)) (n : ℕ)
    (I : Ideal R) (hI : I ^ n = ⊥) (a b : R) (ha : a ∈ I) (hb : b ∈ I) :
    (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * (a + b + a * b) ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * a ^ (k + 1)) +
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * b ^ (k + 1)) := by
  let F : R[X] → R[X] := fun u => ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)
  let J : Ideal R[X] := I.map (C : R →+* R[X])
  have hJ : ∀ u ∈ J, u ^ n = 0 := by
    intro u hu
    have := Ideal.pow_mem_pow hu n
    rwa [← Ideal.map_pow, hI, Ideal.map_bot, Ideal.mem_bot] at this
  set s : R[X] := C a * X with hs
  set t : R[X] := C b * X with ht
  have hsJ : s ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ ha)
  have htJ : t ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ hb)
  have huJ : s + t + s * t ∈ J := J.add_mem (J.add_mem hsJ htJ) (J.mul_mem_right _ hsJ)
  have e1 : (1 + s) * derivative (F s) = _ := one_add_mul_derivative_trunc n s (hJ _ hsJ)
  have e2 : (1 + t) * derivative (F t) = _ := one_add_mul_derivative_trunc n t (hJ _ htJ)
  have e3 : (1 + (s + t + s * t)) * derivative (F (s + t + s * t)) = _ :=
    one_add_mul_derivative_trunc n _ (hJ _ huJ)
  have hunit : IsUnit (1 + (s + t + s * t)) := IsNilpotent.isUnit_one_add ⟨n, hJ _ huJ⟩
  have hD : derivative (F (s + t + s * t) - F s - F t) = 0 := by
    apply hunit.mul_left_cancel
    rw [derivative_add, derivative_add, derivative_mul (f := s) (g := t)] at e3
    rw [derivative_sub, derivative_sub]
    linear_combination e3 - (1 + t) * e1 - (1 + s) * e2
  have hC : F (s + t + s * t) - F s - F t = C ((F (s + t + s * t) - F s - F t).coeff 0) := by
    ext k
    cases k with
    | zero => simp only [coeff_C_zero]
    | succ k =>
      have h := congrArg (fun (p : R[X]) => p.coeff k) hD
      simp only [coeff_derivative, coeff_zero] at h
      rw [coeff_C_succ]
      have hu : IsUnit ((k : R) + 1) := by exact_mod_cast hR (k + 1) (Nat.succ_ne_zero k)
      exact (hu.mul_left_eq_zero).1 h
  have h0 : (F (s + t + s * t) - F s - F t).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [F, hs, ht, eval_finsetSum]
  rw [h0, map_zero] at hC
  have h1 := congrArg (eval 1) hC
  simp only [F, hs, ht, eval_sub, eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one,
    eval_natCast, eval_add, eval_C, eval_X, mul_one, eval_zero] at h1
  linear_combination h1

theorem tm_sub_one_mem (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
  apply GlobalTheory.RingIface.alg_mem_kerP
  simp [he]

theorem map_mul_sub_one {M A B : Type} [Monoid M] [CommRing A] [CommRing B] (g : M →* A)
    (f : A →+* B) (e e' : M) :
    f (g (e * e') - 1) = f (g e - 1) + f (g e' - 1) + f (g e - 1) * f (g e' - 1) := by
  simp only [map_sub, map_mul, map_one]
  ring

theorem tm_mul_sub_one (l : ℕ) [Fact l.Prime] (e e' : Per.Fl l) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm (e * e') - 1) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) *
          algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) :=
  map_mul_sub_one (WittVector.teichmuller l) _ e e'

theorem log_add : ∀ (l : ℕ) [Fact l.Prime], ∀ (e e' : Per.Fl l) (y y' z : Per.BdRp l),
    e.untilt = 1 → e'.untilt = 1 → Per.IsLog l e y → Per.IsLog l e' y' →
      Per.IsLog l (e * e') z → z = y + y' := by
  intro l _ e e' y y' z he he' hy hy' hz
  refine GlobalTheory.RingIface.ev_ext l _ _ fun n => ?_
  let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Per.AinfP l ⧸ Per.kerP l ^ n) := fun m hm => by
    have := (GlobalTheory.RingBasics.isUnit_nat l m hm).map q
    rwa [map_natCast] at this
  apply (hR _ n.factorial_ne_zero).mul_left_cancel
  rw [map_add (f := _), mul_add, GlobalTheory.CrisIncl.factorial_mul_ev l e y he hy n,
    GlobalTheory.CrisIncl.factorial_mul_ev l e' y' he' hy' n,
    GlobalTheory.CrisIncl.factorial_mul_ev l _ z (by rw [map_mul, he, he', mul_one]) hz n]
  have hI : ((Per.kerP l).map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have key := trunc_add hR n _ hI _ _ (Ideal.mem_map_of_mem q (tm_sub_one_mem l e he))
    (Ideal.mem_map_of_mem q (tm_sub_one_mem l e' he'))
  rw [tm_mul_sub_one]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = a at key ⊢
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) = b at key ⊢
  change q _ = q _ + q _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, map_add (f := _)]
  exact key

end GlobalTheory.MemLoc.LogAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.ThetaD

section general
variable {R : Type} [CommRing R] (I : Ideal R)

theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by
  induction y using AdicCompletion.induction_on with
  | _ x =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl

theorem isUnit_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n y) := by
  have key : IsUnit (AdicCompletion.evalₐ I (n + 1) y) := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
    rw [← factorPow_evalₐ I (show 1 ≤ n + 1 by omega), ← ha] at hy
    obtain ⟨b, hb⟩ := hy.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : a * b - 1 ∈ I ^ 1 := by
      rw [← Ideal.Quotient.eq]
      exact hb
    rw [pow_one] at h1
    have hn : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) (a * b - 1)) :=
      ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h1 _⟩
    have hu := hn.isUnit_add_one
    rw [map_sub, map_one, sub_add_cancel, map_mul] at hu
    rw [← ha]
    exact isUnit_of_mul_isUnit_left hu
  rw [← factorPow_evalₐ I (Nat.le_succ n)]
  exact key.map _

theorem isUnit_of_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by
  let f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n := fun n =>
    IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ I y hy n)
  have hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x := fun n x =>
    IsLocalization.Away.lift_eq y _ x
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, hf0, factorPow_evalₐ]
  have e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y :=
    AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]
  rw [← e]
  exact (IsLocalization.Away.algebraMap_isUnit y).map _

end general

variable (l : ℕ) [Fact l.Prime]

theorem frob_surj : Function.Surjective (frobenius (ModP (Per.OC l) l) l) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl
  have hb1 : b ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC]
    have := (GlobalTheory.RingBasics.mem_OC _).1 a.2
    rw [← hb, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne').1 this
  refine ⟨Ideal.Quotient.mk _ ⟨b, hb1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  exact congrArg _ (Subtype.ext hb)

theorem θ_surj : Function.Surjective (Per.θ l) := surjective_fontaineTheta (frob_surj l)

theorem fontaineTheta_algebraMap₂ (a : Per.Ainf l) : Per.θP l (algebraMap _ _ a) = (Per.θ l a : ℂ_[l]) :=
  GlobalTheory.RingIface.fontaineTheta_algebraMap l a

theorem fontaineTheta_eq_zero (a : Per.AinfP l) : Per.θP l a = 0 ↔ a ∈ Per.kerP l := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l a (by rwa [pow_one])⟩
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) a
  have hs := IsLocalization.map_units (Per.AinfP l) s
  have h1 := congrArg (Per.θP l) hx
  rw [map_mul, h, zero_mul, fontaineTheta_algebraMap₂] at h1
  have h2 : Per.θ l x = 0 := Subtype.ext h1.symm
  have h3 := GlobalTheory.RingIface.alg_mem_kerP l h2
  have h4 : a * algebraMap (Per.Ainf l) (Per.AinfP l) (s : Per.Ainf l) ∈ Per.kerP l := by
    rw [hx]; exact h3
  exact (Ideal.mul_unit_mem_iff_mem _ hs).1 h4

theorem fontaineTheta_surjective' : Function.Surjective (Per.θP l) := by
  intro c
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℂ_[l]) ^ n * c‖ ≤ 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : ℂ_[l])) GlobalTheory.RingBasics.norm_p_lt).mul_const ‖c‖
    rw [zero_mul] at h
    obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds one_pos)).exists
    exact ⟨n, by rwa [norm_mul, norm_pow]⟩
  obtain ⟨a, ha⟩ := θ_surj l ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩
  obtain ⟨u, hu⟩ := ((GlobalTheory.RingBasics.isUnit_l l).pow n).exists_left_inv
  refine ⟨u * algebraMap _ _ a, ?_⟩
  have h := congrArg (Per.θP l) hu
  rw [map_mul, map_pow, map_natCast, map_one] at h
  rw [map_mul, fontaineTheta_algebraMap₂, ha]
  change _ * (_ * c) = c
  rw [← mul_assoc, h, one_mul]

theorem θP_σ (g : Per.Gq l) (a : Per.AinfP l) :
    Per.θP l (Per.extP (Per.σA g) a) = Per.σC g (Per.θP l a) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := (Per.θP l).comp (Per.extP (Per.σA g))) (k := (Per.σC g).comp (Per.θP l))
    (RingHom.ext fun y => ?_)) a
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, fontaineTheta_algebraMap₂, GlobalTheory.RingBasics.θ_σA]
  exact GlobalTheory.RingIface.sigO_coe l g _

theorem θD_of_ev (y : Per.BdRp l) (a : Per.AinfP l) (h : Ideal.Quotient.mk _ a = Per.ev l 1 y) :
    Per.θD l y = Per.θP l a := by
  have h1 : y - algebraMap (Per.AinfP l) (Per.BdRp l) a ∈ Per.FilP l 1 := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, GlobalTheory.RingIface.ev_alg, h, sub_self]
  have h2 := GlobalTheory.RingIface.thetaD_of_mem_FilP l h1
  rwa [map_sub, GlobalTheory.RingIface.thetaD_alg, sub_eq_zero] at h2

theorem θD_alg (a : Per.AinfP l) : Per.θD l (algebraMap _ _ a) = Per.θP l a :=
  GlobalTheory.RingIface.thetaD_alg l a

end GlobalTheory.MemLoc.ThetaD


open GlobalTheory.MemLoc.ThetaD in
theorem GlobalTheory.MemLoc.thetaD_props : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θD l) ∧ (∀ y : Per.BdRp l, Per.θD l y = 0 ↔ y ∈ Per.FilP l 1) ∧ (∀ y : Per.BdRp l, Per.θD l y ≠ 0 → IsUnit y) ∧ (∀ a : Per.Ainf l, Per.θD l (aDp l a) = (Per.θ l a : ℂ_[l])) ∧ ∀ (g : Per.Gq l) (y : Per.BdRp l), Per.θD l (Per.σDp g y) = Per.σC g (Per.θD l y) := by
  intro l _
  refine ⟨fun c => ?_, fun y => ?_, fun y hy => ?_, fun a => ?_, fun g y => ?_⟩
  · obtain ⟨a, rfl⟩ := fontaineTheta_surjective' l c
    exact ⟨_, θD_alg l a⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha, fontaineTheta_eq_zero, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← ha,
      Ideal.Quotient.eq_zero_iff_mem, pow_one]
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha] at hy
    obtain ⟨b, hb⟩ := fontaineTheta_surjective' l (Per.θP l a)⁻¹
    have h1 : a * b - 1 ∈ Per.kerP l ^ 1 := by
      rw [pow_one, ← fontaineTheta_eq_zero, map_sub, map_mul, hb, map_one, mul_inv_cancel₀ hy, sub_self]
    have hu : IsUnit (Per.ev l 1 y) := by
      rw [← ha]
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ b) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)), Ideal.Quotient.eq]
      exact h1
    obtain ⟨e, -, he⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
    rw [← he] at hu
    have h2 := (isUnit_of_evalₐ (Per.kerP l) (e y) hu).map e.symm
    rwa [RingEquiv.symm_apply_apply] at h2
  · exact (θD_alg l _).trans (fontaineTheta_algebraMap₂ l a)
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha, ← θP_σ]
    exact θD_of_ev l _ _ (GlobalTheory.RingIface.ev_sigDp l g 1 y a ha.symm).symm
end

