module

public import ReciprocityTheory.DualLattices.Bundle0003
public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0001
public import ReciprocityTheory.DualLattices.VIntCastLtOneOfDvd

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.SubgroupFreenessStatement
section
noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def SubgroupFreenessStatement : Prop :=
  IsAlgClosed C → CharZero C →
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    let B := AA.carrier.comap (pullQ (R := R) K)
    let AK := AA.carrier.map (resK (R := R) K)
    let IK := (augIdeal B).map (pullQ K)
    (∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ B.map (pullQ K)) ∧ g = ∑ j, b j * f j) ∧
    (∀ g ∈ AA.carrier, resK (R := R) K g = 0 → g ∈ IK * AA.carrier) ∧
    (∀ c cB cK, HasColen R v AA.carrier c → HasColen R v B cB → HasColen R v AK cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K)) ∧
    (∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈ augIdeal AK * augIdeal AK →
      g ∈ IK ⊔ augIdeal AA.carrier * augIdeal AA.carrier)

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.SubgroupQuotientStatement
section
noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def SubgroupQuotientStatement : Prop :=
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    (∃ AK : HopfOrder (C := C) R K, AK.carrier = AA.carrier.map (resK K)) ∧
    (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = AA.carrier.comap (pullQ K)) ∧
    dualLat (AA.carrier.map (resK (R := R) K)) = (dualLat AA.carrier).comap (extK K) ∧
    dualLat (AA.carrier.comap (pullQ (R := R) K)) = (dualLat AA.carrier).map (pushQ K)

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.SumInvMulTrace
section
namespace ReciprocityTheory.PGsh

open Finset

private lemma sum_inv_mul_trace (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [inst : Algebra (ZMod p) F] :
    ∑ a : F, a⁻¹ * algebraMap (ZMod p) F (Algebra.trace (ZMod p) F a) = -1 := by
  classical
  simp_rw [_root_.trace_eq_sum_automorphisms, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
  have h1 : ∑ a : F, a⁻¹ * (1 : F ≃ₐ[ZMod p] F) a = -1 := by
    have : ∀ a : F, a⁻¹ * (1 : F ≃ₐ[ZMod p] F) a = 1 - if a = 0 then 1 else 0 := by
      intro a
      by_cases h : a = 0
      · simp [h]
      · simp [h]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, nsmul_eq_mul, mul_one,
      FiniteField.cast_card_eq_zero, zero_sub]
  have h2 : ∀ σ : F ≃ₐ[ZMod p] F, σ ≠ 1 → ∑ a : F, a⁻¹ * σ a = 0 := by
    intro σ hσ
    obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h)
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
    have key : ∑ a : F, (b⁻¹ * σ b) * (a⁻¹ * σ a) = ∑ a : F, a⁻¹ * σ a := by
      refine Fintype.sum_equiv (Equiv.mulLeft₀ b hb0) _ _ (fun a => ?_)
      simp only [Equiv.mulLeft₀_apply, map_mul, mul_inv]
      ring
    rw [← Finset.mul_sum] at key
    have hne : b⁻¹ * σ b ≠ 1 := fun h => hb ((inv_mul_eq_one₀ hb0).mp h).symm
    have : (b⁻¹ * σ b - 1) * ∑ a : F, a⁻¹ * σ a = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  rw [h1, Finset.sum_eq_zero (fun σ hσ => h2 σ (Finset.ne_of_mem_erase hσ)), add_zero]

theorem gaussCongruence : GaussCongruenceStatement := by
  intro p _ F _ _ _ O _ _ m _ ι ω ζ hF hζ hω
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  show ∃ y ∈ m, (∑ a : F, ω⁻¹ a * ζ ^ (Algebra.trace (ZMod p) F a).val) = (ζ - 1) * (y - 1)
  obtain ⟨c, rfl⟩ : ∃ c, ζ = 1 + c := ⟨ζ - 1, by ring⟩
  simp only [add_sub_cancel_left]
  have : CharP (O ⧸ m) p := charP_of_injective_ringHom ι.injective p

  have hc : c ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h : (Ideal.Quotient.mk m c) ^ p = 0 := by
      have e : Ideal.Quotient.mk m c = Ideal.Quotient.mk m (1 + c) - 1 := by
        rw [map_add (f := _), map_one]; ring
      rw [e, sub_pow_char, one_pow, ← map_pow, hζ, map_one, sub_self]
    exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h

  have hbin : ∀ n : ℕ, ∃ r : O, (1 + c) ^ n = 1 + (n : O) * c + c ^ 2 * r := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨n + r + c * r, by rw [pow_succ, hr]; push_cast; ring⟩
  choose r hr using hbin

  obtain ⟨b, hb0, hb1⟩ : ∃ b : F, b ≠ 0 ∧ b ≠ 1 := by
    classical
    by_contra h
    push Not at h
    apply hF
    have h1 : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have h2 := Finset.card_le_card h1
    have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    have h4 := Fintype.one_lt_card (α := F)
    rw [Finset.card_univ] at h2
    omega
  have hω1 : ω ≠ 1 := by
    intro h
    have e := hω b
    have e1 := MulChar.one_apply_coe (R' := O) (Units.mk0 b hb0)
    rw [Units.val_mk0] at e1
    rw [h, e1, map_one] at e
    exact hb1 (ι.injective (e.symm.trans ι.map_one.symm))
  have hsum0 : ∑ a : F, ω⁻¹ a = 0 := MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hω1)
  set t : F → ℕ := fun a => (Algebra.trace (ZMod p) F a).val with ht
  refine ⟨1 + ∑ a : F, ω⁻¹ a * (t a : O) + c * ∑ a : F, ω⁻¹ a * r (t a), ?_, ?_⟩
  · refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hc)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_add (f := _), map_one, map_sum]
    have e : ∀ a : F, Ideal.Quotient.mk m (ω⁻¹ a * (t a : O)) =
        ι (a⁻¹ * algebraMap (ZMod p) F (Algebra.trace (ZMod p) F a)) := by
      intro a
      rw [map_mul, map_mul, MulChar.inv_apply', hω, map_natCast, ← map_natCast ι, ht,
        ZMod.natCast_val]
      rfl
    simp_rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, sum_inv_mul_trace p F, map_neg, map_one, add_neg_cancel]
  · calc ∑ a : F, ω⁻¹ a * (1 + c) ^ t a
        = ∑ a : F, (ω⁻¹ a + c * (ω⁻¹ a * (t a : O) + c * (ω⁻¹ a * r (t a)))) :=
          Finset.sum_congr rfl fun a _ => by rw [hr]; ring
      _ = ∑ a : F, ω⁻¹ a + c * (∑ a : F, ω⁻¹ a * (t a : O) + c * ∑ a : F, ω⁻¹ a * r (t a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hsum0]; ring

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.SumLambdaWeight
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

structure IsTeich (v : Valuation C NNReal) (ω : ZMod p → C) : Prop where
  pow : ∀ a, ω a ^ p = ω a
  cong : ∀ a, v (ω a - (a.val : C)) < 1
  zero : ω 0 = 0
  one : ω 1 = 1
  mul : ∀ a b, ω (a * b) = ω a * ω b
  sep : ∀ a b, a ≠ b → v (ω a - ω b) = 1

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem int (a : ZMod p) : v (ω a) ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha, hω.zero, map_zero]
    exact zero_le
  · have h := hω.sep a 0 ha
    rw [hω.zero, sub_zero] at h
    exact h.le

theorem v_eq_one {a : ZMod p} (ha : a ≠ 0) : v (ω a) = 1 := by
  have h := hω.sep a 0 ha
  rwa [hω.zero, sub_zero] at h

theorem ne_zero {a : ZMod p} (ha : a ≠ 0) : ω a ≠ 0 := by
  intro h
  have h1 := hω.v_eq_one ha
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem pow_pred {a : ZMod p} (ha : a ≠ 0) : ω a ^ (p - 1) = 1 := by
  have hne := hω.ne_zero ha
  have h1 : ω a ^ (p - 1) * ω a = 1 * ω a := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, one_mul]
    exact hω.pow a
  exact mul_right_cancel₀ hne h1

end IsTeich

def wt (ω : ZMod p → C) (a : ZMod p) : C := ω a ^ (2 * p - 3)

def sS (ω : ZMod p → C) : C := ∑ b, wt ω b

def u0 (ω : ZMod p → C) (a : ZMod p) : C := wt ω a - if a = 0 then sS ω else 0

def lam (ω : ZMod p → C) (f : ZMod p → C) : C := ∑ a, u0 ω a * f a

section wt

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem wt_zero : wt ω 0 = 0 := by
  unfold wt
  rw [hω.zero]
  exact zero_pow (by have := hp.out.two_le; omega)

theorem wt_mul_self {a : ZMod p} (ha : a ≠ 0) : wt ω a * ω a = 1 := by
  unfold wt
  rw [← pow_succ]
  have e : 2 * p - 3 + 1 = (p - 1) * 2 := by
    have := hp.out.two_le
    omega
  rw [e, pow_mul, hω.pow_pred ha, one_pow]

theorem wt_int (a : ZMod p) : v (wt ω a) ≤ 1 := by
  unfold wt
  rw [map_pow]
  exact pow_le_one₀ (zero_le) (hω.int a)

private theorem lam_eq_sum_wt_mul_sub (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  simp [lam, u0, sS, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

theorem lam_eq (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  exact lam_eq_sum_wt_mul_sub hω f

theorem lam_omega : lam ω ω = (p : C) - 1 := by
  rw [lam_eq_sum_wt_mul_sub hω, hω.zero]
  simp only [sub_zero]
  have h1 : ∀ a, wt ω a * ω a = 1 - if a = 0 then 1 else 0 := fun a => by
    split_ifs with ha
    · rw [ha, hω.wt_zero, zero_mul, sub_self]
    · rw [hω.wt_mul_self ha, sub_zero]
  simp only [h1, Finset.sum_sub_distrib]
  simp

end IsTeich

end wt

section hopf

variable (hv : v.Integers R)
include hv

omit hv in
theorem pow_mem' (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (n : ℕ) : f ^ n ∈ AA.carrier := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact AA.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact AA.mul_mem _ _ ih hf


variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

end hopf

end ReciprocityTheory.PGsh.Up.U3
end
end

-- bundled from ReciprocityTheory.DualLattices.TransposeMulSelf
section
namespace ReciprocityTheory.PGsh

open Matrix

section

variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private noncomputable def invPerm (e : G ≃ AddChar G K) : Equiv.Perm G :=
  Function.Involutive.toPerm (fun h => e.symm (e h)⁻¹) (fun h => by simp)

private lemma invPerm_apply (e : G ≃ AddChar G K) (h : G) :
    invPerm e h = e.symm (e h)⁻¹ := rfl

private lemma transpose_mul_self (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g)ᵀ * (Matrix.of fun g h : G => e h g) =
      (Fintype.card G : K) • (invPerm e).permMatrix K := by
  ext g h
  have key : ∀ x, e g x * e h x = (e g * e h) x := fun x => (AddChar.mul_apply _ _ _).symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, smul_eq_mul, key]
  by_cases hgh : e g * e h = 1
  · have h1 : invPerm e g = h := by
      rw [invPerm_apply, inv_eq_of_mul_eq_one_right hgh, Equiv.symm_apply_apply]
    rw [if_pos h1, hgh]
    simp
  · have h1 : ¬ invPerm e g = h := by
      intro h1
      apply hgh
      rw [invPerm_apply] at h1
      rw [← h1, Equiv.apply_symm_apply, mul_inv_cancel]
    rw [if_neg h1, AddChar.sum_eq_zero_of_ne_one hgh, mul_zero]

private lemma det_sq (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g).det ^ 2 =
      (Fintype.card G : K) ^ Fintype.card G * (Equiv.Perm.sign (invPerm e) : K) := by
  have h := congrArg Matrix.det (transpose_mul_self e)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_permutation] at h
  rw [sq]
  exact h

end

theorem charTable : CharTableStatement := by
  intro K _ G _ _ _ e
  rw [det_sq e]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (invPerm e)) with h | h <;> rw [h]
  · left; simp
  · right; simp

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.VDetEqOneOfIntegral
section
namespace ReciprocityTheory.PGsh

open Matrix

section

variable {K : Type} [Field K] (v : Valuation K NNReal) {ι : Type} [Fintype ι] [DecidableEq ι]

def IsIntegralMat (U : Matrix ι ι K) : Prop := ∀ i j, v (U i j) ≤ 1

def IsIntegralVec (c : ι → K) : Prop := ∀ j, v (c j) ≤ 1

variable {v}

theorem IsIntegralMat.det_le_one {U : Matrix ι ι K} (hU : IsIntegralMat v U) : v U.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine v.map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  have hs : v ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hs, one_mul]
  exact Finset.prod_le_one₀ (fun _ _ => zero_le) fun i _ => hU _ _

private theorem nnreal_mul_le_one {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  simpa using mul_le_mul ha hb (zero_le) zero_le_one

theorem IsIntegralMat.mulVec {U : Matrix ι ι K} {c : ι → K} (hU : IsIntegralMat v U)
    (hc : IsIntegralVec v c) : IsIntegralVec v (U *ᵥ c) := by
  intro i
  show v (∑ j, U i j * c j) ≤ 1
  exact v.map_sum_le fun j _ => by rw [map_mul]; exact _root_.ReciprocityTheory.PGsh.nnreal_mul_le_one (hU i j) (hc j)

theorem isIntegralVec_single (j : ι) : IsIntegralVec v (Pi.single j (1 : K)) := by
  intro k
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

end

structure Lat {K : Type} [Field K] (v : Valuation K NNReal) (ι : Type) [Fintype ι]
    [DecidableEq ι] where

  B : Matrix ι ι K
  det_ne : B.det ≠ 0

namespace Lat

variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

def pts (L : Lat v ι) : Set (ι → K) := {x | ∃ c, IsIntegralVec v c ∧ x = L.B *ᵥ c}

def std (v : Valuation K NNReal) (ι : Type) [Fintype ι] [DecidableEq ι] : Lat v ι :=
  ⟨1, by simp⟩

theorem isUnit_det (L : Lat v ι) : IsUnit L.B.det :=
  isUnit_iff_ne_zero.mpr L.det_ne

theorem pts_subset_iff (L' L : Lat v ι) :
    L'.pts ⊆ L.pts ↔ IsIntegralMat v (L.B⁻¹ * L'.B) := by
  constructor
  · intro h i j
    obtain ⟨c, hc, hx⟩ := h ⟨Pi.single j 1, ReciprocityTheory.PGsh.isIntegralVec_single j, rfl⟩
    have hM : (L.B⁻¹ * L'.B) *ᵥ Pi.single j 1 = c := by
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_det L), Matrix.one_mulVec]
    have e := congrFun hM i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at e
    rw [e]
    exact hc i
  · intro hM x ⟨c, hc, hx⟩
    refine ⟨(L.B⁻¹ * L'.B) *ᵥ c, hM.mulVec hc, ?_⟩
    rw [hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det L),
      Matrix.one_mul]

theorem v_det_eq_one_of_integral {U V : Matrix ι ι K} (hU : IsIntegralMat v U)
    (hV : IsIntegralMat v V) (hUV : U * V = 1) : v U.det = 1 := by
  refine le_antisymm hU.det_le_one ?_
  calc (1 : NNReal) = v U.det * v V.det := by
        rw [← map_mul, ← Matrix.det_mul, hUV, Matrix.det_one, map_one]
    _ ≤ v U.det * 1 := mul_le_mul_of_nonneg_left hV.det_le_one (zero_le)
    _ = v U.det := mul_one _

private theorem valuation_lat_det_ne_zero (L : ReciprocityTheory.PGsh.Lat v ι) : v L.B.det ≠ 0 :=
  (Valuation.ne_zero_iff v).mpr L.det_ne

private theorem valuation_det_inv_mul_eq_div (L' L : ReciprocityTheory.PGsh.Lat v ι) :
    v (L.B⁻¹ * L'.B).det = v L'.B.det / v L.B.det := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_mul, map_inv₀,
    div_eq_inv_mul]

theorem v_det_eq_of_pts_eq {L₁ L₂ : Lat v ι} (h : L₁.pts = L₂.pts) :
    v L₁.B.det = v L₂.B.det := by
  have h₁ := (pts_subset_iff L₁ L₂).mp h.subset
  have h₂ := (pts_subset_iff L₂ L₁).mp h.symm.subset
  have hMN : (L₂.B⁻¹ * L₁.B) * (L₁.B⁻¹ * L₂.B) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L₁.B,
      Matrix.mul_nonsing_inv _ (isUnit_det L₁), Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (isUnit_det L₂)]
  have := v_det_eq_one_of_integral h₁ h₂ hMN
  rw [valuation_det_inv_mul_eq_div] at this
  exact (div_eq_one_iff_eq (valuation_lat_det_ne_zero L₂)).mp this

end Lat

section colen

variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def colen (L' L : Lat v ι) : NNReal := v L'.B.det / v L.B.det

theorem colen_eq_v_det (L' L : Lat v ι) : colen L' L = v (L.B⁻¹ * L'.B).det := by
  rw [_root_.ReciprocityTheory.PGsh.Lat.valuation_det_inv_mul_eq_div]
  rfl

theorem colen_congr {L₁' L₂' L₁ L₂ : Lat v ι} (h' : L₁'.pts = L₂'.pts) (h : L₁.pts = L₂.pts) :
    colen L₁' L₁ = colen L₂' L₂ := by
  unfold colen
  rw [ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h', ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h]

end colen

end ReciprocityTheory.PGsh
end

