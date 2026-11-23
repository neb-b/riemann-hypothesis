module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CompInv
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

section Tools

variable {R : Type u} [CommRing R]

theorem eq_substInv_of_right (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s))
    (t : R⟦X⟧) (ht0 : constantCoeff t = 0) (ht : s.subst t = X) :
    t = s.substInvOfIsUnit h1 := by
  have hs : HasSubst s := HasSubst.of_constantCoeff_zero' h0
  have hT : HasSubst t := HasSubst.of_constantCoeff_zero' ht0
  have key := subst_comp_subst_apply hs hT (s.substInvOfIsUnit h1)
  rw [subst_substInvOfIsUnit_left s h0 h1, subst_X hT, ht, X_subst] at key
  exact key

theorem eq_substInv_of_left (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s))
    (t : R⟦X⟧) (ht : t.subst s = X) :
    t = s.substInvOfIsUnit h1 := by
  have hs : HasSubst s := HasSubst.of_constantCoeff_zero' h0
  have hq : HasSubst (s.substInvOfIsUnit h1) := HasSubst.substInvOfIsUnit s h1
  have key := subst_comp_subst_apply hs hq t
  rw [subst_substInvOfIsUnit_right s h0 h1, ht, subst_X hq, X_subst] at key
  exact key.symm

theorem compInv_eq_substInv (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s)) :
    compInv s = s.substInvOfIsUnit h1 := by
  have hex : ∃ t : R⟦X⟧, constantCoeff t = 0 ∧ s.subst t = X :=
    ⟨s.substInvOfIsUnit h1, constantCoeff_substInvOfIsUnit s h1,
      subst_substInvOfIsUnit_right s h0 h1⟩
  unfold compInv
  rw [dite_eq_left hex]
  exact eq_substInv_of_right s h0 h1 _ hex.choose_spec.1 hex.choose_spec.2

end Tools

theorem composition_inverse_spec : CompInvSpec.{u} := by
  intro R _ s h0 h1
  rw [compInv_eq_substInv s h0 h1]
  refine ⟨constantCoeff_substInvOfIsUnit s h1, subst_substInvOfIsUnit_right s h0 h1,
    subst_substInvOfIsUnit_left s h0 h1, ?_, fun t ht0 ht => eq_substInv_of_right s h0 h1 t ht0 ht,
    fun t _ ht => eq_substInv_of_left s h0 h1 t ht⟩
  rw [coeff_one_substInvOfIsUnit]
  exact h1.val_inv_mul

theorem composition_inverse_map : CompInvMap.{u, v} := by
  intro R S _ _ φ s h0 h1
  have h0' : constantCoeff (PowerSeries.map φ s) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have h1' : IsUnit (coeff 1 (PowerSeries.map φ s)) := by
    rw [coeff_map]; exact h1.map φ
  rw [compInv_eq_substInv _ h0' h1', compInv_eq_substInv s h0 h1]
  apply eq_substInv_of_right _ h0' h1'
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_substInvOfIsUnit, map_zero]
  · have := PowerSeries.map_subst (HasSubst.substInvOfIsUnit s h1) (h := φ) s
    rw [subst_substInvOfIsUnit_right s h0 h1] at this
    rw [← PowerSeries.map_X φ]
    exact this.symm

theorem integration_spec : IntegSpec.{u} := by
  unfold IntegSpec
  intro K _ _ f
  have hc : ∀ n : ℕ, coeff (n + 1) (integ f) = coeff n f / ((n : K) + 1) := by
    intro n
    unfold integ
    simp
  have hd : PowerSeries.derivative (integ f) = f := by
    ext n
    rw [coeff_derivative, hc]
    have : ((n : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    field_simp
  refine ⟨?_, hd, ?_⟩
  · unfold integ
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp
  · intro g hg0 hg
    ext n
    cases n with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, hg0]
      unfold integ
      simp
    | succ k =>
      rw [hc]
      have h1 := congrArg (coeff k) hg
      rw [coeff_derivative] at h1
      have : ((k : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
      rw [← h1]
      field_simp

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.EqWSerSubst
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace ISer

variable {R : Type u} [CommRing R]

def subHom (s : R⟦X⟧) (hs : constantCoeff s = 0) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom (HasSubst.of_constantCoeff_zero' hs)

theorem subHom_apply (s : R⟦X⟧) (hs : constantCoeff s = 0) (f : R⟦X⟧) :
    subHom s hs f = f.subst s := by
  unfold subHom
  rw [PowerSeries.coe_substAlgHom]

theorem subHom_X (s : R⟦X⟧) (hs : constantCoeff s = 0) : subHom s hs X = s := by
  rw [subHom_apply, PowerSeries.subst_X (HasSubst.of_constantCoeff_zero' hs)]

theorem subHom_C (s : R⟦X⟧) (hs : constantCoeff s = 0) (a : R) : subHom s hs (C a) = C a := by
  have h := (subHom s hs).commutes a
  simpa using h

theorem eq_wSer_subst (hW : WSerSpec.{u}) (W : WeierstrassCurve R) (s v : R⟦X⟧)
    (hs : constantCoeff s = 0) (hv : constantCoeff v = 0)
    (h : v = s ^ 3 + C W.a₁ * s * v + C W.a₂ * s ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * s * v ^ 2
      + C W.a₆ * v ^ 3) : v = (wSer W).subst s := by
  set w := (wSer W).subst s with hw
  obtain ⟨hfix0, hfix⟩ := (hW R W).1
  have hweq : w = s ^ 3 + C W.a₁ * s * w + C W.a₂ * s ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * s * w ^ 2
      + C W.a₆ * w ^ 3 := by
    have h2 := congrArg (subHom s hs) hfix
    simp only [map_add (f := _), map_mul, map_pow, subHom_X, subHom_C] at h2
    rw [subHom_apply] at h2
    exact h2
  have hw0 : constantCoeff w = 0 := by
    obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hfix0
    have h3 : w = s * subHom s hs q := by
      rw [hw, ← subHom_apply s hs, hq, map_mul, subHom_X]
    rw [h3, map_mul, hs, zero_mul]
  set E := C W.a₁ * s + C W.a₂ * s ^ 2 + C W.a₃ * (v + w) + C W.a₄ * s * (v + w)
    + C W.a₆ * (v ^ 2 + v * w + w ^ 2) with hE
  have h4 : v - w = (v - w) * E := by
    rw [hE]
    linear_combination h - hweq
  have hd : (v - w) * (1 - E) = 0 := by linear_combination h4
  have hu : IsUnit (1 - E) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h5 : constantCoeff E = 0 := by
      rw [hE]
      simp [hs, hv, hw0]
    rw [map_sub, map_one, h5, sub_zero]
    exact isUnit_one
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp hd)

end ISer

open ISer in
theorem iSerSpec_of (hW : WSerSpec.{u}) (hF : WSerFactor.{u}) (hU : UnitSpec.{u})
    (hD : FlowU.{u}) (hN : FlowNegUW.{u}) : ISerSpec.{u} := by
  intro R _ W
  obtain ⟨hw3, -, hUx, -, -⟩ := hF R W
  obtain ⟨-, hfo, -, -, -, hq0, hqr⟩ := hU R W
  obtain ⟨hDer, hConst, hFlow, -, -, hom⟩ := hD R W
  have hw0 : constantCoeff (wSer W) = 0 := (hW R W).1.1
  set r : R⟦X⟧ := invOfUnit (iDen W) (-1) with hr
  have hq : iDen W = -1 + C W.a₁ * X + C W.a₃ * wSer W := rfl
  have hi : iSer W = X * r := rfl
  have hr0 : constantCoeff r = -1 := by
    rw [hr, constantCoeff_invOfUnit]; simp
  have hi0 : constantCoeff (iSer W) = 0 := by rw [hi]; simp
  have hi1 : coeff 1 (iSer W) = -1 := by
    rw [hi, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      hr0]

  have hneg := hN R⟦X⟧ (curveS W) (D W) X (wSer W) r hDer hConst hFlow
    (by
      have : (-1 + (curveS W).a₁ * X + (curveS W).a₃ * wSer W : R⟦X⟧) = iDen W := rfl
      rw [this, mul_comm]; exact hqr)
  obtain ⟨hE, hDi, -⟩ := hneg
  have hwi : (wSer W).subst (iSer W) = wSer W * r := by
    symm
    apply eq_wSer_subst hW W (iSer W) (wSer W * r) hi0 (by simp [hw0])
    exact hE
  set φ := subHom (iSer W) hi0 with hφ
  have φa : ∀ f, f.subst (iSer W) = φ f := fun f => (subHom_apply _ _ f).symm
  have φX : φ X = X * r := subHom_X _ _
  have φC : ∀ a, φ (C a) = C a := subHom_C _ _
  have φw : φ (wSer W) = wSer W * r := by rw [← φa, hwi]
  have φq : φ (iDen W) = r := by
    rw [hq]
    simp only [map_add (f := _), map_mul, map_neg, map_one, φX, φC, φw]
    rw [hq] at hqr
    linear_combination hqr
  have φr : φ r = iDen W := by
    have h1 : φ (iDen W) * φ r = 1 := by rw [← map_mul, hqr, map_one]
    rw [φq] at h1
    linear_combination (iDen W) * h1 - (φ r) * hqr
  have hii : φ (iSer W) = X := by
    rw [hi, map_mul, φX, φr]
    linear_combination X * hqr
  have φU : φ (wU W) = wU W * iDen W ^ 2 := by
    have h1 : φ (wSer W) = φ X ^ 3 * φ (wU W) := by rw [← map_pow, ← map_mul, ← hw3]
    rw [φw, φX] at h1
    have h2 : X ^ 3 * (wU W * r) = X ^ 3 * (r ^ 3 * φ (wU W)) := by
      linear_combination h1 - r * hw3
    have h3 := X_pow_mul_cancel h2
    linear_combination (-(iDen W) ^ 3) * h3
      + (wU W * iDen W ^ 2 - φ (wU W) * ((iDen W * r) ^ 2 + iDen W * r + 1)) * hqr
  have φx : φ (xS W) = r ^ 2 * xS W := by
    have h1 : φ (wU W) * φ (xS W) = 1 := by rw [← map_mul, hUx, map_one]
    rw [φU] at h1
    linear_combination (r ^ 2 * xS W) * h1 - φ (xS W) * (iDen W * r) ^ 2 * hUx
      - φ (xS W) * (iDen W * r + 1) * hqr
  have φfw : φ (fw W) = fwAt (curveS W) (X * r) (wSer W * r) := by
    have : fwAt (curveS W) (X * r) (wSer W * r) = 1 - C W.a₁ * (X * r) - C W.a₂ * (X * r) ^ 2
      - 2 * C W.a₃ * (wSer W * r) - 2 * C W.a₄ * (X * r) * (wSer W * r)
      - 3 * C W.a₆ * (wSer W * r) ^ 2 := rfl
    rw [this, fw]
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, φX, φC, φw]
  have hDi' : D W (iSer W) = -φ (fw W) := by
    rw [φfw, ← hDi, hi, neg_neg]
  refine ⟨hi0, hi1, ?_, hwi, ?_, ?_, ?_, ?_⟩
  · rw [φa, hii]
  · rw [φa, φx]
  · rw [φa, yS, map_neg, φx]
    rw [hq] at hqr
    linear_combination (r ^ 2 * xS W) * hqr - r ^ 3 * C W.a₃ * xS W * hw3
      - r ^ 3 * C W.a₃ * X ^ 3 * hUx
  · rw [φa, hDi']
  · rw [φa, ← hom, hDi']
    have h1 : φ (fw W) * φ (om W) = 1 := by rw [← map_mul, hfo, map_one]
    linear_combination (-om W) * h1

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

variable {R : Type u} [CommRing R]

theorem dL_coeff (f : LaurentSeries R) (n : ℤ) :
    (dL f).coeff n = ((n + 1 : ℤ) : R) * f.coeff (n + 1) := by
  show (LaurentSeries.hasseDeriv R 1 f).coeff n = _
  rw [LaurentSeries.hasseDeriv_coeff]
  simp [Ring.choose_one_right, zsmul_eq_mul]

theorem uPow_mul_coeff (m n : ℤ) (f : LaurentSeries R) :
    (uPow m * f).coeff n = f.coeff (n - m) := by
  first
    | (have h := HahnSeries.coeff_single_mul_add (r := (1 : R)) (x := f) (a := n - m) (b := m)
       rw [sub_add_cancel, one_mul] at h
       exact h)
    | (have h := HahnSeries.single_mul_coeff_add (r := (1 : R)) (x := f) (a := n - m) (b := m)
       rw [sub_add_cancel, one_mul] at h
       exact h)

theorem C_mul_coeff (r : R) (f : LaurentSeries R) (n : ℤ) :
    (HahnSeries.C r * f).coeff n = r * f.coeff n := by
  rw [HahnSeries.C_mul_eq_smul]
  first | rw [HahnSeries.coeff_smul, smul_eq_mul] | rw [HahnSeries.smul_coeff, smul_eq_mul] | simp

theorem toL_coeff_nat (f : R⟦X⟧) (n : ℕ) : (toL f).coeff (n : ℤ) = coeff n f := by
  exact HahnSeries.ofPowerSeries_apply_coeff f n

theorem toL_coeff_neg (f : R⟦X⟧) {n : ℤ} (hn : n < 0) : (toL f).coeff n = 0 := by
  first
    | (rw [PowerSeries.coeff_coe, if_pos hn])
    | (simp only [toL, HahnSeries.ofPowerSeries_apply]
       rw [HahnSeries.embDomain_notin_range]
       rintro ⟨k, hk⟩
       simp at hk
       omega)

theorem uPow_zero : (uPow 0 : LaurentSeries R) = 1 := rfl

theorem uPow_one : (uPow 1 : LaurentSeries R) = toL X := by
  show HahnSeries.single (1 : ℤ) (1 : R) = _
  rw [HahnSeries.ofPowerSeries_X]

theorem uPow_add (m n : ℤ) : (uPow (m + n) : LaurentSeries R) = uPow m * uPow n := by
  show HahnSeries.single (m + n) (1 : R) = HahnSeries.single m 1 * HahnSeries.single n 1
  rw [HahnSeries.single_mul_single, mul_one]

theorem uPow_neg_mul (n : ℤ) : (uPow (-n) : LaurentSeries R) * uPow n = 1 := by
  rw [← uPow_add]
  first | rw [neg_add_cancel] | rw [neg_add_self] | rw [add_left_neg]
  exact uPow_zero

theorem uPow_mul_neg (n : ℤ) : (uPow n : LaurentSeries R) * uPow (-n) = 1 := by
  rw [← uPow_add]
  first | rw [add_neg_cancel] | rw [add_neg_self] | rw [add_right_neg]
  exact uPow_zero

theorem uPow_natCast (n : ℕ) : (uPow (n : ℤ) : LaurentSeries R) = toL (X ^ n) := by
  induction n with
  | zero => simp [uPow_zero]
  | succ k ih => rw [Nat.cast_succ, uPow_add, ih, uPow_one, ← map_mul, pow_succ]

theorem toL_C (r : R) : toL (C r) = (HahnSeries.C r : LaurentSeries R) := by
  first
    | exact HahnSeries.ofPowerSeries_C r
    | simp [toL]

theorem toL_injective : Function.Injective (toL : R⟦X⟧ → LaurentSeries R) := by
  exact HahnSeries.ofPowerSeries_injective

theorem exists_uPow_mul_toL (f : LaurentSeries R) :
    ∃ (m : ℤ) (F : R⟦X⟧), f = uPow m * toL F := by
  refine ⟨f.order, f.powerSeriesPart, ?_⟩
  first
    | exact (LaurentSeries.single_order_mul_powerSeriesPart f).symm
    | (show f = uPow f.order * HahnSeries.ofPowerSeries ℤ R f.powerSeriesPart
       rw [LaurentSeries.ofPowerSeries_powerSeriesPart]
       change f = uPow f.order * (uPow (-f.order) * f)
       rw [← mul_assoc, uPow_mul_neg, one_mul])

theorem dL_uPow_mul (m : ℤ) (f : LaurentSeries R) :
    dL (uPow m * f) = uPow m * dL f + HahnSeries.C ((m : ℤ) : R) * uPow (m - 1) * f := by
  rw [show HahnSeries.C ((m : ℤ) : R) * uPow (m - 1) * f
      = HahnSeries.C ((m : ℤ) : R) * (uPow (m - 1) * f) from mul_assoc _ _ _]
  ext n
  first | rw [HahnSeries.add_coeff] | rw [HahnSeries.coeff_add] | rw [HahnSeries.add_coeff']
  rw [dL_coeff, uPow_mul_coeff, uPow_mul_coeff, dL_coeff, C_mul_coeff, uPow_mul_coeff]
  have h1 : n + 1 - m = n - m + 1 := by ring
  have h2 : n - (m - 1) = n - m + 1 := by ring
  rw [h1, h2]
  push_cast
  ring

theorem dL_toL (f : R⟦X⟧) : dL (toL f) = toL (derivative f) := by
  ext n
  rw [dL_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [toL_coeff_neg _ hn]
    rcases lt_or_eq_of_le (show n + 1 ≤ 0 by omega) with h | h
    · rw [toL_coeff_neg _ h, mul_zero]
    · rw [h]
      simp
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hk : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hk, toL_coeff_nat, toL_coeff_nat, PowerSeries.coeff_derivative]
    push_cast
    ring

theorem dL_mul (f g : LaurentSeries R) : dL (f * g) = f * dL g + g * dL f := by
  obtain ⟨m, F, rfl⟩ := exists_uPow_mul_toL f
  obtain ⟨k, G, rfl⟩ := exists_uPow_mul_toL g
  have e : uPow m * toL F * (uPow k * toL G) = uPow (m + k) * toL (F * G) := by
    rw [uPow_add, map_mul]; ring
  have h0 : (uPow (m + k) : LaurentSeries R) = uPow m * uPow k := uPow_add m k
  have h1 : (uPow (m + k - 1) : LaurentSeries R) = uPow (m - 1) * uPow k := by
    rw [← uPow_add]; congr 1; ring
  have h2 : (uPow (m + k - 1) : LaurentSeries R) = uPow m * uPow (k - 1) := by
    rw [← uPow_add]; congr 1; ring
  have h3 : (HahnSeries.C (((m + k : ℤ)) : R) : LaurentSeries R)
      = HahnSeries.C ((m : ℤ) : R) + HahnSeries.C ((k : ℤ) : R) := by
    rw [Int.cast_add, map_add (f := _)]
  rw [e, dL_uPow_mul, dL_toL, Derivation.leibniz]
  simp only [dL_uPow_mul, dL_toL, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul]
  linear_combination (toL F * toL (derivative G) + toL G * toL (derivative F)) * h0
    + (toL F * toL G * uPow (m + k - 1)) * h3
    + (HahnSeries.C ((m : ℤ) : R) * toL F * toL G) * h1
    + (HahnSeries.C ((k : ℤ) : R) * toL F * toL G) * h2

theorem dL_uPow (n : ℤ) :
    dL (uPow n : LaurentSeries R) = HahnSeries.C ((n : ℤ) : R) * uPow (n - 1) := by
  have h1 : dL (1 : LaurentSeries R) = 0 := by
    have h := dL_toL (R := R) 1
    rwa [map_one, Derivation.map_one_eq_zero, map_zero] at h
  have h := dL_uPow_mul n (1 : LaurentSeries R)
  rw [mul_one, mul_one, h1, mul_zero, zero_add] at h
  exact h

theorem dL_C (r : R) : dL (HahnSeries.C r : LaurentSeries R) = 0 := by
  rw [← toL_C, dL_toL]
  first | rw [PowerSeries.derivative_C, map_zero] | simp

theorem dL_one : dL (1 : LaurentSeries R) = 0 := by
  have h := dL_C (R := R) 1
  rwa [map_one] at h

def derivationOfLeibniz {k A M : Type*} [CommSemiring k] [CommSemiring A] [AddCommGroup M]
    [Algebra k A] [Module A M] [Module k M] (D : A → M)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hsmul : ∀ (r : k) (a : A), D (r • a) = r • D a)
    (hmul : ∀ a b, D (a * b) = a • D b + b • D a) : Derivation k A M :=
  Derivation.mk' { toFun := D, map_add' := hadd, map_smul' := hsmul } hmul

def dLDR (R : Type u) [CommRing R] : Derivation R (LaurentSeries R) (LaurentSeries R) :=
  derivationOfLeibniz (fun f => dL f) (fun a b => map_add dL a b)
    (fun r f => by
      rw [Algebra.smul_def, HahnSeries.algebraMap_apply', ← HahnSeries.C_mul_eq_smul]
      change dL (toL (C r) * f) = _
      rw [toL_C, dL_mul, dL_C, mul_zero, add_zero])
    (fun f g => by rw [smul_eq_mul, smul_eq_mul, dL_mul])

theorem isDer_dL : (∀ a b : LaurentSeries R, dL (a + b) = dL a + dL b) ∧
    (∀ a b : LaurentSeries R, dL (a * b) = a * dL b + b * dL a) := by
  exact ⟨fun a b => map_add dL a b, dL_mul⟩

end Formalism.L2.Th1.A
end
end

