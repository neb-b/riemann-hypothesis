module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriCanon
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

private theorem tc_conj_mat {R D : Type} [CommRing R] [Group D] (r : D →* GG (m := 3) (R := R)) (h : GL (Fin 3) R) (g : D)
    (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

private theorem tc_res {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h) :
    (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 ∧
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
  have h1 : (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hh a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases e : a = b <;> simp [Matrix.one_apply, e]
  refine ⟨h1, ?_⟩
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h).map (residue R) = 1 := by
    rw [Units.inv_mul]; simp
  rwa [Matrix.map_mul, h1, Matrix.mul_one] at this

private theorem tc_res_conj {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h)
    (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    residue R ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h) a b) = residue R (X a b) := by
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h).map (residue R) = X.map (residue R) := by
    rw [Matrix.map_mul, Matrix.map_mul, (tc_res h hh).1, (tc_res h hh).2, Matrix.one_mul, Matrix.mul_one]
  exact congrFun (congrFun this a) b

private theorem tc_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : O) - 1) := by
    rw [show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring] at ht
    exact isUnit_of_mul_isUnit_left ht
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have := ht.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-(t : O)) * e
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have := h1.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-1 : O) * e
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg,
      Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption

private theorem tc_up {R : Type} [CommRing R] (Δ k U : Matrix (Fin 3) (Fin 3) R) (e : Δ * k = k * U)
    (hΔ : Δ.IsDiag) (hU : ∀ a b, wt a b < 0 → U a b = 0) (hu : ∀ a b, a ≠ b → IsUnit (Δ a a - U b b)) :
    ∀ a b, wt a b < 0 → k a b = 0 := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have d10 : Δ 1 0 = 0 := hΔ (by decide)
  have d12 : Δ 1 2 = 0 := hΔ (by decide)
  have d20 : Δ 2 0 = 0 := hΔ (by decide)
  have d21 : Δ 2 1 = 0 := hΔ (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, d10, d12, d20, d21] at e10 e20 e21
  have k10 : k 1 0 = 0 := (hu 1 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e10)
  have k20 : k 2 0 = 0 := (hu 2 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e20)
  have k21 : k 2 1 = 0 := (hu 2 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e21; linear_combination e21)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem tc_low {R : Type} [CommRing R] (Δ k U : Matrix (Fin 3) (Fin 3) R) (e : Δ * k = k * U)
    (hΔ : Δ.IsDiag) (hU : ∀ a b, 0 < wt a b → U a b = 0) (hu : ∀ a b, a ≠ b → IsUnit (Δ a a - U b b)) :
    ∀ a b, 0 < wt a b → k a b = 0 := by
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  have u01 := hU 0 1 (by decide)
  have u02 := hU 0 2 (by decide)
  have u12 := hU 1 2 (by decide)
  have d10 : Δ 1 0 = 0 := hΔ (by decide)
  have d12 : Δ 1 2 = 0 := hΔ (by decide)
  have d02 : Δ 0 2 = 0 := hΔ (by decide)
  have d01 : Δ 0 1 = 0 := hΔ (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, d10, d12, d02, d01] at e01 e02 e12
  have k12 : k 1 2 = 0 := (hu 1 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e12)
  have k02 : k 0 2 = 0 := (hu 0 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e02)
  have k01 : k 0 1 = 0 := (hu 0 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k02] at e01; linear_combination e01)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem tc_up' {R : Type} [CommRing R] (M k U : Matrix (Fin 3) (Fin 3) R) (e : M * k = k * U)
    (hk : ∀ a b, wt a b < 0 → k a b = 0) (hU : ∀ a b, wt a b < 0 → U a b = 0) (hu : ∀ a, IsUnit (k a a)) :
    (∀ a b, wt a b < 0 → M a b = 0) ∧ ∀ a, M a a = U a a := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  have e22 := congrFun (congrFun e 2) 2
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have k10 := hk 1 0 (by decide)
  have k20 := hk 2 0 (by decide)
  have k21 := hk 2 1 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, k10, k20, k21] at e10 e20 e21 e00 e11 e22
  have m10 : M 1 0 = 0 := (hu 0).mul_left_eq_zero.1 (by linear_combination e10)
  have m20 : M 2 0 = 0 := (hu 0).mul_left_eq_zero.1 (by linear_combination e20)
  have m21 : M 2 1 = 0 := (hu 1).mul_left_eq_zero.1 (by rw [m20] at e21; linear_combination e21)
  have m00 : M 0 0 = U 0 0 := sub_eq_zero.1 ((hu 0).mul_left_eq_zero.1 (by linear_combination e00))
  have m11 : M 1 1 = U 1 1 := sub_eq_zero.1 ((hu 1).mul_left_eq_zero.1 (by
    rw [m10] at e11; linear_combination e11))
  have m22 : M 2 2 = U 2 2 := sub_eq_zero.1 ((hu 2).mul_left_eq_zero.1 (by
    rw [m20, m21] at e22; linear_combination e22))
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)
  · fin_cases a <;> assumption

private theorem tc_low' {R : Type} [CommRing R] (M k U : Matrix (Fin 3) (Fin 3) R) (e : M * k = k * U)
    (hk : ∀ a b, 0 < wt a b → k a b = 0) (hU : ∀ a b, 0 < wt a b → U a b = 0) (hu : ∀ a, IsUnit (k a a)) :
    ∀ a b, 0 < wt a b → M a b = 0 := by
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  have u01 := hU 0 1 (by decide)
  have u02 := hU 0 2 (by decide)
  have u12 := hU 1 2 (by decide)
  have k01 := hk 0 1 (by decide)
  have k02 := hk 0 2 (by decide)
  have k12 := hk 1 2 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, k01, k02, k12] at e01 e02 e12
  have m12 : M 1 2 = 0 := (hu 2).mul_left_eq_zero.1 (by linear_combination e12)
  have m02 : M 0 2 = 0 := (hu 2).mul_left_eq_zero.1 (by linear_combination e02)
  have m01 : M 0 1 = 0 := (hu 1).mul_left_eq_zero.1 (by rw [m02] at e01; linear_combination e01)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem tc_rel {R : Type} [CommRing R] (h h' : GL (Fin 3) R) (X : Matrix (Fin 3) (Fin 3) R) :
    (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h) * (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') =
      (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') *
        (((h'⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h') := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (h : Matrix (Fin 3) (Fin 3) R), ← Matrix.mul_assoc (h' : Matrix (Fin 3) (Fin 3) R),
    Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.one_mul]

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.cond_iff_canon :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG (m := 3) (R := R)) (x : D) (h : GL (Fin 3) R), Red η Ψ r → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → Canon (r x).mat h →
      (CondT η Ψ I r ↔ TriIn η Ψ I r h) ∧ (CondD η Ψ I r ↔ DiagIn η Ψ I r h) := by
  intro O R D _ _ _ _ _ _ η Ψ I r x h hr hx hΨ hc
  have cm : ∀ (h : GL (Fin 3) R) (g : D), η g = 1 →
      (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h :=
    fun h g hg => tc_conj_mat r h g ((hr.mult g).trans hg)
  have hX : ∀ a, residue R ((r x).mat a a) = residue R (algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O)) := by
    intro a
    have := (residue_eq_zero_iff _).2 (hr.red x a a)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this]
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]
  have hu : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a b, a ≠ b →
      IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h) a a -
        (((h'⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h') b b) := by
    intro h' hh' a b hab
    rw [← residue_ne_zero_iff_isUnit, map_sub, tc_res_conj h hc.hat, tc_res_conj h' hh', hX, hX, ← map_sub,
      ← map_sub, residue_ne_zero_iff_isUnit]
    exact (tc_unit (Ψ x) hΨ a b hab).map _
  have hk : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a,
      IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') a a) := by
    intro h' hh' a
    have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h').map (residue R) = 1 := by
      rw [Matrix.map_mul, (tc_res h hc.hat).2, (tc_res h' hh').1, Matrix.one_mul]
    have := congrFun (congrFun this a) a
    rw [Matrix.map_apply, Matrix.one_apply_eq] at this
    rw [← residue_ne_zero_iff_isUnit, this]
    exact one_ne_zero
  have hT : ∀ h' : GL (Fin 3) R, InHat h' → TriIn η Ψ I r h' → TriIn η Ψ I r h := by
    intro h' hh' ht
    have k1 := tc_up _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.tri x hx) (hu h' hh')
    have k2 := fun g (hg : η g = 1) => tc_up' _ _ _ (tc_rel h h' (r g).mat) k1
      (by rw [← cm h' g hg]; exact ht.tri g hg) (hk h' hh')
    refine ⟨fun g hg => ?_, fun s hs hg a => ?_⟩
    · rw [cm h g hg]; exact (k2 g hg).1
    · rw [cm h s hg, (k2 s hg).2, ← cm h' s hg]; exact ht.ine s hs hg a
  refine ⟨⟨fun ⟨h', hh', ht⟩ => hT h' hh' ht, fun ht => ⟨h, hc.hat, ht⟩⟩,
    ⟨fun ⟨h', hh', ht⟩ => ⟨hT h' hh' ht.toTriIn, fun g hg => ?_⟩, fun ht => ⟨h, hc.hat, ht⟩⟩⟩
  have k1 := tc_low _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.low x hx) (hu h' hh')
  rw [cm h g hg]
  exact tc_low' _ _ _ (tc_rel h h' (r g).mat) k1 (by rw [← cm h' g hg]; exact ht.low g hg) (hk h' hh')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriangularConditionAtLOfFirstOrderDeformation
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] {m : Ideal R}

private def Kil (m : Ideal R) (X : Matrix (Fin 3) (Fin 3) R) : Prop := ∀ a b, ∀ x ∈ m, x * X a b = 0

private theorem kil_left {X M : Matrix (Fin 3) (Fin 3) R} (hX : Kil m X) (hM : EntIn m M) : M * X = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun c _ => hX c b _ (hM a c)

private theorem kil_right {X M : Matrix (Fin 3) (Fin 3) R} (hX : Kil m X) (hM : EntIn m M) : X * M = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun c _ => by rw [mul_comm]; exact hX a c _ (hM c b)

private theorem ent_left {M : Matrix (Fin 3) (Fin 3) R} (N : Matrix (Fin 3) (Fin 3) R) (hM : EntIn m M) :
    EntIn m (N * M) := fun a b => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hM c b)

private theorem ent_right {M : Matrix (Fin 3) (Fin 3) R} (N : Matrix (Fin 3) (Fin 3) R) (hM : EntIn m M) :
    EntIn m (M * N) := fun a b => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hM a c)

private theorem core {h hi A D Y γ : Matrix (Fin 3) (Fin 3) R} (hh : EntIn m (h - 1)) (hhi : EntIn m (hi - 1))
    (hA : EntIn m (A - D)) (hY : Kil m Y) (hYm : EntIn m Y) (hγ : Kil m γ) :
    hi * (1 + Y) * ((1 + γ) * A) * ((1 - Y) * h) = hi * A * h + (Y * D + γ * D - D * Y) := by
  obtain ⟨p, rfl⟩ : ∃ p, h = 1 + p := ⟨h - 1, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, hi = 1 + q := ⟨hi - 1, by abel⟩
  obtain ⟨e, rfl⟩ : ∃ e, A = D + e := ⟨A - D, by abel⟩
  simp only [add_sub_cancel_left] at hh hhi hA
  have e1 : (1 + Y) * ((1 + γ) * (D + e)) * (1 - Y) = (D + e) + (Y * D + γ * D - D * Y) := by
    have a1 : Y * γ = 0 := kil_left hγ hYm
    have a2 : Y * e = 0 := kil_right hY hA
    have a3 : γ * e = 0 := kil_right hγ hA
    have a4 : e * Y = 0 := kil_left hY hA
    have a5 : Y * (D * Y) = 0 := kil_right hY (ent_left _ hYm)
    have a6 : γ * (D * Y) = 0 := kil_right hγ (ent_left _ hYm)
    have : (1 + Y) * ((1 + γ) * (D + e)) * (1 - Y) = (D + e) + (Y * D + γ * D - D * Y) +
        ((Y * γ) * (D + e) * (1 - Y) + (Y * e) * (1 - Y) + (γ * e) * (1 - Y) - e * Y - Y * (D * Y) - γ * (D * Y)) := by
      noncomm_ring
    rw [this, a1, a2, a3, a4, a5, a6]; simp
  have hW : Kil m (Y * D + γ * D - D * Y) := fun a b x hx => by
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, mul_sub, mul_add, Finset.mul_sum,
      ← mul_assoc, hY _ _ x hx, hγ _ _ x hx, zero_mul, hY _ _ _ (Ideal.mul_mem_right _ _ hx)]
    simp
  generalize Y * D + γ * D - D * Y = W at e1 hW
  have b1 : q * W = 0 := kil_left hW hhi
  have b2 : W * p = 0 := kil_right hW hh
  calc _ = (1 + q) * ((1 + Y) * ((1 + γ) * (D + e)) * (1 - Y)) * (1 + p) := by simp only [Matrix.mul_assoc]
    _ = (1 + q) * (D + e) * (1 + p) + W + ((q * W) * (1 + p) + W * p) := by rw [e1]; noncomm_ring
    _ = _ := by rw [b1, b2]; simp

private theorem conj_mat {D : Type} [Group D] (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

private theorem ad_entry {D k : Type} [Group D] [CommRing k] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D) (hg : η g = 1)
    (X : Matrix (Fin 3) (Fin 3) k) (a b : Fin 3) :
    adRep (r0 η Ψ) g X a b * ((Ψ g ^ wt1 b : kˣ) : k) = ((Ψ g ^ wt1 a : kˣ) : k) * X a b := by
  show (GG.adFun (r0 η Ψ g) X) a b * _ = _
  unfold GG.adFun GG.mat
  rw [unitaryThreeReflection_left, ← map_inv, tor_val, tor_val, Matrix.mul_diagonal, Matrix.diagonal_mul, unitaryThreeReflection_right, if_pos hg,
    mul_assoc, ← Units.val_mul, ← mul_zpow]
  simp

private theorem condT_deform {O D : Type} [CommRing O] [IsLocalRing O] [Group D] [Algebra O R] [IsCO O R]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (f : R) (hf : ∀ x ∈ maximalIdeal R, x * f = 0)
    (hfm : f ∈ maximalIdeal R) (r r₂ : D →* GG (m := 3) (R := R)) (z : D → Matrix (Fin 3) (Fin 3) (ResidueField O))
    (γ : D → Matrix (Fin 3) (Fin 3) R) (hr : Red η Ψ r) (ht : CondT η Ψ I r)
    (hγ : ∀ g a b, ∃ o : O, residue O o = z g a b ∧ γ g a b = o • f) (hd : IsDeform r γ r₂)
    (μ : Matrix (Fin 3) (Fin 3) (ResidueField O))
    (h1 : ∀ g, η g = 1 → ∀ a b, wt a b < 0 →
      μ a b * residue O (psi Ψ b g) + z g a b * residue O (psi Ψ b g) - residue O (psi Ψ a g) * μ a b = 0)
    (h2 : ∀ s ∈ I, ∀ a, z s a a = 0) : CondT η Ψ I r₂ := by
  obtain ⟨h, hh, htri, hine⟩ := ht
  have hk : ∀ o : O, ∀ x ∈ maximalIdeal R, x * (o • f) = 0 := fun o x hx => by
    rw [mul_smul_comm, hf x hx, smul_zero]
  have h0 : ∀ o : O, residue O o = 0 → o • f = 0 := fun o ho => by
    rw [Algebra.smul_def]
    exact hf _ (map_nonunit (algebraMap O R) o ((residue_eq_zero_iff _).1 ho))
  choose o ho using fun a b => residue_surjective (μ a b)
  let Y : Matrix (Fin 3) (Fin 3) R := Matrix.of fun a b => o a b • f
  have hY : Kil (maximalIdeal R) Y := fun a b => hk _
  have hYm : EntIn (maximalIdeal R) Y := fun a b => Submodule.smul_of_tower_mem _ _ hfm
  have hYY : Y * Y = 0 := kil_left hY hYm
  let u : GL (Fin 3) R := ⟨1 - Y, 1 + Y,
    by rw [show (1 - Y) * (1 + Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero],
    by rw [show (1 + Y) * (1 - Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero]⟩
  have hhi : EntIn (maximalIdeal R) (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) - 1) := by
    have := ent_left (-((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) hh
    rwa [Matrix.mul_sub, Matrix.neg_mul, Units.inv_mul, Matrix.mul_one, sub_neg_eq_add, neg_add_eq_sub] at this
  have key : ∀ g, η g = 1 → ∀ a b, ∃ c : O, residue O c = z g a b ∧ (conjBy (u * h)⁻¹ r₂ g).mat a b =
      (conjBy h⁻¹ r g).mat a b + (o a b * psi Ψ b g + c * psi Ψ b g - psi Ψ a g * o a b) • f := by
    intro g hg a b
    obtain ⟨c, hc, hc'⟩ := hγ g a b
    refine ⟨c, hc, ?_⟩
    have hrg : (r g).right = 1 := (hr.mult g).trans hg
    have hγk : Kil (maximalIdeal R) (γ g) := fun a b => by
      obtain ⟨c, -, hc'⟩ := hγ g a b
      rw [hc']; exact hk c
    have hD : ((r0 η Ψ g).mat).map (algebraMap O R) = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g) := by
      unfold GG.mat
      rw [unitaryThreeReflection_left, tor_val, Matrix.diagonal_map (map_zero _)]
      rfl
    have hA := hr.red g
    rw [hD] at hA
    have := core hh hhi hA hY hYm hγk
    rw [conj_mat _ _ _ hrg, conj_mat _ _ _ ((hd g).1.trans hrg), (hd g).2, _root_.mul_inv_rev, Units.val_mul,
      Units.val_mul]
    refine (congrFun (congrFun this a) b).trans ?_
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hc', Y,
      Matrix.of_apply, Algebra.smul_def, map_sub, map_add, map_mul]
    ring
  refine ⟨u * h, ?_, fun g hg a b hab => ?_, fun s hs hη a => ?_⟩
  · have e : ((u * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) - 1 = ((h : Matrix (Fin 3) (Fin 3) R) - 1) - Y * h := by
      show (1 - Y) * (h : Matrix (Fin 3) (Fin 3) R) - 1 = _
      noncomm_ring
    intro a b
    rw [e, Matrix.sub_apply]
    exact Ideal.sub_mem _ (hh a b) (ent_right _ hYm a b)
  · obtain ⟨c, hc, e⟩ := key g hg a b
    rw [e, htri g hg a b hab, zero_add]
    apply h0
    rw [map_sub, map_add (f := _), map_mul, map_mul, map_mul, ho, hc]
    exact h1 g hg a b hab
  · obtain ⟨c, hc, e⟩ := key s hη a a
    rw [e, hine s hs hη a, h0, add_zero]
    rw [map_sub, map_add (f := _), map_mul, map_mul, map_mul, hc, h2 s hs a]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.triangular_condition_at_l_of_first_order_deformation :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f : R), (∀ x ∈ maximalIdeal R, x * f = 0) → f ∈ maximalIdeal R → ∀ (j : ℤ) (v : ι), v = F.vl →
      ∀ (r r₂ : F.D v →* GG (m := 3) (R := R)) (z : F.D v → Gb (k := ResidueField O) j) (γ : F.D v → Matrix (Fin 3) (Fin 3) R), Red (F.ηv v) (F.Ψv v) r → F.LocAt v r →
      z ∈ F.ZL j v → (∀ g a b, ∃ o : O, residue O o = (z g).val a b ∧ γ g a b = o • f) → IsDeform r γ r₂ → F.LocAt v r₂ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF _ R _ _ _ f hf hfm j v hv r r₂ z γ hr hl hz hγ hd
  refine ⟨fun _ => ?_, fun h => absurd (hv ▸ h) hF.vl_notMem, fun h => absurd (Set.mem_insert_iff.2 (Or.inl hv)) h⟩
  have hw : ∀ (X : Gb (k := ResidueField O) j) a b, wt a b ≠ j → X.val a b = 0 := fun X => Subtype.property X
  have h2 : ∀ s ∈ F.Iv v, ∀ a, (z s).val a a = 0 := fun s hs a => by
    by_cases hj : j = 0
    · rw [hz.2.2.2 hv hj s hs]; rfl
    · exact hw _ _ _ (by simpa [wt] using Ne.symm hj)
  by_cases hj : j < 0
  · obtain ⟨μ, hμ⟩ := (mem_coboundaries1 _ _).1 (hz.2.2.1 hv hj)
    refine condT_deform _ _ _ f hf hfm r r₂ (fun g => (z g).val) γ hr (hl.1 hv) hγ hd μ.val ?_ h2
    intro g hg a b _
    have e : (z g).val a b = adRep (r0 F.η F.Ψbar) (F.loc v g) μ.val a b - μ.val a b := by
      rw [hμ g]; rfl
    have hp : ∀ a, residue O (psi (F.Ψv v) a g) = ((F.Ψbar (F.loc v g) ^ wt1 a : (ResidueField O)ˣ) : ResidueField O) :=
      fun a => by
        show _ = ((Units.map (residue O).toMonoidHom (F.Ψ (F.loc v g)) ^ wt1 a : (ResidueField O)ˣ) : ResidueField O)
        rw [← map_zpow]; rfl
    have := ad_entry F.η F.Ψbar (F.loc v g) hg μ.val a b
    simp only [e, hp]
    linear_combination this
  · refine condT_deform _ _ _ f hf hfm r r₂ (fun g => (z g).val) γ hr (hl.1 hv) hγ hd 0 ?_ h2
    intro g _ a b hab
    simp [hw (z g) a b (by omega)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WeightedEntrySubMemIdeal
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]

private theorem conj_app (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) :
    conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl

private theorem conj_comp {D' : Type} [Group D'] (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (f : D' →* D) :
    (conjBy h r).comp f = conjBy h (r.comp f) := rfl

private theorem conj_swap (T h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) :
    conjBy (T * h * T⁻¹)⁻¹ (conjBy T r) = conjBy T (conjBy h⁻¹ r) := by
  ext1 g
  simp only [conj_app, map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
  group

private theorem wt_self (a : Fin 3) : wt a a = 0 := sub_self _

private theorem tor_conj_apply (t : Rˣ) (h : GL (Fin 3) R) (a b : Fin 3) :
    ((tor R t * h * (tor R t)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b =
      ((t ^ wt a b : Rˣ) : R) * (h : Matrix (Fin 3) (Fin 3) R) a b := by
  rw [← map_inv, Units.val_mul, Units.val_mul, tor_val, tor_val, Matrix.mul_diagonal,
    Matrix.diagonal_mul, wt, _root_.zpow_sub, Units.val_mul, _root_.inv_zpow]
  ring

private theorem weighted_entry_sub_mem_ideal (I : Ideal R) (t : Rˣ) (X Y : Matrix (Fin 3) (Fin 3) R)
    (hY : ∀ a b, a ≠ b → Y a b = 0) (h : EntIn I (X - Y)) (a b : Fin 3) :
    ((t ^ wt a b : Rˣ) : R) * X a b - Y a b ∈ I := by
  by_cases hab : a = b
  · subst hab
    rw [wt_self, zpow_zero, Units.val_one, one_mul]
    have := h a a
    rwa [Matrix.sub_apply] at this
  · rw [hY a b hab, sub_zero]
    apply Ideal.mul_mem_left
    have := h a b
    rwa [Matrix.sub_apply, hY a b hab, sub_zero] at this

private theorem inHat_tor [IsLocalRing R] (t : Rˣ) (h : GL (Fin 3) R) (hh : InHat h) :
    InHat (tor R t * h * (tor R t)⁻¹) := by
  intro a b
  rw [Matrix.sub_apply, tor_conj_apply]
  exact weighted_entry_sub_mem_ideal _ t _ 1 (fun a b hab => Matrix.one_apply_ne hab) hh a b

private theorem triIn_tor {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R}
    (t : Rˣ) (H : TriIn η Ψ I r h) : TriIn η Ψ I (conjBy (tor R t) r) (tor R t * h * (tor R t)⁻¹) := by
  obtain ⟨htri, hine⟩ := H
  refine ⟨?_, ?_⟩
  · rw [conj_swap]
    unfold Upper at htri ⊢
    intro g hg a b hab
    rw [(conjBy_tor _ t).1 g a b, htri g hg a b hab, mul_zero]
  · intro s hs hη a
    rw [conj_swap, (conjBy_tor _ t).1 s a a, wt_self, zpow_zero, Units.val_one, one_mul]
    exact hine s hs hη a

private theorem diagIn_tor {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R}
    (t : Rˣ) (H : DiagIn η Ψ I r h) : DiagIn η Ψ I (conjBy (tor R t) r) (tor R t * h * (tor R t)⁻¹) := by
  obtain ⟨H1, hlow⟩ := H
  refine ⟨triIn_tor t H1, ?_⟩
  rw [conj_swap]
  unfold Lower at hlow ⊢
  intro g hg a b hab
  rw [(conjBy_tor _ t).1 g a b, hlow g hg a b hab, mul_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.isPt_tor :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] (g₁ : Γ) (r : Γ →* GG (m := 3) (R := R)) (t : Rˣ), F.IsPt g₁ r → F.IsPt g₁ (conjBy (tor R t) r) := by
  intro O _ _ G Γ ι _ _ _ F R _ _ _ g₁ r t H
  obtain ⟨k1, k2, k3, -⟩ := conjBy_tor r t
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, k3 _ _ H.norm⟩, ?_⟩
  · intro g
    rw [k2, H.mult g]
  · intro g a b
    rw [Matrix.sub_apply, k1]
    refine weighted_entry_sub_mem_ideal _ t _ _ ?_ (H.red g) a b
    intro a b hab
    rw [Matrix.map_apply, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]
  · intro v
    obtain ⟨h1, h2, h3⟩ := H.loc v
    rw [conj_comp]
    refine ⟨fun hv => ?_, fun hv => ?_, fun hv s hs => ?_⟩
    · obtain ⟨h, hh, ht⟩ := h1 hv
      exact ⟨_, inHat_tor t h hh, triIn_tor t ht⟩
    · obtain ⟨h, hh, ht⟩ := h2 hv
      exact ⟨_, inHat_tor t h hh, diagIn_tor t ht⟩
    · rw [conj_app, h3 hv s hs, mul_one, mul_inv_cancel]
  · intro n
    have e : (fun g => (conjBy (tor R t) r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n))) =
        (fun X : Matrix (Fin 3) (Fin 3) (R ⧸ maximalIdeal R ^ n) =>
          Matrix.of fun a b => Ideal.Quotient.mk (maximalIdeal R ^ n) ((t ^ wt a b : Rˣ) : R) * X a b) ∘
        fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) := by
      funext g
      ext a b
      simp only [Function.comp_apply, Matrix.map_apply, Matrix.of_apply, k1, map_mul]
    rw [e]
    exact (H.cont n).comp _
end

