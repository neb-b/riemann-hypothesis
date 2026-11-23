module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTensorWidePullbackLimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

theorem widePullbackCone_congr {X Y W : Scheme.{0}} {n : ℕ} (f : Y ⟶ X) (b : W ⟶ X)
    (π π' : Fin n → (W ⟶ Y)) (h : ∀ i, π i ≫ f = b) (h' : ∀ i, π' i ≫ f = b) (e : π = π')
    (H : Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => f) b π h))) :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => f) b π' h')) := by
  subst e
  exact H

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def l3 : Fin (2 + 1) → (B →+* B ⊗[A] (B ⊗[A] B)) :=
  ![(Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom,
    ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom,
    ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom]

theorem triple_tensor_inclusion_comp_algebraMap : ∀ i, (l3 A B i).comp (algebraMap A B) = algebraMap A (B ⊗[A] (B ⊗[A] B)) := by
  intro i
  fin_cases i <;>
  · simp only [l3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
    rw [AlgHom.toRingHom_eq_coe]
    first
    | exact AlgHom.comp_algebraMap _
    | exact AlgHom.comp_algebraMap (_ : B →ₐ[A] B ⊗[A] (B ⊗[A] B))
    | (ext a; simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def])

theorem tmul_tmul_eq (x y z : B) :
    x ⊗ₜ[A] (y ⊗ₜ[A] z) = l3 A B 0 x * l3 A B 1 y * l3 A B 2 z := by
  simp [l3, Algebra.TensorProduct.tmul_mul_tmul]

theorem triple_tensor_ring_hom_ext {T : Type} [CommRing T] (v w : B ⊗[A] (B ⊗[A] B) →+* T)
    (h : ∀ i, v.comp (l3 A B i) = w.comp (l3 A B i)) : v = w := by
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | tmul x s =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hp, hq]
    | tmul y z =>
      rw [tmul_tmul_eq, map_mul, map_mul, map_mul, map_mul]
      have h0 := RingHom.congr_fun (h 0) x
      have h1 := RingHom.congr_fun (h 1) y
      have h2 := RingHom.congr_fun (h 2) z
      simp only [RingHom.comp_apply] at h0 h1 h2
      rw [h0, h1, h2]

theorem tensor3_univ (T : Type) [CommRing T] (g : Fin (2 + 1) → (B →+* T)) (c : A →+* T)
    (hg : ∀ i, (g i).comp (algebraMap A B) = c) :
    ∃! u : B ⊗[A] (B ⊗[A] B) →+* T, u.comp (algebraMap A _) = c ∧ ∀ i, u.comp (l3 A B i) = g i := by
  letI : Algebra A T := c.toAlgebra
  let G : Fin (2 + 1) → (B →ₐ[A] T) := fun i =>
    { g i with
      commutes' := fun a => by
        have := RingHom.congr_fun (hg i) a
        simpa [RingHom.algebraMap_toAlgebra] using this }
  let inner : B ⊗[A] B →ₐ[A] T := Algebra.TensorProduct.lift (G 1) (G 2) (fun _ _ => Commute.all _ _)
  let U : B ⊗[A] (B ⊗[A] B) →ₐ[A] T := Algebra.TensorProduct.lift (G 0) inner (fun _ _ => Commute.all _ _)
  have hU : ∀ i, U.toRingHom.comp (l3 A B i) = g i := by
    intro i
    fin_cases i <;>
    · ext x
      simp [l3, U, inner, G]
  refine ⟨U.toRingHom, ⟨?_, hU⟩, ?_⟩
  · ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rfl
  · rintro u ⟨-, hu⟩
    exact triple_tensor_ring_hom_ext A B _ _ (fun i => (hu i).trans (hU i).symm)

theorem spec_tensor3_isLimit : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B],
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (2 + 1) => GlobalTheory.CechOne.fB A B)
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B))))) (GlobalTheory.CechOne.y2 A B)
      (GlobalTheory.CechOne.hy2 A B))) := by
  intro A B _ _ _
  have H := GlobalTheory.spec_widePushout_isLimit (2 + 1) A B (B ⊗[A] (B ⊗[A] B)) (algebraMap A B)
    (algebraMap A _) (l3 A B) (triple_tensor_inclusion_comp_algebraMap A B) (fun T _ g c hg => tensor3_univ A B T g c hg)
  refine widePullbackCone_congr _ _ _ _ _ _ ?_ H
  funext i
  fin_cases i <;> rfl

end GlobalTheory.CechOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaResiduallyUnipotentCayleyTransform
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.CayleyAny

open GlobalTheory.UnitLemma.CayleyCase

theorem mem_adjoin_both' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A) (ξ a b : O) (Q : O[X])
    (hQm : Q.Monic) (hQ : aeval g Q = 0) (hQs : IsUnit (Q.eval ξ)) (hab : IsUnit (ξ * a - b))
    (hY : Y * (g - algebraMap O A ξ) = algebraMap O A a * g - algebraMap O A b) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  constructor
  · obtain ⟨w, hw, hgw⟩ := sub_inv_mem g ξ Q hQ hQs
    have e : Y = (algebraMap O A a * g - algebraMap O A b) * w := by
      linear_combination (-Y) * hgw + w * hY
    rw [e]
    exact mul_mem (sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
      (Subalgebra.algebraMap_mem _ _)) hw
  · set n := Q.natDegree
    let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (C ξ * X - C b) ^ i * (X - C a) ^ (n - i)
    have hgY : g * (Y - algebraMap O A a) = algebraMap O A ξ * Y - algebraMap O A b := by
      linear_combination hY
    have hR : aeval Y R = 0 := by
      have : aeval Y R = (Y - algebraMap O A a) ^ n * aeval g Q := by
        conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [R, map_sum, map_mul, map_pow, aeval_C, map_sub, aeval_X]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [← hgY, mul_pow, Algebra.smul_def]
        have : (Y - algebraMap O A a) ^ n = (Y - algebraMap O A a) ^ i * (Y - algebraMap O A a) ^ (n - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hin]
        rw [this]; ring
      rw [this, hQ, mul_zero]
    have hRe : R.eval a = (ξ * a - b) ^ n := by
      simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
      rw [Finset.sum_eq_single n]
      · simp [n, hQm.coeff_natDegree]
      · intro i hi hin
        have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
        rw [zero_pow this.ne', mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
    have hRu : IsUnit (R.eval a) := by
      rw [hRe]; exact hab.pow _
    obtain ⟨v, hv, hYv⟩ := sub_inv_mem Y a R hR hRu
    have e : g = (algebraMap O A ξ * Y - algebraMap O A b) * v := by
      linear_combination (-g) * hYv + v * hgY
    rw [e]
    exact mul_mem (sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
      (Subalgebra.algebraMap_mem _ _)) hv

end GlobalTheory.UnitLemma.CayleyAny

namespace GlobalTheory.UnitLemma.CayleyAny

open GlobalTheory.UnitLemma.CayleyCase

variable {K : UQ}

theorem isUnit_of_conj (K : UQ) (x y : K.O) (h : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hy : IsUnit y) : IsUnit x := by
  obtain ⟨u, rfl⟩ := hy
  obtain ⟨w, hw⟩ := K.c_int (↑u⁻¹ : K.O)
  have h1 : K.c (algebraMap K.O K.E (u : K.O)) = algebraMap K.O K.E x := by rw [← h, K.c_c]
  have h2 : algebraMap K.O K.E (x * w) = 1 := by
    rw [map_mul, ← h1, ← hw, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [← map_one (algebraMap K.O K.E)] at h2
  exact IsUnit.of_mul_eq_one (b := w) (IsFractionRing.injective K.O K.E h2)

theorem mobius_selfadj (B : InvAlg K) (x y ξ : K.O) (Y : B.A) (hu : B.g * B.σ B.g = 1)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hξ : algebraMap K.O K.E ξ * K.c (algebraMap K.O K.E ξ) = 1)
    (w : B.A) (hw : (B.g - algebraMap K.O B.A ξ) * w = 1)
    (hY : Y * (B.g - algebraMap K.O B.A ξ) =
      algebraMap K.O B.A y * B.g - algebraMap K.O B.A x * algebraMap K.O B.A ξ) :
    B.σ Y = Y := by
  have sx : B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y := by
    rw [σ_algebraMap, hxy, ← IsScalarTower.algebraMap_apply]
  have sy : B.σ (algebraMap K.O B.A y) = algebraMap K.O B.A x := by
    rw [σ_algebraMap, ← hxy, K.c_c, ← IsScalarTower.algebraMap_apply]
  have hξA : algebraMap K.O B.A ξ * B.σ (algebraMap K.O B.A ξ) = 1 := by
    rw [σ_algebraMap, IsScalarTower.algebraMap_apply K.O K.E B.A ξ, ← map_mul, hξ, map_one]
  have h1 := congrArg B.σ hY
  rw [map_mul, map_sub, map_sub, map_mul, map_mul, sx, sy] at h1
  set G := B.g
  set Gs := B.σ B.g
  set ξA := algebraMap K.O B.A ξ
  set ξs := B.σ (algebraMap K.O B.A ξ)
  set xA := algebraMap K.O B.A x
  set yA := algebraMap K.O B.A y
  have key : (B.σ Y - Y) * (G - ξA) = 0 := by
    linear_combination (-G * ξA) * h1 - hY - (xA * ξA - B.σ Y * ξA) * hu - (B.σ Y * G - yA * G) * hξA
  calc B.σ Y = B.σ Y * ((G - ξA) * w) := by rw [hw, mul_one]
    _ = Y * ((G - ξA) * w) + (B.σ Y - Y) * (G - ξA) * w := by ring
    _ = Y := by rw [key, hw]; ring

end GlobalTheory.UnitLemma.CayleyAny

namespace GlobalTheory.UnitLemma.CayleyAny

open GlobalTheory.UnitLemma.CayleyCase

theorem identity_of_residually_unipotent_any : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K),
    B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ,
    algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 →
    (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧
      Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) →
    InvAlg.Identity B₁ B₂ := by
  intro hL K B₁ B₂ hu₁ hu₂ hsep s hs ⟨Q, hQ, hQr⟩
  have hinj := IsFractionRing.injective K.O K.E

  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  have hyx : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
  have hxu : IsUnit x := by
    by_contra hx
    have hy : ¬ IsUnit y := fun hy => hx (isUnit_of_conj K x y hxy hy)
    exact hm (Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx) ((IsLocalRing.mem_maximalIdeal _).2 hy))
  have hyu : IsUnit y := isUnit_of_conj K y x hyx hxu
  have hxyu : IsUnit (x - y) := by
    by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  set yi : K.O := ↑hyu.unit⁻¹ with hyi
  have hyyi : y * yi = 1 := hyu.mul_val_inv
  set ξ : K.O := (s : K.O) * x * yi with hξd
  have hξu : IsUnit ξ := (s.isUnit.mul hxu).mul (hyu.unit⁻¹).isUnit
  have hξn : algebraMap K.O K.E ξ * K.c (algebraMap K.O K.E ξ) = 1 := by
    obtain ⟨w, hw⟩ := K.c_int yi
    have e1 : algebraMap K.O K.E x * algebraMap K.O K.E w = 1 := by
      have := congrArg K.c (congrArg (algebraMap K.O K.E) hyyi)
      rw [map_mul, map_mul, hyx, hw, map_one, map_one] at this
      exact this
    have e2 : algebraMap K.O K.E y * algebraMap K.O K.E yi = 1 := by
      rw [← map_mul, hyyi, map_one]
    rw [hξd, map_mul, map_mul, map_mul, map_mul, hxy, hw]
    linear_combination (algebraMap K.O K.E x * algebraMap K.O K.E w * algebraMap K.O K.E y *
      algebraMap K.O K.E yi) * hs + (algebraMap K.O K.E y * algebraMap K.O K.E yi) * e1 + e2
  have hQξ : IsUnit (Q.eval ξ) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval₂_hom, ← eval_map, hQr]
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    apply pow_ne_zero
    intro h0
    apply hm
    set r := IsLocalRing.residue K.O
    have hs0 : r (s : K.O) ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 s.isUnit
    have h3 : r (y * yi) = 1 := by rw [hyyi, map_one]
    rw [map_mul] at h3
    have h4 : r (s : K.O) * (r x - r y) = 0 := by
      rw [hξd, map_mul, map_mul] at h0
      linear_combination r y * h0 - (r (s : K.O) * r x) * h3
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    exact (mul_eq_zero.1 h4).resolve_left hs0
  have hab : IsUnit (ξ * y - x * ξ) := by
    rw [show ξ * y - x * ξ = -(ξ * (x - y)) by ring]
    exact (hξu.mul hxyu).neg
  obtain ⟨Q₁, Q₂, hQQ, e₁, e₂, a₁, a₂, hmQ⟩ := lift_factor B₁ B₂ hsep Q hQ
  have hQs₁ : IsUnit (Q₁.eval ξ) := by
    rw [hQQ, eval_mul] at hQξ; exact isUnit_of_mul_isUnit_left hQξ
  have hQs₂ : IsUnit (Q₂.eval ξ) := by
    rw [hQQ, eval_mul] at hQξ; exact isUnit_of_mul_isUnit_right hQξ
  have hm₁ : Q₁.Monic := monic_of_injective hinj (e₁ ▸ LinearMap.charpoly_monic _)
  have hm₂ : Q₂.Monic := monic_of_injective hinj (e₂ ▸ LinearMap.charpoly_monic _)
  obtain ⟨w₁, -, hw₁⟩ := sub_inv_mem B₁.g ξ Q₁ a₁ hQs₁
  obtain ⟨w₂, -, hw₂⟩ := sub_inv_mem B₂.g ξ Q₂ a₂ hQs₂
  set Y₁ := (algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ) * w₁ with hY₁d
  set Y₂ := (algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ) * w₂ with hY₂d
  have hY₁ : Y₁ * (B₁.g - algebraMap K.O B₁.A ξ) =
      algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ) * hw₁
  have hY₂ : Y₂ * (B₂.g - algebraMap K.O B₂.A ξ) =
      algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ) * hw₂
  have hY₁' : Y₁ * (B₁.g - algebraMap K.O B₁.A ξ) = algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A (x * ξ) := by
    rw [map_mul (algebraMap K.O B₁.A) x ξ]; exact hY₁
  have hY₂' : Y₂ * (B₂.g - algebraMap K.O B₂.A ξ) = algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A (x * ξ) := by
    rw [map_mul (algebraMap K.O B₂.A) x ξ]; exact hY₂
  have adj₁ := mem_adjoin_both' B₁.g Y₁ ξ y (x * ξ) Q₁ hm₁ a₁ hQs₁ hab hY₁'
  have adj₂ := mem_adjoin_both' B₂.g Y₂ ξ y (x * ξ) Q₂ hm₂ a₂ hQs₂ hab hY₂'
  have aQ : aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) Q = 0 := by
    have f1 := aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    have f2 := aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    refine Prod.ext ?_ ?_
    · change AlgHom.fst K.O B₁.A B₂.A _ = 0
      rw [← f1]; change aeval B₁.g Q = 0
      rw [hQQ, map_mul, a₁, zero_mul]
    · change AlgHom.snd K.O B₁.A B₂.A _ = 0
      rw [← f2]; change aeval B₂.g Q = 0
      rw [hQQ, map_mul, a₂, mul_zero]
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * ((B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) ξ) =
      algebraMap K.O (B₁.A × B₂.A) y * (B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) (x * ξ) :=
    Prod.ext hY₁' hY₂'
  have adjP := mem_adjoin_both' ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) ξ y (x * ξ) Q hmQ aQ hQξ hab hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := mobius_selfadj B₁ x y ξ Y₁ hu₁ hxy hξn w₁ hw₁ hY₁
  have sa₂ := mobius_selfadj B₂ x y ξ Y₂ hu₂ hxy hξn w₂ hw₂ hY₂
  have hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable := by
    have := Orbit.prod_P B₁ B₂
    rw [← this] at hsep; exact hsep
  have hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable := by
    rw [← Orbit.prod_P]
    have := separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂)
      (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP
    exact this
  have hId := hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC

  have hr : resultant B₁.P B₂.P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero
  have hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero
  obtain ⟨M₁, l₁, s₁⟩ := exists_stable_lat (E := K.E) B₁.g ⟨Q₁, hm₁, a₁⟩
  obtain ⟨M₂, l₂, s₂⟩ := exists_stable_lat (E := K.E) B₂.g ⟨Q₂, hm₂, a₂⟩
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P) :=
    val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂
  unfold InvAlg.Identity at hId ⊢
  rw [kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂] at hId
  change (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _
  rw [hv]
  exact hId

end GlobalTheory.UnitLemma.CayleyAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactPreadditiveYonedaOfInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem wExact_preadditiveYoneda_of_injective (R : Type) [CommRing R] (T : Type 1) [Category.{0} T]
    (Ψ : T ⥤ PShᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (J : Shv R) (hJ : Injective J) (hq : QuasiIso ((chains R).map (lev Ψ a))) :
    WExact (Ψ ⋙ (free R).op ⋙ preadditiveYoneda.obj J) a := by
  let K : SimplicialObject (Shv R) := ((SimplicialObject.whiskering _ _).obj (free R)).obj ((X ⋙ Ψ).leftOp)
  let B : Shv R := (free R).obj (Ψ.obj U).unop
  let f : K ⟶ (SimplicialObject.const (Shv R)).obj B :=
    ((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a) ≫ (Functor.constComp _ _ _).hom
  haveI h1 : QuasiIso ((chainsN R).map (lev Ψ a)) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).1 hq
  have hq' : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f) := by
    have e : (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f =
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a)) ≫
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp _ _ _).hom :=
      Functor.map_comp _ _ _
    rw [e]
    haveI : IsIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      Functor.map_isIso _ _
    haveI h2 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a))) := h1
    haveI h3 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      quasiIso_of_isIso _
    exact quasiIso_comp (hφ := h2) (hφ' := h3) _ _
  obtain ⟨hepi, ⟨w, hex⟩, hn⟩ := (GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact _ K B f).1 hq'
  have hepi' : Epi ((free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop) := by
    have e : f.app (op (SimplexCategory.mk 0)) = (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop :=
      Category.comp_id _
    rw [← e]; exact hepi
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    change (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ x =
      (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ y at hxy
    exact (cancel_epi _).1 hxy
  · intro y hy
    change (free R).map (Ψ.map (X.δ (n := 0) 0)).unop ≫ y = (free R).map (Ψ.map (X.δ (n := 0) 1)).unop ≫ y at hy
    let y' : K.obj (op (SimplexCategory.mk 0)) ⟶ J := y
    have hy' : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ y' = 0 := by
      refine (Preadditive.sub_comp _ _ _).trans (sub_eq_zero.2 ?_)
      exact hy
    refine ⟨hex.descToInjective (J := J) y' hy', ?_⟩
    exact hex.comp_descToInjective (J := J) y' hy'
  · intro n
    exact GlobalTheory.alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ K J n (hn n)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepBijectionSchwartz
section
open Matrix

namespace GlobalTheory.SchurHeisReindex

variable {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]

noncomputable def eL (k : Type) [Field k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₗ[k] Matrix (Fin n) β k :=
  Matrix.reindexLinearEquiv k k (Equiv.refl (Fin n)) (Fintype.equivFin β).symm

theorem eL_apply (C : Matrix (Fin n) (Fin (Fintype.card β)) k) (i : Fin n) (b : β) :
    eL k n β C i b = C i (Fintype.equivFin β b) := by
  simp [eL, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]

theorem eL_symm_apply (D : Matrix (Fin n) β k) (i : Fin n) (j : Fin (Fintype.card β)) :
    (eL k n β).symm D i j = D i ((Fintype.equivFin β).symm j) := by
  simp [eL, reindexLinearEquiv_symm, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]

theorem continuous_eL : Continuous (eL k n β) := by
  refine continuous_pi fun i => continuous_pi fun b => ?_
  simp only [eL_apply]
  exact (continuous_apply _).comp (continuous_apply i)

theorem continuous_eL_symm : Continuous (eL k n β).symm := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [eL_symm_apply]
  exact (continuous_apply _).comp (continuous_apply i)

noncomputable def eH (k : Type) [Field k] [TopologicalSpace k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₜ Matrix (Fin n) β k where
  toEquiv := (eL k n β).toEquiv
  continuous_toFun := continuous_eL
  continuous_invFun := continuous_eL_symm

theorem comp_mem_SB' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) : (f ∘ e) ∈ GlobalTheory.WeilM.SB Y :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

end GlobalTheory.SchurHeisReindex


open GlobalTheory.SchurHeisReindex in
theorem GlobalTheory.schur_heisenberg_linearModel_fintype : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {β : Type} [Fintype β] [DecidableEq β] {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) β k → ℂ)) (ι₂ : Xt → Matrix (Fin n) β k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) β k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) β k → Xt → Xt) (Mu : (Matrix (Fin n) β k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n β _ _ Xt _ _ V ψ0 hψc hψ1 ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  set e := eL k n β with he
  let ι₁' : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ) := LinearMap.funLeft ℂ ℂ e ∘ₗ ι₁
  have hι₁' : ∀ x, ι₁' x = ι₁ x ∘ e := fun x => rfl
  let ι₂' : Xt → Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ := fun x => ι₂ x ∘ e
  have hsurj : Function.Surjective e := e.surjective
  have hbij' : Set.BijOn ι₁' (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin (Fintype.card β)) k) : Set _) := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun f hf => ?_⟩
    · rw [hι₁']
      exact comp_mem_SB' (eH k n β) (hbij.1 hx)
    · apply hbij.2.1 hx hy
      rw [hι₁', hι₁'] at hxy
      funext Z
      obtain ⟨Y, rfl⟩ := hsurj Z
      exact congrFun hxy Y
    · have hf' : f ∘ (eH k n β).symm ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) β k) := comp_mem_SB' (eH k n β).symm hf
      obtain ⟨x, hx, hxf⟩ := hbij.2.2 hf'
      refine ⟨x, hx, ?_⟩
      rw [hι₁', hxf]
      funext Y
      show f ((eH k n β).symm (e Y)) = f Y
      exact congrArg f ((eL k n β).symm_apply_apply Y)
  have hlin' : ∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂' (c • x + y) = c • ι₂' x + ι₂' y := by
    intro x hx y hy c
    funext Y
    simp [ι₂', hlin x hx y hy c]
  have hadd : ∀ Y C, e (Y + C) = e Y + e C := fun Y C => map_add e Y C
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.LinSchur.eq_smul_of_commute V ψ0 hψc hψ1 ι₁' ι₂' hbij' hlin'
    (fun C => Tr (e C)) (fun l => Mu (l ∘ₗ e.symm.toLinearMap))
    (fun C x hx => by
      obtain ⟨h1, h2, h3⟩ := hTr (e C) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2, hadd]
      · funext Y; simp [ι₂', h3, hadd])
    (fun l x hx => by
      obtain ⟨h1, h2, h3⟩ := hMu (l ∘ₗ e.symm.toLinearMap) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2]
      · funext Y; simp [ι₂', h3])
  refine ⟨c, fun x hx => ?_⟩
  funext Z
  obtain ⟨Y, rfl⟩ := hsurj Z
  have := congrFun (hc x hx) Y
  simpa [ι₂', hι₁'] using this
end

