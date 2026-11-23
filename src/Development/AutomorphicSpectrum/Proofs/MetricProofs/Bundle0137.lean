module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameInverseProperties
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem facts (eqv : n ≃ m) (I : Matrix m m ℂ) (hI : I * I = 1) (G : Matrix n n ℂ) (e : ℂ) (he : e * e = 1)
    (A : Matrix n m ℂ) (hA : Aᴴ * (e • G) * A = I) (c : Matrix m n ℂ) (hc : c = I * Aᴴ * (e • G)) :
    c * A = 1 ∧ A * c = 1 ∧ (cᴴ * c).PosDef ∧ (cᴴ * c) * G⁻¹ * (cᴴ * c) = G ∧
    (∀ a ai : Matrix n n ℂ, a * ai = 1 → aᴴ * G * a = G →
      (a * A)ᴴ * (e • G) * (a * A) = I ∧ I * (a * A)ᴴ * (e • G) = c * ai ∧
      (c * (a * A))ᴴ * I * (c * (a * A)) = I ∧
      ((c * (a * A))ᴴ * (c * (a * A)) = 1 ↔ aᴴ * (cᴴ * c) * a = cᴴ * c)) ∧
    ∀ A' : Matrix n m ℂ, A'ᴴ * (e • G) * A' = I → (A' * c)ᴴ * G * (A' * c) = G := by
  have hee : ∀ X : Matrix n n ℂ, e • e • X = X := fun X => by rw [smul_smul, he, one_smul]
  have h1 : c * A = 1 := by
    calc c * A = I * (Aᴴ * (e • G) * A) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, hI]
  have h2 : A * c = 1 := (Matrix.mul_eq_one_comm_of_equiv eqv.symm).1 h1
  have h1h : Aᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h2h : cᴴ * Aᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have hS : cᴴ * I * c = e • G := by
    calc cᴴ * I * c = cᴴ * (Aᴴ * (e • G) * A) * c := by rw [hA]
      _ = (cᴴ * Aᴴ) * (e • G) * (A * c) := by simp only [Matrix.mul_assoc]
      _ = e • G := by rw [h2h, h2, Matrix.one_mul, Matrix.mul_one]
  have hSX : (e • G) * (A * I * Aᴴ) = 1 := by
    calc (e • G) * (A * I * Aᴴ) = cᴴ * I * (c * A) * I * Aᴴ := by
          rw [← hS]; simp only [Matrix.mul_assoc]
      _ = cᴴ * (I * I) * Aᴴ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hI, Matrix.mul_one, h2h]
  have hGX : G * (e • (A * I * Aᴴ)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul]; exact hSX
  have hGinv : G⁻¹ = e • (A * I * Aᴴ) := Matrix.inv_eq_right_inv hGX
  have hc_inj : Function.Injective c.mulVec := by
    intro v w hvw
    have := congrArg A.mulVec hvw
    simpa [Matrix.mulVec_mulVec, h2] using this
  refine ⟨h1, h2, Matrix.PosDef.conjTranspose_mul_self c hc_inj, ?_, ?_, ?_⟩
  · calc (cᴴ * c) * G⁻¹ * (cᴴ * c) = e • (cᴴ * (c * A) * I * (Aᴴ * cᴴ) * c) := by
          rw [hGinv, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = e • (cᴴ * I * c) := by rw [h1, h1h, Matrix.mul_one, Matrix.mul_one]
      _ = G := by rw [hS, hee]
  · intro a ai hai ha
    have hia : ai * a = 1 := mul_eq_one_comm.1 hai
    have hSa : aᴴ * (e • G) * a = e • G := by rw [Matrix.mul_smul, Matrix.smul_mul, ha]
    have haS : aᴴ * (e • G) = (e • G) * ai := by
      calc aᴴ * (e • G) = aᴴ * (e • G) * (a * ai) := by rw [hai, Matrix.mul_one]
        _ = (aᴴ * (e • G) * a) * ai := by simp only [Matrix.mul_assoc]
        _ = (e • G) * ai := by rw [hSa]
    have hform : (a * A)ᴴ * (e • G) * (a * A) = I := by
      calc (a * A)ᴴ * (e • G) * (a * A) = Aᴴ * (aᴴ * (e • G) * a) * A := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = I := by rw [hSa, hA]
    refine ⟨hform, ?_, ?_, ?_⟩
    · calc I * (a * A)ᴴ * (e • G) = I * Aᴴ * (aᴴ * (e • G)) := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = c * ai := by rw [haS, hc]; simp only [Matrix.mul_assoc]
    · calc (c * (a * A))ᴴ * I * (c * (a * A)) = (a * A)ᴴ * (cᴴ * I * c) * (a * A) := by
            rw [conjTranspose_mul c]; simp only [Matrix.mul_assoc]
        _ = I := by rw [hS, hform]
    · have hu : (c * (a * A))ᴴ * (c * (a * A)) = Aᴴ * (aᴴ * (cᴴ * c) * a) * A := by
        rw [conjTranspose_mul c, conjTranspose_mul a]; simp only [Matrix.mul_assoc]
      rw [hu]
      constructor
      · intro h
        calc aᴴ * (cᴴ * c) * a = (cᴴ * Aᴴ) * (aᴴ * (cᴴ * c) * a) * (A * c) := by
              rw [h2h, h2, Matrix.one_mul, Matrix.mul_one]
          _ = cᴴ * (Aᴴ * (aᴴ * (cᴴ * c) * a) * A) * c := by simp only [Matrix.mul_assoc]
          _ = cᴴ * c := by rw [h, Matrix.mul_one]
      · intro h
        calc Aᴴ * (aᴴ * (cᴴ * c) * a) * A = (Aᴴ * cᴴ) * (c * A) := by
              rw [h]; simp only [Matrix.mul_assoc]
          _ = 1 := by rw [h1h, h1, Matrix.one_mul]
  · intro A' hA'
    have hX : e • ((A' * c)ᴴ * G * (A' * c)) = e • G := by
      calc e • ((A' * c)ᴴ * G * (A' * c)) = cᴴ * (A'ᴴ * (e • G) * A') * c := by
            rw [conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
            simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
        _ = e • G := by rw [hA', hS]
    calc (A' * c)ᴴ * G * (A' * c) = e • e • ((A' * c)ᴴ * G * (A' * c)) := (hee _).symm
      _ = G := by rw [hX, hee]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem sgI_mul_self (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, Matrix.fromBlocks_multiply]

theorem cinv_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * C.sgr τ * A = sgI j j' → C.cinv A τ * A = 1 ∧ A * C.cinv A τ = 1 ∧ ((C.cinv A τ)ᴴ * C.cinv A τ).PosDef ∧ ((C.cinv A τ)ᴴ * C.cinv A τ) * (C.gr τ)⁻¹ * ((C.cinv A τ)ᴴ * C.cinv A τ) = C.gr τ ∧ (∀ a ai : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, a * ai = 1 → aᴴ * C.gr τ * a = C.gr τ → (a * A)ᴴ * C.sgr τ * (a * A) = sgI j j' ∧ C.cinv (a * A) τ = C.cinv A τ * ai ∧ IsSgU (C.cinv A τ * (a * A)) ∧ ((C.cinv A τ * (a * A))ᴴ * (C.cinv A τ * (a * A)) = 1 ↔ aᴴ * ((C.cinv A τ)ᴴ * C.cinv A τ) * a = (C.cinv A τ)ᴴ * C.cinv A τ)) ∧ ∀ A' : Matrix (Fin (j + j')) (Sg j j') ℂ, A'ᴴ * C.sgr τ * A' = sgI j j' → (A' * C.cinv A τ)ᴴ * C.gr τ * (A' * C.cinv A τ) = C.gr τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C τ A hA
  have he : ((C.eps τ : ℝ) : ℂ) * ((C.eps τ : ℝ) : ℂ) = 1 := by
    have h := C.eps_sq τ
    rw [← Complex.ofReal_mul, ← pow_two, h, Complex.ofReal_one]
  exact Adapted.facts finSumFinEquiv.symm (sgI j j') (sgI_mul_self j j') (C.gr τ) ((C.eps τ : ℝ) : ℂ) he A hA
    (C.cinv A τ) rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlternatingFormHermitianDescent
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil

theorem exists_bilin_ext {Λ V : Type*} [AddCommGroup Λ] [AddCommGroup V] [Module ℚ V]
    (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ v : V, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v)
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ) := by
  classical
  choose k x hk hx using hs
  have hkq : ∀ u, (k u : ℚ) ≠ 0 := fun u => Nat.cast_ne_zero.mpr (hk u)
  let B0 : V → V → ℚ := fun u v => ((form (x u) (x v) : ℤ) : ℚ) / ((k u : ℚ) * (k v : ℚ))
  have key : ∀ (u v : V) (m n : ℕ) (p q : Λ), m ≠ 0 → n ≠ 0 → e p = m • u → e q = n • v →
      B0 u v = ((form p q : ℤ) : ℚ) / ((m : ℚ) * (n : ℚ)) := by
    intro u v m n p q hm hn hp hq
    have h1 : (k u) • p = m • x u := he (by
      rw [map_nsmul, map_nsmul, hp, hx, smul_comm])
    have h2 : (k v) • q = n • x v := he (by
      rw [map_nsmul, map_nsmul, hq, hx, smul_comm])
    have h3 : form ((k u) • p) ((k v) • q) = form (m • x u) (n • x v) := by rw [h1, h2]
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
    have h4 : (k v : ℚ) * ((k u : ℚ) * ((form p q : ℤ) : ℚ))
        = (n : ℚ) * ((m : ℚ) * ((form (x u) (x v) : ℤ) : ℚ)) := by
      exact_mod_cast h3
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hu := hkq u
    have hv := hkq v
    simp only [B0]
    rw [div_eq_div_iff (mul_ne_zero hu hv) (mul_ne_zero hm' hn')]
    linear_combination (-1 : ℚ) * h4
  have hsm : ∀ (c : ℚ) (u : V), e (c.num • x u) = (c.den * k u) • (c • u) := by
    intro c u
    rw [map_zsmul, hx, ← Nat.cast_smul_eq_nsmul ℚ (k u) u, ← Nat.cast_smul_eq_nsmul ℚ (c.den * k u),
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
    congr 1
    have := Rat.mul_den_eq_num c
    push_cast
    rw [← this]; ring
  let B : LinearMap.BilinForm ℚ V := LinearMap.mk₂ ℚ B0
    (by
      intro u u' v
      have := key (u + u') v (k u * k u') (k v) ((k u') • x u + (k u) • x u') (x v)
        (mul_ne_zero (hk u) (hk u')) (hk v)
        (by rw [map_add (f := _), map_nsmul, map_nsmul, hx, hx, smul_add, smul_smul, smul_smul,
              mul_comm (k u') (k u)])
        (hx v)
      rw [this]
      simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, B0, nsmul_eq_mul]
      have hu := hkq u
      have hu' := hkq u'
      have hv := hkq v
      push_cast
      field_simp)
    (by
      intro c u v
      have := key (c • u) v (c.den * k u) (k v) (c.num • x u) (x v)
        (mul_ne_zero c.den_nz (hk u)) (hk v) (hsm c u) (hx v)
      rw [this]
      simp only [map_zsmul, LinearMap.smul_apply, B0, zsmul_eq_mul, smul_eq_mul]
      have hu := hkq u
      have hv := hkq v
      have hd : (c.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
      have hc : c = (c.num : ℚ) / (c.den : ℚ) := (Rat.num_div_den c).symm
      push_cast
      conv_rhs => rw [hc]
      field_simp)
    (by
      intro u v v'
      have := key u (v + v') (k u) (k v * k v') (x u) ((k v') • x v + (k v) • x v')
        (hk u) (mul_ne_zero (hk v) (hk v')) (hx u)
        (by rw [map_add (f := _), map_nsmul, map_nsmul, hx, hx, smul_add, smul_smul, smul_smul,
              mul_comm (k v') (k v)])
      rw [this]
      simp only [map_add (f := _), map_nsmul, B0, nsmul_eq_mul]
      have hu := hkq u
      have hv := hkq v
      have hv' := hkq v'
      push_cast
      field_simp)
    (by
      intro c u v
      have := key u (c • v) (k u) (c.den * k v) (x u) (c.num • x v)
        (hk u) (mul_ne_zero c.den_nz (hk v)) (hx u) (hsm c v)
      rw [this]
      simp only [map_zsmul, B0, zsmul_eq_mul, smul_eq_mul]
      have hu := hkq u
      have hv := hkq v
      have hd : (c.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
      have hc : c = (c.num : ℚ) / (c.den : ℚ) := (Rat.num_div_den c).symm
      push_cast
      conv_rhs => rw [hc]
      field_simp)
  refine ⟨B, fun p q => ?_⟩
  have := key (e p) (e q) 1 1 p q one_ne_zero one_ne_zero (one_smul _ _).symm (one_smul _ _).symm
  simpa [B, LinearMap.mk₂_apply] using this

theorem exists_rat_bilin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, (∀ x, form x x = 0) → Function.Bijective form → (∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, form (a • x) y = form x (a' • y)) → ∃ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) ∧ (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) ∧ (∀ u v, B u v = - B v u) ∧ ∀ u, (∀ v, B v u = 0) → u = 0 := by
  intro E _ _ _ Λ _ _ _ _ N e he hlin hs form alt hbij adj
  obtain ⟨B, hB⟩ := exists_bilin_ext e he hs form
  have hskew : ∀ x y, form x y = - form y x := by
    intro x y
    have := alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, alt] at this
    linarith
  have halt : ∀ u, B u u = 0 := by
    intro u
    obtain ⟨k, x, hk, hx⟩ := hs u
    have h := hB x x
    rw [alt, hx, ← Nat.cast_smul_eq_nsmul ℚ k u] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    simpa [hk'] using h
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · intro a u v
    have halg : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : 𝓞 E, (a₀ : E) = n • a := ⟨⟨n • a, hint⟩, rfl⟩
    obtain ⟨a₀', ha₀'⟩ : ∃ a₀' : 𝓞 E, (a₀' : E) = IsCMField.complexConj E (a₀ : E) :=
      ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a₀, rfl⟩
    obtain ⟨k, x, hk, hx⟩ := hs u
    obtain ⟨l, y, hl, hy⟩ := hs v
    have h2 : B (e (a₀ • x)) (e y) = B (e x) (e (a₀' • y)) := by
      rw [hB, hB, adj a₀ a₀' ha₀' x y]
    rw [hlin, hlin, hx, hy] at h2
    have h3 : (a₀ : E) • (k • u) = ((n : ℚ) * (k : ℚ)) • (a • u) := by
      ext i
      simp [ha₀, Rat.smul_def]
      ring
    have h4 : (a₀' : E) • (l • v) = ((n : ℚ) * (l : ℚ)) • (IsCMField.complexConj E a • v) := by
      ext i
      simp [ha₀', ha₀, Rat.smul_def]
      ring
    have h5 : k • u = (k : ℚ) • u := (Nat.cast_smul_eq_nsmul ℚ k u).symm
    have h6 : l • v = (l : ℚ) • v := (Nat.cast_smul_eq_nsmul ℚ l v).symm
    rw [h3, h4, h5, h6] at h2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
    have hn' : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hl' : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hn' hk') hl') (by linear_combination h2)
  · intro u v
    exact (LinearMap.IsAlt.neg (B := B) halt v u).symm
  · intro u hu
    obtain ⟨k, y, hk, hy⟩ := hs u
    have hf : ∀ x, form x y = 0 := by
      intro x
      have h : B (e x) (e y) = 0 := by rw [hy, map_nsmul, hu (e x), smul_zero]
      rw [hB] at h
      exact_mod_cast h
    have h0 : form y = 0 := LinearMap.ext fun x => by
      rw [hskew, hf]; simp
    have y0 : y = 0 := hbij.1 (by rw [h0, map_zero])
    rw [y0, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at hy
    exact (smul_eq_zero.mp hy.symm).resolve_left (Nat.cast_ne_zero.mpr hk)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlternatingFormLatticeCompatible
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem relIndex_ne_zero_of_nsmul_mem {W : Type*} [AddCommGroup W] (L G : AddSubgroup W) [AddGroup.FG L] {D : ℕ} (hD : D ≠ 0)
    (hinj : ∀ y : W, D • y = 0 → y = 0) (hG : ∀ y ∈ G, D • y ∈ L) : L.relIndex G ≠ 0 := by
  let f : G →+ L :=
    { toFun := fun y => ⟨D • (y : W), hG y y.2⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp [smul_add] }
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun a ha => ?_
    have : D • (a : W) = 0 := congrArg Subtype.val ha
    exact Subtype.ext (hinj _ this)
  haveI : Module.Finite ℤ L := Module.Finite.iff_addGroup_fg.2 inferInstance
  haveI : Module.Finite ℤ G := Module.Finite.of_injective f.toIntLinearMap hf
  haveI : AddGroup.FG G := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : Finite (G ⧸ L.addSubgroupOf G) := by
    refine AddCommGroup.finite_of_fg_torsion _ ?_
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨D, Nat.pos_of_ne_zero hD, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      simpa using hG y y.2
  exact AddSubgroup.index_ne_zero_of_finite

theorem latEmb_relIndex_dual_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, Function.Bijective form → ∀ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 → (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) → e.range.relIndex (GroundTheory.Heights₂.Heights.FiniteCovolume.dualLattice h e.range) ≠ 0 := by
  intro E _ _ _ H Λ _ _ _ N e he form hform B hB hskew hnd hspan h m hm htr
  classical
  have hd0 : (H.d : E) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hrtsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have hrt0 : (H.rt : E) ≠ 0 := by
    intro h0
    rw [h0] at hrtsq
    exact hd0 (by simpa using hrtsq.symm)
  have hinv : ((m * H.d : ℕ) : E) * ((m : E) * (H.rt : E))⁻¹ = -(H.rt : E) := by
    push_cast
    field_simp
    linear_combination hrtsq
  have key : ∀ y ∈ GroundTheory.Heights₂.Heights.FiniteCovolume.dualLattice h e.range, ∀ x, ∃ n : ℤ, (n : ℚ) = ((m * H.d : ℕ) : ℚ) * B (e x) y := by
    intro y hy x
    have hint : IsIntegral ℤ (h.toSesq y (e x)) := hy (e x) ⟨x, rfl⟩
    have ht := htr 1 (e x) y
    rw [one_smul, one_mul] at ht
    have h2 : ((m * H.d : ℕ) : ℚ) * B (e x) y
        = Algebra.trace ℚ E (-(H.rt : E) * h.toSesq y (e x)) := by
      rw [← ht, ← hinv, mul_assoc, ← smul_eq_mul (a := ((m * H.d : ℕ) : ℚ)), ← map_smul]
      congr 1
      rw [Algebra.smul_def]
      simp
    have hrti : IsIntegral ℤ (-(H.rt : E)) := (H.rt.2).neg
    have h3 : IsIntegral ℤ (Algebra.trace ℚ E (-(H.rt : E) * h.toSesq y (e x))) :=
      Algebra.isIntegral_trace (hrti.mul hint)
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
    exact ⟨n, by rw [h2, ← hn]; simp⟩
  have hDy : ∀ y ∈ GroundTheory.Heights₂.Heights.FiniteCovolume.dualLattice h e.range, (m * H.d) • y ∈ e.range := by
    intro y hy
    choose n hn using key y hy
    have hadd : ∀ a b, n (a + b) = n a + n b := by
      intro a b
      have : ((n (a + b) : ℤ) : ℚ) = ((n a + n b : ℤ) : ℚ) := by
        push_cast
        rw [hn, hn, hn, map_add (f := _), map_add (f := _), LinearMap.add_apply, mul_add]
      exact_mod_cast this
    let φ : Λ →ₗ[ℤ] ℤ := (AddMonoidHom.mk' n hadd).toIntLinearMap
    obtain ⟨z, hz⟩ := hform.2 φ
    have hzx : ∀ x, form z x = n x := fun x => by rw [hz]; rfl
    have h0 : ∀ x, B (e x) ((m * H.d) • y + e z) = 0 := by
      intro x
      have h1 : B (e x) (e z) = -((n x : ℤ) : ℚ) := by
        rw [hskew, hB, hzx]
      rw [map_add (f := _), map_nsmul, h1, hn, nsmul_eq_mul]
      ring
    have h1 : ∀ v, B v ((m * H.d) • y + e z) = 0 := by
      intro v
      obtain ⟨k, x, hk, hx⟩ := hspan v
      have h2 := h0 x
      rw [hx, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 hk)
    have h2 := hnd _ h1
    exact ⟨-z, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left h2).symm⟩
  haveI : AddGroup.FG e.range := by
    haveI : Module.Finite ℤ e.range :=
      Module.Finite.of_surjective e.rangeRestrict.toIntLinearMap e.rangeRestrict_surjective
    exact Module.Finite.iff_addGroup_fg.1 inferInstance
  refine relIndex_ne_zero_of_nsmul_mem _ _ (D := m * H.d) (mul_ne_zero hm H.d_prime.ne_zero) ?_ hDy
  intro y hy
  funext i
  have h1 := congrFun hy i
  simp only [Pi.smul_apply, Pi.zero_apply] at h1
  rw [nsmul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (mul_ne_zero hm H.d_prime.ne_zero))

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanActionOnLatticeVectors
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem tm_archEmbed_mulVec_vec (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ)
    (C : LatEmb F) (γ : C.h.unitaryGroup) (x : Λ) (τ : Ψ) :
    C.tm (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ) τ *ᵥ C.vec x τ =
      fun i => embOf (F.σ τ)
        (((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) i) := by
  set b := Pi.basisFun E (Fin (j + j')) with hb
  set G : GL (Fin (j + j')) E := (unitaryGroupEquivMatrix C.h b γ).1 with hG
  have hGM : (G : Matrix (Fin (j + j')) (Fin (j + j')) E) =
      LinearMap.toMatrix b b (((γ : C.h.unitaryGroup) :
        (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E)) :=
    unitaryGroupEquivMatrix_apply C.h b γ
  have hact : ∀ v : Fin (j + j') → E, (G : Matrix (Fin (j + j')) (Fin (j + j')) E) *ᵥ v =
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) v := by
    intro v
    rw [hGM, hb, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_mulVec]
    rfl
  have htm : C.tm (archEmbed C.h b γ) τ =
      (G : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) := by
    have hw : ∀ w : InfinitePlace E,
        (((archEmbed C.h b γ : archUnitary C.h b) : InfinitePlace E → GL (Fin (j + j')) ℂ) w :
          Matrix (Fin (j + j')) (Fin (j + j')) ℂ) =
        (G : Matrix (Fin (j + j')) (Fin (j + j')) E).map w.embedding := fun w => rfl
    unfold LatEmb.tm tauMat
    split_ifs with h
    · rw [hw, h]
    · rw [hw]
      rcases InfinitePlace.embedding_mk_eq (embOf (F.σ τ)) with h' | h'
      · exact absurd h' h
      · have h'' : (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) := h'
        rw [h'']
        ext a c
        simp [ComplexEmbedding.conjugate_coe_eq]
  rw [htm]
  funext i
  have := RingHom.map_mulVec (embOf (F.σ τ)) (G : Matrix (Fin (j + j')) (Fin (j + j')) E) (C.e x) i
  rw [hact] at this
  rw [this]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end

