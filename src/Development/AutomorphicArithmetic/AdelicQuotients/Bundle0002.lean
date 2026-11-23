module

public import GroundTheory.AutomorphicForms.StableConjCyclic
public import Mathlib
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0019
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0044
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0053

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.GeneralLinearPiCentralizerCommOfCharpolySeparabl
section
private theorem UpperTheory.commute_of_commute_of_charpoly_separable {E : Type} [Field E] [CharZero E] {n : ℕ}
    (γ a b : Matrix (Fin n) (Fin n) E) (h : γ.charpoly.Separable)
    (ha : a * γ = γ * a) (hb : b * γ = γ * b) : a * b = b * a := by
  haveI : Infinite E := Infinite.of_injective _ (Nat.cast_injective (R := E))
  have hsep : (LinearMap.charpoly (Matrix.toLinAlgEquiv' γ : Module.End E (Fin n → E))).Separable := by
    have : (Matrix.toLinAlgEquiv' γ : Module.End E (Fin n → E)) = Matrix.toLin' γ := rfl
    rw [this, Matrix.charpoly_toLin']
    exact h
  have ha' : Commute γ a := ha.symm
  have hb' : Commute γ b := hb.symm
  have hc := GroundTheory.Automorphic.commute_of_commute_of_separable hsep
    (ha'.map (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)))
    (hb'.map (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)))
  apply (Matrix.toLinAlgEquiv' (R := E) (n := Fin n)).injective
  rw [map_mul, map_mul]
  exact hc

theorem UpperTheory.generalLinearPi_centralizer_comm_of_charpoly_separable :
    ∀ (W : Type) (K : W → Type) [∀ w, Field (K w)] [∀ w, CharZero (K w)] (n : ℕ) (γ : GL (Fin n) (∀ w, K w)), (γ : Matrix (Fin n) (Fin n) (∀ w, K w)).charpoly.Separable → ∀ a b : GL (Fin n) (∀ w, K w), a * γ = γ * a → b * γ = γ * b → a * b = b * a := by
  intro W K _ _ n γ hγ a b ha hb
  apply Units.ext
  ext i j w
  have key := UpperTheory.commute_of_commute_of_charpoly_separable
    ((Pi.evalRingHom K w).mapMatrix (γ : Matrix (Fin n) (Fin n) (∀ w, K w)))
    ((Pi.evalRingHom K w).mapMatrix (a : Matrix (Fin n) (Fin n) (∀ w, K w)))
    ((Pi.evalRingHom K w).mapMatrix (b : Matrix (Fin n) (Fin n) (∀ w, K w)))
    (by rw [RingHom.mapMatrix_apply, Matrix.charpoly_map]; exact hγ.map)
    (by rw [← map_mul, ← map_mul, ← Units.val_mul, ha, Units.val_mul])
    (by rw [← map_mul, ← map_mul, ← Units.val_mul, hb, Units.val_mul])
  rw [← map_mul, ← map_mul] at key
  exact congrFun (congrFun key i) j
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.IrreducibleHermitianFormUnique
section
open MeasureTheory

private lemma exists_orthonormal_basis_sesquilinear {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hh : ∀ a b, B b a = star (B a b))
    (hp : ∀ a, a ≠ 0 → 0 < (B a a).re) :
    ∃ e : Fin (Module.finrank ℂ V) → V,
      (∀ i, B (e i) (e i) = 1) ∧ (∀ x y, B x y = ∑ i, B x (e i) * B (e i) y) ∧
      (∀ x y, ‖B x y‖ ^ 2 ≤ (B x x).re * (B y y).re) :=
  _root_.UpperTheory.Reformulated.B.Qh52.exists_orthonormal_basis_sesquilinear B hh hp

theorem UpperTheory.irreducible_hermitian_form_unique :
    ∀ {G V : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (ρ : G →* Module.End ℂ V)
      (_hI : ∀ W : Submodule ℂ V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (_hh : ∀ a b, B b a = star (B a b)) (_hp : ∀ a, a ≠ 0 → 0 < (B a a).re)
      (_hinv : ∀ g a b, B (ρ g a) (ρ g b) = B a b) (_hm : ∀ a b, Measurable fun g => B (ρ g a) b) (a b c d : V),
      ∫ g, B (ρ g a) b * star (B (ρ g c) d) ∂μ = ((μ.real Set.univ / (Module.finrank ℂ V : ℝ) : ℝ) : ℂ) * B a c * star (B b d) := by
  intro G V _ _ _ μ _ _ _ _ _ _ ρ hI B hh hp hinv hm a b c d
  obtain ⟨e, he1, hpar, hcs⟩ := exists_orthonormal_basis_sesquilinear B hh hp
  have hshift : ∀ (h g : G) (x y : V), B (ρ g x) (ρ h y) = B (ρ (h⁻¹ * g) x) y := by
    intro h g x y
    rw [← hinv h (ρ (h⁻¹ * g) x) y, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hbd : ∀ (x y : V) (g : G), ‖B (ρ g x) y‖ ≤ Real.sqrt ((B x x).re * (B y y).re) := by
    intro x y g
    apply Real.le_sqrt_of_sq_le
    have := hcs (ρ g x) y
    rwa [hinv] at this
  have hint : ∀ x y z w : V, Integrable (fun g => B (ρ g x) y * star (B (ρ g z) w)) μ := by
    intro x y z w
    refine Integrable.of_bound (C := Real.sqrt ((B x x).re * (B y y).re) * Real.sqrt ((B z z).re * (B w w).re)) ?_ ?_
    · exact ((hm x y).mul (continuous_star.measurable.comp (hm z w))).aestronglyMeasurable
    · filter_upwards with g
      rw [norm_mul, norm_star]
      exact mul_le_mul (hbd _ _ _) (hbd _ _ _) (norm_nonneg _) (Real.sqrt_nonneg _)
  let S : V → V → ℂ := fun y w => ∫ g, B (ρ g a) y * star (B (ρ g c) w) ∂μ
  have hS1 : ∀ w w' y, S y (w + w') = S y w + S y w' := by
    intro w w' y
    simp only [S, map_add (f := _), star_add, mul_add]
    exact integral_add (hint _ _ _ _) (hint _ _ _ _)
  have hS2 : ∀ (r : ℂ) w y, S y (r • w) = r * S y w := by
    intro r w y
    have : ∀ g, B (ρ g a) y * star (B (ρ g c) (r • w)) = r * (B (ρ g a) y * star (B (ρ g c) w)) := by
      intro g
      simp [map_smulₛₗ]
      ring
    simp only [S, this]
    exact integral_const_mul _ _
  have hS3 : ∀ w y y', S (y + y') w = S y w + S y' w := by
    intro w y y'
    simp only [S, map_add (f := _), add_mul]
    exact integral_add (hint _ _ _ _) (hint _ _ _ _)
  have hS4 : ∀ (r : ℂ) w y, S (r • y) w = star r * S y w := by
    intro r w y
    have : ∀ g, B (ρ g a) (r • y) * star (B (ρ g c) w) = star r * (B (ρ g a) y * star (B (ρ g c) w)) := by
      intro g
      simp [map_smulₛₗ]
      ring
    simp only [S, this]
    exact integral_const_mul _ _
  let B₁ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun w y => S y w)
      (fun w w' y => hS1 w w' y) (fun r w y => hS2 r w y)
      (fun w y y' => hS3 w y y') (fun r w y => hS4 r w y)
  have hB₁ : ∀ w y, B₁ w y = S y w := fun _ _ => rfl
  have hB₁inv : ∀ h w y, B₁ (ρ h w) (ρ h y) = B₁ w y := by
    intro h w y
    simp only [hB₁, S, hshift]
    exact integral_mul_left_eq_self (μ := μ) (fun g => B (ρ g a) y * star (B (ρ g c) w)) h⁻¹
  obtain ⟨lam, hlam⟩ := UpperTheory.invariant_sesquilinearForm_eq_smul_of_irreducible ρ hI B hh hp hinv B₁ hB₁inv
  have hsum : lam * (Module.finrank ℂ V : ℂ) = ((μ.real Set.univ : ℝ) : ℂ) * B a c := by
    have h1 : ∑ i, S (e i) (e i) = lam * (Module.finrank ℂ V : ℂ) := by
      have : ∀ i, S (e i) (e i) = lam := by
        intro i
        rw [← hB₁, hlam, he1, mul_one]
      simp [this, mul_comm]
    have h2 : ∑ i, S (e i) (e i) = ∫ _g : G, B a c ∂μ := by
      simp only [S]
      rw [← integral_finsetSum _ (fun i _ => hint _ _ _ _)]
      congr 1
      funext g
      rw [← hinv g a c, hpar (ρ g a) (ρ g c)]
      exact Finset.sum_congr rfl fun i _ => by rw [hh (ρ g c) (e i)]
    rw [← h1, h2, integral_const]
    simp
  have hn : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hfin : (∫ g, B (ρ g a) b * star (B (ρ g c) d) ∂μ) = S b d := rfl
  rw [hfin, ← hB₁, hlam, hh b d]
  have hlam' : lam = ((μ.real Set.univ : ℝ) : ℂ) * B a c / (Module.finrank ℂ V : ℂ) := by
    rw [eq_div_iff hn, hsum]
  rw [hlam']
  push_cast
  ring
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.MeasurableOfSeparatingFunctionals
section
theorem UpperTheory.measurable_of_separating_functionals :
    ∀ {G V ι : Type} [MeasurableSpace G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ι → V →ₗ[ℂ] ℂ), (∀ a, (∀ y, l y a = 0) → a = 0) → ∀ T : G → V, (∀ y, Measurable fun g => l y (T g)) → ∀ L : V →ₗ[ℂ] ℂ, Measurable fun g => L (T g) :=
  _root_.UpperTheory.Reformulated.B.Qk65.measurable_of_separating_functionals
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.RieszRepresentationSesquilinear
section
theorem UpperTheory.riesz_representation_sesquilinear :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ a b, B b a = star (B a b)) → (∀ a, a ≠ 0 → 0 < (B a a).re) → ∀ L : V →ₗ⋆[ℂ] ℂ, ∃ u, ∀ b, L b = B u b :=
  _root_.UpperTheory.Reformulated.B.Qh51.riesz_representation_sesquilinear
end

