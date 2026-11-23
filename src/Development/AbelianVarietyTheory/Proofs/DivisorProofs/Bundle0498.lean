module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesRingEquivConj
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma powerSeries_map_mk' (g : ℂ ≃+* ℂ) (c : ℕ → ℂ) :
    PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk c) = PowerSeries.mk fun n ↦ g (c n) := by
  ext n
  simp

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hser_conj : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F)) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) = PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a (m * x) (fun j ↦ κ (π.symm j)) (fun n ↦ g (c n))) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N g m π κ c n hk hN ha hga hlev hexp hemb
  have htr : ∀ μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ,
      PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ)) =
        PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a (m * x) fun j ↦ μ (π.symm j)) := by
    intro μ
    rw [powerSeries_map_mk']
    congr 1
    funext j
    exact _root_.GlobalTheory.HilbFam.ecoef_ringEquiv F k 𝔞 𝔟 a₀ a x N g m π μ j hN ha hga hlev
      hexp hemb
  unfold _root_.GlobalTheory.HilbFam.hser
  subst hk
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_ratCast, map_sum]
  congr 1
  refine Finset.sum_nbij' (fun μ j ↦ μ (π.symm j)) (fun μ i ↦ μ (π i)) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    exact fun j ↦ hμ (π.symm j)
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    intro i
    simpa using hμ (π i)
  · intro μ _
    funext i
    simp
  · intro μ _
    funext j
    simp
  · intro μ _
    have hcoeff : ∀ φ : PowerSeries ℂ,
        g (PowerSeries.coeff n φ) = PowerSeries.coeff n (PowerSeries.map (g : ℂ →+* ℂ) φ) :=
      fun φ ↦ by
        rw [PowerSeries.coeff_map]
        rfl
    rw [map_mul, map_intCast, hcoeff, map_mul, map_pow, powerSeries_map_mk', htr]
    rw [Equiv.prod_comp π.symm fun i ↦
        _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) * (-1) ^ μ i,
      Equiv.sum_comp π.symm fun i ↦ κ i - μ i]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueLinearChange
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem exists_unit_transfQuot_out_eq_smul {F : Type} [Field F] [NumberField F]
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (q : Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F))) :
    ∃ ε : (𝓞 F)ˣ, (_root_.GlobalTheory.HilbFam.transfQuot T q).out = ε • T q.out := by
  have h : _root_.GlobalTheory.HilbFam.transfQuot T q = Quotient.mk _ (T q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [h]
  obtain ⟨ε, hε⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
    (Quotient.mk_out (s := MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) (T q.out)))
  exact ⟨ε, hε.symm⟩

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem gTerm_eq_of_linear_change {F : Type} [Field F] [NumberField F]
    {k : ℕ} (σ : ℂ) {b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F))
    (hc : ∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i =
      lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) (x : Fin 2 → F) :
    _root_.GlobalTheory.HilbFam.gTerm k σ b a x =
      ((∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ)) *
        _root_.GlobalTheory.HilbFam.gTerm k σ b' a' (T x) := by
  unfold _root_.GlobalTheory.HilbFam.gTerm
  simp only [hc, Finset.prod_mul_distrib, norm_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _), mul_inv, mul_pow]
  ring

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem isGVal_of_linear_change {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] {k : ℕ} (hk : Even k) {L L' : _root_.GlobalTheory.HilbFam.Lat F}
    (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) {b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (hL : ∀ x, x ∈ L ↔ T x ∈ L') (hlam : ∀ i, lam i ≠ 0)
    (hc : ∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i =
      lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) {G : ℂ}
    (hG : _root_.GlobalTheory.HilbFam.IsGVal k L' b' a' G) :
    _root_.GlobalTheory.HilbFam.IsGVal k L b a ((∏ i, lam i)⁻¹ ^ k * G) := by
  have hmem : ∀ q, q ∈ _root_.GlobalTheory.HilbFam.cls L ↔
      _root_.GlobalTheory.HilbFam.transfQuot T q ∈ _root_.GlobalTheory.HilbFam.cls L' := by
    intro q
    obtain ⟨ε, hε⟩ := exists_unit_transfQuot_out_eq_smul T q
    simp only [_root_.GlobalTheory.HilbFam.cls, Set.mem_setOf_eq, hε]
    have hz : ε • T q.out ≠ 0 ↔ q.out ≠ 0 := by
      constructor
      · intro h h0
        exact h (by rw [h0, map_zero, smul_zero])
      · intro h h0
        apply h
        apply T.injective
        rw [map_zero]
        simpa using congrArg (fun y => ε⁻¹ • y) h0
    rw [Submodule.smul_mem_iff', hz, ← hL]
  let e : _root_.GlobalTheory.HilbFam.cls L ≃ _root_.GlobalTheory.HilbFam.cls L' :=
    (_root_.GlobalTheory.HilbFam.transfQuot T).subtypeEquiv hmem
  have hterm : ∀ (σ : ℂ) (q : _root_.GlobalTheory.HilbFam.cls L),
      _root_.GlobalTheory.HilbFam.gTerm k σ b' a' (e q).1.out =
        _root_.GlobalTheory.HilbFam.gTerm k σ b' a' (T q.1.out) := by
    intro σ q
    obtain ⟨ε, hε⟩ := exists_unit_transfQuot_out_eq_smul T q
    simp only [e, Equiv.subtypeEquiv_apply]
    rw [hε, _root_.GlobalTheory.HilbFam.gTerm_unit_smul F k σ b' a' ε _ hk]
  have hsum : ∀ (σ G' : ℂ),
      HasSum (fun q : _root_.GlobalTheory.HilbFam.cls L' ↦
        _root_.GlobalTheory.HilbFam.gTerm k σ b' a' q.1.out) G' →
      HasSum (fun q : _root_.GlobalTheory.HilbFam.cls L ↦
        _root_.GlobalTheory.HilbFam.gTerm k σ b a q.1.out)
        ((∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ) * G') := by
    intro σ G' h
    have h' := (e.hasSum_iff.mpr h).mul_left ((∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ))
    have hfun : (fun q : _root_.GlobalTheory.HilbFam.cls L ↦
        _root_.GlobalTheory.HilbFam.gTerm k σ b a q.1.out) = fun q ↦
        (∏ i, lam i)⁻¹ ^ k * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ) *
          ((fun q : _root_.GlobalTheory.HilbFam.cls L' ↦
            _root_.GlobalTheory.HilbFam.gTerm k σ b' a' q.1.out) ∘ e) q := by
      funext q
      simp only [Function.comp_apply, hterm]
      exact gTerm_eq_of_linear_change σ T hc _
    rw [hfun]
    exact h'
  obtain ⟨h₁, h₂⟩ := hG
  refine ⟨fun hk2 => ?_, fun hk2 => ?_⟩
  · simpa using hsum 0 G (h₁ hk2)
  · subst hk2
    obtain ⟨H, hH, hs, rfl⟩ := h₂ rfl
    have hne : ((‖∏ i, lam i‖ : ℝ) : ℂ) ≠ 0 := by
      simp [Finset.prod_ne_zero_iff, hlam]
    refine ⟨fun σ => (∏ i, lam i)⁻¹ ^ 2 * ((‖∏ i, lam i‖ : ℝ) : ℂ) ^ (-2 * σ) * H σ, ?_,
      fun σ hσ => hsum σ _ (hs σ hσ), by simp⟩
    exact (((differentiable_const _).mul
      ((differentiable_id.const_mul (-2 : ℂ)).const_cpow (Or.inl hne))).differentiableOn).mul hH


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.gval_linear_change : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L L' : _root_.GlobalTheory.HilbFam.Lat F) (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), Even k → (∀ x, x ∈ L ↔ T x ∈ L') → (∀ i, lam i ≠ 0) → (∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i = lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) → _root_.GlobalTheory.HilbFam.gval k L b a = (∏ i, lam i)⁻¹ ^ k * _root_.GlobalTheory.HilbFam.gval k L' b' a' := by
  intro F _ _ _ k L L' T b a b' a' lam hk hL hlam hc
  by_cases h : ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L' b' a' G
  · obtain ⟨G, hG⟩ := h
    rw [_root_.GlobalTheory.HilbFam.gval_eq_of_isGVal F k L' b' a' G hG,
      _root_.GlobalTheory.HilbFam.gval_eq_of_isGVal F k L b a _
        (isGVal_of_linear_change hk T hL hlam hc hG)]
  · have h' : ¬ ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L b a G := by
      rintro ⟨G, hG⟩
      refine h ⟨_, isGVal_of_linear_change hk T.symm
        (lam := fun i => (lam i)⁻¹) ?_ (fun i => inv_ne_zero (hlam i)) ?_ hG⟩
      · intro x
        rw [hL (T.symm x), T.apply_symm_apply]
      · intro x i
        rw [hc (T.symm x) i, T.apply_symm_apply, inv_mul_cancel_left₀ (hlam i)]
    rw [_root_.GlobalTheory.HilbFam.gval, dite_eq_right h', _root_.GlobalTheory.HilbFam.gval, dite_eq_right h,
      mul_zero]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMul
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistMul

variable {F : Type} [Field F] [NumberField F]

theorem std_vecMul_int (A : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (A.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h : ∀ i, y i * ((A i j : ℤ) : F) ∈ (1 : Submodule (𝓞 F) F) := fun i ↦ by
    have := Submodule.smul_of_tower_mem (1 : Submodule (𝓞 F) F) (A i j) (hy i (Set.mem_univ i))
    rwa [zsmul_eq_mul, mul_comm] at this
  have e : Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j = y 0 * ((A 0 j : ℤ) : F) + y 1 * ((A 1 j : ℤ) : F) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  change Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j ∈ (1 : Submodule (𝓞 F) F)
  rw [e]
  exact Submodule.add_mem _ (h 0) (h 1)

theorem std_natCast_smul (N : ℕ) {y : Fin 2 → F} (hy : y ∈ stdLat F) : (N : F) • y ∈ stdLat F := by
  rw [Nat.cast_smul_eq_nsmul]
  exact Submodule.smul_of_tower_mem _ N hy

theorem twist_twist : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (α β : Matrix (Fin 2) (Fin 2) (ZMod N)), L ≤ stdLat F → twist N (twist N L α) β = twist N L (α * β) := by
  intro F _ _ _ N L α β hL
  have lift : ∀ γ : Matrix (Fin 2) (Fin 2) (ZMod N), ∃ C : Matrix (Fin 2) (Fin 2) ℤ, C.map (Int.cast : ℤ → ZMod N) = γ :=
    fun γ ↦ ⟨γ.map (ZMod.cast : ZMod N → ℤ), by ext i j; simp⟩
  obtain ⟨A, rfl⟩ := lift α
  obtain ⟨B, rfl⟩ := lift β
  have hm : A.map (Int.cast : ℤ → ZMod N) * B.map (Int.cast : ℤ → ZMod N) = (A * B).map (Int.cast : ℤ → ZMod N) :=
    (Matrix.map_mul (f := Int.castRingHom (ZMod N))).symm
  have hF : (A * B).map (Int.cast : ℤ → F) = A.map (Int.cast : ℤ → F) * B.map (Int.cast : ℤ → F) :=
    Matrix.map_mul (f := Int.castRingHom F)
  have hT : twist N L (A.map (Int.cast : ℤ → ZMod N)) ≤ stdLat F := by
    intro v hv
    obtain ⟨y, hy, w, hw, rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A v hL).1 hv
    exact Submodule.add_mem _ (std_vecMul_int A (hL hy)) (std_natCast_smul N hw)
  rw [hm]
  ext v
  rw [GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ B v hT, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L (A * B) v hL, hF]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    obtain ⟨y, hy, w', hw', rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A u hL).1 hu
    refine ⟨y, hy, Matrix.vecMul w' (B.map (Int.cast : ℤ → F)) + w,
      Submodule.add_mem _ (std_vecMul_int B hw') hw, ?_⟩
    rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.smul_vecMul, smul_add, add_assoc]
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨Matrix.vecMul y (A.map (Int.cast : ℤ → F)),
      (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).2 ⟨y, hy, 0, Submodule.zero_mem _, by simp⟩, w, hw, ?_⟩
    rw [Matrix.vecMul_vecMul]

end GlobalTheory.HilbFam.TwistMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMulSL2Z
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistSL

theorem vecMul_mem_stdLat {F : Type} [Field F] [NumberField F] (B : Matrix (Fin 2) (Fin 2) ℤ) {w : Fin 2 → F}
    (hw : w ∈ stdLat F) : Matrix.vecMul w (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h0 := hw 0 (Set.mem_univ _)
  have h1 := hw 1 (Set.mem_univ _)
  have e : Matrix.vecMul w (B.map (Int.cast : ℤ → F)) j = B 0 j • w 0 + B 1 j • w 1 := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  change Matrix.vecMul w (B.map (Int.cast : ℤ → F)) j ∈ (1 : Submodule (𝓞 F) F)
  rw [e]
  exact Submodule.add_mem _ (zsmul_mem h0 _) (zsmul_mem h1 _)

theorem map_cast_mul (R : Type) [CommRing R] (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B).map (Int.cast : ℤ → R) = A.map (Int.cast : ℤ → R) * B.map (Int.cast : ℤ → R) :=
  Matrix.map_mul (f := Int.castRingHom R)

theorem twist_mul_sl : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) (γ : SL(2, ℤ)), L ≤ stdLat F → twist N L (α * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) = mulMat (twist N L α) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro F _ _ _ N L α γ hL
  obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, α = A.map (Int.cast : ℤ → ZMod N) :=
    ⟨α.map (ZMod.cast : ZMod N → ℤ), by ext i j; simp⟩
  rw [← map_cast_mul]
  have hinv : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F) *
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F) = 1 := by
    rw [← map_cast_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.map_one _ Int.cast_zero Int.cast_one
  ext v
  rw [GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L _ v hL]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨Matrix.vecMul y (A.map (Int.cast : ℤ → F)) +
      (N : F) • Matrix.vecMul w (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)), ?_, ?_⟩
    · exact (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).2 ⟨y, hy, _, vecMul_mem_stdLat _ hw, rfl⟩
    · rw [LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hinv,
        Matrix.vecMul_one, map_cast_mul]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).1 hu
    refine ⟨y, hy, _, vecMul_mem_stdLat (γ : Matrix (Fin 2) (Fin 2) ℤ) hw, ?_⟩
    rw [LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, map_cast_mul]

end GlobalTheory.HilbFam.TwistSL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSplitLatticeTwistDiagonalCoprime
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem twist_split_diagonal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by
  intro F _ _ _ N 𝔞 𝔟 x a hcop hlev
  have hstd : ∀ w : Fin 2 → F, w ∈ stdLat F ↔ ∀ i, w i ∈ (1 : Submodule (𝓞 F) F) := by
    intro w; simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  have hsp : ∀ (z : F) (w : Fin 2 → F), w ∈ split 𝔞 𝔟 z ↔
      w 0 ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F) ∧
      w 1 - w 0 * z ∈ (latM 𝔞 : Submodule (𝓞 F) F) := fun _ _ ↦ Iff.rfl
  have hA : (Matrix.diagonal ![1, (a : ZMod N)]) =
      (Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → ZMod N) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hv0 : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → F)) = ![y 0, a * y 1] := by
    intro y
    ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  have hN : ∀ w ∈ stdLat F, (N : F) • w ∈ split 𝔞 𝔟 x := by
    intro w hw
    have h := hlev.1 w hw
    rw [Nat.cast_smul_eq_nsmul] at h ⊢
    exact h
  have hz : ∀ (n : ℤ) (S : Submodule (𝓞 F) F) (m : F), m ∈ S → (n : F) * m ∈ S := by
    intro n S m hm
    rw [← zsmul_eq_mul]
    exact zsmul_mem hm n
  ext v
  rw [hA, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ _ v hlev.2]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    rw [hv0]
    have hw' := (hstd w).1 hw
    have h0 := (hsp _ _).1 (hN ![w 0, 0] ((hstd _).2 (by
      intro i; fin_cases i
      · exact hw' 0
      · exact Submodule.zero_mem _)))
    have h1 := (hsp _ _).1 (hN ![0, w 1] ((hstd _).2 (by
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hw' 1)))
    have hy' := (hsp _ _).1 hy
    rw [hsp]
    refine ⟨?_, ?_⟩
    · have := Submodule.add_mem _ hy'.1 h0.1
      convert this using 1
      simp
    · have := Submodule.add_mem _ (Submodule.add_mem _ (hz a _ _ hy'.2) h1.2) (hz a _ _ h0.2)
      convert this using 1
      simp
      ring
  · intro hv
    have hv' := (hsp _ _).1 hv
    obtain ⟨u, t, hut⟩ := hcop
    have hut' : (u : F) * a + t * N = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → F) hut
    have hm : ![0, v 1 - v 0 * (a * x)] ∈ split 𝔞 𝔟 x := by
      rw [hsp]
      refine ⟨Submodule.zero_mem _, ?_⟩
      convert hv'.2 using 1
      simp
    have hm' := (hstd _).1 (hlev.2 hm) 1
    refine ⟨![v 0, v 0 * x + u * (v 1 - v 0 * (a * x))], ?_, ![0, t * (v 1 - v 0 * (a * x))], ?_, ?_⟩
    · rw [hsp]
      refine ⟨hv'.1, ?_⟩
      convert hz u _ _ hv'.2 using 1
      simp
    · rw [hstd]
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hz t _ _ hm'
    · rw [hv0]
      ext j; fin_cases j
      · simp
      · simp
        linear_combination (-(v 1 - v 0 * (a * x))) * hut'

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelf
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem trace_pi_eq_sum (n : ℕ) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    LinearMap.trace ℂ (Fin n → ℂ) A = ∑ i, A (Pi.single i 1) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix',
    Matrix.trace]
  simp [LinearMap.toMatrix'_apply]

theorem kills_self : ∀ (G : Type) [Group G] [Finite G] (Y : G → ℂ), IsChar ℂ ℂ Y → Kills Y Y := by
  intro G _ _ Y hY V _ _ _ ρ h
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, σ, hσ⟩ := hY
  have hYc : ∀ g, Y g = σ.character g := fun g => by simpa using hσ g
  have hst : ∀ g, star (Y g) = σ.character g⁻¹ := fun g => by
    rw [star_virt_eq_inv G Y (AddSubgroup.subset_closure ⟨n, σ, hσ⟩) g, hYc]
  rw [finsum_eq_sum_of_fintype] at h
  rw [finsum_eq_sum_of_fintype]
  simp only [hst] at h ⊢

  have hinv : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    have : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast this.ne')
  have hfr := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom σ ρ)
  simp only [Representation.char_linHom] at hfr
  have h' : ∑ g : G, σ.character g⁻¹ * ρ.character g = 0 := h
  rw [h', mul_zero] at hfr
  have hbot : (Representation.linHom σ ρ).invariants = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    exact_mod_cast hfr.symm

  have hsum : ∀ f : (Fin n → ℂ) →ₗ[ℂ] V, ∑ g : G, Representation.linHom σ ρ g f = 0 := by
    intro f
    have hm : ∑ g : G, Representation.linHom σ ρ g f ∈ (Representation.linHom σ ρ).invariants := by
      intro h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  ext v
  have key : ∀ i : Fin n, ∑ g : G, (σ g⁻¹ (Pi.single i 1)) i • ρ g v = 0 := by
    intro i
    have := congrArg (fun F : (Fin n → ℂ) →ₗ[ℂ] V => F (Pi.single i 1))
      (hsum ((LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ).smulRight v))
    simpa [Representation.linHom_apply, LinearMap.sum_apply] using this
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
  simp only [Representation.character, trace_pi_eq_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun i _ => key i)

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImageStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_inf_ideal_sheaf_image : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W), IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) → IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  first | exact @GlobalTheory.isProper_map_inf_subschemeι | exact GlobalTheory.isProper_map_inf_subschemeι | (intros; apply GlobalTheory.isProper_map_inf_subschemeι <;> assumption)
end

