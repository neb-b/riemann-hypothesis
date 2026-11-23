module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0540
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveBijectiveRelationRowVecEqMatrix
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.RelLin

theorem main : ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop),
    (∀ x, ∃ y, R x y) → (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) →
    (∀ x y, R x y → (x = 0 ↔ y = 0)) → ∃ A : GL (Fin 2) (ZMod N), ∀ x, R x (vmul x A) := by
  intro N _ R h1 h2 h3
  choose f hf using h1
  have huniq : ∀ x y y', R x y → R x y' → y = y' := by
    intro x y y' hy hy'
    have h := h3 _ _ (h2 x y x y' hy hy')
    exact sub_eq_zero.mp (h.mp (sub_self x))
  have hsub : ∀ x x', f (x - x') = f x - f x' :=
    fun x x' => huniq _ _ _ (hf (x - x')) (h2 _ _ _ _ (hf x) (hf x'))
  let g : (Fin 2 → ZMod N) →+ (Fin 2 → ZMod N) := AddMonoidHom.ofMapSub f hsub
  let L : (Fin 2 → ZMod N) →ₗ[ZMod N] (Fin 2 → ZMod N) := g.toZModLinearMap N
  have hL : ∀ x, L x = f x := fun x => rfl
  have hinj : Function.Injective f := by
    intro x x' hxx
    have : f (x - x') = 0 := by rw [hsub, hxx, sub_self]
    exact sub_eq_zero.mp ((h3 _ _ (hf (x - x'))).mpr this)
  let M : Matrix (Fin 2) (Fin 2) (ZMod N) := LinearMap.toMatrixRight' L
  have hM : ∀ x, x ᵥ* M = f x := by
    intro x
    rw [← hL, ← Matrix.toLinearMapRight'_apply]
    simp [M]
  have hU : IsUnit M := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, hM x⟩
  refine ⟨hU.unit, fun x => ?_⟩
  have : vmul x hU.unit = f x := by
    simp [vmul, hM]
  rw [this]
  exact hf x

end GlobalTheory.RelLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAll
section
noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

theorem locOrder_eq_of_le {B : Type} [Ring B] [Algebra ℚ B] (OB Λ : Subring B) (hle : OB ≤ Λ)
    (N : ℕ) (hN : 0 < N) (hNΛ : ∀ x ∈ Λ, (N : B) * x ∈ OB) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    locOrder ℓ OB = locOrder ℓ Λ := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.image_mono hle)
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.one_tmul_mem_locOrder_of_nsmul_mem OB x N hN (hNΛ x hx) ℓ hℓ

theorem locOrder_matrix : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  intro F B _ _ _ _ _ _ _ _ _ n hn OB hfin hspan
  obtain ⟨Λ, hle, hΛ, hΛfin, N₁, hN₁, hN₁Λ⟩ := GlobalTheory.T.exists_order_containing_integers F B OB hfin hspan
  have hspanΛ : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ := fun b => by
    obtain ⟨m, hm, hmb⟩ := hspan b; exact ⟨m, hm, hle hmb⟩
  obtain ⟨N₂, hN₂, hfree⟩ := GlobalTheory.T.localOrderTensorPadic_free_almost_all F B Λ hΛ hΛfin hspanΛ
  obtain ⟨N₃, hN₃, hazu⟩ := GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all F B Λ hΛ hΛfin hspanΛ
  refine ⟨N₁ * N₂ * N₃, by positivity, fun ℓ _ hℓ => ?_⟩
  have h₁ : ¬ ℓ ∣ N₁ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
  have h₂ : ¬ ℓ ∣ N₂ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have h₃ : ¬ ℓ ∣ N₃ := fun h => hℓ (Dvd.dvd.mul_left h _)
  have heq := locOrder_eq_of_le OB Λ hle N₁ hN₁ hN₁Λ ℓ h₁
  letI := cenAlgebra ℓ F B Λ hΛ
  haveI := isScalarTower_cenAlgebra ℓ F B Λ hΛ
  haveI : Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := GlobalTheory.cenOrder_finite F ℓ
  obtain ⟨hF, hrank⟩ := hfree ℓ h₂
  haveI := hF
  haveI := hazu ℓ h₃
  obtain ⟨φ⟩ := GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local ℓ (cenOrder ℓ F) (locOrder ℓ Λ) n (hrank.trans hn)
  refine ⟨(Subalgebra.equivOfEq _ _ heq).trans (φ.restrictScalars ℤ_[ℓ]), fun a => ?_⟩
  refine ⟨heq ▸ cenMap_mem ℓ F B Λ hΛ a.2, ?_⟩
  have h2 : (Subalgebra.equivOfEq _ _ heq) ⟨cenMap ℓ F B a, heq ▸ cenMap_mem ℓ F B Λ hΛ a.2⟩ =
      algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a := Subtype.ext rfl
  rw [AlgEquiv.trans_apply, h2, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

end GlobalTheory.LocMatrix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundAtRamifiedPrime
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzRamified

theorem norm_int_eq_one {l : ℕ} [Fact l.Prime] {z : ℤ} (h : ¬ (l : ℤ) ∣ z) : ‖(z : ℂ_[l])‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]) z, norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one z) (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))

theorem norm_bound {l : ℕ} [Fact l.Prime] (W S P : ℂ_[l]) (hl : 4 < l) (hW : W ^ 2 = -(l : ℂ_[l]))
    (hP : ‖12 * P‖ ≤ 1) (hS : ‖((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P‖ ≤ 1) :
    ‖S‖ ≤ (l : ℝ) ^ (1 / 2 : ℝ) := by
  have hpr : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hpr.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]
  have h12 : ‖(12 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 12 := by
      intro h
      have h' : l ∣ 12 := by exact_mod_cast h
      have h4 : l ∣ 2 ^ 2 * 3 := h'
      rcases (Nat.Prime.dvd_mul hpr).1 h4 with h5 | h5
      · have := Nat.le_of_dvd (by norm_num) (hpr.dvd_of_dvd_pow h5); omega
      · have := Nat.le_of_dvd (by norm_num) h5; omega
    simpa using norm_int_eq_one (l := l) hd
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 2 := by
      intro h
      have := Int.le_of_dvd (by norm_num) h
      omega
    simpa using norm_int_eq_one (l := l) hd
  have hW2 : ‖W‖ ^ 2 = (l : ℝ)⁻¹ := by rw [← norm_pow, hW, norm_neg, hn]
  have hW1 : ‖W‖ < 1 := by
    have : ‖W‖ ^ 2 < 1 := by rw [hW2]; exact inv_lt_one_of_one_lt₀ hl1
    nlinarith [norm_nonneg W]
  have h1W : ‖1 + W‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hW1.ne'), norm_one,
      max_eq_left hW1.le]
  have hP1 : ‖P‖ ≤ 1 := by rwa [norm_mul, h12, one_mul] at hP
  have hB : ‖((1 + W) ^ 2 - 1) * P‖ ≤ 1 := by
    have e : ((1 + W) ^ 2 - 1) * P = W * (2 + W) * P := by ring
    have h2W : ‖2 + W‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2.le hW1.le)
    rw [e, norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ hW1.le (norm_nonneg _) h2W) (norm_nonneg _) hP1
  have hA : ‖W‖ * ‖S‖ ≤ 1 := by
    have e : 2 * W * (1 + W) * S =
        (((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P) + ((1 + W) ^ 2 - 1) * P := by
      linear_combination S * hW
    have := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hS hB)
    rwa [← e, norm_mul, norm_mul, norm_mul, h2, h1W, one_mul, mul_one] at this
  have hsq : ‖S‖ ^ 2 ≤ l := by
    have h3 : (‖W‖ * ‖S‖) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hA
    rw [mul_pow, hW2, inv_mul_le_iff₀ hl0, mul_one] at h3
    exact h3
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le hsq

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (w σ p : ℂ), 4 < l → w ^ 2 = -(l : ℂ) → Sz l lam 0 (12 * p) → Sz l lam 0 (((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz l lam (1 / 2) σ := by
  intro l _ lam w σ p hl hw hp hs
  obtain ⟨hp, hp'⟩ := hp
  obtain ⟨hs, hs'⟩ := hs
  rw [Real.rpow_zero] at hp' hs'
  have hlK : (l : ℂ) ∈ algebraicClosure ℚ ℂ := natCast_mem _ l
  have hwK : w ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [← mem_algebraicClosure_iff, hw]
    exact neg_mem hlK
  have hpK : p ∈ algebraicClosure ℚ ℂ := by
    have e : p = (12 * p) / ((12 : ℕ) : ℂ) := by push_cast; ring
    rw [e]
    exact div_mem hp (natCast_mem _ 12)
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hw0 : w ≠ 0 := by
    rintro rfl
    have : (l : ℂ) = 0 := by linear_combination hw
    have h' : l = 0 := by exact_mod_cast this
    omega
  have hw1 : 1 + w ≠ 0 := by
    intro h
    have : ((l + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination hw + (1 - w) * h
    exact Nat.succ_ne_zero l (by exact_mod_cast this)
  have hσK : σ ∈ algebraicClosure ℚ ℂ := by
    have e : σ = ((((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) + ((1 + w) ^ 2 - 1) * p) /
        (((2 : ℕ) : ℂ) * w * (1 + w)) := by
      rw [eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hw0) hw1)]
      push_cast
      linear_combination σ * hw
    have h1 : 1 + w ∈ algebraicClosure ℚ ℂ := add_mem (one_mem _) hwK
    rw [e]
    exact div_mem (add_mem hs (mul_mem (sub_mem (pow_mem h1 2) (one_mem _)) hpK))
      (mul_mem (mul_mem (natCast_mem _ 2) hwK) h1)
  refine ⟨hσK, norm_bound (lam ⟨w, hwK⟩) _ (lam ⟨p, hpK⟩) hl ?_ ?_ ?_⟩
  · have e : (⟨w, hwK⟩ : algebraicClosure ℚ ℂ) ^ 2 = -(l : algebraicClosure ℚ ℂ) := Subtype.ext (by simpa using hw)
    rw [← map_pow, e, map_neg, map_natCast]
  · have e : (⟨12 * p, hp⟩ : algebraicClosure ℚ ℂ) = ((12 : ℕ) : algebraicClosure ℚ ℂ) * ⟨p, hpK⟩ :=
      Subtype.ext (by
        show 12 * p = ((12 : ℕ) : ℂ) * p
        norm_num)
    rw [e, map_mul, map_natCast] at hp'
    exact_mod_cast hp'
  · have e : (⟨_, hs⟩ : algebraicClosure ℚ ℂ) =
        ((1 + ⟨w, hwK⟩) ^ 2 - (1 + (l : algebraicClosure ℚ ℂ))) * ⟨σ, hσK⟩ - ((1 + ⟨w, hwK⟩) ^ 2 - 1) * ⟨p, hpK⟩ :=
      Subtype.ext (by simp)
    rw [e] at hs'
    simpa only [map_sub, map_mul, map_pow, map_add (f := _), map_one, map_natCast] using hs'

end GlobalTheory.SzRamified
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingToOrderedCechDegreeTwoMemCocyclesTwoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternatingToOrderedCechDegreeTwo_mem_cocyclesTwo : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2), δ F 2 c = 0 → e2 F c ∈ Z2 F := by
  first | exact @GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | exact GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | (intros; apply GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqOfFactorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor : ∀ {X Y : Scheme.{0}} {A : CommRingCat.{0}} (κ : Spec A ⟶ Y) [IsOpenImmersion κ] (j : X ⟶ Y) (O : X.Opens) (q : A ⟶ Γ(X, O)) (hO : j ⁻¹ᵁ κ.opensRange = O), O.ι ≫ j = (O.toSpecΓ ≫ Spec.map q) ≫ κ → j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op = κ.appLE κ.opensRange ⊤ (fun x _ ↦ ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso A).hom ≫ q := by
  first | exact @GlobalTheory.SectionsPinch.app_eq_of_factor | exact GlobalTheory.SectionsPinch.app_eq_of_factor | (intros; apply GlobalTheory.SectionsPinch.app_eq_of_factor; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIsoSpreadsToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.IsoSpread

theorem spMap_inclusion_comp {S : Type} [CommRing S] {A B C : Subring S} (h₁ : A ≤ B)
    (h₂ : B ≤ C) :
    spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) =
      spMap (Subring.inclusion (h₁.trans h₂)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem spMap_subtype_comp {S : Type} [CommRing S] {A B : Subring S} (h : A ≤ B) :
    spMap B.subtype ≫ spMap (Subring.inclusion h) = spMap A.subtype := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_isPullback_lift {X₀ X₁ T₀ T₁ T₂ : Scheme.{0}} {f₀ : X₀ ⟶ T₀} {f₁ : X₁ ⟶ T₁}
    {π₁ : X₁ ⟶ X₀} {u : T₁ ⟶ T₂} {v : T₂ ⟶ T₀} {w : T₁ ⟶ T₀} (huv : u ≫ v = w)
    (hp : IsPullback π₁ f₁ f₀ w) :
    ∃ m : X₁ ⟶ pullback f₀ v, m ≫ pullback.fst _ _ = π₁ ∧ m ≫ pullback.snd _ _ = f₁ ≫ u ∧
      IsPullback m f₁ (pullback.snd f₀ v) u := by
  subst huv
  refine ⟨pullback.lift π₁ (f₁ ≫ u) (by rw [Category.assoc, hp.w]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst]
  exact hp

end GlobalTheory.IsoSpread

namespace GlobalTheory


open GlobalTheory.IsoSpread in
theorem iso_spreads_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀] [QuasiCompact q] [QuasiSeparated q] [LocallyOfFinitePresentation q] (φ : X ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → IsPullback φ f q (spMap R₀.subtype) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Z, j ≫ ψ = φ ∧ IsPullback ψ f₁ q (spMap (Subring.inclusion hle)) := by
  classical
  intro S _ R₀ X X₀ Z f f₀ q π _ _ _ _ _ _ φ hπ hφ

  obtain ⟨Fa, ha⟩ := morphism_descends_to_subring S R₀ X X₀ Z f f₀ q π φ hπ
    (hφ.w.trans hπ.w.symm)
  obtain ⟨Fb, hb⟩ := morphism_descends_to_subring S R₀ X Z X₀ f q f₀ φ π hφ
    (hπ.w.trans hφ.w.symm)

  let R₂ : Subring S := Subring.closure ((R₀ : Set S) ∪ (Fa : Set S) ∪ (Fb : Set S))
  have h₀₂ : R₀ ≤ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inl hx))
  have hFa : (Fa : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inr hx))
  have hFb : (Fb : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inr hx)
  obtain ⟨j₂, hj₂f, hj₂s, hj₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hπ
  obtain ⟨k₂, hk₂f, hk₂s, hk₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hφ
  obtain ⟨ψ₂, hψ₂, hψ₂q⟩ := ha R₂ h₀₂ hFa _ _ _ j₂ (IsPullback.of_hasPullback _ _) hj₂f hj₂s
  obtain ⟨χ₂, hχ₂, hχ₂q⟩ := hb R₂ h₀₂ hFb _ _ _ k₂ (IsPullback.of_hasPullback _ _) hk₂f hk₂s
  let α₂ := pullback.lift ψ₂ (pullback.snd f₀ (spMap (Subring.inclusion h₀₂)))
    (by rw [hψ₂q, pullback.condition])
  let β₂ := pullback.lift χ₂ (pullback.snd q (spMap (Subring.inclusion h₀₂)))
    (by rw [hχ₂q, pullback.condition])
  have hα₂f : α₂ ≫ pullback.fst _ _ = ψ₂ := pullback.lift_fst _ _ _
  have hα₂s : α₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hβ₂f : β₂ ≫ pullback.fst _ _ = χ₂ := pullback.lift_fst _ _ _
  have hβ₂s : β₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hjα : j₂ ≫ α₂ = k₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₂f, hψ₂, hk₂f]
    · rw [Category.assoc, hα₂s, hj₂s, hk₂s]
  have hkβ : k₂ ≫ β₂ = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hβ₂f, hχ₂, hj₂f]
    · rw [Category.assoc, hβ₂s, hj₂s, hk₂s]

  obtain ⟨Fc, hc⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ j₂ (α₂ ≫ β₂) (𝟙 _) hj₂
    (by rw [Category.assoc, hβ₂s, hα₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hjα, hkβ, Category.comp_id])
  obtain ⟨Fd, hd⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ k₂ (β₂ ≫ α₂) (𝟙 _) hk₂
    (by rw [Category.assoc, hα₂s, hβ₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hkβ, hjα, Category.comp_id])
  refine ⟨Fa ∪ Fb ∪ Fc ∪ Fd, fun R₁ hle hF X₁ f₁ π₁ j hp₁ hj₁ hjf ↦ ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hFa₁, hFb₁⟩, hFc₁⟩, hFd₁⟩ := hF
  have h₂₁ : R₂ ≤ R₁ := Subring.closure_le.mpr
    (Set.union_subset (Set.union_subset (fun x hx ↦ hle hx) hFa₁) hFb₁)
  obtain ⟨m, hmf, hms, hm⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) hp₁
  obtain ⟨n, hnf, hns, hn⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) (IsPullback.of_hasPullback q (spMap (Subring.inclusion hle)))
  have hmc : m ≫ α₂ ≫ β₂ = m := (hc R₁ h₂₁ hFc₁ X₁ f₁ m hm).trans (Category.comp_id _)
  have hnd : n ≫ β₂ ≫ α₂ = n := (hd R₁ h₂₁ hFd₁ _ _ n hn).trans (Category.comp_id _)
  have hjm : j ≫ m = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hj₁, hj₂f]
    · rw [Category.assoc, hms, reassoc_of% hjf, spMap_subtype_comp, hj₂s]
  have hw : (m ≫ ψ₂) ≫ q = f₁ ≫ spMap (Subring.inclusion hle) := by
    rw [Category.assoc, hψ₂q, reassoc_of% hmf, hp₁.w]
  let α : X₁ ⟶ pullback q (spMap (Subring.inclusion hle)) := pullback.lift (m ≫ ψ₂) f₁ hw
  let β : pullback q (spMap (Subring.inclusion hle)) ⟶ X₁ :=
    hp₁.lift (n ≫ χ₂) (pullback.snd _ _) (by rw [Category.assoc, hχ₂q, reassoc_of% hnf,
      pullback.condition])
  have hαf : α ≫ pullback.fst _ _ = m ≫ ψ₂ := pullback.lift_fst _ _ _
  have hαs : α ≫ pullback.snd _ _ = f₁ := pullback.lift_snd _ _ _
  have hβf : β ≫ π₁ = n ≫ χ₂ := hp₁.lift_fst _ _ _
  have hβs : β ≫ f₁ = pullback.snd _ _ := hp₁.lift_snd _ _ _
  have hαn : α ≫ n = m ≫ α₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hnf, hαf, Category.assoc, hα₂f]
    · rw [Category.assoc, hns, reassoc_of% hαs, Category.assoc, hα₂s, hms]
  have hβm : β ≫ m = n ≫ β₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hβf, Category.assoc, hβ₂f]
    · rw [Category.assoc, hms, reassoc_of% hβs, Category.assoc, hβ₂s, hns]
  have h₁ : α ≫ β = 𝟙 X₁ := by
    apply hp₁.hom_ext
    · rw [Category.assoc, hβf, reassoc_of% hαn, Category.id_comp, ← hβ₂f, ← Category.assoc m,
        ← Category.assoc, Category.assoc m, hmc, hmf]
    · rw [Category.assoc, hβs, hαs, Category.id_comp]
  have h₂ : β ≫ α = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hαf, reassoc_of% hβm, Category.id_comp, ← hα₂f, ← Category.assoc n,
        ← Category.assoc, Category.assoc n, hnd, hnf]
    · rw [Category.assoc, hαs, hβs, Category.id_comp]
  exact ⟨m ≫ ψ₂, by rw [reassoc_of% hjm, hψ₂],
    IsPullback.of_iso_pullback ⟨hw⟩ ⟨α, β, h₁, h₂⟩ hαf hαs⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechBijectiveOfAffineStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_bijective_of_affine : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := by
  first | exact @GlobalTheory.CechPoset.Φ_bijective_of_affine | exact GlobalTheory.CechPoset.Φ_bijective_of_affine | (intros; apply GlobalTheory.CechPoset.Φ_bijective_of_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechDifferentialCommStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_differential_comm : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := by
  first | exact @GlobalTheory.CechPoset.Φ_dB | exact GlobalTheory.CechPoset.Φ_dB | (intros; apply GlobalTheory.CechPoset.Φ_dB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechOneTmulStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_one_tmul : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), Φ w D hD' 0 ((1 : R') ⊗ₜ[R] one s D) = fun _ => 1 := by
  first | exact @GlobalTheory.CechPoset.Φ_one_tmul | exact GlobalTheory.CechPoset.Φ_one_tmul | (intros; apply GlobalTheory.CechPoset.Φ_one_tmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechPullbackCommStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_pullback_comm : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := by
  first | exact @GlobalTheory.CechPoset.Φ_ext_eq_pullCoef | exact GlobalTheory.CechPoset.Φ_ext_eq_pullCoef | (intros; apply GlobalTheory.CechPoset.Φ_ext_eq_pullCoef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenEqBotOfBlockCutCuspidalStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coindEigen_eq_bot_of_block_cut_cuspidal : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) = b (w c) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = ⊥ := by
  first | exact @GlobalTheory.FinGL.MackeyCut.eig_eq_bot_of_cut | exact GlobalTheory.FinGL.MackeyCut.eig_eq_bot_of_cut | (intros; apply GlobalTheory.FinGL.MackeyCut.eig_eq_bot_of_cut <;> assumption)
end

