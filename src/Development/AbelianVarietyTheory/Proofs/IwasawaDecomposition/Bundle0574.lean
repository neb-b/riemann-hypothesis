module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem idlAlong_comap {X X' : Scheme.{0}} (k : X' ⟶ X) (I : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X') : idlAlong (I.comap k) ξ = idlAlong I (ξ ≫ k) := by
  unfold idlAlong
  rw [VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

theorem idlAlong_pow {X : Scheme.{0}} (I : X.IdealSheafData) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) : idlAlong (I ^ n) ξ = idlAlong I ξ ^ n := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  unfold idlAlong
  rw [ds_stalkId_eq_map (I ^ n) ⟨U, hU⟩ _ hx,
    ds_stalkId_eq_map I ⟨U, hU⟩ _ hx, Scheme.IdealSheafData.ideal_pow,
    Pi.pow_apply, Ideal.map_pow, Ideal.map_pow]

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionProperties
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

section Member

theorem finrank_int_eq_finrank_mul (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] :
    Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  rw [← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq,
    Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]

theorem free_int_of_projective (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y] : Module.Free ℤ Y := by
  have : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
  have : Module.IsTorsionFree ℤ Y := Module.IsTorsionFree.trans (𝓞 E)
  exact Module.free_of_finite_type_torsion_free'

theorem mem_psdCone_int {E : Type} [Field E] [NumberField E] (bar : 𝓞 E → 𝓞 E) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X)) : B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, h1, h2, h3⟩ := hB
  have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective r hr
  have : Module.Free ℤ X₁ := free_int_of_projective E
  exact ⟨X₁, _, _, inferInstance, r.restrictScalars ℤ, B₁, hr, ⟨h1.1, fun a y z => by simp⟩, h2, h3⟩

section ClassMin

open scoped Pointwise

variable {M n : ℕ} {C C' : (Fin n → ℤ) → (Fin n → ℤ) → ℝ}

theorem classMin_set_nonempty (M : ℕ) (C : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) (y : Fin n → ZMod (M + 1)) :
    {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x}.Nonempty := by
  obtain ⟨a, ha⟩ := redV_surjective M n y
  exact ⟨_, a, ha, rfl⟩

theorem classMin_set_bddBelow (hC : ∀ a, 0 ≤ C a a) (y : Fin n → ZMod (M + 1)) :
    BddBelow {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x} :=
  ⟨0, by rintro _ ⟨a, -, rfl⟩; exact hC a⟩

theorem classMin_nonneg (hC : ∀ a, 0 ≤ C a a) (y : Fin n → ZMod (M + 1)) : 0 ≤ classMin M C y :=
  le_csInf (classMin_set_nonempty M C y) (by rintro _ ⟨a, -, rfl⟩; exact hC a)

theorem classMin_smul {t : ℝ} (ht : 0 ≤ t) (y : Fin n → ZMod (M + 1)) :
    classMin M (fun a b => t * C a b) y = t * classMin M C y := by
  unfold classMin
  have : {x | ∃ a : Fin n → ℤ, redV M a = y ∧ t * C a a = x} = t • {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x} := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
  rw [this, Real.sInf_smul_of_nonneg ht, smul_eq_mul]

theorem classMin_add_le (hC : ∀ a, 0 ≤ C a a) (hC' : ∀ a, 0 ≤ C' a a) (y : Fin n → ZMod (M + 1)) :
    classMin M C y + classMin M C' y ≤ classMin M (fun a b => C a b + C' a b) y := by
  refine le_csInf (classMin_set_nonempty M (fun a b => C a b + C' a b) y) ?_
  rintro _ ⟨a, ha, rfl⟩
  exact add_le_add (csInf_le (classMin_set_bddBelow hC y) ⟨a, ha, rfl⟩)
    (csInf_le (classMin_set_bddBelow hC' y) ⟨a, ha, rfl⟩)

theorem classMin_exists_nat {β : (Fin n → ℤ) → (Fin n → ℤ) → ℤ} (hβ : ∀ a, 0 ≤ β a a) (y : Fin n → ZMod (M + 1)) :
    ∃ k : ℕ, classMin M (fun a b => (β a b : ℝ)) y = k := by
  classical
  let T : Set ℕ := {k | ∃ a : Fin n → ℤ, redV M a = y ∧ β a a = k}
  have hT : T.Nonempty := by
    obtain ⟨a, ha⟩ := redV_surjective M n y
    exact ⟨(β a a).toNat, a, ha, (Int.toNat_of_nonneg (hβ a)).symm⟩
  obtain ⟨a₀, ha₀, e₀⟩ := Nat.sInf_mem hT
  refine ⟨sInf T, IsLeast.csInf_eq ⟨⟨a₀, ha₀, by simp only [e₀]; push_cast; rfl⟩, ?_⟩⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 : sInf T ≤ (β a a).toNat := Nat.sInf_le ⟨a, ha, (Int.toNat_of_nonneg (hβ a)).symm⟩
  have h2 : ((β a a).toNat : ℤ) = β a a := Int.toNat_of_nonneg (hβ a)
  show ((sInf T : ℕ) : ℝ) ≤ (β a a : ℝ)
  rw [← h2]
  exact_mod_cast h1

end ClassMin

variable {X : Type} [AddCommGroup X] [Module.Finite ℤ X]

theorem fineMean_eval_eq (M : ℕ) {d : ℕ} {s : (Fin d → ℤ) →ₗ[ℤ] X} (hs : Function.Surjective s)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    (fineMean M).eval X (fun a b => B a b) =
      (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y := by
  rw [(fineMean M).eval_eq hs]
  show _ * _ - B (s 0) (s 0) = _
  simp

end Member

theorem baseFun_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ)
    (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q →
    (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ t : ℝ, 0 ≤ t → evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (t • B) =
      t * evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B) ∧
    (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ B' ∈ psdCone (bar := H.bar) (X := X), evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B +
      evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B' ≤ evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (B + B')) ∧
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β = n) ∧
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β) := by
  intro E _ _ _ H g q φs 𝓜 X _ _ _ _ hφ hE hX
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Free ℤ X := free_int_of_projective E
  have hd : Module.finrank ℤ X ≤ g := by
    rw [finrank_int_eq_finrank_mul E X]
    exact (Nat.mul_le_mul_left _ hX).trans hE
  have hφX : IsPolFanOn id φs X := hφ X hd
  set d := Module.finrank ℤ X with hd_def
  let b := Module.finBasis ℤ X
  let s : (Fin d → ℤ) →ₗ[ℤ] X := b.equivFun.symm.toLinearMap
  have hs : Function.Surjective s := b.equivFun.symm.surjective
  set D := fineDen g 𝓜 with hD
  have key : ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, evalR (baseFun (𝓞 E) D φs 𝓜) B = D * (evalR φs B +
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y) := by
    intro B
    rw [evalR, eval_baseFun]
    simp only [fineMean_eval_eq _ hs]
    rfl
  have keyZ : ∀ β : LinearMap.BilinForm ℤ X, (baseFun (𝓞 E) D φs 𝓜).evalZ β = D * (φs.evalZ β +
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => (β (s a) (s b) : ℝ)) y) := by
    intro β
    rw [← evalR_toReal, key, evalR_toReal]
    simp only [toReal_apply]
  refine ⟨fun B hB t ht => ?_, fun B hB B' hB' => ?_, fun β hβ hp => ?_, fun β hβ hp h0 => ?_⟩
  · have hB0 := nonneg_of_mem_psdCone hB
    rw [key, key, hφX.homog B (mem_psdCone_int _ hB) t ht]
    simp only [LinearMap.smul_apply, smul_eq_mul, classMin_smul ht, ← Finset.mul_sum]
    simp only [mul_left_comm _ t, ← Finset.mul_sum]
    ring
  · have h1 := hφX.superadd B (mem_psdCone_int _ hB) B' (mem_psdCone_int _ hB')
    have h2 : ∀ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y +
        (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B' (s a) (s b)) y ≤
        (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => (B + B') (s a) (s b)) y := fun M _ => by
      rw [← mul_add, ← Finset.sum_add_distrib]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (by positivity)
      simp only [LinearMap.add_apply]
      exact classMin_add_le (fun a => nonneg_of_mem_psdCone hB _) (fun a => nonneg_of_mem_psdCone hB' _) y
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_add_distrib] at h3
    rw [key, key, key, ← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  · obtain ⟨n, hn⟩ := hφX.integral β (mem_balForms_int.2 hβ.1) hp
    have hdiv : ∀ M ∈ 𝓜, ∃ e : ℕ, D = (M + 1) ^ d * e := fun M hM =>
      (pow_dvd_pow (M + 1) hd).trans (Finset.dvd_prod_of_mem (fun M => (M + 1) ^ g) hM)
    choose! e he using hdiv
    choose k hk using fun M y => classMin_exists_nat (M := M) (β := fun a b => β (s a) (s b)) (fun a => hp (s a)) y
    refine ⟨D * n + ∑ M ∈ 𝓜, (e M : ℤ) * ∑ y, (k M y : ℤ), ?_⟩
    rw [keyZ, hn]
    simp only [hk]
    push_cast
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun M hM => ?_
    have hM : (D : ℝ) = ((M : ℝ) + 1) ^ d * e M := by exact_mod_cast he M hM
    rw [hM]
    field_simp
  · have h1 := hφX.pos β (mem_balForms_int.2 hβ.1) hp h0
    rw [keyZ]
    refine mul_pos (by exact_mod_cast fineDen_pos g 𝓜) (add_pos_of_pos_of_nonneg h1 (Finset.sum_nonneg fun M _ =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => classMin_nonneg (fun a => ?_) y)))
    exact_mod_cast hp (s a)

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIso
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace UnifSqCompare

theorem mem_sq {X : Scheme.{0}} {L : LB X} {x : X} {j : L.ι} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ↔ x ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun _ => h⟩

end UnifSqCompare


set_option maxHeartbeats 1000000 in
open UnifCompare UnifSqCompare in
theorem unif_sq_polarised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen ∧ wL.IsGen ∧ IsMonHom Φ.hom ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' hL
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  have hGF : GlobalFnsSt := allSixLaws.1.globalFns
  have hS : SecBaseChangeSt := allSixLaws.1.secBaseChange
  have hA : AmpleSt := allSixLaws.1.ample
  obtain ⟨wL₀, hwL₀⟩ := hL
  obtain ⟨wL, hwL, hrig⟩ := GlobalTheory.T.exists_rescale_rigidified_square_iso _ G U.LG U'.LG wL₀ hwL₀
  choose β hβm hβ using unifPre_abelianPart_iso R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre
  choose v hvg hv using fun e =>
    GlobalTheory.T.polarization_squares_agree_at_each_thickening hGF R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre wL hwL hrig e (β e) (hβm e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R (maximalIdeal R) e D.toPre.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q U'.toUnifPre, Category.assoc, hβl,
      trans_comp_q U.toUnifPre, ← Category.assoc, hβl]
  have hR' := hR
  obtain ⟨hN, -, -, hC⟩ := hR'
  obtain ⟨Φ, w, hw, H⟩ := GlobalTheory.T.exists_iso_polarised_of_compatible_thickenings_square hS hA R (maximalIdeal R) D.toPre.P D'.toPre.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R (maximalIdeal R) e D'.toPre.P.A).left,
        y ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') →
        thickMap R (maximalIdeal R) e D'.toPre.P.A y ∈
          ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β (e + 1)).hom.left ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) (e + 1) D'.toPre.P.A).left).U (fun _ => fun _ => j') := by
      intro y hy
      have k : thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left ≫
          (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left =
          (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j)) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j')) (trans_comp_proj e _)).mpr (mem_pull.1 hy.2))⟩
    have hz : r z ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') :=
      ⟨mem_pull.2 (mem_sq.2 hj), mem_pull.2 (mem_sq.2 hj')⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hp e)).mp (mem_sq.1 (mem_pull.1 hx.1))
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_sq.1 (mem_pull.1 hx.2)
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R (maximalIdeal R) e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U'.toUnifPre e x j' jL' hM' hL', gw_trans U.toUnifPre e x j jL hM hL, trans_comp_q U'.toUnifPre,
      trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  have hpG : ∀ e, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot (maximalIdeal R)
  have hΦ : IsMonHom Φ.hom := by
    refine AbelianPartIso.isMonHom_of_thickenings hI D.toPre.P.isAb D'.toPre.P.isAb Φ.hom fun e => ?_
    have := (U.gt e).q_hom
    have := (U'.gt e).q_hom
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    refine AbelianPartIso.isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · have k : ((Over.pullback (thick R (maximalIdeal R) e)).map Φ.hom).left ≫
          pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
          pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
      exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
        ((Category.assoc _ _ _).symm.trans (hpG e)))
    · exact (Over.w _).trans (Over.w (U.gt e).q).symm
  refine ⟨Φ, w, wL, hw, hwL, hΦ, fun e => ⟨hpG e, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
    ((congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hp e)).mpr hM) hM'
  rw [Category.assoc] at h
  exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolDiv

theorem idlAlong_fromSpecStalk {X : Scheme.{0}} (I : X.IdealSheafData) (x : X) {W : Type} [CommRing W] [IsLocalRing W]
    (g : X.presheaf.stalk x →+* W) :
    idlAlong I (Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x) = (FinalTheorems.stalkId I x).map g := by
  obtain ⟨⟨U, hU⟩, hx, -⟩ := EffCartierData.exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have e0 : ∀ (y : X) (hy : y ∈ U), X.fromSpecStalk y = Spec.map (X.presheaf.germ U y hy) ≫ hU'.fromSpec :=
    fun y hy => (hU'.fromSpecStalk_eq_fromSpecStalk hy).symm
  generalize hχ : Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x = χ
  have e1 : χ = Spec.map (X.presheaf.germ U x hx ≫ CommRingCat.ofHom g) ≫ hU'.fromSpec := by
    rw [← hχ, e0 x hx]
    exact (Spec.map_comp_assoc (X.presheaf.germ U x hx) (CommRingCat.ofHom g) hU'.fromSpec).symm
  have hc : χ (closedPoint W) ∈ U := by
    have : χ (closedPoint W) ∈ Set.range hU'.fromSpec :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f => f (closedPoint W)) e1.symm)⟩
    rwa [hU'.range_fromSpec] at this
  have e2 : χ = Spec.map (X.presheaf.germ U _ hc ≫ Scheme.stalkClosedPointTo χ) ≫ hU'.fromSpec := by
    rw [Spec.map_comp, Category.assoc, ← e0 _ hc]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ).symm
  have e3 := Spec.map_injective ((cancel_mono hU'.fromSpec).1 (e1.symm.trans e2))
  unfold idlAlong
  rw [ds_stalkId_eq_map I ⟨U, hU⟩ _ hc, ds_stalkId_eq_map I ⟨U, hU⟩ x hx, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← e3]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.PolDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalPolarizationOfMumfordBundleSiegelFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SiegFibrePol

theorem polAV_of_lam_univ : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (K : Type) [Field K] (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A y α → IsSquare α α₂ → ∀ L : LB B.left, L.IsLB → Rigidified B L → Out.Sym B L → LBIso (abelian₂ B L) (F.univ.P.pull α₂) → IsAbelianScheme B ∧ RelAmple B L ∧ KTriv B L := by
  intro o _ ζ g n F K _ y B _ α α₂ hpb hsq L hL hrig hsym hΛ
  open GlobalTheory.CechPic GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw in
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hpb
  have := hB.comm
  have laws : Out.Laws := GlobalTheory.allSixLaws.1
  haveI : IsProper F.univ.A.hom := F.univ.ab.proper
  have hP' : (F.univ.P.pull α₂).IsLB := pull_isLB F.univ.isLB α₂
  have hrefl : LBIso (F.univ.P.pull α₂) (F.univ.P.pull α₂) := (GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl
  have hn := GlobalTheory.SiegelPull.nondeg_pull hpb hsq F.univ.isLB hP' hrefl F.princ.2
  have hM0 : (F.univ.diag.pull α).IsLB := pull_isLB (pull_isLB F.univ.isLB _) α
  have hamp0 : Out.RelAmple B (F.univ.diag.pull α) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback (pull_isLB F.univ.isLB _) F.princ.1 hpb.1
  have hd : ((F.univ.P.pull α₂).pull (lift (𝟙 B) (𝟙 B)).left).IsLB := pull_isLB hP' _
  have hdiag := GlobalTheory.SiegelPull.diag_iso hsq hrefl
  have eM0 : GlobalTheory.CechPic.cls _ hM0 = GlobalTheory.CechPic.cls _ hd := ((GlobalTheory.CechPic.cls_eq_iff hd hM0).2 hdiag).symm
  have hp : IsProjBy B.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B _ hB hM0 hamp0 K (𝟙 _) _ (𝟙 _) B.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ := GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy laws K B hB hp L hL
  have s₁ := GlobalTheory.SameLam.pull_inv_cls hL hsym
  have e₀ : GlobalTheory.CechPic.cls _ hP' = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (fst B B) (snd B B) :=
    ((GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) hP').2 hΛ).symm.trans
      (GlobalTheory.CechPic.cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  have hη : GlobalTheory.CechPic.pull (η[B] : 𝟙_ _ ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [← GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)]
    exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hL _)).2 hrig
  have h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp, hη, map_zero]
  have e₃ : GlobalTheory.CechPic.cls _ hd = 2 • GlobalTheory.CechPic.cls L hL := by
    refine (GlobalTheory.CechPic.cls_pull hP' _ _).trans ?_
    rw [e₀, GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd, GlobalTheory.SymRoot.lam_diag hL hΘ s₁, GlobalTheory.SymRoot.rigCls, h1, sub_zero]
  have f : IsFinite (𝟙 B : B ⟶ B).left := by rw [Over.id_left]; infer_instance
  have iso : LBIso (F.univ.diag.pull α) (lbPow L 2) :=
    (GlobalTheory.CechPic.cls_eq_iff hM0 (isLB_lbPow hL 2)).1 (eM0.trans (e₃.trans (cls_lbPow hL 2 _).symm))
  have hamp : Out.RelAmple B L :=
    (GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) L 2 two_pos hB hB hL f).2.1.1
      ((GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) _ 2 two_pos hB hB hM0 f).2.2.2 _ (isLB_lbPow hL 2) iso hamp0)
  exact ⟨hB, hamp, GlobalTheory.ThetaExtend.kTriv_of_lam hL hP' e₀ hn⟩

end GlobalTheory.SiegFibrePol
end
end

