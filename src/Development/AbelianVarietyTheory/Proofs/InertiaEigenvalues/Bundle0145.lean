module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
section
noncomputable section

namespace GlobalTheory.DeRhamCompare

open Module

section Lin

end Lin

section Period

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

section Mul

variable {R : Type} [CommRing R] [Algebra Qp R]

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
variable {R : Type} [CommRing R] [Algebra Qp R] in
theorem _root_.GlobalTheory.DeRhamCompare.comm_mp (b : R) (x : V ⊗[Qp] R) :
    TensorProduct.comm Qp V R (_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) b x) =
      b • TensorProduct.comm Qp V R x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v r =>
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

end Mul

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.mem_DdR (x : V ⊗[Qp] BdR) :
    x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ ↔ ∀ g, _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g x = x := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.DdR
  simp [Submodule.mem_iInf, sub_eq_zero]

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.mulK_mem (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c) x ∈
      _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ := by
  rw [_root_.GlobalTheory.DeRhamCompare.mem_DdR] at hx ⊢
  intro g
  have key : ∀ y : V ⊗[Qp] BdR,
      _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g (_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V)
        (algebraMap K BdR c) y) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c)
        (_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v r => simp [_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR, _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  rw [key, hx g]

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.finite_DdR [FiniteDimensional LL V] (h : _root_.Formalism.MainNotions.N.IsDR PD ρ) :
    FiniteDimensional LL (_root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) := by
  have hK : FiniteDimensional Qp K := by cases PD; assumption
  unfold _root_.Formalism.MainNotions.N.IsDR at h
  by_cases hV : Module.finrank LL V = 0
  · have hsV : Subsingleton V := Module.finrank_zero_iff.mp hV
    have hzero : ∀ z : V ⊗[Qp] BdR, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul v r => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    have hsub : Subsingleton (_root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :=
      ⟨fun x y => Subtype.ext (by rw [hzero x, hzero y])⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.FildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) ≤ _root_.Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FildR
  refine inf_le_inf_left _ ?_
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp :=
    PD.Fil_anti a
  rintro x ⟨y, rfl⟩
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) y, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
  rfl

end Period

section Comparison

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def DdRK : Submodule K (BdR ⊗[Qp] V) where
  carrier := {y | (TensorProduct.comm Qp V BdR).symm y ∈ DdR PD ρ}
  zero_mem' := by simp
  add_mem' := fun hx hy => by
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact Submodule.add_mem _ hx hy
  smul_mem' := fun c y hy => by
    obtain ⟨x, rfl⟩ := (TensorProduct.comm Qp V BdR).surjective y
    simp only [Set.mem_setOf_eq, LinearEquiv.symm_apply_apply] at *
    rw [← algebraMap_smul BdR, ← comm_mp (LL := LL), LinearEquiv.symm_apply_apply]
    exact mulK_mem PD ρ c x hy

open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.mem_DdRK (y : BdR ⊗[Qp] V) :
    y ∈ _root_.GlobalTheory.DeRhamCompare.DdRK PD ρ ↔ (TensorProduct.comm Qp V BdR).symm y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ :=
  Iff.rfl

def toK (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) : DdRK PD ρ :=
  ⟨TensorProduct.comm Qp V BdR x, by rw [mem_DdRK, LinearEquiv.symm_apply_apply]; exact hx⟩

end Comparison

section Filtered

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

end Filtered

end GlobalTheory.DeRhamCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardStableLattices
section
noncomputable section

namespace GlobalTheory.StableLatCount

open GlobalTheory.UnitLemma Polynomial

theorem card_stable_lattices : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → (Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  intro O _ _ _ _ E _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ hres M₁ M₂ hM₁ hM₂ hs₁ hs₂
  have hdet : LinearMap.det (adE E g₁ g₂) = resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly :=
    _root_.GlobalTheory.DetAdResultant.det_ad_eq_resultant E A₁ A₂ (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₂)
  have hdet0 : LinearMap.det (adE E g₁ g₂) ≠ 0 := hdet ▸ hres
  have hunit : IsUnit (adE E g₁ g₂) := (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet0)
  have hbij : Function.Bijective ((adE E g₁ g₂).restrictScalars O) := by
    have := (Module.End.isUnit_iff _).1 hunit
    simpa only [LinearMap.coe_restrictScalars] using this
  have hN : ∀ x ∈ homLat E M₁ M₂, (adE E g₁ g₂) x ∈ homLat E M₁ M₂ := by
    intro ψ hψ x hx
    rw [adE_apply]
    exact M₁.sub_mem (hs₁ _ (hψ x hx)) (hψ _ (hs₂ x hx))
  have hL := _root_.GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top O E A₁ A₂ M₁ M₂ hM₁ hM₂
  have h2 := GlobalTheory.card_kernel_quot_of_bijective O _ (homLat E M₁ M₂) ((adE E g₁ g₂).restrictScalars O) hbij hN
  simp only [LinearMap.coe_restrictScalars] at h2
  rw [GlobalTheory.StableGraph.card_stable_eq_card_hom O A₁ A₂ g₁ g₂ M₁ M₂ hs₂, GlobalTheory.StableLatCount.card_commMaps_eq_card_homQuot O E A₁ A₂ g₁ g₂ M₁ M₂ hM₂ hs₁ hs₂, h2,
    GlobalTheory.LatIndexDet.card_quot_eq_pow_val O E _ (homLat E M₁ M₂) hL.1 hL.2 (adE E g₁ g₂) hdet0 hN, hdet]

end GlobalTheory.StableLatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfTracePowers
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.TracePowCharpoly

open Polynomial Finset

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → ℂ) (k : ℕ) :
    (k : ℂ) * (univ.val.map f).esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) k
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq (s t : Multiset ℂ) (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    ∀ k, s.esymm k = t.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq (s t : Multiset ℂ) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext k
  by_cases hk : k ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hk, Multiset.prod_X_sub_C_coeff t (hc ▸ hk), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hk
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

end GlobalTheory.TracePowCharpoly

namespace GlobalTheory.TracePowCharpoly

open Polynomial

theorem trace_pow_eq_sum_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (k : ℕ) :
    LinearMap.trace ℂ V (f ^ k) =
      ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (· ^ k)).sum := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V), ← GlobalTheory.CharpolyPow.roots_charpoly_pow,
    ← Matrix.trace_eq_sum_roots_charpoly]
  congr 1
  induction k with
  | zero => simp [LinearMap.toMatrix_one]
  | succ n ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]

theorem charpoly_eq_prod_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    f.charpoly = ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (fun a => X - C a)).prod := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  exact (IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic _)

theorem charpoly_eq_of_trace_pow_eq : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  intro V V' _ _ _ _ _ _ f g h
  have hdim : Module.finrank ℂ V = Module.finrank ℂ V' := by
    have h0 := h 0
    simp only [pow_zero, LinearMap.trace_one] at h0
    exact_mod_cast h0
  rw [charpoly_eq_prod_roots f, charpoly_eq_prod_roots g]
  apply prod_eq_of_psum_eq
  · rw [GlobalTheory.CharpolyPow.card_roots_charpoly, GlobalTheory.CharpolyPow.card_roots_charpoly, hdim]
  · intro k
    rw [← trace_pow_eq_sum_roots, ← trace_pow_eq_sum_roots, h k]

end GlobalTheory.TracePowCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapEqOfContinuousAdicCompletionIso
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.PlaceOver

open Filter Topology

theorem isOpen_valuation_lt_one {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) :
    IsOpen {z : P.adicCompletion F | Valued.v z < 1} := by
  have h := Valued.isOpen_ball (P.adicCompletion F) 1
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using h

theorem valuation_lt_one_of_continuous {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F']
    {P : HeightOneSpectrum (𝓞 F)} {P' : HeightOneSpectrum (𝓞 F')}
    (i : P.adicCompletion F →+* P'.adicCompletion F') (hi : Continuous i)
    {x : P.adicCompletion F} (hx : Valued.v x < 1) : Valued.v (i x) < 1 := by
  have hU : {y : P'.adicCompletion F' | Valued.v y < 1} ∈ 𝓝 (i 0) := by
    rw [map_zero]
    exact (isOpen_valuation_lt_one P').mem_nhds (by simp)
  have hV := hi.continuousAt.preimage_mem_nhds hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hV
  have hγ0 : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by
    simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx (Units.mk0 _ hγ0)
  have hxn : x ^ n ∈ i ⁻¹' {y : P'.adicCompletion F' | Valued.v y < 1} := by
    apply hγ
    show Valued.v.restrict (x ^ n) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
    exact hn
  have h1 : Valued.v (i x) ^ n < 1 := by simpa [map_pow] using hxn
  by_contra h
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 h)))

end GlobalTheory.PlaceOver

namespace GlobalTheory.PlaceOver

theorem valued_algebraMap {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (P.adicCompletion F) k) = P.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k

theorem comap_eq_of_continuous_iso : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    w'.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal := by
  intro E E' _ _ _ _ _ w w' i hi hc
  have hle : w.asIdeal ≤ w'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) := by
    intro e he
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E')]
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) (e : E)) < 1 := by
      rw [valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w e).2 he
    have h2 := valuation_lt_one_of_continuous (i : w.adicCompletion E →+* w'.adicCompletion E') hi h1
    have h3 : (i : w.adicCompletion E →+* w'.adicCompletion E') (algebraMap E (w.adicCompletion E) (e : E)) =
        algebraMap E' (w'.adicCompletion E') (algebraMap E E' (e : E)) := hc _
    rw [h3, valued_algebraMap] at h2
    exact h2
  exact (w.isMaximal.eq_of_le (Ideal.comap_ne_top _ w'.isPrime.ne_top) hle).symm

end GlobalTheory.PlaceOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_orbit_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ y : PadicComplex l, Continuous (fun g => act g y) := by
  first | exact @GlobalTheory.Cyc.IsActC.continuous_orbit | exact GlobalTheory.Cyc.IsActC.continuous_orbit | (intros; apply GlobalTheory.Cyc.IsActC.continuous_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjectiveStatement
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicChar_inertia_surjective : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ v : ℤ_[l]ˣ, ∃ σ ∈ Ine (F := ℚ) A, cycZ (F := ℚ) (Ω := Ω) l σ = v := by
  first | exact @GlobalTheory.CycInertia.cycZ_Ine_surjective | exact GlobalTheory.CycInertia.cycZ_Ine_surjective | (intros; apply GlobalTheory.CycInertia.cycZ_Ine_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseNearOfDecompositionFixedStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_near_of_decomposition_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (z : Ω), (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r := by
  first | exact @GlobalTheory.exists_base_near_of_dec_fixed | exact GlobalTheory.exists_base_near_of_dec_fixed | (intros; apply GlobalTheory.exists_base_near_of_dec_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralUnramifiedExtIffIsIntegralBaseStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (a : B.A), @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ a ↔ IsIntegral K.O a := by
  first | exact @GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | exact GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | (intros; apply GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff <;> assumption)
end

