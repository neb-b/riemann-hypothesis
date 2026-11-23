module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactVersion
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0003

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.QuadraticSemicharactersOfProductThetaMem
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Arith

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem relIdx_smul_mem (Λ₁ Λ₂ : AddSubgroup V) {x : V} (hx : x ∈ Λ₂) :
    (relIdx Λ₁ Λ₂ : ℂ) • x ∈ Λ₁ := by
  have h := AddSubgroup.nsmul_index_mem (Λ₁.addSubgroupOf Λ₂) ⟨x, hx⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h
  unfold relIdx
  rw [Nat.cast_smul_eq_nsmul]
  simpa [AddSubgroup.relIndex] using h

theorem altE_natCast_smul_left (H : Sesq V) (N : ℕ) (s x : V) :
    altE H ((N : ℂ) • s) x = (N : ℝ) * altE H s x := by
  simp [altE, map_smul]

theorem phase_root (H : Sesq V) (Λ : AddSubgroup V) (hΛ : Λ ≤ dualLat H Λ) (N : ℕ) {s x : V}
    (hs : (N : ℂ) • s ∈ Λ) (hx : x ∈ Λ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) ^ (2 * N) = 1 := by
  obtain ⟨m, hm⟩ := (show ∀ y ∈ Λ, ∃ m : ℤ, altE H ((N : ℂ) • s) y = (m : ℝ) from hΛ hs) x hx
  rw [altE_natCast_smul_left] at hm
  have hm' : (N : ℂ) * (altE H s x : ℂ) = (m : ℂ) := by exact_mod_cast hm
  rw [← Complex.exp_nat_mul]
  have h2 : ((2 * N : ℕ) : ℂ) * (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) =
      ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hm'
  rw [h2, Complex.exp_int_mul_two_pi_mul_I]

theorem phase_root_selfDual (H : Sesq V) (Λ : AddSubgroup V) (hΛ : IsSelfDual H Λ) (N : ℕ) {s x : V}
    (hs : (N : ℂ) • s ∈ Λ) (hx : x ∈ Λ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) ^ (2 * N) = 1 := by
  exact phase_root H Λ hΛ.ge N hs hx

end Arith

theorem quadraticSemicharacters_of_productThetaMem (hF0 : ProductThetaMem) : quadraticSemicharacterIdentityReformulated₂ := by
  intro L ω₀ n _ _ h Λ α β g D ε θ hθ S hS t y
  have hH : IsHerm (stdH L (Fin 4 × n)) := (standardFormBasic L (Fin 4 × n)).2.1
  have hfix : F0 L ω₀ (Fin 4 × n) ∈ fixedBy (stdH L (Fin 4 × n)) β (stdLat L (Fin 4 × n)) :=
    ((hF0 L ω₀ (Fin 4 × n) D.per D.half β D.betaStd).1).2

  have h1 : tens4 (opU (matH h) t θ) (g.symm y)
      = opU (matH (blk4 h)) (fun w => t w.2) (tens4 θ) (g.symm y) :=
    ((heisenbergFourfold n h).2 (fun w => t w.2) (fun _ => θ) (g.symm y)).symm

  have h2 : tens4 θ = fun v => ε * (fun z => ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ *
        ∑ x ∈ S, β x * opU (stdH L (Fin 4 × n)) x (F0 L ω₀ (Fin 4 × n)) z)
          ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) v) := by
    rw [hθ]
    funext v
    have := InterReps_of semicharacterHom (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hH (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β D.betaSemi _ hfix S hS (g v)
    simp only [Pi.smul_apply, smul_eq_mul, kernel4]
    rw [this]
    rfl
  rw [h1, h2, Inv.opU_const_mul]
  erw [heisenbergIsometry _ _ _ _ _ D.isom (fun w => t w.2) (fun z => ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ *
        ∑ x ∈ S, β x * opU (stdH L (Fin 4 × n)) x (F0 L ω₀ (Fin 4 × n)) z) (g.symm y)]
  rw [Inv.opU_const_mul, Inv.opU_finset_sum]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Inv.opU_const_mul, heisenbergMul _ _ hH, F0, heisenbergStandard]
  simp only [Pi.add_apply]
  ring

end Formalism.L2.Th1.H
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.SubstSingleVar
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.H

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)

namespace FormalGroupLawNegation

section Formal

variable {K : Type} [Field K] {n : Type} [Fintype n]

theorem cc_lin {σ m : Type} [Fintype m] (c : m → K) {u : m → MvPowerSeries σ K}
    (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) :
    MvPowerSeries.constantCoeff (∑ j, MvPowerSeries.C (c j) * u j) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [map_mul, hu j, mul_zero]

theorem subst_lin {σ ρ m : Type} [Finite σ] [Fintype m] (c : m → K) (u : m → MvPowerSeries σ K)
    {φ : σ → MvPowerSeries ρ K} (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (∑ j, MvPowerSeries.C (c j) * u j) =
      ∑ j, MvPowerSeries.C (c j) * MvPowerSeries.subst φ (u j) := by
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom h, MvPowerSeries.subst_C]

theorem subst_tensor4 {ρ : Type} (T : MvPowerSeries n K) {φ : Fin 4 × n → MvPowerSeries ρ K}
    (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (tensor4 T) = ∏ a : Fin 4, MvPowerSeries.subst (fun i => φ (a, i)) T := by
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
  unfold tensor4
  rw [← MvPowerSeries.coe_substAlgHom h, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.coe_substAlgHom h, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _) h]
  congr 1
  funext i
  exact MvPowerSeries.subst_X h _

theorem subst_single_var {σ ρ : Type} [Finite σ] (s : σ) (f : PowerSeries K) {φ : σ → MvPowerSeries ρ K}
    (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (at1 s f) = PowerSeries.subst (φ s) f := by
  unfold at1
  rw [Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X s) hφ,
    MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ)]

theorem left_side {lg linv : PowerSeries K} (h : IsLogPair lg linv) {O : Type} [Semiring O] (τ : O →+* K)
    (γ : Matrix (Fin 4 × n) (Fin 4 × n) O) (B' : Matrix n n K) (M : Matrix (Fin 4 × n) (Fin 4 × n) K)
    (hM : ∀ (a : Fin 4) (i : n) (w : Fin 4 × n), ∑ j, B' i j * τ (γ (a, j) w) = M (a, i) w)
    (T : MvPowerSeries n K) :
    MvPowerSeries.subst (matCoord lg linv τ γ)
        (tensor4 (MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (B' i j) * at1 j lg) T)) =
      MvPowerSeries.subst (fun w => at1 w lg) (linSubst M (tensor4 T)) := by
  have hat : ∀ {σ : Type} (s : σ), MvPowerSeries.constantCoeff (at1 s lg : MvPowerSeries σ K) = 0 :=
    fun s => Formalism.L2.Th1.E.CompatibleChartOperations.constantCoeff_inVar_eq_zero s h.1
  have hmc : ∀ w, MvPowerSeries.constantCoeff (matCoord lg linv τ γ w) = 0 := fun w =>
    Formalism.L2.Th1.C.Pts.constantCoeff_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
  have hB : ∀ i, MvPowerSeries.constantCoeff
      (∑ j, MvPowerSeries.C (B' i j) * (at1 j lg : MvPowerSeries n K)) = 0 :=
    fun i => cc_lin _ fun j => hat j
  have hL : ∀ w, MvPowerSeries.constantCoeff
      (∑ w', MvPowerSeries.C (M w w') * (MvPowerSeries.X w' : MvPowerSeries (Fin 4 × n) K)) = 0 :=
    fun w => cc_lin _ fun j => MvPowerSeries.constantCoeff_X _
  rw [subst_tensor4 _ hmc, linSubst, subst_tensor4 _ hL,
    ← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => hat w), map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hB)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => hmc (a, i)),
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => hL (a, i))
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => hat w)]
  congr 1
  funext i
  rw [subst_lin _ _ fun j => hmc (a, j), subst_lin _ _ fun w => hat w]
  have h1 : ∀ j, MvPowerSeries.subst (fun i => matCoord lg linv τ γ (a, i)) (at1 j lg) =
      ∑ w, MvPowerSeries.C (τ (γ (a, j) w)) * at1 w lg := by
    intro j
    rw [subst_single_var _ _ fun j => hmc (a, j)]
    exact Formalism.L2.Th1.C.Pts.l_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => hat w), ← hM, map_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_assoc]

theorem right_side {lg : PowerSeries K} (hlg : PowerSeries.constantCoeff lg = 0) {m κ : Type} [Fintype m]
    (S : Finset κ) (r : κ → K) (f : κ → m → PowerSeries K) :
    MvPowerSeries.subst (fun w => at1 w lg) (∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w (f x w)) =
      ∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w ((f x w).subst lg) := by
  have hat : ∀ s : m, MvPowerSeries.constantCoeff (at1 s lg : MvPowerSeries m K) = 0 :=
    fun s => Formalism.L2.Th1.E.CompatibleChartOperations.constantCoeff_inVar_eq_zero s hlg
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hat
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom h, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_prod, MvPowerSeries.coe_substAlgHom h, MvPowerSeries.subst_C]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [subst_single_var _ _ hat]
  unfold at1
  rw [Formalism.L2.Th1.C.Pts.subst_subst hlg (MvPowerSeries.constantCoeff_X w)]

end Formal

section Map

variable {K₀ K : Type} [Field K₀] [Field K] (ι : K₀ →+* K) {n : Type} [Fintype n]

theorem map_tensor4 (T : MvPowerSeries n K₀) :
    MvPowerSeries.map ι (tensor4 T) = tensor4 (MvPowerSeries.map ι T) := by
  unfold tensor4
  rw [map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.map_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _)]
  congr 1
  funext i
  exact MvPowerSeries.map_X _ _

theorem map_linSubst {m : Type} [Finite m] (M : Matrix m n K₀) (T : MvPowerSeries m K₀) :
    MvPowerSeries.map ι (linSubst M T) = linSubst (M.map ι) (MvPowerSeries.map ι T) := by
  have hs : MvPowerSeries.HasSubst
      (fun i => ∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X j : MvPowerSeries n K₀)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_lin _ fun j => MvPowerSeries.constantCoeff_X _
  unfold linSubst
  rw [MvPowerSeries.map_subst hs]
  congr 1
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X, Matrix.map_apply]

theorem map_sumProd {κ : Type} (S : Finset κ) (r : κ → K₀) (f : κ → n → PowerSeries K₀) :
    MvPowerSeries.map ι (∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w (f x w)) =
      ∑ x ∈ S, MvPowerSeries.C (ι (r x)) * ∏ w, at1 w (PowerSeries.map ι (f x w)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_prod, MvPowerSeries.map_C]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  exact Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_inVar ι w _

end Map

end FormalGroupLawNegation

end Formalism.L2.Th1.H
end
end

