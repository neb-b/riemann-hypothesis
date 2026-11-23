module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.DetE
section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem tr1_two_eq_hq_trace_det (g : GL (Fin 2) ℂ) (n : ℕ) :
    tr1 2 n g = hq (↑g : Matrix (Fin 2) (Fin 2) ℂ).trace (↑g : Matrix (Fin 2) (Fin 2) ℂ).det n := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := ↑g with hA
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  have hcard : Multiset.card A.charpoly.roots = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have hp : A.charpoly = ∏ i, (X - C (![a, b] i)) := by
    rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic A), hab]
    simp [Fin.prod_univ_two]
  have htr : A.trace = a + b := by
    rw [Matrix.trace_eq_sum_roots_charpoly, hab]; simp
  have hdet : A.det = a * b := by
    rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp
  rw [trOne 2 n g ![a, b] hp, hqTwo, htr, hdet]

theorem UpperTheory.V.Z.Sym.Wt.trDC :
    UpperTheory.V.Z.Sym.Wt.TrDC := by
  intro I _ n e g
  rw [repD_apply, map_smul, smul_eq_mul]
  have h := trProd I 2 (fun _ => n) g
  simp only [VD] at *
  rw [h]
  simp only [detE, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => by rw [tr1_two_eq_hq_trace_det]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.TwineC
section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem tr_pi {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (f : ∀ i, Module.End ℂ (V i)) (F : Module.End ℂ (∀ i, V i)) (h : ∀ x i, F x i = f i (x i)) :
    LinearMap.trace ℂ _ F = ∑ i, LinearMap.trace ℂ _ (f i) := by
  have e : F = ∑ i, (LinearMap.single ℂ V i) ∘ₗ (f i ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x => funext fun k => ?_
    rw [h, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb.symm]
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm']
  congr 1
  ext x
  simp

theorem UpperTheory.V.Z.Sym.Wt.twineC :
    UpperTheory.V.Z.Sym.Wt.TwineC := by
  intro I _ _ j hj g τ h
  haveI : ∀ S : I → Bool, FiniteDimensional ℂ (Bi 3 (dg j S)) := fun S => finMH _ _ _
  rw [tr_pi (fun S : I → Bool => sg S • (biRep 3 (dg j S) g * swp 3 (dg j S))) _ fun x S => by
    rw [Module.End.mul_apply, repG_apply, thG_apply, map_smul]; rfl]
  simp only [map_smul, trSwap _, smul_eq_mul, sg, ← Finset.prod_mul_distrib, dg]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset Bool))
    fun v b => (if b = true then (-1 : ℂ) else 1) * tr1 3 (if b = true then j - 1 else j) (g v * invT ℂ 3 (g v))]
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a * a = τ v ^ 2 - 4 := IsAlgClosed.exists_eq_mul_self _ |>.imp fun _ h => h.symm
  have h1 : (τ v + a) / 2 + (τ v - a) / 2 = τ v := by ring
  have h2 : (τ v + a) / 2 * ((τ v - a) / 2) = 1 := by linear_combination (-1 / 4 : ℂ) * ha
  have hc : ((g v * invT ℂ 3 (g v) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).charpoly =
      ∏ i, (X - C (![(τ v + a) / 2, 1, (τ v - a) / 2] i)) := by
    rw [h, Fin.prod_univ_three]
    have e1 := congrArg (C : ℂ →+* ℂ[X]) h1
    have e2 := congrArg (C : ℂ →+* ℂ[X]) h2
    rw [map_add (f := _)] at e1
    rw [map_mul, map_one] at e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_one]
    linear_combination (X - 1) * X * e1 - (X - 1) * e2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := hqThree k ((τ v + a) / 2) ((τ v - a) / 2)
  rw [h1, h2] at this
  rw [Fintype.sum_bool, ← this]
  simp only [if_true, Bool.false_eq_true, if_false, Nat.add_sub_cancel, trOne _ _ _ _ hc]
  ring
end

