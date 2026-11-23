module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PBConjTranspose
section
noncomputable section

open Formalism.REAL (UJ KG toM inG Jm)
open GlobalTheory.PsCo.Pc1
open scoped Matrix

namespace GlobalTheory.PsCo.Pc3

variable {n : ℕ}

theorem pB_conjTranspose (ε : Fin n → Bool) (B : Mode ε → ℂ) : (pB ε B)ᴴ = pB ε B := by
  ext a b
  simp only [Matrix.conjTranspose_apply]
  cases ha : ε a <;> cases hb : ε b <;> simp [pB, ha, hb]

theorem pB_ne (ε : Fin n → Bool) (B : Mode ε → ℂ) (a b : Fin n) (h : ε a = ε b) : pB ε B a b = 0 := by
  simp only [pB]
  rw [dite_eq_right (by rintro ⟨h1, h2⟩; rw [h, h2] at h1; simp at h1),
    dite_eq_right (by rintro ⟨h1, h2⟩; rw [← h, h2] at h1; simp at h1)]

theorem pB_inG (ε : Fin n → Bool) (B : Mode ε → ℂ) : inG ε (pB ε B) := by
  unfold inG
  rw [pB_conjTranspose]
  ext a b
  simp only [Matrix.add_apply, Matrix.zero_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ε a = ε b
  · rw [pB_ne ε B a b h]; simp
  · cases ha : ε a <;> cases hb : ε b <;> simp_all

theorem continuous_pB (ε : Fin n → Bool) : Continuous (pB ε) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [pB]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).star
  · exact continuous_const

theorem pB_zero (ε : Fin n → Bool) : pB ε 0 = 0 := by
  ext a b; simp only [pB]; split_ifs <;> simp

theorem toM_eB (ε : Fin n → Bool) (B : Mode ε → ℂ) : toM (eB ε B) = NormedSpace.exp (pB ε B) := by
  rw [eB, Formalism.REAL.toM_expG ε _ 1 (pB_inG ε B)]; simp

theorem toM_inv (ε : Fin n → Bool) (g : UJ ε) : toM g⁻¹ = (toM g)⁻¹ := by
  show (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
  rw [Matrix.coe_units_inv]

theorem stEB : StEB := by
  intro n ε
  refine ⟨?_, ?_, fun B => ⟨toM_eB ε B, ?_⟩⟩
  · rw [(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.continuous_iff]
    change Continuous fun B => toM (eB ε B)
    simp_rw [toM_eB]
    have hc : Continuous (NormedSpace.exp : Mat n → Mat n) := by
      letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℚ) (α := ℂ)
      exact @NormedSpace.exp_continuous (Matrix (Fin n) (Fin n) ℂ) _ _
        (inferInstanceAs (CompleteSpace (Fin n → Fin n → ℂ)))
    exact hc.comp (continuous_pB ε)
  · apply Subtype.ext; apply Units.ext
    change toM (eB ε 0) = 1
    rw [toM_eB, pB_zero, NormedSpace.exp_zero]
  · rw [toM_inv, toM_eB]
    rw [Matrix.exp_neg]

end GlobalTheory.PsCo.Pc3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

def cavg {G : Type} [Group G] (K : Subgroup G) (f : G → ℂ) (x : G) : ℂ :=
  avg fun k : K => f ((k : G)⁻¹ * x * k)

def adL {k : Type} [Field k] {a b : ℕ} (A : GL (Fin a) k) (B : Matrix (Fin b) (Fin b) k) :
    Matrix (Fin a) (Fin b) k →ₗ[k] Matrix (Fin a) (Fin b) k where
  toFun X := X - (A⁻¹ : GL (Fin a) k).val * X * B
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

variable {E : Type} [Field E] [NumberField E]

def parP (a n : ℕ) (w : Pl E) : Subgroup (GLw n w) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular fun i : Fin n => decide (a ≤ (i : ℕ))}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    exact hg.mul hh
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one]
    exact Matrix.blockTriangular_one
  inv_mem' {g} hg := by
    let := g.invertible
    simp only [Set.mem_ofPred_eq, Matrix.coe_units_inv] at *
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def orbN {n a b : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  hint (intMat a b w) fun X => cavg (GlobalTheory.LFun.KGL w (n := n)) f
    ((blk h w 1 (Multiplicative.toAdd X))⁻¹ * blk h w m 0 * blk h w 1 (Multiplicative.toAdd X))

end GlobalTheory.LeviDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationOperatorFormulaGroupAndProjectors
section
set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.PolarFormula

theorem weight_rowW_le_colSum {N : ℕ} (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (rowW N N) d c ≤ ∑ s, Finsupp.weight (colW N N) d s := by
  classical
  have h2 : ∑ c', Finsupp.weight (rowW N N) d c' = ∑ s, Finsupp.weight (colW N N) d s := by
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), Pi.add_apply, Finset.sum_add_distrib, hf, hg]
    | single v k => simp [Finsupp.weight_apply, rowW, colW, Finsupp.sum_single_index, Pi.single_apply]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)).trans h2.le

theorem sum_rowComp {O : Type} [CommRing O] {N : ℕ} (ν : Fin N → ℕ) (M : ℕ) (hM : ∑ s, ν s ≤ M)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : IsWeightedHomogeneous (colW N N) f ν) :
    ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      weightedHomogeneousComponent (rowW N N) w f = f := by
  classical
  ext d
  rw [coeff_sum]
  simp_rw [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    rw [Fintype.mem_piFinset]
    intro c
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have e := hf (Ne.symm hne)
    calc _ ≤ _ := weight_rowW_le_colSum d c
      _ = ∑ s, ν s := by rw [e]
      _ ≤ M := hM

theorem comp_of_rowZ {O : Type} [CommRing O] {N : ℕ} (H : Fin N → ℤ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h H) (w : Fin N → ℕ) :
    weightedHomogeneousComponent (rowW N N) w h = if (fun c => (w c : ℤ)) = H then h else 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : AddMonoidAlgebra.coeff h d = 0
  · split_ifs <;> simp [hd]
  · have e := hh hd
    have key : Finsupp.weight (rowW N N) d = w ↔ (fun c => (w c : ℤ)) = H := by
      rw [← e]
      constructor
      · intro hw; funext c; rw [GlobalTheory.LvT.KerLat.weight_rowZ, hw]
      · intro hw; funext c
        have := congrFun hw c
        rw [GlobalTheory.LvT.KerLat.weight_rowZ] at this
        exact_mod_cast this.symm
    by_cases hw : (fun c => (w c : ℤ)) = H
    · rw [if_pos (key.mpr hw), if_pos hw]
    · rw [if_neg (mt key.mp hw), if_neg hw, AddMonoidAlgebra.coeff_zero] <;> rfl

theorem eq_zero_of_rowZ_neg {O : Type} [CommRing O] {N : ℕ} (H : Fin N → ℤ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h H) (c : Fin N) (hc : H c < 0) : h = 0 := by
  ext d
  simp only [AddMonoidAlgebra.coeff_zero, Pi.zero_apply]
  by_contra hd
  have e := congrFun (hh hd) c
  rw [GlobalTheory.LvT.KerLat.weight_rowZ] at e
  omega

theorem rowZ_of_rowW {O : Type} [CommRing O] {N : ℕ} (w : Fin N → ℕ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (rowW N N) h w) :
    IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h (fun c => (w c : ℤ)) := by
  intro d hd
  funext c
  rw [GlobalTheory.LvT.KerLat.weight_rowZ, hh hd]

theorem rowAct_transvection {O : Type} [CommRing O] {N : ℕ} (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) O) :
    rowAct O (n := N) (Matrix.transvection b a (1 : O)) f = (rowGen O a b f).eval 1 := by
  have e : (rowAct O (n := N) (Matrix.transvection b a (1 : O))).toRingHom =
      (Polynomial.evalRingHom (1 : MvPolynomial (Fin N × Fin N) O)).comp (rowGen O a b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [rowAct, rowGen]
    · intro v
      simp [rowAct, rowGen, Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Finset.sum_add_distrib,
        add_mul, ite_and]
      by_cases hv : v.1 = b
      · simp [hv]
      · simp [hv, Ne.symm hv]
  exact congrArg (fun φ : MvPolynomial (Fin N × Fin N) O →+* MvPolynomial (Fin N × Fin N) O => φ f) e

end GlobalTheory.PolarFormula

namespace GlobalTheory.PolarFormula

theorem comp_rowAct_transvection {O : Type} [CommRing O] {N : ℕ} (a b : Fin N) (hab : a ≠ b) (w : Fin N → ℕ)
    (h : MvPolynomial (Fin N × Fin N) O) (hh : IsWeightedHomogeneous (rowW N N) h w) :
    weightedHomogeneousComponent (rowW N N) (w + Pi.single a 1 - Pi.single b 1)
      (rowAct O (n := N) (Matrix.transvection b a (1 : O)) h) = rowDiv O a b 1 h := by
  classical
  have hZ := rowZ_of_rowW w h hh
  rw [rowAct_transvection, Polynomial.eval_eq_sum_range' (n := (rowGen O a b h).natDegree + 2) (by omega)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [one_pow, mul_one, map_sum]
  have hk : ∀ k ∈ Finset.range ((rowGen O a b h).natDegree + 2),
      weightedHomogeneousComponent (rowW N N) (w + Pi.single a 1 - Pi.single b 1) ((rowGen O a b h).coeff k) =
        if k = 1 then rowDiv O a b 1 h else 0 := by
    intro k _
    have hs := GlobalTheory.LvT.KerLat.rowDiv_shift O _ a b k h hZ
    change weightedHomogeneousComponent _ _ (rowDiv O a b k h) = _
    rw [comp_of_rowZ _ _ hs]
    by_cases hk1 : k = 1
    · subst hk1
      by_cases hb : 1 ≤ w b
      · rw [if_pos, if_pos rfl]
        funext c
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
        by_cases hca : c = a
        · subst hca; simp [hab]
        · by_cases hcb : c = b
          · subst hcb; simp [hca]; omega
          · simp [hca, hcb]
      · have h0 : rowDiv O a b 1 h = 0 :=
          eq_zero_of_rowZ_neg _ _ hs b (by simp [Pi.single_apply, Ne.symm hab]; omega)
        simp [h0]
    · rw [if_neg hk1, if_neg]
      intro he
      have := congrFun he a
      simp [Pi.single_apply, hab] at this
      omega
  rw [Finset.sum_congr rfl hk, Finset.sum_ite_eq', if_pos (by simp)]

end GlobalTheory.PolarFormula

namespace GlobalTheory.PolarFormula

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

theorem polar_formula : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι) (M : ℕ) (a b : Fin N), ∃ F : FreeAlgebra O (Letter O N ι), ∀ (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)), (∀ σ, Antitone (res N (lam σ))) → (∀ σ w, IsProj O N lam σ w (P σ w)) → ∑ c : Fin N, lam τ c ≤ M → ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O a b 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧ evalE O N lam P F (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y) := by
  intro O _ N ι _ _ τ M a b
  by_cases hab : a = b
  · subst hab
    refine ⟨∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      (w a : O) • FreeAlgebra.ι O (Sum.inr (τ, w)), ?_⟩
    intro lam P _ hP hM x
    refine ⟨⟨rowDiv O a a 1 (x τ), Formalism.GradedWeylDivisibility.rowDivStable O N N _ a a 1 _ (x τ).2⟩, rfl, ?_⟩
    have hcol := ((rowdiv_mem_dualWeyl_iff O N N _ _).mp (x τ).2).1
    let cmp : (Fin N → ℕ) → dualWeyl O N N (res N (lam τ)) := fun w =>
      ⟨weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O),
        Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N _ w _ (x τ).2⟩
    have hPx : ∀ w, P τ w (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (Function.update x τ (cmp w)) :=
      fun w => hP τ w x (cmp w) rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [evalE, map_sum, map_smul, FreeAlgebra.lift_ι_apply, Sum.elim_inr, LinearMap.sum_apply,
      Finset.sum_apply, LinearMap.smul_apply, hPx]
    have hsum : (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        (w a : O) • PiTensorProduct.tprod O (Function.update x τ (cmp w))) =
        ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
          PiTensorProduct.tprod O (Function.update x τ ((w a : O) • cmp w)) := by
      apply Finset.sum_congr rfl
      intro w _
      exact ((PiTensorProduct.tprod O).map_update_smul x τ (w a : O) (cmp w)).symm
    rw [hsum]
    rw [← MultilinearMap.map_update_sum]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    conv_rhs => rw [← sum_rowComp _ M hM _ hcol]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show rowDiv O a a 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) =
        rowDivL O a a 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) from rfl, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rowDivL_apply, (GlobalTheory.ValCmp.rowDiv_rowWeight O N N w _
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)).2 a 1, Nat.choose_one_right,
      Nat.cast_smul_eq_nsmul]
  · let gt : GL (Fin N) O := ⟨Matrix.transvection b a (-1), Matrix.transvection b a 1,
        by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp,
        by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp⟩
    let g : ι → GL (Fin N) O := Pi.mulSingle τ gt
    refine ⟨∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      FreeAlgebra.ι O (Sum.inr (τ, w + Pi.single a 1 - Pi.single b 1)) * FreeAlgebra.ι O (Sum.inl g) *
        FreeAlgebra.ι O (Sum.inr (τ, w)), ?_⟩
    intro lam P _ hP hM x
    refine ⟨⟨rowDiv O a b 1 (x τ), Formalism.GradedWeylDivisibility.rowDivStable O N N _ a b 1 _ (x τ).2⟩, rfl, ?_⟩
    have hcol := ((rowdiv_mem_dualWeyl_iff O N N _ _).mp (x τ).2).1
    let cmp : (Fin N → ℕ) → dualWeyl O N N (res N (lam τ)) → dualWeyl O N N (res N (lam τ)) := fun w v =>
      ⟨weightedHomogeneousComponent (rowW N N) w (v : MvPolynomial (Fin N × Fin N) O),
        Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N _ w _ v.2⟩
    have hPz : ∀ w (z : ∀ σ, dualWeyl O N N (res N (lam σ))), P τ w (PiTensorProduct.tprod O z) =
        PiTensorProduct.tprod O (Function.update z τ (cmp w (z τ))) :=
      fun w z => hP τ w z (cmp w (z τ)) rfl
    have hg : ∀ z : ∀ σ, dualWeyl O N N (res N (lam σ)), grp O N lam g (PiTensorProduct.tprod O z) =
        PiTensorProduct.tprod O (Function.update z τ (Formalism.UG.dualWeylRep O N N _ gt (z τ))) := by
      intro z
      unfold grp
      rw [(Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun σ => res N (lam σ)) g z).1]
      congr 1
      funext σ
      by_cases hσ : σ = τ
      · subst hσ; simp [g]
      · simp [g, hσ, Pi.mulSingle_eq_of_ne hσ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [evalE, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inr, Sum.elim_inl, LinearMap.sum_apply,
      Finset.sum_apply, Module.End.mul_apply, hPz, hg, Function.update_self, Function.update_idem]
    rw [← MultilinearMap.map_update_sum]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_sum]
    conv_rhs => rw [← sum_rowComp _ M hM _ hcol]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show rowDiv O a b 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) =
        rowDivL O a b 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) from rfl, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rowDivL_apply]
    exact comp_rowAct_transvection a b hab w _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

end GlobalTheory.PolarFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceGLConjMaxCompactIff
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.CongConj

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {m : ℕ}

theorem v_le_one_of_mem_KGL {c : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w (n := m)) (i j : Fin m) :
    Valued.v (c.val i j) ≤ 1 := by
  obtain ⟨a, rfl⟩ := hc
  exact (a.val i j).2

theorem v_mul_left_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) ≤ γ) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hA i l) (hB l j)

theorem v_mul_right_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ γ) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_of_le_one (hA i l) (hB l j)

theorem conj_imp (k : ℕ) {c N : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w (n := m))
    (hN : N ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) :
    c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j -
      (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  refine ⟨mul_mem (mul_mem (inv_mem hc) hN.1) hc, fun i j => ?_⟩
  have hid : (c⁻¹ * N * c).val - 1 = (c⁻¹).val * (N.val - 1) * c.val := by
    have h1 : (c⁻¹).val * c.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have := v_mul_right_le (v_mul_left_le (B := N.val - 1) (v_le_one_of_mem_KGL (inv_mem hc)) (fun a b => by
    rw [Matrix.sub_apply]; exact hN.2 a b)) (v_le_one_of_mem_KGL hc) i j
  rw [← hid, Matrix.sub_apply] at this
  exact this

end GlobalTheory.CongConj

theorem GlobalTheory.congConj_iff : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (m k : ℕ) (c N : GLw m w), c ∈ GlobalTheory.LFun.KGL w (n := m) → ((c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ (N ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)))) := by
  intro E _ _ w m k c N hc
  constructor
  · intro h
    have h2 := GlobalTheory.CongConj.conj_imp k (inv_mem hc) h
    simpa [mul_assoc] using h2
  · exact GlobalTheory.CongConj.conj_imp k hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAdjoinRootAlgebrasGeneratedByPair
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem fits_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K)
    (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ →
    Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  intro E _ _ _ w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep h₁ h₂
  obtain ⟨ha₁, hr₁, hd₁, hs₁⟩ := h₁
  obtain ⟨ha₂, hr₂, hd₂, hs₂⟩ := h₂
  have hne : Q₁ * Q₂ ≠ 0 := hsep.ne_zero
  have hQ₁ : Q₁ ≠ 0 := left_ne_zero_of_mul hne
  have hQ₂ : Q₂ ≠ 0 := right_ne_zero_of_mul hne
  have hcop : IsCoprime (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) :=
    hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
  have hfst : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).1 = aeval u₁ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  have hsnd : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).2 = aeval u₂ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Algebra.adjoin K.E {((u₁, u₂) : B₁.A × B₂.A)} = ⊤
    obtain ⟨a, b, hab⟩ := hcop
    have e₁ : aeval u₁ b * aeval u₁ (Q₂.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₁) hab
      rw [map_add (f := _), map_mul, map_mul, hr₁, mul_zero, zero_add, map_one] at this
      exact this
    have e₂ : aeval u₂ a * aeval u₂ (Q₁.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₂) hab
      rw [map_add (f := _), map_mul, map_mul, hr₂, mul_zero, add_zero, map_one] at this
      exact this
    rw [eq_top_iff]
    rintro ⟨y, z⟩ -
    have hy : y ∈ (aeval u₁ : K.E[X] →ₐ[K.E] B₁.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₁]; trivial
    have hz : z ∈ (aeval u₂ : K.E[X] →ₐ[K.E] B₂.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₂]; trivial
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hz
    have key : ((aeval u₁ p, aeval u₂ r) : B₁.A × B₂.A) =
        aeval ((u₁, u₂) : B₁.A × B₂.A) (b * Q₂.map e.symm.toRingHom * p + a * Q₁.map e.symm.toRingHom * r) := by
      refine Prod.ext ?_ ?_
      · rw [hfst, map_add (f := _), map_mul, map_mul, map_mul, map_mul, hr₁, mul_zero, zero_mul, add_zero, e₁, one_mul]
      · rw [hsnd, map_add (f := _), map_mul, map_mul, map_mul, map_mul, hr₂, mul_zero, zero_mul, zero_add, e₂, one_mul]
    exact key ▸ Polynomial.aeval_mem_adjoin_singleton K.E _
  · show aeval ((u₁, u₂) : B₁.A × B₂.A) ((Q₁ * Q₂).map e.symm.toRingHom) = 0
    rw [Polynomial.map_mul]
    refine Prod.ext ?_ ?_
    · rw [hfst, map_mul, hr₁, zero_mul]; rfl
    · rw [hsnd, map_mul, hr₂, mul_zero]; rfl
  · show Module.finrank K.E (B₁.A × B₂.A) = (Q₁ * Q₂).natDegree
    rw [Module.finrank_prod, hd₁, hd₂, natDegree_mul hQ₁ hQ₂]
  · exact Prod.ext hs₁ hs₂

end GlobalTheory.KapLat
end

