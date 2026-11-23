module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallinePeriodMatrixRelation
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

private theorem specRoot_semi {R K U : Type} [Field R] [Field K] [Algebra R K] [AddCommGroup U] [Module R U]
    {d : ℕ} (Φ : (Fin d → K) → U) (hadd : ∀ a b, Φ (a + b) = Φ a + Φ b)
    (hsm : ∀ (r : R) a, Φ (r • a) = r • Φ a) (T : Module.End R U) (F : Matrix (Fin d) (Fin d) K)
    (h : ∀ c, T (Φ c) = Φ (F.mulVec c)) (q : R[X]) (c : Fin d → K) :
    aeval T q (Φ c) = Φ ((aeval F q).mulVec c) := by
  have hp : ∀ (n : ℕ) (c : Fin d → K), (T ^ n) (Φ c) = Φ ((F ^ n).mulVec c) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ', Module.End.mul_apply, ih, h, Matrix.mulVec_mulVec, pow_succ']
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq, Matrix.add_mulVec, hadd]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, LinearMap.smul_apply, hp,
      Matrix.smul_mulVec, hsm]

private theorem specRoot_spec {R K L : Type} [Field R] [Field K] [Field L] [Algebra R K] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsAlgClosed L] {d : ℕ} (F : Matrix (Fin d) (Fin d) K) (q : R[X])
    (hq : q ≠ 0) (c : Fin d → K) (hc : c ≠ 0) (h : (aeval F q).mulVec c = 0) :
    ∃ β ∈ spectrum L (F.map (algebraMap K L)), aeval β q = 0 := by
  have h1 : (aeval F q).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc, h⟩
  have h2 : (algebraMap K L).mapMatrix (aeval F q) =
      aeval (F.map (algebraMap K L)) (q.map (algebraMap R L)) := by
    refine Polynomial.map_aeval_eq_aeval_map (φ := algebraMap R L)
      (ψ := (algebraMap K L).mapMatrix) ?_ q F
    ext r i j
    simp only [RingHom.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs
    · simp [← IsScalarTower.algebraMap_apply]
    · simp
  have h3 : ¬ IsUnit (aeval (F.map (algebraMap K L)) (q.map (algebraMap R L))) := by
    rw [← h2, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det, h1, map_zero]
    exact not_isUnit_zero
  have hq' : q.map (algebraMap R L) ≠ 0 := Polynomial.map_ne_zero hq
  have hs := (IsAlgClosed.splits (q.map (algebraMap R L))).eq_prod_roots
  obtain ⟨β, hβ, e⟩ := spectrum.exists_mem_of_not_isUnit_aeval_prod (p := q.map (algebraMap R L))
    (a := F.map (algebraMap K L)) (fun hu => h3 (by
      rw [hs, map_mul, aeval_C]
      exact ((IsUnit.mk0 _ (leadingCoeff_ne_zero.2 hq')).map _).mul hu))
  exact ⟨β, hβ, by rwa [eval_map_algebraMap] at e⟩

theorem UpperTheory.crystalline_period_matrix_relation :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V) (M M' : Matrix (Fin d) (Fin d) (Bcr l)), M * M' = 1 → (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) → ∀ F : Matrix (Fin d) (Fin d) ↥(K0 K), M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ x ∈ Dcris ((PP l).PD K) ρ, x ≠ 0 → ∀ q : ℚ_[l][X], q ≠ 0 → aeval ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ f) q x = 0 → ∃ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), aeval β q = 0 := by
  intro l _ K f hσ V _ _ _ ρ d e M M' hMM hρ F hF x hx hx0 q hq h0
  obtain ⟨c, hc⟩ := UpperTheory.crystalline_vector_basis_expansion K ρ e M M' hMM hρ x hx
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  let j := algebraMap ↥(K0 K) (Bcr l)
  let Φ : (Fin d → ↥(K0 K)) → V ⊗[ℚ_[l]] Bcr l := fun c =>
    ∑ i, e i ⊗ₜ[ℚ_[l]] (M.mulVec (fun k => j (c k)) i)
  have hfix : ∀ (k : ℕ) (c : ↥(K0 K)), ((PP l).φB)^[k] (j c) = j ((((PP l).PD K).σ)^[k] c) := by
    intro k
    induction k with
    | zero => intro c; rfl
    | succ k ih =>
      intro c
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]
  have hT : ∀ (k : ℕ) (v : V) (b : Bcr l),
      ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ k) (v ⊗ₜ[ℚ_[l]] b) =
        v ⊗ₜ[ℚ_[l]] (((PP l).φB)^[k] b) := by
    intro k
    induction k with
    | zero => intro v b; rfl
    | succ k ih =>
      intro v b
      rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply', ← (PP l).PD_φ K]
      rfl
  let ψ : Bcr l →+* Bcr l := (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
  have hψ : (ψ : Bcr l → Bcr l) = ((PP l).φB)^[f] := AlgHom.coe_pow _ _
  have key := specRoot_semi Φ (fun a b => by
      simp only [Φ, Pi.add_apply, map_add (f := _), ← Finset.sum_add_distrib, ← TensorProduct.tmul_add]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib])
    (fun (r : ℚ_[l]) a => by
      simp only [Φ, Finset.smul_sum, ← TensorProduct.tmul_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, Pi.smul_apply, Algebra.smul_def, map_mul, j,
        ← IsScalarTower.algebraMap_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ f) F
    (fun c => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Φ, map_sum, hT]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [← hψ, RingHom.map_mulVec, hψ, hF, ← Matrix.mulVec_mulVec]
      have e1 : ((PP l).φB)^[f] ∘ (fun k => j (c k)) = j ∘ c := by
        funext m
        exact (hfix f _).trans (congrArg j (hσ _))
      have e2 : (F.map j).mulVec (j ∘ c) = fun k => j (F.mulVec c k) := by
        funext k
        exact (RingHom.map_mulVec j F c k).symm
      rw [e1, e2]) q c
  have hxc : x = Φ c := hc
  rw [← hxc, h0] at key
  refine specRoot_spec F q hq c ?_ ?_
  · rintro rfl
    apply hx0
    rw [hc]
    simp [Matrix.mulVec, dotProduct]
  · set y := (aeval F q).mulVec c
    have h1 := TensorProduct.sum_tmul_basis_left_eq_zero e
      (Finsupp.equivFunOnFinite.symm (M.mulVec (fun k => j (y k)))) (by
        rw [Finsupp.sum_fintype _ _ (fun i => TensorProduct.tmul_zero _ _)]
        exact key.symm)
    have h2 : M.mulVec (fun k => j (y k)) = 0 := by
      funext i
      exact DFunLike.congr_fun h1 i
    have h3 := congrArg M'.mulVec h2
    rw [Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec, Matrix.mulVec_zero] at h3
    haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by
      rw [← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]; exact Submodule.zero_mem _)⟩⟩
    funext k
    exact j.injective ((congrFun h3 k).trans (map_zero j).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsBasisAlgModLaplacianOfTypesCentre
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem algMod_add {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (A B : Module.End ℂ M)
    (hAB : A * B = B * A) (hA : AlgMod S ⊥ A) (hB : AlgMod S ⊥ B) : AlgMod S ⊥ (A + B) := by
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting M S {A, B} ?_ ?_ (A + B)
    (Subalgebra.add_mem _ (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp)))
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact hAB | exact hAB.symm
  · intro T hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    rcases hT with rfl | rfl <;> assumption

theorem UpperTheory.exists_basis_algMod_laplacian_of_types_centre :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → Centre S → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra), AlgMod S ⊥ (uAction (laplacianU K n b)) := by
  intro K _ _ n S hT hC
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData K n
  refine ⟨d, b, ?_⟩
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hΩ : casimir b ε ∈ (isExpLieAlgebra K n).centerU := casimir_mem_center hε2 horth hsymm hinv
  rw [laplacianU_eq_casimir_add b ε, map_add (f := _)]
  refine algMod_add S _ _ (Zc_comm_uAction (uAction_mem_Zc hΩ) _).eq (hC _ hΩ) ?_
  refine UpperTheory.algMod_bot_compact_casimir_of_types K n S hT (Fin d) (fun i => b i) (fun i => 1 - ε i) fun i => ?_
  rcases hε i with e | e
  · exact Or.inl (by rw [e, sub_self])
  · exact Or.inr (hK i e)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiltrationEntriesOfFrobeniusMatrix
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

namespace UpperTheory.V

variable {l : ℕ} [Fact l.Prime]

private def slS (l : ℕ) [Fact l.Prime] : Subring (Bcr l) where
  carrier := {b | (PP l).ιB b ∈ ((PP l).PD (botExt l)).Fil 0}
  mul_mem' := fun {a b} ha hb => by
    have := ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ ha hb
    rw [add_zero, ← map_mul] at this
    exact this
  one_mem' := by
    change (PP l).ιB 1 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_one]; exact ((PP l).PD (botExt l)).one_mem
  add_mem' := fun {a b} ha hb => by
    change (PP l).ιB (a + b) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    change (PP l).ιB 0 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha => by
    change (PP l).ιB (-a) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_neg]; exact Submodule.neg_mem _ ha

private theorem sl_alg (K : FinExt l) (c : ↥(K0 K)) : algebraMap ↥(K0 K) (Bcr l) c ∈ slS l := by
  have h : (PP l).ιB (algebraMap ↥(K0 K) (Bcr l) c) ∈ ((PP l).PD K).Fil 0 := by
    rw [← (PP l).PD_ι K, AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 (PP l).R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact (((PP l).PD K).Fil 0).smul_mem _ ((PP l).PD K).one_mem
  have h2 := (PP l).PD_Fil K (botExt l) 0
  change (PP l).ιB _ ∈ (((PP l).PD (botExt l)).Fil 0 : Set (PP l).R.BdR)
  rw [← h2]
  exact h

end UpperTheory.V

open UpperTheory.V in
theorem UpperTheory.filtration_entries_of_frobenius_matrix :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A F : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 → IsUnit A.det → M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ a : ℤ, (∀ i j, (PP l).ιB (M i j) ∈ ((PP l).PD (botExt l)).Fil a) → ∀ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖((l : Om l) ^ f) ^ (-a) * β‖ ≤ 1 := by
  intro l hl K f hf hσ d M M' A F hMM hA hφ hF a hFil β hβ
  obtain ⟨u, hu, hφu⟩ := UpperTheory.exists_crystalline_unit_frobenius_eigen l (-a)
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hc : ∀ k : ℕ, ((PP l).φB)^[k] = ⇑((PP l).φB ^ k) := fun k => (AlgHom.coe_pow _ _).symm
  have hit : ∀ k : ℕ, ((PP l).φB)^[k] (u : Bcr l) =
      algebraMap ℚ_[l] (Bcr l) (((l : ℚ_[l]) ^ (-a)) ^ k) * (u : Bcr l) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, AlgHom.commutes, hφu, pow_succ, map_mul, mul_assoc]
  have huM : ∀ i j, (u : Bcr l) * M i j ∈ slS l := fun i j => by
    have := ((PP l).PD (botExt l)).Fil_mul _ _ _ _ hu (hFil i j)
    rw [neg_add_cancel, ← map_mul] at this
    exact this
  have key : ∀ (k : ℕ) (E : Matrix (Fin d) (Fin d) ↥(K0 K)),
      M.map (((PP l).φB)^[k]) = M * E.map (algebraMap ↥(K0 K) (Bcr l)) →
      ((u : Bcr l) • M).map (((PP l).φB)^[k]) = ((u : Bcr l) • M) *
        (algebraMap ℚ_[l] ↥(K0 K) (((l : ℚ_[l]) ^ (-a)) ^ k) • E).map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro k E hE
    ext i j
    have h1 := congrFun (congrFun hE i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at h1
    have h2 : ((PP l).φB)^[k] ((u : Bcr l) * M i j) =
        ((PP l).φB)^[k] (u : Bcr l) * ((PP l).φB)^[k] (M i j) := by
      rw [hc, map_mul]
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    rw [h2, hit, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    ring
  have h := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ ((u : Bcr l) • M) (((u⁻¹ : (Bcr l)ˣ) : Bcr l) • M') _
    (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul, hMM'])
    (fun k i j => by
      obtain ⟨E, -, hE⟩ := UpperTheory.frobenius_iterate_matrix_form K M A hA hφ k
      have h1 := congrFun (congrFun (key k E hE) i) j
      rw [Matrix.map_apply, Matrix.mul_apply] at h1
      rw [h1]
      exact Subring.sum_mem (slS l) fun r _ => Subring.mul_mem _ (huM _ _) (sl_alg K _))
    (key f F hF)
  apply h
  have hl0 : ((l : Om l) ^ f) ^ (-a) ≠ 0 :=
    zpow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
  have e : (algebraMap ℚ_[l] ↥(K0 K) (((l : ℚ_[l]) ^ (-a)) ^ f) • F).map (algebraMap ↥(K0 K) (Om l)) =
      Units.mk0 _ hl0 • F.map (algebraMap ↥(K0 K) (Om l)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_zpow₀, map_natCast,
      Units.smul_mk0]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm (f : ℤ)]
  rw [e]
  exact (spectrum.smul_mem_smul_iff (r := Units.mk0 _ hl0)).2 hβ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharSignFixed
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]

private theorem place_eq {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (v v' : InfinitePlace F) : v = v' := by
  rw [← v.mk_embedding, ← v'.mk_embedding]
  congr 1
  ext x
  obtain ⟨q, rfl⟩ := h x
  simp

private theorem exists_sign {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (χ : HChar F) : ∃ m : ℕ, ∀ v : InfinitePlace F, χ.locInf v (-1) = (-1) ^ m := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e
  · exact ⟨0, fun v => by rw [place_eq h v v₀, pow_zero]; exact Units.ext e⟩
  · exact ⟨1, fun v => by rw [place_eq h v v₀, pow_one]; exact Units.ext e⟩

theorem UpperTheory.heckeChar_sign_fixed :
    UpperTheory.V.Af.Bc.SignFix := by
  intro E Ω _ _ _ hE _ _ _ l _ ι χ μ ⟨hμc, art, a, ha, hχ, hL⟩ n
  obtain ⟨m, hm⟩ := exists_sign (surjective_algebraMap_real E hE) χ
  have ho : (quadChar E ^ (m + n)).OrderDvd 2 := by
    have := quadChar_order E
    unfold HChar.OrderDvd at this ⊢
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have hη := isAlgPos_zero_of_orderDvd two_pos ho
  obtain ⟨δ, hδc, hδ⟩ := ha.exists_isLAdicOf ι hη
  have h0 : (1 : HChar E).IsAbsPow 0 := ⟨fun v x _ => rfl, fun v => by simp [HChar.val, HChar.locK, HChar.loc],
    fun k => by simp [HChar.inf]⟩
  have h1 : compNorm E 1 = 1 * (GlobalTheory.ThetaPull.thetaChar (1 : HChar E))⁻¹ := by
    rw [map_one, one_mul, eq_comm, inv_eq_one]
    exact Subtype.ext (MonoidHom.ext fun x => inv_one)
  have hres := _root_.GlobalTheory.PolCharRes.restrict_eq_cycBar_pow E Ω l ι 1 0 h0 1 h1 (m + n) δ (by rw [one_mul]; exact ⟨hδc, art, 0, ha, hη, hδ⟩) 0 (by simp)
  refine ⟨χ * quadChar E ^ (m + n), μ * δ, ⟨hμc.mul hδc, art, a + 0, ha, isAlgPos_mul hχ hη, hL.mul hδ⟩, ?_, ?_, fun v => ?_⟩
  · rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  · rw [MonoidHom.mul_comp, hres, zpow_zero, mul_one]
  · change χ.locInf v (-1) * (quadChar E ^ (m + n)).locInf v (-1) = (-1) ^ n
    rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneCharacterTwistPeriod
section
noncomputable section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct GlobalTheory.Pst Polynomial

private theorem zpow_fix {Q R : Type} [Field Q] [CommRing R] [Algebra Q R] (f : R →ₐ[Q] R) (T : Rˣ) (c : Qˣ)
    (h : (c : Q) • f (T : R) = T) (m : ℤ) : ((c ^ m : Qˣ) : Q) • f ((T ^ m : Rˣ) : R) = ((T ^ m : Rˣ) : R) := by
  have e : Units.map (algebraMap Q R : Q →* R) c * Units.map (f : R →* R) T = T := by
    ext; simpa [Algebra.smul_def] using h
  have e' : Units.map (algebraMap Q R : Q →* R) (c ^ m) * Units.map (f : R →* R) (T ^ m) = T ^ m := by
    rw [map_zpow, map_zpow, ← mul_zpow, e]
  rw [Algebra.smul_def]
  exact congrArg Units.val e'

private theorem smul_mul_tmul {Q A R : Type} [Field Q] [Field A] [CommRing R] [Algebra Q R] [Algebra Q A]
    (c : Q) (x : A ⊗[Q] R) (b : R) : algebraMap Q A c • (x * (1 : A) ⊗ₜ[Q] b) = x * (1 : A) ⊗ₜ[Q] (c • b) := by
  rw [algebraMap_smul, tmul_smul, mul_smul_comm]

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l}

private theorem stRep_mul (κ η : ↥(GK K) →* (↥L.1)ˣ) (g : ↥(GK K)) (a : ↥L.1) (h : (κ g : ↥L.1) = a * η g)
    (u : ↥L.1 ⊗[ℚ_[l]] Bst P) (b : Bst P) :
    stRep P (UpperTheory.V.Loc.chRep κ) g (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) =
      a • (stRep P (UpperTheory.V.Loc.chRep η) g u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] actSt P (g : GQ l) b) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, stRep_tmul, stRep_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      map_mul (actSt P (g : GQ l)), smul_tmul']
    congr 1
    simp [UpperTheory.V.Loc.chRep, h, mul_assoc]
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy, smul_add]

private theorem phiV_mul (u : ↥L.1 ⊗[ℚ_[l]] Bst P) (b : Bst P) :
    phiV P ↥L.1 ↥L.1 (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) = phiV P ↥L.1 ↥L.1 u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiSt P b := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, phiV_tmul, phiV_tmul, Algebra.TensorProduct.tmul_mul_tmul, map_mul]
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]

private theorem phiV_pow_mul (c : ℚ_[l]) (b : Bst P) (hb : c • phiSt P b = b) (k : ℕ) (u : ↥L.1 ⊗[ℚ_[l]] Bst P) :
    (algebraMap ℚ_[l] ↥L.1 c) ^ k • (phiV P ↥L.1 ↥L.1 ^ k) (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) =
      (phiV P ↥L.1 ↥L.1 ^ k) u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, mul_smul, ← map_smul, phiV_mul, smul_mul_tmul, hb, ih]

theorem UpperTheory.weilDeligne_character_twist_period :
    UpperTheory.V.Af.Wd.TwistPer := by
  intro l _ K L κ χ η m hκ hc hη
  have hu := UpperTheory.weilDeligne_unramified_period l K L η hc hη
  unfold UpperTheory.V.Af.Wd.cycL at hκ
  generalize UpperTheory.V.Loc.PP l = P at hu hκ ⊢
  obtain ⟨u, hu0, hu1, hu2⟩ := hu
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  let T : (Bst P)ˣ := Units.map (C : P.R.B →+* Bst P) (isUnit_tB P).unit⁻¹
  have hT : (T : Bst P) = C (tInv P) := rfl
  have h1 : ∀ g : GQ l, ((P.χQ g ^ m : ℚ_[l]ˣ) : ℚ_[l]) • actSt P g ((T ^ m : (Bst P)ˣ) : Bst P) = ((T ^ m : (Bst P)ˣ) : Bst P) :=
    fun g => zpow_fix (actSt P g) T (P.χQ g) (by rw [hT, actSt_C, smul_C, smul_actQ_tInv]) m
  have h2 := zpow_fix (phiSt P) T (Units.mk0 _ hl) (by rw [hT, phiSt_C, smul_C, Units.val_mk0, smul_phiB_tInv]) m
  refine ⟨u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] ((T ^ m : (Bst P)ˣ) : Bst P), fun h0 => hu0 ?_, fun g => ?_, fun g k hk => ?_⟩
  · have := congrArg (· * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] (((T ^ m)⁻¹ : (Bst P)ˣ) : Bst P)) h0
    simpa only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one, zero_mul,
      ← Algebra.TensorProduct.one_def] using this
  · rw [stRep_mul P κ η g ((χ g : ↥L.1) * algebraMap ℚ_[l] ↥L.1 ((P.χQ (g : GQ l) ^ m : ℚ_[l]ˣ) : ℚ_[l])) ?_, hu1,
      mul_smul, smul_mul_tmul, h1]
    rw [hκ g, Units.val_mul, Units.val_mul, mul_comm (χ g : ↥L.1)]
    simp
  · have e : (l : ↥L.1) ^ (m * k) = (algebraMap ℚ_[l] ↥L.1 ((Units.mk0 _ hl ^ m : ℚ_[l]ˣ) : ℚ_[l])) ^ k := by
      simp [zpow_mul]
    rw [e, mul_smul, phiV_pow_mul P _ _ h2, ← smul_mul_assoc, hu2 g k hk]
end
end

