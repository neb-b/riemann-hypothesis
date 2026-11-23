module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0021
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0022
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaOfInterfaces

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.RestAOfHighestVectorIntegrality
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def HighestWeightVectorIntegrality : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (lam : Fin n → ℤ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (v : V), IsIrrHW E lam v →
      v ∈ Nabla (O := O) E lam v

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.SpecialiseGenericMatrixInverse
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem zpow_finset_sum_root_weights {G α : Type*} [CommGroup G] (u : G) (s : Finset α) (f : α → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem torus_acts_through_weight : TorusActsThroughWeight := by
  intro R B _ _ ι _ LL n S φ D m c
  classical
  have hu : (∏ v : ι × Fin n, (if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) ^ (m v)) = ∏ a, D a ^ (wtS LL S m a) := by
    simp only [wtS, zpow_finset_sum_root_weights]
    rw [Fintype.prod_prod_type_right]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun l _ => ?_
    split_ifs <;> simp [zpow_neg, zpow_natCast, inv_pow]
  have hU : (∏ v : ι × Fin n, (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) ^ (m v)) = ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B) := by
    rw [← hu, Units.coe_prod]
    simp only [Units.val_pow_eq_pow_val]
  simp only [matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, RingHom.coe_comp,
    Function.comp_apply]
  rw [Finsupp.prod_congr (g2 := fun v e => (MvPolynomial.C (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) * X v) ^ e) ?_]
  · rw [Finsupp.prod_fintype _ _ (fun _ => by simp),
      Finset.prod_congr rfl (fun v _ => mul_pow _ _ _), Finset.prod_mul_distrib,
      MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), ← hU]
    simp only [map_mul, map_prod, map_pow]
    ring
  · intro v _
    congr 1
    split_ifs with h1 h2
    · rw [Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [Matrix.diagonal_apply]
    · rw [Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [Matrix.diagonal_apply]
    · simp

theorem specialise_coefficientMap {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (mul_sp φ g0 g0inv h).comp (coefficientMap R n) = φ := by
  ext r
  simp only [coefficientMap, RingHom.comp_apply, mul_sp_alg, genericMatrixEvaluation, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_C]

theorem specialise_genericMatrix {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (genericMatrixRootWeights R n).map (mul_sp φ g0 g0inv h) = g0 := by
  ext i k
  have hg := congrFun (congrFun (generic_matrix_evaluation_eq (j := φ) (g0 := g0)) i) k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hg
  simp only [genericMatrixRootWeights, Matrix.map_apply, mul_sp_alg]
  exact hg

theorem specialise_genericMatrixInverse {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (genericMatrixInverse R n).map (mul_sp φ g0 g0inv h) = g0inv := by
  have hadj : g0.adjugate = g0.det • g0inv := by
    calc g0.adjugate = g0.adjugate * (g0 * g0inv) := by rw [h, Matrix.mul_one]
      _ = (g0.adjugate * g0) * g0inv := (Matrix.mul_assoc _ _ _).symm
      _ = g0.det • g0inv := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hu := mul_sp_inv (j := φ) (g0 := g0) (g0inv := g0inv) h
  ext i k
  have hA := congrFun (congrFun (RingHom.map_adjugate (genericMatrixEvaluation φ g0) (genMat R n)) i) k
  rw [generic_matrix_evaluation_eq] at hA
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hA
  simp only [genericMatrixInverse, Matrix.map_apply, map_mul, mul_sp_alg, hA, hadj, Matrix.smul_apply, smul_eq_mul]
  linear_combination (g0inv i k) * hu

theorem generic_monomials_specialise : GenericMonomialsSpecialise := by
  intro R _ ι _ LL n S k1 _ φ g0 g0inv h G
  have hAi : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixInverse R n a b) = g0inv a b := fun a b => by
    have e := congrFun (congrFun (specialise_genericMatrixInverse φ h) a) b
    simpa only [Matrix.map_apply] using e
  have hAg : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixRootWeights R n a b) = g0 a b := fun a b => by
    have e := congrFun (congrFun (specialise_genericMatrix φ h) a) b
    simpa only [Matrix.map_apply] using e
  have hAc : ∀ r, mul_sp φ g0 g0inv h (coefficientMap R n r) = φ r := fun r =>
    RingHom.congr_fun (specialise_coefficientMap φ h) r
  have e : (MvPolynomial.map (mul_sp φ g0 g0inv h)).comp
      (matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n)) = matrixSubst LL S φ g0inv g0 := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
        MvPolynomial.map_C, hAc]
    · intro w
      simp only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      split_ifs <;> simp [map_sum, hAi, hAg]
  have key : matrixSubst LL S φ g0inv g0 G = MvPolynomial.map (mul_sp φ g0 g0inv h) (genericTranslate LL S G) := by
    rw [← e]
    rfl
  rw [key]
  exact MvPolynomial.support_map_subset _ _

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
section
noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_Hs (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

theorem cr_mem_Hs (E : GLOps n K V) (lam : Fin n → ℤ) (x : V) :
    x ∈ cr_Hs E lam ↔ x ∈ weightSp E lam ∧ ∀ a b : Fin n, a < b → E a b x = 0 := by
  simp only [cr_Hs, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem cr_compl [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (hT : (⨆ ν, weightSp E ν) = ⊤) (W : Submodule K V) (hW : IsStableUnderOperators E W) :
    ∃ W' : Submodule K V, IsCompl W W' ∧ IsStableUnderOperators E W' := by
  classical
  choose Q hQ using fun lam : Fin n → ℤ => Submodule.exists_isCompl (cr_Hs E lam ⊓ W)
  set H' : (Fin n → ℤ) → Submodule K V := fun lam => cr_Hs E lam ⊓ Q lam with hH'
  set W' : Submodule K V := ⨆ lam, isotypicPartIn E (H' lam) lam with hW'
  have hW'st : IsStableUnderOperators E W' := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E (H' mu) mu
  refine ⟨W', ⟨?_, ?_⟩, hW'st⟩
  ·
    rw [disjoint_iff]
    by_contra hne
    have hst : IsStableUnderOperators E (W ⊓ W') := fun a b x hx => ⟨hW a b x hx.1, hW'st a b x hx.2⟩
    obtain ⟨lam, w, hwm, hw⟩ := v2rep_exists_hwv E hR (W ⊓ W') hst (le_top.trans hT.ge) hne
    have hdl : Dominant lam := cr_hwv_dom E hR hw
    obtain ⟨r, hr1, hr2⟩ := casimir_polynomial_isolates_level E hR H' w hwm.2 (cr_c lam)
    rw [cr_aeval_eig (cr_C E) _ w (cr_C_hwv E hR lam w hw) r, hr1, one_smul] at hr2
    have hle : (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = cr_c lam}, isotypicPartIn E (H' ν) ν) ≤
        H' lam ⊔ cr_WS E {τ | τ ≠ lam} := by
      refine iSup₂_le fun ν hν x hx => ?_
      by_cases hνl : ν = lam
      · subst hνl
        have hsub : cr_Low ν ⊆ {τ | τ ≠ ν} := by
          intro τ hτ h
          have h2 := hτ.2
          rw [h, sub_self, cr_ht_zero] at h2
          exact lt_irrefl _ h2
        exact (sup_le_sup inf_le_left (cr_WS_mono E hsub)) (cr_isoIn_le E hR (H' ν) ν hx)
      · by_cases hx0 : x = 0
        · rw [hx0]; exact zero_mem _
        · have hd := cr_isoIn_dom E hR (H' ν) hx hx0
          have hsub : weightsBelow ν ⊆ {τ | τ ≠ lam} := by
            intro τ hτ h
            have hτ' : ν - τ ∈ cr_Pos n := hτ
            rw [h] at hτ'
            rcases cr_Pos_zero_or hτ' with h0 | h0
            · exact hνl (sub_eq_zero.1 h0)
            · have := cr_c_lt hd hdl hτ' h0
              have hν' : cr_c ν = cr_c lam := hν
              omega
          exact Submodule.mem_sup_right (cr_WS_mono E hsub (isotypic_component_le_lower_weights E hR (H' ν) ν hx))
    obtain ⟨h, hh, l, hl, hsum⟩ := Submodule.mem_sup.1 (hle hr2)
    have hhw : h ∈ weightSp E lam := ((cr_mem_Hs E lam h).1 hh.1).1
    have hl0 : l = 0 := by
      by_contra hl0
      have hlw : l ∈ weightSp E lam := by
        have : l = w - h := by rw [← hsum]; abel
        rw [this]; exact Submodule.sub_mem _ hw.2.1 hhw
      exact (cr_WS_mem E hl hlw hl0) rfl
    rw [hl0, add_zero] at hsum
    rw [hsum] at hh
    have hwHs : w ∈ cr_Hs E lam ⊓ W := ⟨hh.1, hwm.1⟩
    have := (hQ lam).disjoint.le_bot ⟨hwHs, hh.2⟩
    exact hw.1 ((Submodule.mem_bot K).1 this)
  ·
    rw [codisjoint_iff, eq_top_iff]
    refine (cr_CR E hR hT ⊤ (fun _ _ _ _ => trivial)).trans (iSup_le fun mu => ?_)
    refine Submodule.span_le.2 ?_
    rintro x ⟨u, hu, v, _, hv, rfl⟩
    have hvHs : v ∈ cr_Hs E mu := (cr_mem_Hs E mu v).2 ⟨hv.2.1, hv.2.2⟩
    have hvt : v ∈ (cr_Hs E mu ⊓ W) ⊔ Q mu := by rw [(hQ mu).sup_eq_top]; trivial
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 hvt
    have hv2Hs : v2 ∈ cr_Hs E mu := by
      have : v2 = (v1 + v2) - v1 := by abel
      rw [this]; exact Submodule.sub_mem _ hvHs hv1.1
    show u (v1 + v2) ∈ W ⊔ W'
    rw [map_add (f := _)]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (v2rep_Umon_stable E W hW u hu v1 hv1.2))
      (Submodule.mem_sup_right ?_)
    by_cases h0 : v2 = 0
    · rw [h0, map_zero]; exact zero_mem _
    · have h2 := (cr_mem_Hs E mu v2).1 hv2Hs
      exact Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨u, hu, v2, ⟨hv2Hs, hv2⟩, ⟨h0, h2.1, h2.2⟩, rfl⟩)

theorem weight_condition_from_integral_form (D : Formalism.BasicNotions.D7) : adm2 D := by
  intro K V _ _ _ _ _ n E hE W hW
  exact cr_compl E hE.1 hE.2.2 W hW

end Formalism.MainNotions.G.GLWeightTheory
end
end

