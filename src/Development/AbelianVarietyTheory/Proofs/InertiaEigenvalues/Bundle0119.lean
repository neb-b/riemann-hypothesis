module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHermitianMatrixCongruentOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0103
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureLUnitSmulAbsKSq
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory.JR.ScaleHaarL

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by
  intro F E _ _ _ _ U A μ hμ c S
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := GlobalTheory.JR.EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  let u : A.Lˣ := Units.map (algebraMap A.K A.L : A.K →* A.L) c
  have hu : (u : A.L) = algebraMap A.K A.L (c : A.K) := rfl
  have hset : {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = u • S := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, Units.smul_def, hu, smul_eq_mul]
    exact ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩
  have hc1 : Continuous (b.equivFun.symm : (Fin 2 → A.K) → A.L) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F)
  have hc2 : Continuous (b.equivFun : A.L → (Fin 2 → A.K)) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)
  let e : (Fin 2 → A.K) ≃ₜ+ A.L :=
    { b.equivFun.symm.toAddEquiv with
      continuous_toFun := hc1
      continuous_invFun := hc2 }
  have key : distribHaarChar A.L u = distribHaarChar A.K c ^ 2 := by
    rw [GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e c u (fun x => ?_),
      GlobalTheory.JR.ModuleNorm.distribHaarChar_pi_two]
    change b.equivFun.symm ((c : A.K) • x) = (u : A.L) * b.equivFun.symm x
    rw [map_smul, Algebra.smul_def, hu]
  rw [hset, ← distribHaarChar_mul μ u S, key, GlobalTheory.JR.EtMeas.absK_unit]
  rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.JR.ScaleHaarL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharOnIdMulSqrtAbsNormInvMemSubring
section
open NumberField IsDedekindDomain

noncomputable section
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeIdealValue

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem finite_supp (χ : HChar L) (J : FractionalIdeal (𝓞 L)⁰ L) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v J).Finite := by
  refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors J)).subset fun v hv h => hv ?_
  simp [h]

theorem onId_mul (χ : HChar L) {a b : FractionalIdeal (𝓞 L)⁰ L} (ha : a ≠ 0) (hb : b ≠ 0) :
    χ.onId (a * b) = χ.onId a * χ.onId b := by
  unfold HChar.onId
  rw [← finprod_mul_distrib (finite_supp χ _) (finite_supp χ _)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul L v ha hb, zpow_add]

theorem onId_one (χ : HChar L) : χ.onId (1 : FractionalIdeal (𝓞 L)⁰ L) = 1 := by
  unfold HChar.onId
  simp [FractionalIdeal.count_one]

theorem onId_prime (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId ((v.asIdeal : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by
  unfold HChar.onId
  rw [finprod_eq_single _ v, FractionalIdeal.count_self, zpow_one]
  intro w hw
  rw [FractionalIdeal.count_maximal_coprime L w (Ne.symm hw), zpow_zero]

theorem inv_mem (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)) :
    cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal →
      (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) →
    (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ I hI =>
    intro _ _
    have hI' : I = ⊤ := Ideal.isUnit_iff.1 hI
    subst hI'
    rw [FractionalIdeal.coeIdeal_top, onId_one, Ideal.absNorm_top]
    simp
  | h₃ I p hI hp ih =>
    intro _ hP
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hv := hP v Ideal.mul_le_left
    have hrest := ih hI fun P hle => hP P (le_trans Ideal.mul_le_right hle)
    rw [FractionalIdeal.coeIdeal_mul, onId_mul χ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.2 hI), map_mul, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Units.val_mul, Complex.ofReal_mul]
    have e : χ.onId ((p : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := onId_prime χ v
    rw [e]
    have : (((χ.val v : ℂˣ) : ℂ) * (χ.onId (I : FractionalIdeal (𝓞 L)⁰ L) : ℂ) *
        (((Real.sqrt (Ideal.absNorm p) : ℝ) : ℂ) * ((Real.sqrt (Ideal.absNorm I) : ℝ) : ℂ)))⁻¹ =
        (((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ))⁻¹ *
        (((χ.onId (I : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm I) : ℝ) : ℂ))⁻¹ := by
      rw [← mul_inv]; congr 1; ring
    rw [this]
    exact O.mul_mem hv hrest

end GlobalTheory.HeckeIdealValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgDvrOfSeparableCharpoly
section
open GlobalTheory.UnitLemma Polynomial Module

namespace GlobalTheory.IntClosureSep

theorem isRoot_minpoly_of_isRoot_charpoly {E A L : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] [Field L] [Algebra E L] (g : A) {α : L}
    (hα : ((LinearMap.mulLeft E g).charpoly.map (algebraMap E L)).IsRoot α) :
    ((minpoly E g).map (algebraMap E L)).IsRoot α := by
  classical
  let b := Module.finBasis E A
  set M := Algebra.leftMulMatrix b g with hM
  have hQ : (LinearMap.mulLeft E g).charpoly = M.charpoly := by
    rw [← LinearMap.charpoly_toMatrix (LinearMap.mulLeft E g) b]; rfl
  set M' := M.map (algebraMap E L) with hM'
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' M') α := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', Matrix.charpoly_map,
      ← hQ]
    exact hα
  obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
  have h2 : aeval M (minpoly E g) = 0 := by
    rw [hM, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have h3 : aeval M' ((minpoly E g).map (algebraMap E L)) = 0 := by
    rw [aeval_map_algebraMap]
    have : M' = (Algebra.ofId E L).mapMatrix M := rfl
    rw [this, Polynomial.aeval_algHom_apply, h2, map_zero]
  have h4 := Module.End.aeval_apply_of_hasEigenvector (p := (minpoly E g).map (algebraMap E L)) hv
  have h5 : aeval (Matrix.toLin' M') ((minpoly E g).map (algebraMap E L)) = 0 := by
    have : Matrix.toLin' M' = Matrix.toLinAlgEquiv' M' := rfl
    rw [this, Polynomial.aeval_algEquiv, AlgHom.comp_apply, h3, map_zero]
  rw [h5, LinearMap.zero_apply] at h4
  exact (smul_eq_zero.mp h4.symm).resolve_right hv.2

theorem integralClosure_fg_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ g hsep
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (Subalgebra.toSubmodule (integralClosure O A)) ⊥]
    exact Submodule.fg_bot
  let L := AlgebraicClosure E
  set Q := (LinearMap.mulLeft E g).charpoly with hQ
  set n := finrank E A with hn
  have hQdeg : Q.natDegree = n := LinearMap.charpoly_natDegree _
  set R := (Q.map (algebraMap E L)).roots with hR
  have hRnodup : R.Nodup := nodup_roots (hsep.map)
  have hRcard : Multiset.card R = n := by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hQdeg]
  set m := minpoly E g with hm
  have hsub : ∀ α ∈ R, aeval α m = 0 := fun α hα => by
    have := isRoot_minpoly_of_isRoot_charpoly g (isRoot_of_mem_roots hα)
    rwa [IsRoot, eval_map_algebraMap] at this
  have hm_ne : m ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral g)
  have hdeg_ge : n ≤ m.natDegree := by
    have hle : R ≤ (m.map (algebraMap E L)).roots := (Multiset.le_iff_subset hRnodup).mpr
      fun α hα => by
        rw [mem_roots (Polynomial.map_ne_zero hm_ne), IsRoot, eval_map_algebraMap]
        exact hsub α hα
    calc n = Multiset.card R := hRcard.symm
      _ ≤ _ := Multiset.card_le_card hle
      _ ≤ (m.map (algebraMap E L)).natDegree := card_roots' _
      _ = m.natDegree := natDegree_map _
  have hdeg_le : m.natDegree ≤ n := by
    simpa using (linearIndependent_pow (K := E) g).fintype_card_le_finrank
  have hdeg : m.natDegree = n := le_antisymm hdeg_le hdeg_ge
  haveI : Nonempty (Fin m.natDegree) := ⟨⟨0, by rw [hdeg, hn]; exact Module.finrank_pos⟩⟩
  let pb : PowerBasis E A :=
    { gen := g, dim := m.natDegree
      basis := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_pow g) (by simp [hdeg, m, n])
      basis_eq_pow := fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank] }
  let ι : Type := ↥R.toFinset
  have hcard : Fintype.card ι = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hRnodup, hRcard]
  let P : ι → (A →ₐ[E] L) := fun α => pb.lift α.1 (hsub α.1 (Multiset.mem_toFinset.mp α.2))
  have hP : Function.Injective P := fun a b h => Subtype.ext (by
    have h' : (P a) pb.gen = (P b) pb.gen := congrArg (fun f : A →ₐ[E] L => f pb.gen) h
    simpa only [P, PowerBasis.lift_gen] using h')
  let b0 : Basis ι E A := (Module.finBasisOfFinrankEq E A hcard.symm).reindex (Fintype.equivFin ι).symm
  have hex : ∀ i, ∃ c : nonZeroDivisors O, IsIntegral O ((c : O) • b0 i) := fun i =>
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors O) (b0 i)
      (Algebra.IsIntegral.isIntegral (R := E) (b0 i))
  choose c hc using hex
  let e : Basis ι E A := b0.isUnitSMul (w := fun i => algebraMap O E (c i))
    (fun i => (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (c i).2).isUnit)
  have he : ∀ i, e i = (c i : O) • b0 i := fun i => by
    simp [e, Basis.isUnitSMul_apply, algebraMap_smul]
  have he_int : ∀ i, IsIntegral O (e i) := fun i => (he i) ▸ hc i
  have hdisc : Algebra.discr E e ≠ 0 := fun h =>
    GlobalTheory.algebraMap_discr_basis_ne_zero e hP (by rw [h, map_zero])
  have hnd : (Algebra.traceForm E A).Nondegenerate := by
    have hT : LinearMap.BilinForm.toMatrix e (Algebra.traceForm E A) = Algebra.traceMatrix E e := by
      ext i j
      rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e, hT]
    exact hdisc
  have htr : ∀ x : A, IsIntegral O x → ∃ r : O, algebraMap O E r = Algebra.trace E A x := by
    intro x hx
    have h1 : IsIntegral O (algebraMap E L (Algebra.trace E A x)) := by
      rw [GlobalTheory.algebraMap_trace_eq_sum_algHom_of_card hcard hP x]
      refine IsIntegral.sum _ fun j _ => ?_
      exact hx.map ((P j).restrictScalars O)
    have h2 : IsIntegral O (Algebra.trace E A x) :=
      (isIntegral_algHom_iff ((Algebra.ofId E L).restrictScalars O)
        (algebraMap E L).injective).mp h1
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  set d := (Algebra.traceForm E A).dualBasis hnd e
  have hle : Subalgebra.toSubmodule (integralClosure O A) ≤ Submodule.span O (Set.range d) := by
    intro x hx
    have hx' : IsIntegral O x := hx
    rw [← d.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    obtain ⟨r, hr⟩ := htr _ (hx'.mul (he_int i))
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range d)) hle

end GlobalTheory.IntClosureSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralUnitaryGroupTransitiveNormOneVectors
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.UnitaryTransitive

variable {E : Type} [NormedField E] [StarRing E]

theorem nsub [IsUltrametricDist E] (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]; simpa using IsUltrametricDist.norm_add_le_max a (-b)

def ext0 {r : ℕ} (x : Fin r → E) : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) x 0

@[simp] theorem snocZeroLastCoordinate_castSucc {r : ℕ} (x : Fin r → E) (j : Fin r) : ext0 x j.castSucc = x j := by
  simp [ext0]
@[simp] theorem snocZeroLastCoordinate_last {r : ℕ} (x : Fin r → E) : ext0 x (Fin.last r) = 0 := by
  simp [ext0]

theorem star_snocZeroLastCoordinate_dotProduct {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    star (ext0 x) ⬝ᵥ f = star x ⬝ᵥ (fun j => f j.castSucc) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

theorem dotProduct_snocZeroLastCoordinate {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    f ⬝ᵥ ext0 x = (fun j => f j.castSucc) ⬝ᵥ x := by
  simp [dotProduct, Fin.sum_univ_castSucc]

end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive
variable {E : Type} [Field E] [StarRing E]
theorem rank_one_entry {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (a b : Fin r → E) (m m' : Fin r) :
    (gᴴ * (replicateCol Unit a * replicateRow Unit b) * g) m m' = (gᴴ *ᵥ a) m * (b ᵥ* g) m' := by
  have e : gᴴ * (replicateCol Unit a * replicateRow Unit b) * g =
      replicateCol Unit (gᴴ *ᵥ a) * replicateRow Unit (b ᵥ* g) := by
    rw [Matrix.replicateCol_mulVec, Matrix.replicateRow_vecMul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e]; simp [Matrix.mul_apply]

theorem star_dot_col {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (w : Fin r → E) (m : Fin r) :
    star (star w ⬝ᵥ (fun j => g j m)) = (gᴴ *ᵥ w) m := by
  simp [dotProduct, Matrix.mulVec, star_sum, mul_comm]

theorem dot_col {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (b : Fin r → E) (m : Fin r) :
    b ⬝ᵥ (fun j => g j m) = (b ᵥ* g) m := by
  simp [dotProduct, Matrix.vecMul]
end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive

theorem uO_transitive_of_last_unit (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E) (hv : ∀ i, ‖v i‖ ≤ 1) (h1 : star v ⬝ᵥ v = 1)
    (hn : ‖v (Fin.last r)‖ = 1) : ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  haveI := Unram.ultraE (F := F) (E := E)
  have hst : ∀ x : E, ‖star x‖ = ‖x‖ := Unram.norm_star (F := F)
  set w : Fin r → E := fun j => v j.castSucc with hw
  set G : Matrix (Fin r) (Fin r) E := 1 + replicateCol Unit (-w) * replicateRow Unit (star w) with hG
  have hGe : ∀ i j, G i j = (1 : Matrix (Fin r) (Fin r) E) i j - w i * star (w j) := by
    intro i j; simp [G, Matrix.mul_apply, sub_eq_add_neg]
  have hGh : G.IsHermitian := by
    apply Matrix.IsHermitian.ext; intro i j; rw [hGe, hGe]
    by_cases h : i = j
    · subst h; simp [mul_comm]
    · simp [Matrix.one_apply, h, Ne.symm h, mul_comm]
  have hGi : ∀ i j, ‖G i j‖ ≤ 1 := by
    intro i j; rw [hGe]; refine (nsub _ _).trans (max_le ?_ ?_)
    · by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · rw [norm_mul, hst]; exact mul_le_one₀ (hv _) (norm_nonneg _) (hv _)
  have hsplit : star v ⬝ᵥ v = star w ⬝ᵥ w + star (v (Fin.last r)) * v (Fin.last r) := by
    simp [dotProduct, Fin.sum_univ_castSucc, w]
  have hGd : ‖G.det‖ = 1 := by
    rw [hG, det_one_add_replicateCol_mul_replicateRow, dotProduct_neg]
    have : 1 + -(star w ⬝ᵥ w) = star (v (Fin.last r)) * v (Fin.last r) := by
      linear_combination h1.symm + hsplit
    rw [this, norm_mul, hst, hn]; norm_num
  obtain ⟨g, hgi, -, hg⟩ := _root_.GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj F E r G hGh hGi hGd
  set c : Fin r → E := fun m => star w ⬝ᵥ (fun j => g j m) with hc
  have hg' : ∀ m m', star (fun j => g j m) ⬝ᵥ (fun j => g j m') - star (c m) * c m' = (1 : Matrix (Fin r) (Fin r) E) m m' := by
    intro m m'
    have := congrFun (congrFun hg m) m'
    rw [← this, hG, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.add_apply, rank_one_entry,
      hc, star_dot_col, dot_col, Matrix.mulVec_neg]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, sub_eq_add_neg]
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun i l =>
    Fin.lastCases (motive := fun _ => E) (v i) (fun m => ext0 (fun j => g j m) i - c m * v i) l
  have cl : (fun i => K i (Fin.last r)) = v := by funext i; simp [K]
  have cs : ∀ m, (fun i => K i m.castSucc) = ext0 (fun j => g j m) - c m • v := by
    intro m; funext i; simp [K]
  have key : ∀ a b, (star K * K) a b = star (fun i => K i a) ⬝ᵥ (fun i => K i b) := by
    intro a b; rfl
  have d2 : ∀ m, star v ⬝ᵥ ext0 (fun j => g j m) = c m := by
    intro m; rw [dotProduct_snocZeroLastCoordinate]; rfl
  have d3 : ∀ m, star (ext0 (fun j => g j m)) ⬝ᵥ v = star (c m) := by
    intro m; rw [star_snocZeroLastCoordinate_dotProduct, hc, star_dot_col]; rfl
  have d4 : ∀ m m', star (ext0 (fun j => g j m)) ⬝ᵥ ext0 (fun j => g j m') =
      star (fun j => g j m) ⬝ᵥ (fun j => g j m') := by
    intro m m'; rw [star_snocZeroLastCoordinate_dotProduct]; simp
  have hU : star K * K = 1 := by
    ext a b
    rw [key]
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rw [cl, h1]; simp
      | cast m' =>
        rw [cl, cs, dotProduct_sub, dotProduct_smul, d2, h1, smul_eq_mul, mul_one, sub_self,
          Matrix.one_apply_ne (Fin.castSucc_ne_last m').symm]
    | cast m =>
      induction b using Fin.lastCases with
      | last =>
        rw [cl, cs, star_sub, star_smul, sub_dotProduct, smul_dotProduct, d3, h1]
        simp [Matrix.one_apply, (Fin.castSucc_ne_last m)]
      | cast m' =>
        rw [cs, cs, star_sub, star_smul, sub_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_sub,
          dotProduct_smul, dotProduct_smul, d2, d3, d4, h1]
        have e1 : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) m.castSucc m'.castSucc =
            (1 : Matrix (Fin r) (Fin r) E) m m' := by
          simp [Matrix.one_apply, Fin.castSucc_inj]
        rw [e1, ← hg' m m']
        simp only [smul_eq_mul]
        ring
  refine ⟨⟨K, Matrix.mem_unitaryGroup_iff'.2 hU⟩, ?_, ?_⟩
  · intro i l
    show ‖K i l‖ ≤ 1
    induction l using Fin.lastCases with
    | last => simpa [K] using hv i
    | cast m =>
      simp only [K, Matrix.of_apply, Fin.lastCases_castSucc]
      have hcm : ‖c m‖ ≤ 1 := by
        rw [hc]
        exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun j _ => by
          rw [norm_mul, Pi.star_apply, hst]; exact mul_le_one₀ (hv _) (norm_nonneg _) (hgi _ _))
      refine (nsub _ _).trans (max_le ?_ ?_)
      · induction i using Fin.lastCases with
        | last => simp
        | cast j => simpa using hgi j m
      · rw [norm_mul]; exact mul_le_one₀ hcm (norm_nonneg _) (hv _)
  · show K *ᵥ Pi.single (Fin.last r) 1 = v
    rw [Matrix.mulVec_single_one]; exact cl

end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive

theorem uO_transitive : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 →
    ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  intro F E _ _ _ _ _ r v hv h1
  haveI := Unram.ultraE (F := F) (E := E)
  have hst : ∀ x : E, ‖star x‖ = ‖x‖ := Unram.norm_star (F := F)
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le (Finset.univ : Finset (Fin (r + 1)))
    (fun i => star (v i) * v i)
  have hs : (∑ j, star (v j) * v j) = 1 := h1
  rw [hs, norm_one, norm_mul, hst] at hi
  have hvi : ‖v i‖ = 1 := by nlinarith [hv i, norm_nonneg (v i)]
  set σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap i (Fin.last r) with hσ
  have hσσ : ∀ j, σ (σ j) = j := fun j => Equiv.swap_apply_self _ _ _
  have h1' : star (v ∘ σ) ⬝ᵥ (v ∘ σ) = 1 := by
    rw [← hs]; exact Equiv.sum_comp σ (fun j => star (v j) * v j)
  have hn' : ‖(v ∘ σ) (Fin.last r)‖ = 1 := by simp [hσ, hvi]
  obtain ⟨k, hk, hkv⟩ := uO_transitive_of_last_unit F E r (v ∘ σ) (fun j => hv _) h1' hn'
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) E := k.1.submatrix σ id
  have hU : star K * K = 1 := by
    have hk1 : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
    ext a b
    rw [← hk1]
    simp only [K, Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, id]
    exact Equiv.sum_comp σ (fun j => star (k.1 j a) * k.1 j b)
  refine ⟨⟨K, Matrix.mem_unitaryGroup_iff'.2 hU⟩, fun a b => hk (σ a) b, ?_⟩
  show K *ᵥ Pi.single (Fin.last r) 1 = v
  funext j
  have := congrFun hkv (σ j)
  rw [Matrix.mulVec_single_one] at this ⊢
  simpa [K, hσσ] using this

end GlobalTheory.UnitaryTransitive
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobRestrictScalarsOfPrimeAbsNormStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrob_restrictScalars_of_prime_absNorm' : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Z : IntermediateField F Ω) [NumberField Z] (w : HeightOneSpectrum (𝓞 Z)) (v : HeightOneSpectrum (𝓞 F)), w.asIdeal.LiesOver v.asIdeal → (Ideal.absNorm w.asIdeal).Prime → ∀ B : ValuationSubring Ω, IsPlaceOver (F := Z) B w → ∀ σ : G Z Ω, IsFrob B (normV w) σ → Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal ∧ IsPlaceOver (F := F) B v ∧ IsFrob (F := F) B (normV v) (σ.restrictScalars F) := by
  first | exact @GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | exact GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | (intros; apply GlobalTheory.isFrob_restrictScalars_of_prime_absNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  first | exact @GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | exact GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | (intros; apply GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfLieReg
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem InvAlg.isReduced_of_lieReg : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A :=
  fun _ B h => GlobalTheory.SepGen.isReduced B.g h.2

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPowGeneratorEqTopOfCharpolySeparableStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  first | exact @GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable | exact GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable | (intros; apply GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationExistsEtaleOfSubsingletonStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Subsingleton A.K → WeilAt A := by
  first | exact @GlobalTheory.JR.weilAt_of_subsingleton | exact GlobalTheory.JR.weilAt_of_subsingleton | (intros; apply GlobalTheory.JR.weilAt_of_subsingleton <;> assumption)
end

