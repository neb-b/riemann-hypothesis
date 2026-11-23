module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarProperSubmoduleEqZeroModuleTopologyStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ s : Submodule F V, s ≠ ⊤ → μ (s : Set V) = 0 := by
  first | exact @GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero | exact GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero | (intros; apply GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaOrderOne
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

theorem norm_mulVec_le_one_of_integral_matrix {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (x : m → F) (hx : Integral x) (i : m) :
    ‖A.mulVec x i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hA i j) (norm_nonneg _) (hx j)

theorem integralNormVector_pow_sub_mulVec {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (q : ℕ) (x : m → F) (hx : Integral x) :
    Integral (fun i => x i ^ q - A.mulVec x i) := by
  intro i
  have h1 : ‖x i ^ q‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx i)
  have h2 := norm_mulVec_le_one_of_integral_matrix A hA x hx i
  calc ‖x i ^ q - A.mulVec x i‖ = ‖x i ^ q + -A.mulVec x i‖ := by rw [sub_eq_add_neg]
    _ ≤ max ‖x i ^ q‖ ‖-A.mulVec x i‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := by rw [norm_neg]; exact max_le h1 h2

theorem additiveSystemFrobeniusPowerSum_zero {F : Type} [NormedField F] {m : Type} [Fintype m] (q D : ℕ) (hq : 0 < q)
    (U : ℕ → Matrix m m F) : gsum q D U (fun _ => 0) = 0 := by
  unfold gsum
  refine Finset.sum_eq_zero (fun n _ => ?_)
  have : (fun _ : m => (0 : F) ^ q ^ n) = 0 := by
    funext i; simp [zero_pow (pow_pos hq n).ne']
  rw [this, Matrix.mulVec_zero]

theorem gl1 : GLOnto 1 ∧ GLCount 1 := by
  constructor
  · intro F _ _ _ _ p _ _ m _ _ e D he hD M hM b hb
    obtain ⟨A, U, hA, hU0, hUn, -, hfac⟩ := _root_.GlobalTheory.PMonE.preparation F p m e D he hD M hM
    obtain ⟨y, ⟨hy, hyb⟩, -⟩ := GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq F p m e D he U hU0 hUn b hb
    obtain ⟨x, hx, hxy⟩ := _root_.GlobalTheory.PMonE.LangOnto.lang_onto F p m e he A hA y hy
    refine ⟨x, hx, ?_⟩
    rw [hfac]
    have : (fun i => x i ^ p ^ e - A.mulVec x i) = y := funext hxy
    rw [this, hyb]
  · intro F _ _ _ _ p _ _ m _ _ e D he hD M hM hdet
    obtain ⟨A, U, hA, hU0, hUn, hM0, hfac⟩ := _root_.GlobalTheory.PMonE.preparation F p m e D he hD M hM
    have hAdet : A.det ≠ 0 := by
      intro h
      apply hdet
      rw [hM0, Matrix.det_neg, Matrix.det_mul, h, mul_zero, mul_zero]
    obtain ⟨hInt, hcard⟩ := _root_.GlobalTheory.PMonE.langCount F p m e he A hA hAdet
    have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
    obtain ⟨z, -, hz⟩ := GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq F p m e D he U hU0 hUn 0 (fun i => by simp)
    have key : ∀ x : m → F, Integral x →
        (gsum (p ^ e) D M x = 0 ↔ ∀ i, x i ^ p ^ e = A.mulVec x i) := by
      intro x hx
      rw [hfac]
      constructor
      · intro h0
        have h1 := hz _ ⟨integralNormVector_pow_sub_mulVec A hA (p ^ e) x hx, h0⟩
        have h2 := hz (fun _ => 0) ⟨fun i => by simp, additiveSystemFrobeniusPowerSum_zero _ D hq U⟩
        intro i
        have := congrFun (h1.trans h2.symm) i
        exact sub_eq_zero.mp this
      · intro h
        have : (fun i => x i ^ p ^ e - A.mulVec x i) = fun _ => 0 := funext fun i => by rw [h i, sub_self]
        rw [this]
        exact additiveSystemFrobeniusPowerSum_zero _ D hq U
    have eqv : {x : m → F // Integral x ∧ gsum (p ^ e) D M x = 0} ≃
        {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} :=
      { toFun := fun x => ⟨x.1, (key x.1 x.2.1).mp x.2.2⟩
        invFun := fun x => ⟨x.1, hInt x.1 x.2, (key x.1 (hInt x.1 x.2)).mpr x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [Nat.card_congr eqv, hcard, mul_one]

end GlobalTheory.PMonE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable
section
open Polynomial

namespace GlobalTheory.SepGen

variable {E : Type} [Field E] {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A]

theorem charpoly_dvd (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) (f : E[X])
    (hf : aeval y f = 0) : (LinearMap.mulLeft E y).charpoly ∣ f := by
  have h0 : aeval (LinearMap.mulLeft E y) f = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul E A) y f
    rw [hf, map_zero] at this
    exact this
  by_cases hz : f = 0
  · rw [hz]; exact dvd_zero _
  classical
  have hP := hs.ne_zero
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
    Multiset.le_iff_subset
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
  intro p hp
  rw [Polynomial.mem_normalizedFactors_iff hP] at hp
  rw [Polynomial.mem_normalizedFactors_iff hz]
  exact ⟨hp.1, hp.2.1,
    GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩

theorem aeval_charpoly (y : A) : aeval y (LinearMap.mulLeft E y).charpoly = 0 := by
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul E A) y (LinearMap.mulLeft E y).charpoly
  have h2 : aeval (Algebra.lmul E A y) (LinearMap.mulLeft E y).charpoly = 0 :=
    LinearMap.aeval_self_charpoly _
  rw [h2] at h
  simpa using (LinearMap.congr_fun h 1).symm

theorem adjoin_eq_top (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) :
    Algebra.adjoin E ({y} : Set A) = ⊤ := by
  have hi : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  have h1 := natDegree_le_of_dvd (charpoly_dvd y hs _ (minpoly.aeval E y)) (minpoly.ne_zero hi)
  rw [LinearMap.charpoly_natDegree] at h1
  have h2 : Module.finrank E (Algebra.adjoin E ({y} : Set A)) = (minpoly E y).natDegree :=
    (Algebra.adjoin.powerBasis hi).finrank
  have h3 : Subalgebra.toSubmodule (Algebra.adjoin E ({y} : Set A)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h1.trans h2.ge))
  rw [← Algebra.toSubmodule_eq_top]
  exact h3

theorem isReduced (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) : IsReduced A := by
  have h3 := adjoin_eq_top y hs
  refine ⟨fun z ⟨k, hk⟩ => ?_⟩
  have hz : z ∈ Algebra.adjoin E ({y} : Set A) := by rw [h3]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, rfl⟩ := hz
  have h4 := charpoly_dvd y hs (p ^ k) (by rw [map_pow]; exact hk)
  obtain ⟨r, hr⟩ := hs.squarefree.isRadical k p h4
  change aeval y p = 0
  rw [hr, map_mul, aeval_charpoly, zero_mul]

theorem adjoin_eq_top_and_isReduced : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (y : A), (LinearMap.mulLeft E y).charpoly.Separable →
    Algebra.adjoin E ({y} : Set A) = ⊤ ∧ IsReduced A :=
  fun _ _ _ _ _ _ y hs => ⟨adjoin_eq_top y hs, isReduced y hs⟩

end GlobalTheory.SepGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeft
section
open Polynomial

namespace GlobalTheory

theorem etale_of_separable_charpoly_mulLeft (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (h : (LinearMap.mulLeft E g).charpoly.Separable) :
    Algebra.Etale E A := by
  have hd := GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable (LinearMap.mulLeft E g) h
  have h2 : minpoly E (LinearMap.mulLeft E g) = minpoly E g :=
    minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective) g
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm : (minpoly E g).Monic := minpoly.monic hint
  have hd' : minpoly E g ∣ (LinearMap.mulLeft E g).charpoly := by
    rw [← h2]; exact LinearMap.minpoly_dvd_charpoly _
  rw [h2] at hd
  have heq : minpoly E g = (LinearMap.mulLeft E g).charpoly :=
    eq_of_monic_of_associated hm (LinearMap.charpoly_monic _) (associated_of_dvd_dvd hd' hd)
  have hsep : (minpoly E g).Separable := heq ▸ h
  have hdeg : (minpoly E g).natDegree = Module.finrank E A := by
    rw [heq, LinearMap.charpoly_natDegree]
  haveI : Module.Finite E (AdjoinRoot (minpoly E g)) := hm.finite_adjoinRoot
  let φ : AdjoinRoot (minpoly E g) →ₐ[E] A := AdjoinRoot.liftAlgHom (minpoly E g) (Algebra.ofId E A) g (minpoly.aeval E g)
  have hli : LinearIndependent E fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ) :=
    linearIndependent_pow g
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp [hdeg])
  have hsurj : Function.Surjective φ.toLinearMap := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨AdjoinRoot.root (minpoly E g) ^ (i : ℕ), ?_⟩
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', AlgHom.toLinearMap_apply, map_pow]
    congr 1
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hfr : Module.finrank E (AdjoinRoot (minpoly E g)) = Module.finrank E A := by
    rw [(AdjoinRoot.powerBasis' hm).finrank]; simpa using hdeg
  have hinj : Function.Injective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj
  let e : AdjoinRoot (minpoly E g) ≃ₐ[E] A := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hu : IsUnit (AdjoinRoot.mk (minpoly E g) (minpoly E g).derivative) := by
    obtain ⟨a, c, hac⟩ := hsep
    have := congrArg (AdjoinRoot.mk (minpoly E g)) hac
    rw [map_add (f := _), map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact this⟩
  have := GlobalTheory.etale_adjoinRoot_of_isUnit_derivative hm hu
  exact Algebra.Etale.of_equiv e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedConjugationDiagOneLiftBlockMatrix
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step.ActEmbLift

theorem embHom_mul_full_mul (k : Type) [CommRing k] (r : ℕ) (g h : Matrix (Fin r) (Fin r) k) (Z : Gl r k) :
    embHom r k g * full Z * embHom r k h = full (g * Z.1 * h, g *ᵥ Z.2.1, Z.2.2.1 ᵥ* h, Z.2.2.2) := by
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, full, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]

theorem embHom_mulVec_eL (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    embHom r k g *ᵥ eL r k = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.mulVec_single_one]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

theorem eL_vecMul_embHom (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    eL r k ᵥ* embHom r k g = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.single_one_vecMul]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

theorem act_emb_lift (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k) :
    act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  have hinv : ((emb r k g)⁻¹ : GL (Fin (r + 1)) k) = emb r k g⁻¹ := (map_inv _ _).symm
  simp only [act, lift, hinv, emb, Units.coe_map, MonoidHom.coe_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact embHom_mul_full_mul k r _ _ Z
  · simp only [Matrix.mulVec_smul, embHom_mulVec_eL]
  · exact eL_vecMul_embHom k r _

end GlobalTheory.JR.Step.ActEmbLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedInvariantsAndHankelDetMapRingHomStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.borderedInvariants_and_hankelDet_map_ringHom : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ), (∀ Y : Gl r k, inv (GlobalTheory.JR.Step.glMap φ Y) = (inv Y).map φ) ∧ (∀ a : Inv r k, Delta (a.map φ) = φ (Delta a)) := by
  first | exact @GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | exact GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | (intros; apply GlobalTheory.JR.Step.InvMap.inv_and_Delta_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedMatrixInvariantSpaceExistsCompactOpenSubStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.borderedMatrixInvariantSpace_exists_compact_open_subset : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F), IsOpen U → a₀ ∈ U → ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := by
  first | exact @GlobalTheory.InverseCompactOpen.inv_exists_compact_open | exact GlobalTheory.InverseCompactOpen.inv_exists_compact_open | (intros; apply GlobalTheory.InverseCompactOpen.inv_exists_compact_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittSemisimpleMatrixRepresentations
section
open scoped BigOperators

namespace GlobalTheory.BrauerNesbittMatrix

def colRep {k G : Type} [Field k] [Monoid G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) k) :
    Representation k G (Fin n → k) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom.toRingHom.toMonoidHom.comp ρ

theorem colRep_apply {k G : Type} [Field k] [Monoid G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) k) (g : G) :
    colRep ρ g = Matrix.toLin' (ρ g) := rfl

theorem colRep_asAlgebraHom {k G : Type} [Field k] [Monoid G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) k)
    (a : MonoidAlgebra k G) :
    (colRep ρ).asAlgebraHom a = Matrix.toLin' (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a) := by
  have : (colRep ρ).asAlgebraHom =
      (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom.comp
        (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ) := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp [Representation.asAlgebraHom_single, colRep_apply]
      rfl
    · exact Subsingleton.elim _ _
  rw [this]
  rfl

theorem colRep_semisimple {k G : Type} [Field k] [Monoid G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) k)
    (h : ∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (ρ g).mulVec v ∈ W') :
    (colRep ρ).IsSemisimpleRepresentation := by
  refine ⟨fun P => ?_⟩
  obtain ⟨W', h2, h1⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
  refine ⟨⟨W', fun g v hv => h1 g v hv⟩, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h2
  exact h2

theorem main : ∀ {k G : Type} [Field k] [Group G] (n : ℕ) (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (ρ g).mulVec v ∈ W') → (∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (σ g).mulVec v ∈ W) → ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (σ g).mulVec v ∈ W') → (∀ g, (ρ g).charpoly = (σ g).charpoly) → ∃ P : GL (Fin n) k, ∀ g, (P : Matrix (Fin n) (Fin n) k) * ρ g = σ g * P := by
  intro k G _ _ n ρ σ hρ hσ hc
  obtain ⟨e, he⟩ := GlobalTheory.T.brauerNesbitt_exists_equiv_of_charpoly_eq' (colRep ρ) (colRep σ) (colRep_semisimple ρ hρ) (colRep_semisimple σ hσ)
    fun a => by
      rw [colRep_asAlgebraHom, colRep_asAlgebraHom, Matrix.charpoly_toLin', Matrix.charpoly_toLin']
      exact _root_.GlobalTheory.charpoly_lift_eq_of_charpoly_eq n ρ σ hc a
  let P : GL (Fin n) k :=
    ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨P, fun g => ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  have hh : Matrix.toLin' (P : Matrix (Fin n) (Fin n) k) = e.toLinearMap := Matrix.toLin'_toMatrix' _
  rw [hh]
  refine LinearMap.ext fun v => ?_
  have := he g v
  rw [colRep_apply, colRep_apply] at this
  exact this

end GlobalTheory.BrauerNesbittMatrix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardClProdFiniteAlgebraWithInvolution
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section
namespace GlobalTheory.UnitLemma.InvAlg.ClProd

variable {K : UQ} (B₁ B₂ : InvAlg K)

def mkU (a : B₁.Aˣ) (b : B₂.Aˣ) : (B₁.prod B₂).Aˣ where
  val := ((a : B₁.A), (b : B₂.A))
  inv := (((a⁻¹ : B₁.Aˣ) : B₁.A), ((b⁻¹ : B₂.Aˣ) : B₂.A))
  val_inv := Prod.ext a.mul_inv b.mul_inv
  inv_val := Prod.ext a.inv_mul b.inv_mul

def u₁ (x : (B₁.prod B₂).Aˣ) : B₁.Aˣ := Units.map (RingHom.fst B₁.A B₂.A).toMonoidHom x

def u₂ (x : (B₁.prod B₂).Aˣ) : B₂.Aˣ := Units.map (RingHom.snd B₁.A B₂.A).toMonoidHom x

def toPair : (B₁.prod B₂).Cl → B₁.Cl × B₂.Cl :=
  Quot.lift (fun x => (Quot.mk _ ⟨u₁ B₁ B₂ x.1, congrArg Prod.fst x.2⟩,
      Quot.mk _ ⟨u₂ B₁ B₂ x.1, congrArg Prod.snd x.2⟩)) (by
    rintro x y ⟨u, hu⟩
    refine Prod.ext (Quot.sound ⟨u₁ B₁ B₂ u, congrArg Prod.fst hu⟩)
      (Quot.sound ⟨u₂ B₁ B₂ u, congrArg Prod.snd hu⟩))

def ofPair : B₁.Cl × B₂.Cl → (B₁.prod B₂).Cl := fun p =>
  Quot.lift₂ (r := _) (s := _) (fun (a : {x : B₁.Aˣ // B₁.σ (x : B₁.A) = x})
      (b : {x : B₂.Aˣ // B₂.σ (x : B₂.A) = x}) =>
      (Quot.mk _ ⟨mkU B₁ B₂ a.1 b.1, Prod.ext a.2 b.2⟩ : (B₁.prod B₂).Cl))
    (by
      rintro a b c ⟨u, hu⟩
      exact Quot.sound ⟨mkU B₁ B₂ 1 u, Prod.ext
        (show ((a.1 : B₁.Aˣ) : B₁.A) = a.1 * (((1 : B₁.Aˣ) : B₁.A) * B₁.σ ((1 : B₁.Aˣ) : B₁.A)) by simp) hu⟩)
    (by
      rintro a b c ⟨u, hu⟩
      exact Quot.sound ⟨mkU B₁ B₂ u 1, Prod.ext hu
        (show ((c.1 : B₂.Aˣ) : B₂.A) = c.1 * (((1 : B₂.Aˣ) : B₂.A) * B₂.σ ((1 : B₂.Aˣ) : B₂.A)) by simp)⟩) p.1 p.2

def clEquiv : (B₁.prod B₂).Cl ≃ B₁.Cl × B₂.Cl where
  toFun := toPair B₁ B₂
  invFun := ofPair B₁ B₂
  left_inv := by
    intro k
    induction k using Quot.ind with
    | mk x => rfl
  right_inv := by
    rintro ⟨k₁, k₂⟩
    induction k₁ using Quot.ind with
    | mk a => induction k₂ using Quot.ind with
      | mk b => rfl

theorem card_cl_prod (K : UQ) (B₁ B₂ : InvAlg K) :
    Nat.card (B₁.prod B₂).Cl = Nat.card B₁.Cl * Nat.card B₂.Cl := by
  rw [Nat.card_congr (clEquiv B₁ B₂), Nat.card_prod]

end GlobalTheory.UnitLemma.InvAlg.ClProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosEqIntegralAdditiveSystemStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F), (∀ j, π j ≠ 0) → ∀ (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F), (∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) → Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} = Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  first | exact @GlobalTheory.PMonE.winPt_card | exact GlobalTheory.PMonE.winPt_card | (intros; apply GlobalTheory.PMonE.winPt_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnHermitianBlockMatrixOfInvariantsStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_hermitianBlockMatrixOfInvariants : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E), ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det) → ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := by
  first | exact @GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det | exact GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det | (intros; apply GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMassStatement
section
open GlobalTheory.UnimodMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass : ∀ (G : Type) [Group G] (Γ W K : Subgroup G), W ≤ K → Finite (GlobalTheory.UnimodMass.DC Γ W) → (∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) → W.relIndex K ≠ 0 ∧ GlobalTheory.UnimodMass.mass Γ W = (W.relIndex K : ℚ) * GlobalTheory.UnimodMass.mass Γ K := by
  first | exact @GlobalTheory.UnimodMass.mass_eq_relIndex_mul | exact GlobalTheory.UnimodMass.mass_eq_relIndex_mul | (intros; apply GlobalTheory.UnimodMass.mass_eq_relIndex_mul <;> assumption)
end

