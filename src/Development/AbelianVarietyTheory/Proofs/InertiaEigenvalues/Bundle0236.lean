module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LocalIntegers

theorem finite_quotient_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (n : ℕ) : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n}) := by
  have h : Ideal.span {((l : ℕ) : O) ^ n} =
      (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O) := by
    simp [Ideal.map_span]
  rw [h]
  haveI : Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}) := by
    rw [← PadicInt.ker_toZModPow]
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact Finite.of_injective _ (RingHom.kerLift_injective (PadicInt.toZModPow (p := l) n))
  haveI : Module.Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})
      (O ⧸ (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  exact Module.finite_of_finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})

theorem isOpen_integers (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    IsOpen (Set.range (algebraMap ↥(OL LL) ↥LL.1)) := by
  have h : Set.range (algebraMap ↥(OL LL) ↥LL.1) =
      (fun x : ↥LL.1 => (x : PadicAlgCl l)) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    rw [Set.mem_preimage, mem_closedBall_zero_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage continuous_subtype_val

theorem good_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) ∧ ∀ n : ℕ, Finite (↥(OL LL) ⧸ Ideal.span {((l : ℕ) : ↥(OL LL)) ^ n}) := by
  intro l _ LL
  haveI := LL.2
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := finite_integralClosure_padicInt l ↥LL.1
  haveI : ContinuousSMul ℚ_[l] ↥LL.1 :=
    Topology.IsInducing.continuousSMul (f := id) (g := fun x : ↥LL.1 => (x : PadicAlgCl l))
      Topology.IsInducing.subtypeVal continuous_id rfl
  haveI : IsTopologicalRing ↥LL.1 := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  refine ⟨⟨⟨inferInstance, isDiscreteValuationRing_integralClosure_padicInt l ↥LL.1,
    isFractionRing_integralClosure_padicInt l ↥LL.1⟩, LL.2, isModuleTopologyOfFiniteDimensional,
    inferInstance, isOpen_integers l LL⟩, finite_quotient_pow l _⟩

end GlobalTheory.LocalIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

open scoped Topology

theorem fixingSubgroupEquiv_bicontinuous (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] :
    Continuous (IntermediateField.fixingSubgroupEquiv K) ∧
      Continuous (IntermediateField.fixingSubgroupEquiv K).symm := by
  refine ⟨continuous_of_continuousAt_one _ ?_, continuous_of_continuousAt_one _ ?_⟩
  · rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro s hs
    obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
    have : IsScalarTower k K E := ⟨fun a b x => Subtype.ext (smul_assoc a b (x : Ω))⟩
    have hE' : Module.Finite k E := Module.Finite.trans K E
    have hfin : FiniteDimensional k (E.restrictScalars k) := hE'
    rw [mem_nhds_subtype]
    refine ⟨(E.restrictScalars k).fixingSubgroup,
      (krullTopology_mem_nhds_one_iff k Ω _).2 ⟨E.restrictScalars k, hfin, subset_rfl⟩, ?_⟩
    intro σ hσ
    apply hEs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx
  · rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro s hs
    obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).1 hs
    obtain ⟨E, hE, hEu⟩ := (krullTopology_mem_nhds_one_iff k Ω u).1 hu
    let F : IntermediateField K Ω := IntermediateField.extendScalars (le_sup_right : K ≤ E ⊔ K)
    have hk : FiniteDimensional k (E ⊔ K : IntermediateField k Ω) := inferInstance
    have : Module.Finite k F := hk
    have hF : FiniteDimensional K F := Module.Finite.of_restrictScalars_finite k K F
    refine (krullTopology_mem_nhds_one_iff K Ω _).2 ⟨F, hF, ?_⟩
    intro τ hτ
    apply hus
    apply hEu
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      ((IntermediateField.mem_extendScalars _).2 (le_sup_left (a := E) hx))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSubMulSurjective
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

namespace GlobalTheory.ArtinSchreierWitt

open Polynomial

theorem frob_sub_mul_surjective (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p]
    [PerfectRing k p] (h : ∀ c y : k, ∃ x : k, x ^ p - c * x = y) (c y : WittVector p k) :
    ∃ β : WittVector p k, WittVector.frobenius β - c * β = y := by
  have hc : IsAdicComplete (Ideal.span {(p : ℤ)}) (WittVector p k) := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := WittVector p k), Ideal.map_span,
      Set.image_singleton, map_natCast]
    infer_instance
  let f : WittVector p k →ₗ[ℤ] WittVector p k :=
    (WittVector.frobenius (p := p) (R := k)).toAddMonoidHom.toIntLinearMap
      - (AddMonoidHom.mulLeft c).toIntLinearMap
  have hf : ∀ β, f β = WittVector.frobenius β - c * β := fun β => rfl
  have hs : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ)}) fun G => ?_
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
    obtain ⟨x, hx⟩ := h (c.coeff 0) (g.coeff 0)
    refine ⟨WittVector.teichmuller p x, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hf]
    have h0 : (WittVector.frobenius (WittVector.teichmuller p x)
        - c * WittVector.teichmuller p x - g) ∈ Ideal.span {(p : WittVector p k)} := by
      rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_sub, map_mul]
      simp only [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
        WittVector.teichmuller_coeff_zero]
      rw [hx, sub_self]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h0
    rw [hu]
    have : (p : WittVector p k) * u = (p : ℤ) • u := by simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨β, hβ⟩ := hs y
  exact ⟨β, (hf β).symm.trans hβ⟩

theorem monic_as (p : ℕ) [hp : Fact p.Prime] {k : Type} [CommRing k] [Nontrivial k] (c y : k) :
    (X ^ p - (C c * X + C y) : k[X]).Monic ∧ (X ^ p - (C c * X + C y) : k[X]).degree = p := by
  have h1 : (C c * X + C y : k[X]).degree < (p : WithBot ℕ) :=
    lt_of_le_of_lt degree_linear_le (by exact_mod_cast hp.out.one_lt)
  refine ⟨monic_X_pow_sub h1, ?_⟩
  rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]

theorem exists_root_field (p : ℕ) [hp : Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K]
    (c y : K) : ∃ x : K, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ p - (C c * X + C y) : K[X]) (by
    rw [(monic_as p c y).2]; exact_mod_cast hp.out.ne_zero)
  refine ⟨x, ?_⟩
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_add, eval_mul, eval_C] at hx
  linear_combination hx

theorem exists_root_ring (p : ℕ) [hp : Fact p.Prime] {O K : Type} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [IsAlgClosed K]
    (c y : O) : ∃ x : O, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := exists_root_field p (algebraMap O K c) (algebraMap O K y)
  have hi : IsIntegral O x := by
    refine ⟨X ^ p - (C c * X + C y), (monic_as p c y).1, ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    linear_combination hx
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  refine ⟨z, IsFractionRing.injective O K ?_⟩
  rw [map_sub, map_pow, map_mul, hx]

theorem fixed_frob (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (b : WittVector p K)
    (hb : WittVector.map (frobenius K p) b = b) : ∃ z : ℤ_[p], b = zlW p K z := by
  have h : ∀ n, ∃ a : ZMod p, ZMod.castHom (dvd_refl p) K a = b.coeff n := by
    intro n
    have h1 : (b.coeff n) ^ p = b.coeff n := by
      have := congrArg (fun w => WittVector.coeff w n) hb
      simpa [WittVector.map_coeff, frobenius_def] using this
    have h2 := (Subfield.mem_bot_iff_pow_eq_self K p).2 h1
    have h3 : (⊥ : Subfield K) ≤ (ZMod.castHom (dvd_refl p) K).fieldRange := bot_le
    exact h3 h2
  choose a ha using h
  refine ⟨WittVector.equiv p (WittVector.mk p a), ?_⟩
  ext n
  simp [zlW, WittVector.map_coeff, ← ha]

theorem main : ∀ (l : ℕ) [Fact l.Prime], (∀ y : WCb l, ∃ b, frobW l b - b = y) ∧ (∀ b : WCb l, frobW l b = b → ∃ z : ℤ_[l], b = algebraMap ℤ_[l] (WCb l) z) ∧ ∀ (c p : Ainf l), ∃ β : Ainf l, WittVector.frobenius β - c * β = p := by
  intro l _
  obtain ⟨hK, hV⟩ := _root_.GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l
  refine ⟨fun y => ?_, fun b hb => fixed_frob l (Cb l) b hb, fun c p => ?_⟩
  · obtain ⟨β, hβ⟩ := frob_sub_mul_surjective l (Cb l) (exists_root_field l) 1 y
    refine ⟨β, ?_⟩
    rw [one_mul, WittVector.frobenius_eq_map_frobenius] at hβ
    exact hβ
  · exact frob_sub_mul_surjective l (OCb l) (exists_root_ring l (K := Cb l)) c p

end GlobalTheory.ArtinSchreierWitt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrobIntegralCoeff

section Generic

variable {R O : Type} [CommRing R] [CommRing O] [Algebra R O] {I : Type} [Fintype I] [DecidableEq I]
  (b : Module.Basis I R O)

def regRep (W : Type) [CommRing W] [Algebra R W] : O ⊗[R] W →ₐ[R] Matrix I I W :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId R W)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom R W (Matrix I I W))
    (fun _ w => (Algebra.commutes w _).symm)

variable {W W' : Type} [CommRing W] [Algebra R W] [CommRing W'] [Algebra R W']

theorem regRep_tmul (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = Algebra.leftMulMatrix b o i j • w := by
  erw [Algebra.TensorProduct.lift_tmul]
  simp [Algebra.smul_def, Matrix.algebraMap_eq_diagonal, Matrix.mul_diagonal, mul_comm]

theorem regRep_map (f : W →ₐ[R] W') (z : O ⊗[R] W) (i j : I) :
    regRep b W' (Algebra.TensorProduct.map (AlgHom.id O O) f z) i j = f (regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, regRep_tmul, regRep_tmul, map_smul]
  | add x y hx hy => simp [map_add (f := _), Matrix.add_apply, hx, hy]

private theorem regRep_tmul' (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = b.repr (o * b j) i • w := by
  rw [regRep_tmul, Algebra.leftMulMatrix_eq_repr_mul]

theorem eq_sum_regRep (z : O ⊗[R] W) :
    z = ∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp_rw [regRep_tmul', ← TensorProduct.smul_tmul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, ← TensorProduct.sum_tmul, b.sum_repr, TensorProduct.smul_tmul',
      ← TensorProduct.sum_tmul]
    congr 1
    simp_rw [← mul_smul_comm, ← Finset.mul_sum, b.sum_repr, mul_one]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp [map_add (f := _), Matrix.add_apply, TensorProduct.tmul_add, smul_add, Finset.sum_add_distrib]

theorem mem_range_of_regRep (f : W →ₐ[R] W') (z : O ⊗[R] W')
    (h : ∀ i j, regRep b W' z i j ∈ Set.range f) :
    z ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  choose g hg using h
  refine ⟨∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] g i j), ?_⟩
  conv_rhs => rw [eq_sum_regRep b z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [TensorProduct.smul_tmul', map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hg]

def blow {p q : Type} (Z : Matrix p q (O ⊗[R] W)) : Matrix (p × I) (q × I) W :=
  Matrix.of fun x y => regRep b W (Z x.1 y.1) x.2 y.2

theorem blow_map {p q : Type} (f : W →ₐ[R] W') (Z : Matrix p q (O ⊗[R] W)) :
    blow b (Z.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) = (blow b Z).map f := by
  ext x y
  simp [blow, regRep_map]

theorem blow_add {p q : Type} (Z Z' : Matrix p q (O ⊗[R] W)) :
    blow b (Z + Z') = blow b Z + blow b Z' := by
  ext x y
  simp [blow, map_add (f := _)]

theorem blow_mul {p q r : Type} [Fintype q] (Z : Matrix p q (O ⊗[R] W))
    (Z' : Matrix q r (O ⊗[R] W)) : blow b (Z * Z') = blow b Z * blow b Z' := by
  ext x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [blow, Matrix.mul_apply, map_sum, Matrix.sum_apply, Fintype.sum_prod_type]


omit b [Fintype I] [DecidableEq I] in
theorem integrality_baseChange [Module.Free R O] [Module.Finite R O] (f : W →ₐ[R] W')
    (φ : W' →ₐ[R] W')
    (H : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q W') (S : Matrix p p W)
      (S' : Matrix q q W) (Y : Matrix p q W),
      Z.map φ = S.map f * Z * S'.map f + Y.map f → ∀ a b, Z a b ∈ Set.range f)
    (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (O ⊗[R] W')) (S : Matrix p p (O ⊗[R] W))
    (S' : Matrix q q (O ⊗[R] W)) (Y : Matrix p q (O ⊗[R] W))
    (h : Z.map (Algebra.TensorProduct.map (AlgHom.id O O) φ) =
      S.map (Algebra.TensorProduct.map (AlgHom.id O O) f) * Z *
        S'.map (Algebra.TensorProduct.map (AlgHom.id O O) f) +
      Y.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) (x : p) (y : q) :
    Z x y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R (O ⊗[R] W')
    exact ⟨0, Subsingleton.elim _ _⟩
  classical
  let c := Module.Free.chooseBasis R O
  have key := congrArg (blow c) h
  rw [blow_map, blow_add, blow_mul, blow_mul, blow_map, blow_map, blow_map] at key
  apply mem_range_of_regRep c f (Z x y)
  intro i j
  exact H _ _ (blow c Z) (blow c S) (blow c S') (blow c Y) key (x, i) (y, j)

private theorem module_free_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Free ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  have : Module.IsTorsionFree ℤ_[l] K := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  exact IsIntegralClosure.module_free ℤ_[l] ℚ_[l] K _

private theorem module_finite_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Finite ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] K _

end Generic

theorem frobenius_integrality_coeff : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (RW LL)) (S : Matrix p p (RA LL)) (S' : Matrix q q (RA LL)) (Y : Matrix p q (RA LL)), Z.map (φRW LL) = S.map (inclR LL) * Z * S'.map (inclR LL) + Y.map (inclR LL) → ∀ a b, Z a b ∈ Set.range (inclR LL) := by
  intro l _ LL p q _ _ Z S S' Y h a b
  unfold RW RA inclR φRW at *
  have := module_free_zpadic_OL l LL
  have := module_finite_zpadic_OL l LL
  exact integrality_baseChange (R := ℤ_[l]) (O := OL LL) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => _root_.GlobalTheory.FrobInt.frobenius_integrality l p q Z S S' Y h) p q Z S S' Y h a b

end GlobalTheory.FrobIntegralCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepWeilJumps
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory
open Formalism.MainNotions.SumRepresentations.At

section Tw
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (g : Γ) :
    ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det • ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := by
  simp only [twGL, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_map]
  simp [Algebra.algebraMap_eq_smul_one, Matrix.GeneralLinearGroup.val_det_apply]

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have hu : ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _).1 (χ g).isUnit |>.ne_zero
    have := W.smul_mem (((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det)⁻¹ (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hu, one_smul] at this
    exact this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (h : IsSSRep ρ) :
    IsSSRep (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 hW', hc⟩

end Tw

theorem contQ_twGL (D : D7) (i : D.nd.Loc) {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)))
    (χ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) (hρ : ContQ D.nd i ρ) (hχ : ContQ D.nd i χ) :
    ContQ D.nd i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  unfold ContQ at *
  simp only [twGL_val]
  exact (hχ.matrix_det).smul hρ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionSubMemSpanPowSuccStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaAction_sub_mem_span_pow_succ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ g ∈ W.GKs, ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ k, W.γA (W.resΓ g) a - a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ (k + 1) := by
  intro D HW l _ K s LL h W g hg
  have hχ := (W.GKs_def g).1 hg
  rw [← W.χΓ_res g] at hχ
  have hs : (1 : WithTop ℚ) ≤ (W.s : WithTop ℚ) := by exact_mod_cast W.s_pos
  obtain ⟨c, hc⟩ := GlobalTheory.GamFilt.exists_eq_one_add (D.loc l) LL _ (hs.trans hχ)
  exact GlobalTheory.GamFilt.letγ_sub_mem (W.γ₀ (W.resΓ g)) l c
    (W.γ₀_X _).1 ((W.γ₀_X _).2.trans hc)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegree
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.TrIdem

theorem zOf_coeff {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (y : G) :
    (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem coeff_mul_zOf_one {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ := by
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum_fintype _ _ (by simp)]
  simp only [tr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [zOf_coeff, mul_eq_one_iff_eq_inv', Finset.sum_ite_eq', Finset.mem_univ, if_true, inv_inv]
  ring

theorem trace_asAlgebraHom {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom (k := ℂ) (V.ρ : Representation ℂ G V) a) =
      tr a V.character := by
  simp only [tr, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, FDRep.character]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp

theorem tr_idem_nat {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ)
    (ha : a * a = a) (hχ : IsChar χ) : ∃ n : ℕ, tr a χ = n := by
  obtain ⟨V, hV⟩ := hχ
  have hc : V.character = χ := funext hV
  set f := Representation.asAlgebraHom (k := ℂ) (V.ρ : Representation ℂ G V) a with hf
  have hi : IsIdempotentElem f := by
    rw [IsIdempotentElem, hf, ← map_mul, ha]
  refine ⟨Module.finrank ℂ (LinearMap.range f), ?_⟩
  rw [← hc, ← trace_asAlgebraHom, ← hf]
  exact (LinearMap.IsIdempotentElem.isProj_range f hi).trace

theorem irr_one_pos {G : Type} [Group G] (χ : G → ℂ) (hχ : IsIrr χ) : ∃ d : ℕ, 0 < d ∧ χ 1 = d := by
  obtain ⟨V, hs, hV⟩ := hχ
  refine ⟨Module.finrank ℂ V, Nat.pos_of_ne_zero fun h => ?_, by rw [← hV, FDRep.char_one]⟩
  apply CategoryTheory.Simple.not_isZero V
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  have : Subsingleton V := Module.finrank_zero_iff.mp h
  ext x
  exact Subsingleton.elim _ _

end GlobalTheory.GLq.TrIdem

theorem GlobalTheory.GLq.trIdem : ∀ (G : Type) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ),
    (a * a = a → IsChar χ → ∃ n : ℕ, tr a χ = n) ∧ (IsIrr χ → ∃ d : ℕ, 0 < d ∧ χ 1 = d) ∧
      (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ :=
  fun _ _ _ a χ => ⟨GlobalTheory.GLq.TrIdem.tr_idem_nat a χ, GlobalTheory.GLq.TrIdem.irr_one_pos χ,
    GlobalTheory.GLq.TrIdem.coeff_mul_zOf_one a χ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAcrisLogOneAddAddOfMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAcrisLogOneAdd_add_of_mul : ∀ (l : ℕ) [Fact l.Prime] (a b : Per.Ainf l) (y y' : Per.Acris l), GlobalTheory.LogU.InJ a → GlobalTheory.LogU.InJ b → GlobalTheory.LogU.IsLogJ a y → GlobalTheory.LogU.IsLogJ b y' → GlobalTheory.LogU.IsLogJ (a + b + a * b) (y + y') := by
  first | (exact @GlobalTheory.LogU.isLogJ_add) | (exact GlobalTheory.LogU.isLogJ_add) | (intros; apply GlobalTheory.LogU.isLogJ_add  <;> assumption)
end

