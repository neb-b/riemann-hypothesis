module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeneralLinearGroupCharEqOneOfDetEqOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adele_mul_integral {a b : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) (hb : b v ∈ v.adicCompletionIntegers F) :
    (a * b) v ∈ v.adicCompletionIntegers F := by
  have : (a * b) v = a v * b v := RestrictedProduct.mul_apply _ a b v
  rw [this]; exact mul_mem ha hb

theorem adele_add_integral {a b : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) (hb : b v ∈ v.adicCompletionIntegers F) :
    (a + b) v ∈ v.adicCompletionIntegers F := by
  have : (a + b) v = a v + b v := RestrictedProduct.add_apply _ a b v
  rw [this]; exact add_mem ha hb

theorem adele_neg_integral {a : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) :
    (-a) v ∈ v.adicCompletionIntegers F := by
  have : (-a) v = -a v := RestrictedProduct.neg_apply _ a v
  rw [this]; exact neg_mem ha

theorem adele_one_integral (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := RestrictedProduct.one_apply _ _
  rw [this]; exact one_mem _

theorem adele_zero_integral (v : HeightOneSpectrum (𝓞 F)) :
    (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (0 : FiniteAdeleRing (𝓞 F) F) v = 0 := RestrictedProduct.zero_apply _ _
  rw [this]; exact zero_mem _

theorem tmul_mem_adelicCompletion_of_integral {J : Set E} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {x : E} (hx : x ∈ J) :
    a ⊗ₜ[F] x ∈ hat1 F J :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem one_tmul_mem_adelicCompletionOfElementSet {J : Set E} {x : E} (hx : x ∈ J) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F J :=
  tmul_mem_adelicCompletion_of_integral F (adele_one_integral F) hx

theorem mul_mem_adelicCompletionOfElementSet_of_mul_mem {I J K : Set E} (h : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ K)
    {x y : RA F E} (hx : x ∈ hat1 F I) (hy : y ∈ hat1 F J) : x * y ∈ hat1 F K := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_adelicCompletion_of_integral F (fun v => adele_mul_integral F (ha v) (hb v))
        (h x hx y hy)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h1 => rw [neg_mul]; exact neg_mem h1

theorem galoisAut_mem_adelicCompletionOfElementSet (c : E ≃ₐ[F] E) {I J : Set E} (h : ∀ x ∈ I, c x ∈ J)
    {z : RA F E} (hz : z ∈ hat1 F I) : sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F J := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    exact tmul_mem_adelicCompletion_of_integral F ha (h x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [map_add (f := _)]; exact add_mem h1 h2
  | neg y _ h1 => rw [map_neg]; exact neg_mem h1

theorem mem_range_iff_adele_integral (x : F) :
    x ∈ (algebraMap (𝓞 F) F).range ↔
      ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F := by
  simp only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  constructor
  · rintro ⟨a, rfl⟩ v
    exact v.valuation_le_one a
  · exact HeightOneSpectrum.mem_integers_of_valuation_le_one F x

theorem linearForm_integral_of_one_tmul_mem_adelicCompletion {I : Set E} (t : E →ₗ[F] F)
    (ht : ∀ y ∈ I, t y ∈ (algebraMap (𝓞 F) F).range) {x : E}
    (hx : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F I) :
    t x ∈ (algebraMap (𝓞 F) F).range := by
  let T : RA F E →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
    (TensorProduct.rid F _).toLinearMap ∘ₗ LinearMap.lTensor _ t
  have hT : ∀ a y, T (a ⊗ₜ[F] y) = algebraMap F _ (t y) * a := by
    intro a y
    simp [T, Algebra.smul_def]
  have key : ∀ z ∈ hat1 F I, ∀ v, T z v ∈ v.adicCompletionIntegers F := by
    intro z hz v
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hx
      rw [hT]
      exact adele_mul_integral F
        ((mem_range_iff_adele_integral F _).1 (ht y hy) v) (ha v)
    | zero => rw [map_zero]; exact adele_zero_integral F v
    | add y z _ _ h1 h2 => rw [map_add (f := _)]; exact adele_add_integral F h1 h2
    | neg y _ h1 => rw [map_neg]; exact adele_neg_integral F h1
  rw [mem_range_iff_adele_integral]
  have := key _ hx
  rwa [hT, mul_one] at this

variable [NumberField E]

theorem one_tmul_mem_adelicCompletion_fractionalIdeal_iff (I : FractionalIdeal (𝓞 E)⁰ E) (x : E) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I := by
  refine ⟨fun hx => ?_, fun hx => one_tmul_mem_adelicCompletionOfElementSet F hx⟩
  by_cases hI : I = 0
  · subst hI
    rw [FractionalIdeal.mem_zero_iff]
    by_contra h0
    obtain ⟨t, ht⟩ := Module.Projective.exists_dual_eq_one F h0
    apply RingOfIntegers.not_isField F
    rw [← IsFractionRing.surjective_iff_isField (K := F)]
    intro c
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (c • t) (fun y hy => by
      have hy' : y = 0 := (FractionalIdeal.mem_zero_iff _).1 hy
      rw [hy', map_zero]; exact zero_mem _) hx
    simpa [ht] using this
  · rw [← FractionalIdeal.dual_dual (𝓞 F) F I,
      FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero _ _ hI)]
    intro y hy
    rw [FractionalIdeal.mem_dual hI] at hy
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (Algebra.traceForm F E y) hy hx
    rwa [Algebra.traceForm_apply, mul_comm] at this

theorem mem_adelicCompletion_mul_inv_fractionalIdeal (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E) (hI : I ≠ 0)
    (h : ∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) :
    z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  have h1 : (1 : E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
  have key : ∀ w ∈ I * I⁻¹, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] w) ∈
      hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro w hw
    refine FractionalIdeal.mul_induction_on hw (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (K := ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
        (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) (h x hx) (one_tmul_mem_adelicCompletionOfElementSet F hy)
      rwa [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
    · rw [TensorProduct.tmul_add, mul_add]; exact add_mem hx hy
  have := key 1 h1
  rwa [← Algebra.TensorProduct.one_def, mul_one] at this

end

theorem adelicCompletion_fractionalIdeal_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by
  intro F E _ _ _ _ _
  exact ⟨fun I J x hx y hy => mul_mem_adelicCompletionOfElementSet_of_mul_mem F
      (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) hx hy,
    one_tmul_mem_adelicCompletion_fractionalIdeal_iff F, mem_adelicCompletion_mul_inv_fractionalIdeal F, fun c I I' h z hz => galoisAut_mem_adelicCompletionOfElementSet F c h hz⟩

end GlobalTheory.AdLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetCharacterReductionInvariant
section
set_option autoImplicit false

namespace GlobalTheory

open scoped TensorProduct

theorem char_eq_one_of_inverse_det_one_of_basis {R S V Q A : Type} [CommRing R] [CommRing S] [Finite S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V] [AddCommGroup Q] [Module R Q] [CommGroup A]
    {r : ℕ} (b : Module.Basis (Fin r) S V) (e : Q ≃ₗ[R] V) (ψ : (Q ≃ₗ[R] Q) →* A)
    (h4 : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 4 ≤ Nat.card (S ⧸ 𝔪)) (f : V →ₗ[S] V) (hf : LinearMap.det f = 1)
    (k : Q ≃ₗ[R] Q) (hk : ∀ q, f (e (k q)) = e q) : ψ k = 1 := by
  classical
  let φ2 : Module.End S V →* Module.End R V :=
    { toFun := fun g => g.restrictScalars R, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let φ4 : (V ≃ₗ[R] V) →* (Q ≃ₗ[R] Q) :=
    { toFun := fun u => e.trans (u.trans e.symm)
      map_one' := by ext q; simp
      map_mul' := by intro u v; ext q; simp }
  let Φ : GL (Fin r) S →* (Q ≃ₗ[R] Q) :=
    φ4.comp ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V).toMonoidHom.comp
      ((Units.map φ2).comp (Units.map ((Matrix.toLinAlgEquiv b :
        Matrix (Fin r) (Fin r) S ≃ₐ[S] Module.End S V) : Matrix (Fin r) (Fin r) S →* Module.End S V))))
  have hdet : IsUnit (LinearMap.toMatrix b b f).det := by
    rw [LinearMap.det_toMatrix, hf]; exact isUnit_one
  let g : GL (Fin r) S := Matrix.nonsingInvUnit _ hdet
  have hg : (g : Matrix (Fin r) (Fin r) S).det = 1 := by
    show (LinearMap.toMatrix b b f).det = 1
    rw [LinearMap.det_toMatrix, hf]
  have h1 : (ψ.comp Φ) g = 1 := generalLinearGroup_char_eq_one_of_det_eq_one S r A (ψ.comp Φ) h4 g hg
  have h2 : Φ g * k = 1 := by
    ext q
    show e.symm ((Matrix.toLinAlgEquiv b (LinearMap.toMatrix b b f)) (e (k q))) = q
    rw [show LinearMap.toMatrix b b f = LinearMap.toMatrixAlgEquiv b f from rfl,
      Matrix.toLinAlgEquiv_toMatrixAlgEquiv, hk, LinearEquiv.symm_apply_apply]
  have h3 := congrArg ψ h2
  rw [map_mul, map_one] at h3
  simp only [MonoidHom.comp_apply] at h1
  rw [h1, one_mul] at h3
  exact h3

private theorem free_quotient_tensor_of_projective {R : Type} [CommRing R] [IsDomain R] (L' : Type)
    [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R)
    [Finite (R ⧸ I)] : Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] L') := by
  refine Module.free_of_flat_of_finrank_eq (R ⧸ I) _ (Module.finrank R L') fun P => ?_
  let := Ideal.Quotient.field P.1
  rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.1)
    ((R ⧸ I) ⧸ P.1) L').finrank_eq]
  have h := Module.rankAtStalk_baseChange (R := R) (M := L') (S := (R ⧸ I) ⧸ P.1)
    ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] at h
  rw [h]
  exact (Ideal.finrank_fiber_eq_rankAtStalk (M := L') _).symm.trans (Ideal.finrank_fiber_eq_finrank _)

theorem char_eq_one_of_inverse_reduction_det_one : ∀ (R : Type) [CommRing R] [IsDomain R] (L L' : Type) [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R) [Finite (R ⧸ I)] (A : Type) [CommGroup A] (ψ : ((L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))) →* A) (t : L →ₗ[R] L') (γ : L' →ₗ[R] L') (k : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))), (∀ 𝔪 : Ideal (R ⧸ I), 𝔪.IsMaximal → 4 ≤ Nat.card ((R ⧸ I) ⧸ 𝔪)) → (∀ b, ∃ a, b - t a ∈ (I • ⊤ : Submodule R L')) → (∀ a, t a ∈ (I • ⊤ : Submodule R L') → a ∈ (I • ⊤ : Submodule R L)) → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 → (∀ a, ∃ a', (Submodule.Quotient.mk a' : L ⧸ (I • ⊤ : Submodule R L)) = k (Submodule.Quotient.mk a) ∧ γ (t a') - t a ∈ (I • ⊤ : Submodule R L')) → ψ k = 1 := by
  intro R _ _ L L' _ _ _ _ _ _ I _ A _ ψ t γ k h4 hsurj hinj hdet hk
  have := free_quotient_tensor_of_projective L' I
  obtain ⟨r, ⟨b⟩⟩ : ∃ r : ℕ, Nonempty (Module.Basis (Fin r) (R ⧸ I) ((R ⧸ I) ⊗[R] L')) := by
    rcases subsingleton_or_nontrivial (R ⧸ I) with h | h
    · have := Module.subsingleton (R ⧸ I) ((R ⧸ I) ⊗[R] L')
      exact ⟨0, ⟨Module.Basis.empty _⟩⟩
    · exact ⟨_, ⟨Module.finBasis (R ⧸ I) ((R ⧸ I) ⊗[R] L')⟩⟩
  have hle : (I • ⊤ : Submodule R L) ≤ (I • ⊤ : Submodule R L').comap t := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  let tb := (I • ⊤ : Submodule R L).mapQ (I • ⊤ : Submodule R L') t hle
  have tbij : Function.Bijective tb := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hinj a hx)
    · intro y
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨a, ha⟩ := hsurj c
      exact ⟨Submodule.Quotient.mk a, ((Submodule.Quotient.eq _).mpr ha).symm⟩
  let e : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (R ⧸ I) ⊗[R] L' :=
    (LinearEquiv.ofBijective tb tbij).trans (TensorProduct.quotTensorEquivQuotSMul L' I).symm
  have he : ∀ a, e (Submodule.Quotient.mk a) = (1 : R ⧸ I) ⊗ₜ[R] t a := by
    intro a
    simp [e, tb, TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  have hz : ∀ x ∈ (I • ⊤ : Submodule R L'), (1 : R ⧸ I) ⊗ₜ[R] x = 0 := by
    intro x hx
    have h0 : (Submodule.Quotient.mk x : L' ⧸ (I • ⊤ : Submodule R L')) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk, h0, map_zero]
  refine char_eq_one_of_inverse_det_one_of_basis b e ψ h4 (LinearMap.baseChange (R ⧸ I) γ) hdet k ?_
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a', ha', hγ⟩ := hk a
  rw [← ha', he, he, LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub]
  exact hz _ hγ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.AdSplit

theorem exists_prod_equiv (F E A B : Type) [CommRing F] [CommRing E] [Algebra F E]
    [CommRing A] [Algebra F A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [Algebra F B] [TopologicalSpace B] [IsTopologicalRing B] :
    letI : TopologicalSpace ((A × B) ⊗[F] E) := moduleTopology (A × B) ((A × B) ⊗[F] E)
    letI : TopologicalSpace (B ⊗[F] E) := moduleTopology B (B ⊗[F] E)
    letI : TopologicalSpace (A ⊗[F] E) := moduleTopology A (A ⊗[F] E)
    ∃ e : ((A × B) ⊗[F] E) ≃+* (A ⊗[F] E) × (B ⊗[F] E),
      (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z ∧
        (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) ∧
      Continuous e ∧ Continuous e.symm := by
  letI : TopologicalSpace ((A × B) ⊗[F] E) := moduleTopology (A × B) ((A × B) ⊗[F] E)
  letI : TopologicalSpace (B ⊗[F] E) := moduleTopology B (B ⊗[F] E)
  letI : TopologicalSpace (A ⊗[F] E) := moduleTopology A (A ⊗[F] E)
  haveI : IsModuleTopology (A × B) ((A × B) ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology B (B ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd ((A × B) ⊗[F] E) := IsModuleTopology.toContinuousAdd (A × B) _
  haveI : ContinuousAdd (A ⊗[F] E) := IsModuleTopology.toContinuousAdd A _
  haveI : ContinuousAdd (B ⊗[F] E) := IsModuleTopology.toContinuousAdd B _
  let p := Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E)
  let q := Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E)
  let l := TensorProduct.prodLeft F F A B E
  have hl : ∀ z, l z = (p z, q z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [Prod.ext_iff]
    | tmul a x => obtain ⟨a, b⟩ := a; simp [l, p, q]
    | add x y hx hy => simp [hx, hy]
  let e : ((A × B) ⊗[F] E) ≃+* (A ⊗[F] E) × (B ⊗[F] E) :=
    { l.toAddEquiv with
      map_mul' := fun x y => by
        change l (x * y) = l x * l y
        simp [hl] }
  have he : ∀ z, e z = (p z, q z) := hl
  let i : A ⊗[F] E →ₗ[F] (A × B) ⊗[F] E := LinearMap.rTensor E (LinearMap.inl F A B)
  let j : B ⊗[F] E →ₗ[F] (A × B) ⊗[F] E := LinearMap.rTensor E (LinearMap.inr F A B)
  have hp : Continuous p := by
    let φ : (A × B) ⊗[F] E →ₛₗ[RingHom.fst A B] A ⊗[F] E :=
      { toFun := p
        map_add' := map_add p
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [p, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_fst φ
  have hq : Continuous q := by
    let φ : (A × B) ⊗[F] E →ₛₗ[RingHom.snd A B] B ⊗[F] E :=
      { toFun := q
        map_add' := map_add q
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [q, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_snd φ
  have hi : Continuous i := by
    let φ : A ⊗[F] E →ₑ+[MonoidHom.inl A B] (A × B) ⊗[F] E :=
      { toFun := i
        map_zero' := map_zero i
        map_add' := map_add i
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [i, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
    exact IsModuleTopology.continuous_of_distribMulActionHomₑ
      (continuous_id.prodMk continuous_const) φ
  have hj : Continuous j := by
    let φ : B ⊗[F] E →ₑ+[MonoidHom.inr A B] (A × B) ⊗[F] E :=
      { toFun := j
        map_zero' := map_zero j
        map_add' := map_add j
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [j, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
    exact IsModuleTopology.continuous_of_distribMulActionHomₑ
      (continuous_const.prodMk continuous_id) φ
  have hpi : ∀ x, p (i x) = x ∧ q (i x) = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [i, p, q]
    | add x y hx hy => simp [hx.1, hx.2, hy.1, hy.2]
  have hpj : ∀ x, p (j x) = 0 ∧ q (j x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [j, p, q]
    | add x y hx hy => simp [hx.1, hx.2, hy.1, hy.2]
  refine ⟨e, fun z => by rw [he]; exact ⟨rfl, rfl⟩, ?_, ?_⟩
  · have : (e : _ → _) = fun z => (p z, q z) := funext he
    rw [this]
    exact hp.prodMk hq
  · have : (e.symm : _ → _) = fun w => i w.1 + j w.2 := by
      funext w
      rw [RingEquiv.symm_apply_eq, he]
      simp [(hpi _).1, (hpi _).2, (hpj _).1, (hpj _).2]
    rw [this]
    exact (hi.comp continuous_fst).add (hj.comp continuous_snd)

theorem exists_adele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] , letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ e : (AdeleRing (𝓞 F) F ⊗[F] E) ≃+* (InfiniteAdeleRing F ⊗[F] E) × (FiniteAdeleRing (𝓞 F) F ⊗[F] E), (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z ∧ (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z) ∧ Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _
  exact exists_prod_equiv F E (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

end GlobalTheory.AdSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFgSubalgebraDescAway
section
namespace GlobalTheory

theorem exists_awayMap_subalgebra (K : Type) [Field K] (S : Type) [CommRing S] [Algebra K S]
    (S₁ : Subalgebra K S) (x : S) (hx : x ∈ S₁) :
    ∃ κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x,
      (∀ s : S₁, κ (algebraMap S₁ _ s) = algebraMap S _ (s : S)) ∧ Function.Injective κ ∧
      ∀ (z : Localization.Away x) (m : ℕ) (s : S), s ∈ S₁ →
        z * algebraMap S _ x ^ m = algebraMap S _ s → z ∈ κ.range := by
  first
  | exact @_root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding
  | exact _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding
  | (apply _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding ..)

theorem exists_fg_subalgebra_desc_away : ∀ (K : Type) [Field K] (S : Type) [CommRing S] [Algebra K S] (S₀ : Subalgebra K S), S₀.FG → ∀ (n : ℕ) (h : Fin n → S) (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)], (∀ i, Algebra.FiniteType K (A i)) → ∀ a : ∀ i, A i →ₐ[K] Localization.Away (h i), Ideal.span (Set.range h) = ⊤ → ∃ (S₁ : Subalgebra K S) (h₁ : Fin n → S₁), S₁.FG ∧ S₀ ≤ S₁ ∧ (∀ i, (h₁ i : S) = h i) ∧ Ideal.span (Set.range h₁) = ⊤ ∧ ∀ i, ∃ (κ : Localization.Away (h₁ i) →ₐ[K] Localization.Away (h i)) (a' : A i →ₐ[K] Localization.Away (h₁ i)), (∀ s : S₁, κ (algebraMap S₁ _ s) = algebraMap S _ (s : S)) ∧ Function.Injective κ ∧ κ.comp a' = a i := by
  classical
  intro K _ S _ _ S₀ hS₀ n h A _ _ hA a hspan
  obtain ⟨c, hc⟩ : ∃ c : Fin n → S, ∑ i, c i * h i = 1 :=
    Ideal.mem_span_range_iff_exists_fun.1 (hspan ▸ Submodule.mem_top)
  choose G hG using fun i => (hA i).out
  choose m s hs using fun i (g : A i) => IsLocalization.Away.surj (h i) (a i g)
  let T : Finset S := Finset.univ.image h ∪ Finset.univ.image c ∪
    Finset.univ.biUnion fun i => (G i).image (s i)
  let S₁ : Subalgebra K S := S₀ ⊔ Algebra.adjoin K (T : Set S)
  have hT : ∀ t ∈ T, t ∈ S₁ := fun t ht =>
    (le_sup_right : Algebra.adjoin K (T : Set S) ≤ S₁) (Algebra.subset_adjoin ht)
  have hh : ∀ i, h i ∈ S₁ := fun i => hT _ (by simp [T])
  have hcm : ∀ i, c i ∈ S₁ := fun i => hT _ (by simp [T])
  have hsm : ∀ i, ∀ g ∈ G i, s i g ∈ S₁ := fun i g hg => hT _ (by
    simp only [T, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
    exact Or.inr ⟨i, Finset.mem_univ _, g, hg, rfl⟩)
  refine ⟨S₁, fun i => ⟨h i, hh i⟩, hS₀.sup ⟨T, rfl⟩, le_sup_left, fun _ => rfl, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => ⟨c i, hcm i⟩, Subtype.ext ?_⟩
    simpa using hc
  · intro i
    obtain ⟨κ, hκ, hinj, hr⟩ := exists_awayMap_subalgebra K S S₁ (h i) (hh i)
    have hmem : ∀ y : A i, a i y ∈ κ.range := by
      intro y
      have : (⊤ : Subalgebra K (A i)) ≤ κ.range.comap (a i) := by
        rw [← hG i, Algebra.adjoin_le_iff]
        intro g hg
        exact hr _ (m i g) _ (hsm i g hg) (hs i g)
      exact this Algebra.mem_top
    refine ⟨κ, (AlgEquiv.ofInjective κ hinj).symm.toAlgHom.comp ((a i).codRestrict _ hmem),
      hκ, hinj, ?_⟩
    ext y
    have := AlgEquiv.ofInjective_apply κ hinj
      ((AlgEquiv.ofInjective κ hinj).symm ⟨a i y, hmem y⟩)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
section
namespace GlobalTheory.CompRat

theorem exists_ringEquiv_complex_comp_eq :
    ∀ (k : Type) [Field k] [Countable k] (φ ψ : k →+* ℂ), ∃ τ : ℂ ≃+* ℂ, ∀ x, τ (φ x) = ψ x :=
  fun _ _ _ φ ψ => GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq φ ψ

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ImportsBis
section
namespace GlobalTheory.IntegralOpen

open IsDedekindDomain NumberField

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F),
        (a : (w : HeightOneSpectrum (RingOfIntegers F)) → HeightOneSpectrum.adicCompletion F w) v ∈
          HeightOneSpectrum.adicCompletionIntegers F v} :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun w : HeightOneSpectrum (RingOfIntegers F) => HeightOneSpectrum.adicCompletion F w)
    (A := fun w => (HeightOneSpectrum.adicCompletionIntegers F w : Set (HeightOneSpectrum.adicCompletion F w)))
    (fun _ => Valued.isOpen_valuationSubring _)

end GlobalTheory.IntegralOpen
end

