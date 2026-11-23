module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoequifiberedDiagramMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpecHomCompCoaction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothDescent

open TensorProduct

theorem exists_common_model (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] :
    ∃ (A B₁ C₁ : Type) (_ : CommRing A) (_ : Algebra A R) (_ : CommRing B₁) (_ : CommRing C₁)
      (_ : Algebra A B₁) (_ : Algebra A C₁), IsNoetherianRing A ∧ Algebra.Smooth A B₁ ∧
      Algebra.Smooth A C₁ ∧ Nonempty (R ⊗[A] B₁ ≃ₐ[R] B) ∧ Nonempty (R ⊗[A] C₁ ≃ₐ[R] C) := by
  obtain ⟨A₁, B₁, _, _, hA₁, _, ⟨eB⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R B
  obtain ⟨A₂, C₁, _, _, hA₂, _, ⟨eC⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R C
  let A : Subalgebra ℤ R := A₁ ⊔ A₂
  let : Algebra A₁ A := (Subalgebra.inclusion (le_sup_left : A₁ ≤ A)).toRingHom.toAlgebra
  let : Algebra A₂ A := (Subalgebra.inclusion (le_sup_right : A₂ ≤ A)).toRingHom.toAlgebra
  have : IsScalarTower A₁ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A₂ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).mp (hA₁.sup hA₂)
  exact ⟨A, A ⊗[A₁] B₁, A ⊗[A₂] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ A, inferInstance,
    inferInstance, ⟨(Algebra.TensorProduct.cancelBaseChange A₁ A R R B₁).trans eB.symm⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange A₂ A R R C₁).trans eC.symm⟩⟩

variable {A R B₁ C₁ : Type} [CommRing A] [CommRing R] [CommRing B₁] [CommRing C₁] [Algebra A R]
  [Algebra A B₁] [Algebra A C₁]

noncomputable abbrev incl (C₁ : Type) [CommRing C₁] [Algebra A C₁] (S : Subalgebra A R) :
    S ⊗[A] C₁ →ₐ[A] R ⊗[A] C₁ :=
  Algebra.TensorProduct.map S.val (AlgHom.id A C₁)

theorem range_incl_mono {S T : Subalgebra A R} (h : S ≤ T) :
    (incl C₁ S).range ≤ (incl C₁ T).range := by
  have e : incl C₁ S = (incl C₁ T).comp
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A C₁)) :=
    Algebra.TensorProduct.ext' fun _ _ => rfl
  rw [e]
  exact AlgHom.range_comp_le_range _ _

theorem exists_fg_mem_range_incl (x : R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ x ∈ (incl C₁ S).range := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Subalgebra.fg_bot, zero_mem _⟩
  | tmul r c =>
    exact ⟨Algebra.adjoin A {r}, ⟨{r}, by simp⟩,
      (AlgHom.mem_range _).mpr ⟨⟨r, Algebra.subset_adjoin rfl⟩ ⊗ₜ c, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨S, hS, hxS⟩ := hx
    obtain ⟨T, hT, hyT⟩ := hy
    exact ⟨S ⊔ T, hS.sup hT,
      add_mem (range_incl_mono le_sup_left hxS) (range_incl_mono le_sup_right hyT)⟩

theorem exists_fg_subset_range_incl (t : Finset (R ⊗[A] C₁)) :
    ∃ S : Subalgebra A R, S.FG ∧ (t : Set (R ⊗[A] C₁)) ⊆ (incl C₁ S).range := by
  classical
  refine Finset.induction_on t ⟨⊥, Subalgebra.fg_bot, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨S, hS, hSt⟩ := ih
  obtain ⟨T, hT, haT⟩ := exists_fg_mem_range_incl (C₁ := C₁) a
  refine ⟨S ⊔ T, hS.sup hT, ?_⟩
  rw [Finset.coe_insert, Set.insert_subset_iff]
  exact ⟨range_incl_mono le_sup_right haT,
    hSt.trans (SetLike.coe_subset_coe.mpr (range_incl_mono le_sup_left))⟩

theorem exists_fg_range_le [Algebra.FiniteType A B₁] (φ : B₁ →ₐ[A] R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ φ.range ≤ (incl C₁ S).range := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B₁).FG)
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := C₁) (s.image φ)
  refine ⟨S, hS, ?_⟩
  rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rwa [Finset.coe_image] at hsub

theorem incl_injective [Module.Flat A C₁] (S : Subalgebra A R) :
    Function.Injective (incl C₁ S) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) S.val.toLinearMap
    Subtype.val_injective

theorem exists_lift {D E : Type} [CommRing D] [CommRing E] [Algebra A D] [Algebra A E]
    (φ : B₁ →ₐ[A] E) (i : D →ₐ[A] E) (hi : Function.Injective i) (h : φ.range ≤ i.range) :
    ∃ ψ : B₁ →ₐ[A] D, ∀ b, i (ψ b) = φ b := by
  let e := AlgEquiv.ofInjective i hi
  let φ' := φ.codRestrict i.range fun b => h (AlgHom.mem_range_self φ b)
  refine ⟨e.symm.toAlgHom.comp φ', fun b => ?_⟩
  have h1 : ((e (e.symm (φ' b)) : i.range) : E) = (φ' b : E) := by rw [e.apply_symm_apply]
  exact h1

theorem cancel_one_tmul (S : Subalgebra A R) (x : S ⊗[A] C₁) :
    Algebra.TensorProduct.cancelBaseChange A S R R C₁ (1 ⊗ₜ x) = incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s c => simp [Algebra.TensorProduct.cancelBaseChange_tmul, incl, Algebra.smul_def]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add (f := _), hx, hy, map_add (f := _)]

theorem incl_tmul (S : Subalgebra A R) (s : S) (c : C₁) :
    incl C₁ S (s ⊗ₜ c) = (s : R) • ((1 : R) ⊗ₜ[A] c) := by
  simp [incl, TensorProduct.smul_tmul']

theorem incl_smul (S : Subalgebra A R) (s : S) (x : S ⊗[A] C₁) :
    incl C₁ S (s • x) = (s : R) • incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s' c => simp [incl, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

noncomputable def extend (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) : S ⊗[A] B₁ →ₐ[S] D :=
  Algebra.TensorProduct.lift (Algebra.ofId S D) ψ fun _ _ => Commute.all _ _

theorem extend_tmul (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) (s : S) (b : B₁) :
    extend S ψ (s ⊗ₜ b) = s • ψ b := by
  simp [extend, Algebra.smul_def]

theorem incl_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁)
    (ψ : B₁ →ₐ[A] S ⊗[A] C₁) (h : ∀ b, incl C₁ S (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    incl C₁ S (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => rw [extend_tmul, incl_smul, h, incl_tmul, map_smul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem val_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R)
    (ψ : B₁ →ₐ[A] S) (h : ∀ b, S.val (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    S.val (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
    rw [extend_tmul, smul_eq_mul, map_mul, h, incl_tmul, map_smul, smul_eq_mul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

end GlobalTheory.SmoothDescent

namespace GlobalTheory

open TensorProduct SmoothDescent

theorem exists_noetherian_model_of_smooth :
    ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] (f g : B →ₐ[R] C) (r : B →ₐ[R] R), ∃ (R₀ B₀ C₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ R) (_ : CommRing B₀) (_ : CommRing C₀) (_ : Algebra R₀ B₀) (_ : Algebra R₀ C₀) (f₀ g₀ : B₀ →ₐ[R₀] C₀) (r₀ : B₀ →ₐ[R₀] R₀) (β' : TensorProduct R₀ R B₀ ≃ₐ[R] B) (δ' : TensorProduct R₀ R C₀ ≃ₐ[R] C), Module.Flat R₀ B₀ ∧ Module.Flat R₀ C₀ ∧ ∀ b : B₀, f (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ f₀ b) ∧ g (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ g₀ b) ∧ r (β' (1 ⊗ₜ b)) = algebraMap R₀ R (r₀ b) := by
  intro R B C _ _ _ _ _ _ _ f g r
  obtain ⟨A, B₁, C₁, _, _, _, _, _, _, hA, hB, hC, ⟨eB⟩, ⟨eC⟩⟩ := exists_common_model R B C
  let F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp f).comp eB.toAlgHom
  let G : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp g).comp eB.toAlgHom
  let ρ : R ⊗[A] B₁ →ₐ[R] R := r.comp eB.toAlgHom
  let j : B₁ →ₐ[A] R ⊗[A] B₁ := Algebra.TensorProduct.includeRight
  let φF : B₁ →ₐ[A] R ⊗[A] C₁ := (F.restrictScalars A).comp j
  let φG : B₁ →ₐ[A] R ⊗[A] C₁ := (G.restrictScalars A).comp j
  let φr : B₁ →ₐ[A] R := (ρ.restrictScalars A).comp j
  obtain ⟨S₁, hS₁, h₁⟩ := exists_fg_range_le (C₁ := C₁) φF
  obtain ⟨S₂, hS₂, h₂⟩ := exists_fg_range_le (C₁ := C₁) φG
  have h₃ : φr.range.FG := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map φr Algebra.FiniteType.out
  let S : Subalgebra A R := S₁ ⊔ S₂ ⊔ φr.range
  have : Algebra.FiniteType A S := (Subalgebra.fg_iff_finiteType S).mp ((hS₁.sup hS₂).sup h₃)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  have hF : φF.range ≤ (incl C₁ S).range :=
    h₁.trans (range_incl_mono (le_sup_left.trans le_sup_left))
  have hG : φG.range ≤ (incl C₁ S).range :=
    h₂.trans (range_incl_mono (le_sup_right.trans le_sup_left))
  have hr : φr.range ≤ S.val.range := by
    rw [Subalgebra.range_val]
    exact le_sup_right
  obtain ⟨ψF, hψF⟩ := exists_lift φF (incl C₁ S) (incl_injective S) hF
  obtain ⟨ψG, hψG⟩ := exists_lift φG (incl C₁ S) (incl_injective S) hG
  obtain ⟨ψr, hψr⟩ := exists_lift φr S.val Subtype.val_injective hr
  refine ⟨S, S ⊗[A] B₁, S ⊗[A] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, extend S ψF, extend S ψG, extend S ψr,
    (Algebra.TensorProduct.cancelBaseChange A S R R B₁).trans eB,
    (Algebra.TensorProduct.cancelBaseChange A S R R C₁).trans eC, inferInstance, inferInstance,
    fun b => ⟨?_, ?_, ?_⟩⟩
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S F ψF hψF]
    simp [F]
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S G ψG hψG]
    simp [G]
  · rw [AlgEquiv.trans_apply, cancel_one_tmul]
    change _ = S.val (extend S ψr b)
    rw [val_extend S ρ ψr hψr]
    simp [ρ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsQuotientSchemeOfFiniteFlatSubgroup
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineQuotient

set_option backward.isDefEq.respectTransparency false


open TensorProduct Algebra.TensorProduct in
lemma exists_coaction {R Λ : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] (i : specOver R Λ ⟶ A) {Y : Scheme.{0}}
    (f : A.left ⟶ Y) (g : (specOver R Λ ⊗ A).left ⟶ Y)
    (ha : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A).left ≫ f = g)
    (hp : (snd (specOver R Λ) A).left ≫ f = g) (U : Y.Opens) (hf : IsAffineOpen (f ⁻¹ᵁ U))
    (hg : IsAffineOpen (g ⁻¹ᵁ U)) :
    ∃ (_ : Algebra R Γ(A.left, f ⁻¹ᵁ U)) (v : specOver R Γ(A.left, f ⁻¹ᵁ U) ⟶ A) (_ : Mono v)
      (ρ : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R] Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)
      (e : Γ((specOver R Λ ⊗ A).left, g ⁻¹ᵁ U) ⟶ .of (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)) (_ : IsIso e),
      specHom ρ ≫ v = (specHom includeRight ≫ i) * (specHom includeLeft ≫ v) ∧
      pullOver f g _ ha U ≫ e = CommRingCat.ofHom ρ.toRingHom ∧
      pullOver f g _ hp U ≫ e = CommRingCat.ofHom (includeLeft : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ).toRingHom := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hf.fromSpec ≫ A.hom)
  let : Algebra R Γ(A.left, f ⁻¹ᵁ U) := φ.hom.toAlgebra
  let v : specOver R Γ(A.left, f ⁻¹ᵁ U) ⟶ A := Over.homMk hf.fromSpec hφ.symm
  have : Mono v.left := inferInstanceAs (Mono hf.fromSpec)
  have P₁ : IsPullback (Spec.map (pullOver f g _ hp U))
      (hg.fromSpec ≫ (fst (specOver R Λ) A).left) (Spec.map φ) (specOver R Λ).hom := by
    rw [hφ]
    exact (isPullback_pullOver f g _ hp hf hg).paste_vert
      (IsPullback.of_hasPullback (specOver R Λ).hom A.hom).flip
  have P₂ : IsPullback (specHom (includeLeft : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).left (specHom (includeRight : Λ →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).left (Spec.map φ) (specOver R Λ).hom :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R Γ(A.left, f ⁻¹ᵁ U) Λ)
  obtain ⟨e, he⟩ := Spec.map_surjective (P₂.isoIsPullback _ _ P₁).hom
  have : IsIso (Spec.map e) := by rw [he]; infer_instance
  have : IsIso e := by
    have : IsIso (Scheme.Spec.map e.op) := this
    have := Spec.fullyFaithful.isIso_of_isIso_map e.op
    exact isIso_of_op e
  have h₁ := P₂.isoIsPullback_hom_fst _ _ P₁
  have h₂ := P₂.isoIsPullback_hom_snd _ _ P₁
  rw [← he] at h₁ h₂
  have hw : (Spec.map e ≫ hg.fromSpec) ≫ (specOver R Λ ⊗ A).hom =
      (specOver R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).hom := by
    rw [← Over.w (fst (specOver R Λ) A), Category.assoc, reassoc_of% h₂, Over.w]
  let k : specOver R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ) ⟶ specOver R Λ ⊗ A :=
    Over.homMk (Spec.map e ≫ hg.fromSpec) hw
  have k₁ : k ≫ fst _ _ = specHom includeRight := by
    ext1
    rw [← h₂]
    exact Category.assoc ..
  have k₂ : k ≫ snd _ _ = specHom includeLeft ≫ v := by
    ext1
    rw [Over.comp_left, Over.comp_left, ← h₁]
    change (Spec.map e ≫ hg.fromSpec) ≫ _ = (Spec.map e ≫ _) ≫ hf.fromSpec
    rw [Category.assoc, Category.assoc, SpecMap_pullOver f g _ hp hf hg]
  have k₃ : (k ≫ ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A)).left =
      Spec.map (pullOver f g _ ha U ≫ e) ≫ hf.fromSpec := by
    rw [Spec.map_comp, Category.assoc, SpecMap_pullOver f g _ ha hf hg]
    exact Category.assoc ..
  have h₃ : φ ≫ pullOver f g _ ha U ≫ e =
      CommRingCat.ofHom (algebraMap R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, ← Category.assoc, ← k₃, Over.w]
    rfl
  let ρ : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R] Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ :=
    ⟨(pullOver f g _ ha U ≫ e).hom, fun r ↦ congr($h₃ r)⟩
  refine ⟨inferInstance, v, Over.mono_of_mono_left v, ρ, e, this, ?_, rfl, ?_⟩
  · rw [← k₂, ← k₁, Category.assoc, ← comp_mul]
    ext1
    exact k₃.symm
  · apply Spec.map_injective
    rw [Spec.map_comp, h₁]
    rfl

lemma exists_quotient_hopf
    (hq : (∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}))
    {R Λ : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ]
    [Module.Projective R Λ]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] [IsCommMonObj A] (i : specOver R Λ ⟶ A)
    [IsMonHom i] [Mono i] {Y : Over (Spec (CommRingCat.of R))} [IsLocallyNoetherian Y.left]
    (f : A ⟶ Y) [IsFinite f.left]
    (h : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A) ≫ f = snd (specOver R Λ) A ≫ f) :
    ∃ (Q : Over (Spec (CommRingCat.of R))) (q : A ⟶ Q) (π : Q ⟶ Y), IsFinite π.left ∧
      IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A) (snd (specOver R Λ) A) q q := by
  have : IsAffine (specOver R Λ).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (specOver R Λ).hom := inferInstance
  have : IsAffineHom (snd (specOver R Λ) A).left :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) (specOver R Λ).hom A.hom this
  have ha : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A).left ≫ f.left =
    (snd (specOver R Λ) A).left ≫ f.left := congr(($h).left)
  obtain ⟨Q, q, π, h₀, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient f.left _ _ ha _ rfl (fun U ↦ by
    obtain ⟨_, v, _, ρ, e, _, hρ, e₁, e₂⟩ :=
      exists_coaction i f.left _ ha rfl U.1 (U.2.preimage _) (U.2.preimage _)
    have hs := coaction_free i v ρ hρ
    obtain ⟨-, hff, hk⟩ := hq R Λ _ ρ (coaction_assoc i v ρ hρ) (coaction_counit i v ρ hρ) hs
    have hC : invariants f.left _ _ ha _ rfl U.1 = ρ.toRingHom.eqLocus
        (Algebra.TensorProduct.includeLeft : Γ(A.left, f.left ⁻¹ᵁ U.1) →ₐ[R] _).toRingHom := by
      ext x
      rw [mem_invariants, ← (ConcreteCategory.bijective_of_isIso e).1.eq_iff,
        ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e₁, e₂]
      rfl
    rw [hC]
    refine ⟨hff, ?_⟩
    refine (isPushout_equalizer ρ _ hs hk).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso e).symm (by simp) (by simp) ?_ ?_
    · rw [← e₁]; simp
    · rw [← e₂]; simp)
  refine ⟨Over.mk (π ≫ Y.hom), Over.homMk q (by simp [reassoc_of% h₀]), Over.homMk π rfl,
    h₁, h₂, h₃, h₄, ?_⟩
  exact IsPullback.of_map_of_faithful (Over.forget _) h₅

lemma exists_hopfAlgebra (R : Type) [CommRing R] [IsNoetherianRing R]
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsFinite H.hom] [Flat H.hom] :
    ∃ (Λ : Type) (_ : CommRing Λ) (_ : HopfAlgebra R Λ) (_ : Module.Finite R Λ)
      (_ : Module.Projective R Λ) (e : specOver R Λ ≅ H), IsMonHom e.hom := by
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨⟨Λ⟩, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of R) (G := Grp.mk H)).2 this
  let e' : specOver R Λ ≅ H := (Grp.forget _).mapIso e
  have h₁ : IsFinite (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have h₂ : Flat (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have : Module.Finite R Λ := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h₁)
  have : Module.Flat R Λ := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h₂)
  have : Module.FinitePresentation R Λ := Module.finitePresentation_of_finite R Λ
  exact ⟨Λ, inferInstance, inferInstance, inferInstance,
    Module.Flat.projective_of_finitePresentation, e', e.hom.hom.isMonHom_hom⟩

end GlobalTheory.AffineQuotient

namespace GlobalTheory

open AffineQuotient


set_option backward.isDefEq.respectTransparency false in
theorem exists_quotient_scheme_of_finite_flat_subgroup :
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsCommMonObj H], IsFinite H.hom → Flat H.hom → ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1) → (∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R))) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧ IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q := by
  intro hk hq hm R _ _ P H _ i _ _ _ _
  have := P.isAb.comm
  have := P.isAb.proper
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := hk R H ‹_› ‹_›
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  have := (hm _ P N hN).1
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra R H
  have hi : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf hq (e.hom ≫ i) (mulA P.A N) (by
    rw [mulA, comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
      ← comp_pow i, hi, comp_one, comp_one, _root_.one_mul])
  refine ⟨Q, q, h₂, h₃, h₄, ?_, ?_, ?_⟩
  · rw [← Over.w π]; infer_instance
  · rw [← Over.w π]; infer_instance
  · refine h₅.of_iso (whiskerRightIso e P.A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsFieldGlobalFnsSpec
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem heis_irred_of_isField
    (H : ∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤)
    (R G V : Type) [CommRing R] (hR : IsField R) [CommGroup G] [Finite G] [AddCommGroup V]
    [Module R V] (hpos : 0 < Module.finrank R V) (U : G → V ≃ₗ[R] V) (e : G → G →* Rˣ)
    (h1 : ∀ x y v, U x (U y v) = (e x y : R) • U y (U x v)) (h2 : Function.Injective e)
    (h3 : Module.finrank R V ^ 2 ≤ Nat.card G) (W : Submodule R V)
    (hW : ∀ x v, v ∈ W → U x v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  letI := hR.toField
  haveI : Module.Finite R V := Module.finite_of_finrank_pos hpos
  exact H R G V U e h1 h2 h3 W hW

theorem isField_globalFns_spec (K : Type) [Field K] :
    IsField Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
  MulEquiv.isField (Field.toIsField K)
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv

theorem irredSt_of_heis : (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v)) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ))) → (∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤) → WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → WeilNondegSt → MulNSt → GlobalSectionsRankAlgClosed → IrredSt := by
  intro hρ hWC hH hW hW3 hND hM hH0 K _ _ P k hk hkK W hstab
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ρ, hact, hcomm, -, -⟩ := hρ _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨hwc, hlift⟩ := hWC _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨hex, hmul, -, -⟩ := hW _ P k (baseOver (Spec (CommRingCat.of K)))
  obtain ⟨-, hskew, -⟩ := hW3 _ P k (baseOver (Spec (CommRingCat.of K)))
  have hsub : Subsingleton (baseOver (Spec (CommRingCat.of K))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let G : Subgroup (baseOver (Spec (CommRingCat.of K)) ⟶ P.A) := (powMonoidHom k).ker
  have hG : ∀ x : G, x.1 ^ k = 1 := fun x => x.2
  have hcard : Nat.card G = k ^ (2 * P.g) :=
    (hM _ P k hk1).2.2.2.2 K (𝟙 _) hkK
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  choose θ hθ using fun x : G => hlift x.1 (hG x) hsub
  choose c hc hcu using fun x y : G => hex x.1 y.1 (hG x) (hG y)
  have hcmul : ∀ x x' y : G, c (x * x') y = c x y * c x' y := fun x x' y =>
    (hcu (x * x') y _ (hmul _ _ _ _ _ (hc x y) (hc x' y))).symm
  have hcskew : ∀ x y : G, c y x = (c x y)⁻¹ := fun x y =>
    (hcu y x _ (hskew _ _ _ (hc x y))).symm
  let e : G → G →* Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ := fun x =>
    MonoidHom.mk' (fun y => c x y) (fun y y' => by
      rw [hcskew (y * y') x, hcmul, hcskew y x, hcskew y' x, mul_inv])
  have hfr := hH0 K P k hk1
  refine heis_irred_of_isField hH _ G _ (isField_globalFns_spec K)
    (by rw [hfr]; positivity) (fun x => ρ (θ x)) e ?_ ?_ ?_ W ?_
  · intro x y v
    refine hcomm _ _ _ ((hwc _ _ _).1 ?_) v
    rw [(hθ x).1, (hθ y).1]
    exact hc x y
  · intro x x' hxx
    have hone : ∀ y : G, c 1 y = 1 := fun y => by
      have := hcmul 1 1 y
      rw [_root_.mul_one] at this
      exact left_eq_mul.1 this
    have h : (x * x'⁻¹).1 = 1 := by
      refine hND K P k hkK _ (hG _) fun y hy => ?_
      have h1 : c x ⟨y, hy⟩ = c x' ⟨y, hy⟩ := DFunLike.congr_fun hxx ⟨y, hy⟩
      have h2 : c (x * x'⁻¹) ⟨y, hy⟩ = 1 := by
        rw [hcmul, h1, ← hcmul, mul_inv_cancel, hone]
      have := hc (x * x'⁻¹) ⟨y, hy⟩
      rwa [h2] at this
    exact mul_inv_eq_one.1 (Subtype.ext h)
  · rw [hfr, hcard, ← pow_mul, mul_comm]
  · intro x v hv
    exact hstab (θ x) (SecM.toSec P.A v) (SecM.toSec P.A (ρ (θ x) v)) ((hact _ _ _).2 rfl) hv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilStOfParts
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem weilSt_of_parts :
    (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A), x ^ k = 1 → y ^ k = 1 → ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x x' y : T ⟶ P.A) (c c' : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k x' y c' → WeilIs P.A P.L k (x * x') y (c * c')) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (l : ℕ) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), IsUnit ((k * l : ℕ) : Γ(T.left, ⊤)) → x ^ (k * l) = 1 → y ^ k = 1 → (WeilIs P.A P.L (k * l) x y c ↔ WeilIs P.A P.L k (x ^ l) y c)) → WeilSt := by
  intro h₁ h₂ h₃ h₄ S _ P k T
  exact ⟨h₁ S P k T, h₂ S P k T, (h₃ S P k T).1, h₄ S P k T⟩

end GlobalTheory
end

