module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinEtaleFormallyUnramified
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj CategoryTheory.MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem exists_algHom_apply_ne_zero_of_pointDerivation_eq_zero {C B : Type} [Field C] [IsAlgClosed C]
    [CommRing B] [Algebra C B] [FiniteDimensional C B]
    (hder : ∀ (φ : B →ₐ[C] C) (D : B →ₗ[C] C),
      (∀ a b, D (a * b) = φ a * D b + φ b * D a) → D = 0)
    {y : B} (hy : y ≠ 0) : ∃ φ : B →ₐ[C] C, φ y ≠ 0 := by
  classical
  set I : Ideal B := LinearMap.ker (LinearMap.mulRight B y) with hI
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ I := h ▸ Submodule.mem_top
    apply hy
    simpa [hI] using h1
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hItop
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.IsIntegral C (B ⧸ m) := Algebra.IsIntegral.of_finite C (B ⧸ m)
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C) (K := B ⧸ m)
  let e := AlgEquiv.ofBijective (Algebra.ofId C (B ⧸ m)) hbij
  let φ : B →ₐ[C] C := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m)
  have hφ : ∀ b, φ b = 0 ↔ b ∈ m := by
    intro b
    simp [φ, Ideal.Quotient.eq_zero_iff_mem]
  have hφa : ∀ b, b - algebraMap C B (φ b) ∈ m := by
    intro b
    rw [← hφ, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  refine ⟨φ, fun hy0 => ?_⟩
  have hym : y ∈ m := (hφ y).1 hy0
  have hmm : m ≤ m * m := by
    intro x hx
    by_contra hx2
    obtain ⟨ℓ, hℓx, hℓ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
      (p := (m * m).restrictScalars C) hx2 inferInstance
    have hℓ0 : ∀ z ∈ m * m, ℓ z = 0 := by
      intro z hz
      have hmem := Submodule.mem_map_of_mem (f := ℓ)
        (show z ∈ (m * m).restrictScalars C from hz)
      rw [hℓ] at hmem
      exact (Submodule.mem_bot C).1 hmem
    let D : B →ₗ[C] C := ℓ.comp (LinearMap.id - (Algebra.linearMap C B).comp φ.toLinearMap)
    have hDapp : ∀ b, D b = ℓ (b - algebraMap C B (φ b)) := fun b => rfl
    have hD : ∀ a b, D (a * b) = φ a * D b + φ b * D a := by
      intro a b
      have key : a * b - algebraMap C B (φ (a * b)) =
          φ a • (b - algebraMap C B (φ b)) + φ b • (a - algebraMap C B (φ a)) +
            (a - algebraMap C B (φ a)) * (b - algebraMap C B (φ b)) := by
        rw [map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
        ring
      rw [hDapp, hDapp, hDapp, key, map_add (f := _), map_add (f := _), map_smul, map_smul,
        hℓ0 _ (Ideal.mul_mem_mul (hφa a) (hφa b)), smul_eq_mul, smul_eq_mul, add_zero]
    have hD0 := hder φ D hD
    apply hℓx
    have h2 : D x = ℓ x := by
      rw [hDapp, (hφ x).2 hx, map_zero, sub_zero]
    rw [← h2, hD0, LinearMap.zero_apply]
  haveI : IsNoetherianRing B := isNoetherian_of_tower C inferInstance
  have hidem : IsIdempotentElem m := le_antisymm Ideal.mul_le_left hmm
  obtain ⟨e', _he', hme⟩ := (Ideal.isIdempotentElem_iff_of_fg m (IsNoetherian.noetherian m)).1 hidem
  have he'm : e' ∈ m := hme ▸ Submodule.mem_span_singleton_self e'
  have hyspan : y ∈ B ∙ e' := hme ▸ hym
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 hyspan
  have hey : e' * y = y := by
    rw [← hz, smul_eq_mul, ← _root_.mul_assoc, mul_comm e' z, _root_.mul_assoc, _he'.eq]
  have h1e : 1 - e' ∈ m := hIm (by
    rw [hI, LinearMap.mem_ker, LinearMap.mulRight_apply, sub_mul, _root_.one_mul, hey, sub_self])
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.add_mem h1e he'm))

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj CategoryTheory.MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem finrank_eq_card_algHom_of_pointDerivation_eq_zero {C B : Type} [Field C] [IsAlgClosed C]
    [CommRing B] [Algebra C B] [FiniteDimensional C B]
    (hder : ∀ (φ : B →ₐ[C] C) (D : B →ₗ[C] C),
      (∀ a b, D (a * b) = φ a * D b + φ b * D a) → D = 0) :
    Finite (B →ₐ[C] C) ∧ Module.finrank C B = Nat.card (B →ₐ[C] C) := by
  classical
  haveI hfin : Finite (B →ₐ[C] C) :=
    (linearIndependent_algHom_toLinearMap C B C).finite_of_isNoetherian
  refine ⟨hfin, le_antisymm ?_ (card_algHom_le_finrank C B C)⟩
  letI := Fintype.ofFinite (B →ₐ[C] C)
  let ev : B →ₗ[C] ((B →ₐ[C] C) → C) := LinearMap.pi fun φ => φ.toLinearMap
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    by_contra hb0
    obtain ⟨φ, hφ⟩ := exists_algHom_apply_ne_zero_of_pointDerivation_eq_zero hder hb0
    exact hφ (congrFun hb φ)
  calc Module.finrank C B ≤ Module.finrank C ((B →ₐ[C] C) → C) :=
        LinearMap.finrank_le_finrank_of_injective hev
    _ = Nat.card (B →ₐ[C] C) := by
        rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]


open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj CategoryTheory.MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.finEtale_main :
    (∀ (C O A : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) [CommRing O]
      [Algebra O C], v.Integers O →
      ∀ [CommRing A] [Algebra O A] [Module.Free O A] [Module.Finite O A],
      (∀ φ φ' : A →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ') →
      Finite (A →ₐ[O] O) ∧ (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) ∧
        Module.finrank O A = Nat.card (A →ₐ[O] O)) := by
  intro C O A _ _ v _ _ hv _ _ _ _ hpts
  classical
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hder : ∀ (φ : C ⊗[O] A →ₐ[C] C) (D : C ⊗[O] A →ₗ[C] C),
      (∀ a b, D (a * b) = φ a * D b + φ b * D a) → D = 0 := by
    intro φ D hD
    have hD1 : D 1 = 0 := by
      have h11 := hD 1 1
      rw [_root_.mul_one, map_one φ, _root_.one_mul] at h11
      linear_combination -h11
    let L : C ⊗[O] A →ₗ[C] DualNumber C :=
      (Algebra.linearMap C (DualNumber C)).comp φ.toLinearMap + (TrivSqZeroExt.inrHom C C).comp D
    have hLfst : ∀ b, (L b).fst = φ b := by
      intro b; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
    have hLsnd : ∀ b, (L b).snd = D b := by
      intro b; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
    let F : C ⊗[O] A →ₐ[C] DualNumber C := AlgHom.ofLinearMap L
      (TrivSqZeroExt.ext (by rw [hLfst, map_one]; rfl) (by rw [hLsnd, hD1]; rfl))
      (fun a b => TrivSqZeroExt.ext (by rw [TrivSqZeroExt.fst_mul, hLfst, hLfst, hLfst, map_mul])
        (by
          rw [TrivSqZeroExt.snd_mul, hLsnd, hLsnd, hLsnd, hLfst, hLfst, hD, smul_eq_mul,
            MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
          ring))
    let χ₁ : A →ₐ[O] DualNumber C := (F.restrictScalars O).comp Algebra.TensorProduct.includeRight
    let χ₀ : A →ₐ[O] DualNumber C :=
      (((Algebra.ofId C (DualNumber C)).comp φ).restrictScalars O).comp
        Algebra.TensorProduct.includeRight
    have hχ : χ₁ = χ₀ := hpts χ₁ χ₀ (fun a => by
      show (L _).fst = _
      rw [hLfst]
      rfl)
    have hDA : ∀ a : A, D ((1 : C) ⊗ₜ[O] a) = 0 := by
      intro a
      have h1 := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hχ a)
      change (L ((1 : C) ⊗ₜ[O] a)).snd =
        (algebraMap C (DualNumber C) (φ ((1 : C) ⊗ₜ[O] a))).snd at h1
      rw [hLsnd, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl] at h1
      exact h1
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      have hca : c ⊗ₜ[O] a = c • ((1 : C) ⊗ₜ[O] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [hca, map_smul, hDA, smul_zero, LinearMap.zero_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, LinearMap.zero_apply, add_zero]
  obtain ⟨_, hrankB⟩ := finrank_eq_card_algHom_of_pointDerivation_eq_zero hder
  let Ψ : (A →ₐ[O] O) → (C ⊗[O] A →ₐ[C] C) := fun ψ =>
    Algebra.TensorProduct.lift (Algebra.ofId C C) ((Algebra.ofId O C).comp ψ)
      (fun _ _ => Commute.all _ _)
  have hΨapp : ∀ ψ a, Ψ ψ ((1 : C) ⊗ₜ[O] a) = algebraMap O C (ψ a) := by
    intro ψ a; simp [Ψ]
  have hΨ : Function.Bijective Ψ := by
    refine ⟨fun ψ₁ ψ₂ h => AlgHom.ext fun a => hinj (by rw [← hΨapp, ← hΨapp, h]), fun φ => ?_⟩
    let φA : A →ₐ[O] C := (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
    have hmem : ∀ a, φA a ∈ (Algebra.ofId O C).range := by
      intro a
      have hint : IsIntegral O (φA a) := (Algebra.IsIntegral.isIntegral a).map φA
      obtain ⟨x, hx⟩ := hv.exists_of_le_one (hv.mem_of_integral hint)
      exact ⟨x, hx⟩
    let eO := AlgEquiv.ofInjective (Algebra.ofId O C) hinj
    refine ⟨eO.symm.toAlgHom.comp (φA.codRestrict _ hmem), ?_⟩
    apply Algebra.TensorProduct.ext (AlgHom.ext fun c => (AlgHom.commutes _ c).trans (AlgHom.commutes _ c).symm)
    refine AlgHom.ext fun a => ?_
    show Ψ _ ((1 : C) ⊗ₜ[O] a) = φ ((1 : C) ⊗ₜ[O] a)
    rw [hΨapp]
    show algebraMap O C (eO.symm ⟨φA a, hmem a⟩) = φA a
    have h1 := congrArg Subtype.val (eO.apply_symm_apply ⟨φA a, hmem a⟩)
    exact h1
  haveI hfinA : Finite (A →ₐ[O] O) := Finite.of_injective Ψ hΨ.1
  refine ⟨hfinA, fun f hf => ?_, ?_⟩
  · have h1 : (1 : C) ⊗ₜ[O] f = 0 := by
      by_contra hne
      obtain ⟨φ, hφ⟩ := exists_algHom_apply_ne_zero_of_pointDerivation_eq_zero hder hne
      obtain ⟨ψ, rfl⟩ := hΨ.2 φ
      apply hφ
      rw [hΨapp, hf ψ, map_zero]
    have hflat : Function.Injective ((Algebra.linearMap O C).rTensor A) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hinj
    have h2 : ((Algebra.linearMap O C).rTensor A) ((1 : O) ⊗ₜ[O] f) = 0 := by
      rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
      exact h1
    have h3 : (1 : O) ⊗ₜ[O] f = 0 := hflat (by rw [h2, map_zero])
    simpa using congrArg (TensorProduct.lid O A) h3
  · haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
    rw [← Module.finrank_baseChange (R := C), hrankB, Nat.card_eq_of_bijective Ψ hΨ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinRepExistsIsPullbackSpec
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finRep_exists_isPullback_spec {X Y : Scheme.{0}} (m : X ⟶ Y) [IsFinite m] [Flat m]
    (O : CommRingCat.{0}) (u : Spec O ⟶ Y) :
    ∃ (A : CommRingCat.{0}) (φ : O ⟶ A) (y : Spec A ⟶ X),
      φ.hom.Finite ∧ φ.hom.Flat ∧ IsPullback y (Spec.map φ) m u := by
  let N := Limits.pullback m u
  haveI : IsAffine N := isAffine_of_isAffineHom (Limits.pullback.snd m u)
  let f : Spec Γ(N, ⊤) ⟶ Spec O := N.isoSpec.inv ≫ Limits.pullback.snd m u
  have hf : Spec.map (Spec.preimage f) = f := Spec.map_preimage f
  refine ⟨Γ(N, ⊤), Spec.preimage f, N.isoSpec.inv ≫ Limits.pullback.fst m u, ?_, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hf]
    infer_instance
  · rw [← HasRingHomProperty.Spec_iff (P := @Flat), hf]
    infer_instance
  · rw [hf]
    refine (IsPullback.of_hasPullback m u).of_iso N.isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_ <;> simp [f]

theorem finRep_one_left {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    {P S : Type} [CommRing P] [Algebra R₀ P] [CommRing S] [Algebra R₀ S] (g : P →ₐ[R₀] S) :
    (1 : sp (R₀ := R₀) S ⟶ G).left =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (1 : sp (R₀ := R₀) P ⟶ G).left := by
  rw [← spMap_left, ← Over.comp_left, MonObj.comp_one]

theorem finRep_kernel_mul_finite_free :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ), IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra (O : Type) A) (_ : Algebra R₀ A) (_ : IsScalarTower R₀ (O : Type) A),
      Module.Free (O : Type) A ∧ Module.Finite (O : Type) A ∧ ∃ y : sp (R₀ := R₀) A ⟶ G, y ^ p = 1 ∧
      ∀ (S : Type) [CommRing S] [Algebra (O : Type) S] [Algebra R₀ S] [IsScalarTower R₀ (O : Type) S] (z : sp (R₀ := R₀) S ⟶ G), z ^ p = 1 →
        ∃! φ : A →ₐ[(O : Type)] S, spMap (φ.restrictScalars R₀) ≫ y = z) := by
  intro R₀ _ G _ _ O p hfin hflat _
  obtain ⟨A, φ, y, hφf, hφl, hpb⟩ := finRep_exists_isPullback_spec ((𝟙 G) ^ p : G ⟶ G).left
    (CommRingCat.of (O : Type)) (1 : sp (R₀ := R₀) (O : Type) ⟶ G).left
  letI : Algebra (O : Type) A := φ.hom.toAlgebra
  letI : Algebra R₀ A := (φ.hom.comp (algebraMap R₀ (O : Type))).toAlgebra
  haveI : IsScalarTower R₀ (O : Type) A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (O : Type) A := hφf
  haveI : Module.Flat (O : Type) A := hφl
  have hpow : ∀ {T : Over (Spec (CommRingCat.of R₀))} (z : T ⟶ G),
      z.left ≫ ((𝟙 G) ^ p : G ⟶ G).left = (z ^ p).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hy : y ≫ G.hom = (sp (R₀ := R₀) A).hom := by
    rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hpb.w, Category.assoc,
      Over.w (1 : sp (R₀ := R₀) (O : Type) ⟶ G)]
    simp only [sp, Over.mk_hom]
    rw [← Spec.map_comp]
    rfl
  let y' : sp (R₀ := R₀) A ⟶ G := Over.homMk y hy
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.free_of_flat_of_isLocalRing, inferInstance, y', ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [← hpow, finRep_one_left G (IsScalarTower.toAlgHom R₀ (O : Type) A)]
    exact hpb.w
  · intro S _ _ _ _ z hz
    have hw : z.left ≫ ((𝟙 G) ^ p : G ⟶ G).left =
        Spec.map (CommRingCat.ofHom (algebraMap (O : Type) S)) ≫
          (1 : sp (R₀ := R₀) (O : Type) ⟶ G).left := by
      rw [hpow, hz, finRep_one_left G (IsScalarTower.toAlgHom R₀ (O : Type) S)]
      rfl
    let l : Spec (CommRingCat.of S) ⟶ Spec A := hpb.lift _ _ hw
    have hl : Spec.map (Spec.preimage l) = l := Spec.map_preimage l
    have h1 : φ ≫ Spec.preimage l = CommRingCat.ofHom (algebraMap (O : Type) S) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hl]
      exact hpb.lift_snd _ _ hw
    refine ⟨⟨(Spec.preimage l).hom, fun r => congrArg (fun f => f.hom r) h1⟩, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change Spec.map (Spec.preimage l) ≫ y = z.left
      rw [hl]
      exact hpb.lift_fst _ _ hw
    · intro ψ hψ
      have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom : A ⟶ CommRingCat.of S) = l := by
        apply hpb.hom_ext
        · rw [hpb.lift_fst _ _ hw, ← hψ]
          rfl
        · rw [hpb.lift_snd _ _ hw, ← Spec.map_comp]
          congr 1
          ext r
          exact ψ.commutes r
      have h3 := Spec.map_injective (h2.trans hl.symm)
      ext a
      exact congrArg (fun f => f.hom a) h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FiniteAlgebraSplitLocal
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem finSplit_max_eq {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] (φ : A →ₐ[O] O) (N : Ideal A) (hN : N.IsMaximal)
    (h : RingHom.ker φ ≤ N) : N = (maximalIdeal O).comap φ := by
  refine hN.eq_of_le ?_ ?_
  · intro htop
    have h1 : (1 : A) ∈ (maximalIdeal O).comap φ := htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h1) isUnit_one
  · intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hN.ne_top
    rw [Ideal.eq_top_iff_one]
    have hy : algebraMap O A (↑hu.unit⁻¹) * x ∈ N := N.mul_mem_left _ hx
    have hφy : φ (algebraMap O A (↑hu.unit⁻¹) * x) = 1 := by
      rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      exact hu.val_inv_mul
    have hk : 1 - algebraMap O A (↑hu.unit⁻¹) * x ∈ N :=
      h (by rw [RingHom.mem_ker, map_sub, map_one, hφy, sub_self])
    simpa using N.add_mem hk hy

private theorem finSplit_exists {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [Finite (A →ₐ[O] O)] (M : Ideal A) :
    ∃ e : A, ∀ φ : A →ₐ[O] O, ((maximalIdeal O).comap φ = M → φ e = 1) ∧
      ((maximalIdeal O).comap φ ≠ M → φ e = 0) := by
  classical
  have := Fintype.ofFinite (A →ₐ[O] O)
  have key : ∀ φ ψ : A →ₐ[O] O, ∃ x : A, (maximalIdeal O).comap φ = M →
      (maximalIdeal O).comap ψ ≠ M → φ x = 1 ∧ ψ x = 0 := by
    intro φ ψ
    by_cases hφ : (maximalIdeal O).comap φ = M
    swap
    · exact ⟨0, fun h => absurd h hφ⟩
    by_cases hψ : (maximalIdeal O).comap ψ = M
    · exact ⟨0, fun _ h => absurd hψ h⟩
    have htop : RingHom.ker φ ⊔ RingHom.ker ψ = ⊤ := by
      by_contra hne
      obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal _ hne
      have e1 := finSplit_max_eq φ N hN (le_sup_left.trans hle)
      have e2 := finSplit_max_eq ψ N hN (le_sup_right.trans hle)
      exact hψ (e2.symm.trans (e1.trans hφ))
    have h1 : (1 : A) ∈ RingHom.ker φ ⊔ RingHom.ker ψ := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨b, fun _ _ => ⟨?_, RingHom.mem_ker.1 hb⟩⟩
    have hφab := congrArg φ hab
    rw [map_add (f := _), RingHom.mem_ker.1 ha, zero_add, map_one] at hφab
    exact hφab
  choose x hx using key
  refine ⟨1 - ∏ φ ∈ Finset.univ.filter (fun φ : A →ₐ[O] O => (maximalIdeal O).comap φ = M),
      (1 - ∏ ψ ∈ Finset.univ.filter (fun ψ : A →ₐ[O] O => (maximalIdeal O).comap ψ ≠ M), x φ ψ),
      fun φ0 => ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
  · rw [map_sub, map_one, map_prod, sub_eq_self]
    apply Finset.prod_eq_zero (i := φ0) (by simp [h0])
    rw [map_sub, map_one, map_prod, sub_eq_zero, eq_comm]
    apply Finset.prod_eq_one
    intro ψ hψ
    exact (hx φ0 ψ h0 (Finset.mem_filter.1 hψ).2).1
  · rw [map_sub, map_one, map_prod, sub_eq_zero, eq_comm]
    apply Finset.prod_eq_one
    intro φ hφ
    rw [map_sub, map_one, map_prod, sub_eq_self]
    apply Finset.prod_eq_zero (i := φ0) (by simp [h0])
    exact (hx φ φ0 (Finset.mem_filter.1 hφ).2 h0).2

theorem finite_algebra_split_local :
  (∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Finite (A →ₐ[O] O)],
    (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) →
    ∃ (n : ℕ) (ε : Fin n → A), CompleteOrthogonalIdempotents ε ∧ ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})) := by
  intro O A _ _ _ _ _ _ hsep
  classical
  have := Fintype.ofFinite (A →ₐ[O] O)
  have hone : (1 : O) ∉ maximalIdeal O := fun h =>
    mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h) isUnit_one
  let Pts := Set.range (fun φ : A →ₐ[O] O => (maximalIdeal O).comap φ)
  let eqv : Fin (Fintype.card Pts) ≃ Pts := (Fintype.equivFin Pts).symm
  choose e he using fun M : Ideal A => finSplit_exists (O := O) M
  have hval : ∀ (M : Ideal A) (φ : A →ₐ[O] O),
      φ (e M) = if (maximalIdeal O).comap φ = M then 1 else 0 := by
    intro M φ
    split_ifs with h
    · exact (he M φ).1 h
    · exact (he M φ).2 h
  have ext : ∀ a b : A, (∀ φ : A →ₐ[O] O, φ a = φ b) → a = b := fun a b h =>
    sub_eq_zero.1 (hsep _ fun φ => by rw [map_sub, h φ, sub_self])
  have hmax : ∀ N : Ideal A, N.IsMaximal → ∃ φ : A →ₐ[O] O, (maximalIdeal O).comap φ = N := by
    intro N hN
    by_contra hcon
    simp only [not_exists] at hcon
    have hnot : ∀ φ : A →ₐ[O] O, ¬ RingHom.ker φ ≤ N := fun φ hle =>
      hcon φ (finSplit_max_eq φ N hN hle).symm
    simp only [SetLike.not_le_iff_exists] at hnot
    choose a ha haN using hnot
    have := hN.isPrime
    have h0 : ∏ φ, a φ = 0 := hsep _ fun ψ => by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ ψ) (RingHom.mem_ker.1 (ha ψ))
    have hin : ∏ φ, a φ ∈ N := h0 ▸ N.zero_mem
    obtain ⟨φ, -, hφ⟩ := Ideal.IsPrime.prod_mem_iff.1 hin
    exact haN φ hφ
  refine ⟨Fintype.card Pts, fun i => e (eqv i).1, ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩
  · show e (eqv i).1 * e (eqv i).1 = e (eqv i).1
    apply ext
    intro φ
    rw [map_mul, hval]
    split_ifs <;> simp
  · show e (eqv i).1 * e (eqv j).1 = 0
    have hne : (eqv i).1 ≠ (eqv j).1 := fun h => hij (eqv.injective (Subtype.ext h))
    apply ext
    intro φ
    rw [map_mul, hval, hval, map_zero]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) hne
    all_goals simp
  · apply ext
    intro φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [hval]
    rw [Fintype.sum_equiv eqv _
      (fun M : Pts => if (maximalIdeal O).comap φ = M.1 then (1 : O) else 0) (fun _ => rfl)]
    rw [Finset.sum_eq_single ⟨(maximalIdeal O).comap φ, φ, rfl⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · obtain ⟨φ0, hφ0⟩ := (eqv i).2
    replace hφ0 : (maximalIdeal O).comap φ0 = (eqv i).1 := hφ0
    have hmem : ∀ ψ : A →ₐ[O] O,
        1 - e (eqv i).1 ∈ (maximalIdeal O).comap ψ ↔ (maximalIdeal O).comap ψ = (eqv i).1 := by
      intro ψ
      rw [Ideal.mem_comap, map_sub, map_one, hval]
      split_ifs with h
      · simp [h]
      · simp only [sub_zero, h, iff_false]
        exact hone
    have hJM : Ideal.span {1 - e (eqv i).1} ≤ (eqv i).1 := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have h := (hmem φ0).2 hφ0
      rw [hφ0] at h
      exact h
    have hMtop : (eqv i).1 ≠ ⊤ := by
      rw [← hφ0]
      intro h
      have h1 : (1 : A) ∈ (maximalIdeal O).comap φ0 := h ▸ Submodule.mem_top
      rw [Ideal.mem_comap, map_one] at h1
      exact hone h1
    have hJ : Ideal.span {1 - e (eqv i).1} ≠ ⊤ := fun h => hMtop (top_le_iff.1 (h ▸ hJM))
    have := Ideal.Quotient.nontrivial_iff.2 hJ
    obtain ⟨Q0, hQ0⟩ := Ideal.exists_maximal (A ⧸ Ideal.span {1 - e (eqv i).1})
    have hcomap : ∀ Q : Ideal (A ⧸ Ideal.span {1 - e (eqv i).1}), Q.IsMaximal →
        Q = (eqv i).1.map (Ideal.Quotient.mk _) := by
      intro Q hQ
      have := hQ
      have hQ' : (Q.comap (Ideal.Quotient.mk (Ideal.span {1 - e (eqv i).1}))).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      obtain ⟨ψ, hψ⟩ := hmax _ hQ'
      have hin : 1 - e (eqv i).1 ∈ Q.comap (Ideal.Quotient.mk (Ideal.span {1 - e (eqv i).1})) := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))]
        exact Q.zero_mem
      rw [← hψ] at hin
      have hψM := (hmem ψ).1 hin
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, ← hψ, hψM]
    exact IsLocalRing.of_unique_max_ideal
      ⟨Q0, hQ0, fun Q hQ => (hcomap Q hQ).trans (hcomap Q0 hQ0).symm⟩

end GlobalTheory
end

