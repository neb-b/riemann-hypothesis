module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanEqTopOfFinrankFibreEq
section
open TensorProduct Module

namespace GlobalTheory

open TensorProduct Module in
variable {B A M : Type*} [CommRing B] [CommRing A] [Algebra B A] [Algebra.IsIntegral B A]
  [AddCommGroup M] [Module B M] {r : ℕ} in
private lemma finrank_fiber_eq (hinj : Function.Injective (algebraMap B A))
    (b : Basis (Fin r) A (A ⊗[B] M)) (P : Ideal B) [P.IsMaximal] :
    letI := Ideal.Quotient.field P
    finrank (B ⧸ P) ((B ⧸ P) ⊗[B] M) = r := by
  letI := Ideal.Quotient.field P
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  haveI : Q.LiesOver P := ⟨hQP.symm⟩
  letI := Ideal.Quotient.field Q
  have h1 : finrank (A ⧸ Q) ((A ⧸ Q) ⊗[A] (A ⊗[B] M)) = r := by
    rw [finrank_eq_card_basis (Algebra.TensorProduct.basis (A ⧸ Q) b), Fintype.card_fin]
  rw [← Module.finrank_baseChange (R := A ⧸ Q),
    (AlgebraTensorModule.cancelBaseChange B (B ⧸ P) (A ⧸ Q) (A ⧸ Q) M).finrank_eq,
    ← (AlgebraTensorModule.cancelBaseChange B A (A ⧸ Q) (A ⧸ Q) M).finrank_eq, h1]


open TensorProduct Module in
theorem _root_.GlobalTheory.nonempty_basis_of_basis_baseChange {B A M : Type*} [CommRing B] [CommRing A]
    [Finite (MaximalSpectrum B)] [Algebra B A] [Algebra.IsIntegral B A] [AddCommGroup M]
    [Module B M] [Module.Finite B M] {r : ℕ}
    (hinj : Function.Injective (algebraMap B A)) (b : Basis (Fin r) A (A ⊗[B] M)) :
    Nonempty (Basis (Fin r) B M) := by
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum B)
  have hfib : ∀ P : MaximalSpectrum B, ∃ e : Fin r → M,
      Submodule.span (B ⧸ P.asIdeal) (Set.range fun j => (1 : B ⧸ P.asIdeal) ⊗ₜ[B] e j) = ⊤ := by
    intro P
    haveI := P.isMaximal
    letI := Ideal.Quotient.field P.asIdeal
    let β := Module.finBasisOfFinrankEq (B ⧸ P.asIdeal) _ (finrank_fiber_eq hinj b P.asIdeal)
    choose e he using fun j => TensorProduct.mk_surjective B M (B ⧸ P.asIdeal)
      Ideal.Quotient.mk_surjective (β j)
    refine ⟨e, ?_⟩
    have : (fun j => (1 : B ⧸ P.asIdeal) ⊗ₜ[B] e j) = β := funext he
    rw [this, β.span_eq]
  choose e he using hfib
  have hcrt : ∀ P : MaximalSpectrum B, ∃ c : B,
      ∀ P' : MaximalSpectrum B, c - (if P' = P then 1 else 0) ∈ P'.asIdeal := fun P =>
    Ideal.exists_forall_sub_mem_ideal (I := fun P' : MaximalSpectrum B => P'.asIdeal)
      (fun P₁ P₂ h => by
        haveI := P₁.isMaximal
        haveI := P₂.isMaximal
        exact Ideal.isCoprime_of_isMaximal fun h' => h (MaximalSpectrum.ext h')) _
  choose c hc using hcrt
  let x : Fin r → M := fun j => ∑ P, c P • e P j
  let N := Submodule.span B (Set.range x)
  have key : ∀ P : MaximalSpectrum B, (⊤ : Submodule B (M ⧸ N)) ≤ P.asIdeal • ⊤ := by
    intro P
    have hmk : ∀ P', Ideal.Quotient.mk P.asIdeal (c P') = if P = P' then 1 else 0 := by
      intro P'
      have := hc P' P
      split_ifs at this ⊢ with h
      · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
        exact this
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using this)
    have hsm : ∀ (a : B) (y : (B ⧸ P.asIdeal) ⊗[B] M),
        a • y = Ideal.Quotient.mk P.asIdeal a • y := fun a y =>
      (algebraMap_smul (B ⧸ P.asIdeal) a y).symm
    have hx : ∀ j, (1 : B ⧸ P.asIdeal) ⊗ₜ[B] x j = 1 ⊗ₜ e P j := by
      intro j
      simp only [x, tmul_sum, tmul_smul]
      simp only [hsm, hmk, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
    have h0 : N.mkQ.baseChange (B ⧸ P.asIdeal) = 0 := by
      apply LinearMap.ext_on_range (he P)
      intro j
      rw [← hx, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨j, rfl⟩), tmul_zero,
        LinearMap.zero_apply]
    have hsurj : Function.Surjective (N.mkQ.baseChange (B ⧸ P.asIdeal)) :=
      LinearMap.lTensor_surjective (B ⧸ P.asIdeal) N.mkQ_surjective
    have hsub : Subsingleton ((B ⧸ P.asIdeal) ⊗[B] (M ⧸ N)) := ⟨fun y z => by
      obtain ⟨y', rfl⟩ := hsurj y
      obtain ⟨z', rfl⟩ := hsurj z
      simp [h0]⟩
    have hq := (TensorProduct.quotTensorEquivQuotSMul (M ⧸ N) P.asIdeal).symm.toEquiv.subsingleton
    rw [Submodule.Quotient.subsingleton_iff] at hq
    rw [hq]
  have hann : Module.annihilator B (M ⧸ N) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨t, ht1, ht⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P ⊤
      Module.Finite.fg_top (key ⟨P, hP⟩)
    have htP : t ∈ P := hle (Module.mem_annihilator.mpr fun q => ht q trivial)
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using P.sub_mem htP ht1))
  have hN : N = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have h1 : (1 : B) ∈ Module.annihilator B (M ⧸ N) := hann ▸ Submodule.mem_top
    have := Module.mem_annihilator.mp h1 (N.mkQ m)
    simpa [Submodule.Quotient.mk_eq_zero] using this
  let f := Fintype.linearCombination B x
  have hfs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hN
  let F := f.baseChange A
  have hFs : Function.Surjective F := LinearMap.lTensor_surjective A hfs
  let φ : (Fin r → A) →ₗ[A] (Fin r → A) := b.equivFun.toLinearMap ∘ₗ F ∘ₗ
    (TensorProduct.piScalarRight B A A (Fin r)).symm.toLinearMap
  have hφs : Function.Surjective φ := by
    simpa [φ] using b.equivFun.surjective.comp
      (hFs.comp (TensorProduct.piScalarRight B A A (Fin r)).symm.surjective)
  have hφi := OrzechProperty.injective_of_surjective_endomorphism φ hφs
  have hFi : Function.Injective F := by
    intro y z hyz
    have := @hφi (TensorProduct.piScalarRight B A A (Fin r) y)
      (TensorProduct.piScalarRight B A A (Fin r) z) (by
        simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hyz])
    exact (TensorProduct.piScalarRight B A A (Fin r)).injective this
  have hfi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have h1 : F ((1 : A) ⊗ₜ v) = F 0 := by
      rw [LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hv, tmul_zero, map_zero]
    have h2 := congrArg (TensorProduct.piScalarRight B A A (Fin r)) (hFi h1)
    rw [Submodule.mem_bot]
    funext i
    exact hinj (by rw [Pi.zero_apply, map_zero, Algebra.algebraMap_eq_smul_one]; simpa using congrFun h2 i)
  exact ⟨Basis.ofEquivFun (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).symm⟩


open TensorProduct Module in
theorem _root_.GlobalTheory.finrank_eq_mul_of_basis_tensor_self (k B A : Type) [Field k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Module.Finite k A] (r : ℕ)
    (hinj : Function.Injective (algebraMap B A))
    (hb : Nonempty (Module.Basis (Fin r) A (TensorProduct B A A))) :
    Module.finrank k A = r * Module.finrank k B := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · haveI : Subsingleton A := by
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_zero (algebraMap B A), ← map_one (algebraMap B A), Subsingleton.elim (0 : B) 1]
    simp [Module.finrank_zero_of_subsingleton]
  haveI : Module.Finite k B :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom k B A).toLinearMap hinj
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  haveI : Module.Finite B A := Module.Finite.of_restrictScalars_finite k B A
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  obtain ⟨β⟩ := _root_.GlobalTheory.nonempty_basis_of_basis_baseChange (M := A) hinj hb.some
  haveI : Module.Free B A := Module.Free.of_basis β
  rw [← Module.finrank_mul_finrank k B A, finrank_eq_card_basis β, Fintype.card_fin, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkRetractionOfSmallLifting
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.SmallLift

theorem map_closedPoint {X : Scheme.{0}} {x : X} {R : CommRingCat.{0}} [IsLocalRing R]
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (closedPoint R) = x := by
  refine (Scheme.Hom.comp_apply (Spec.map φ) (X.fromSpecStalk x) (closedPoint R)).trans ?_
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := φ))).trans
    Scheme.fromSpecStalk_closedPoint

theorem step {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (C : Type) [CommRing C] [IsLocalRing C]
    (I : Ideal C) [IsLocalRing (C ⧸ I)]
    (H : ∀ (a : Spec (CommRingCat.of (C ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of C) ⟶ Y),
      a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b →
      ∃ l : Spec (CommRingCat.of C) ⟶ X,
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b)
    (π : Y.presheaf.stalk (f x) ⟶ CommRingCat.of C)
    (ψ : X.presheaf.stalk x ⟶ CommRingCat.of (C ⧸ I)) [IsLocalHom ψ.hom]
    (hψ : ψ.hom.comp (f.stalkMap x).hom = (Ideal.Quotient.mk I).comp π.hom) :
    ∃ g : X.presheaf.stalk x →+* C, IsLocalHom g ∧ g.comp (f.stalkMap x).hom = π.hom := by
  have e : f.stalkMap x ≫ ψ =
      π ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    ext1
    exact hψ
  obtain ⟨l, hl, hs⟩ := H (Spec.map ψ ≫ X.fromSpecStalk x)
    (Spec.map π ≫ Y.fromSpecStalk (f x)) (by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc, e])
  obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.surjective l
  rw [SpecToEquivOfLocalRing_symm_apply] at hs hl
  dsimp only at hs hl
  have hmk : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hx : x' = x := by
    rw [← Spec.map_comp_assoc] at hl
    have : IsLocalHom (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
      @RingHom.isLocalHom_comp _ _ _ _ _ _ _ φ.hom hmk hφ
    have h1 := map_closedPoint (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))
    rw [hl] at h1
    exact h1.symm.trans (map_closedPoint ψ)
  subst hx
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
  have : Mono (Y.fromSpecStalk (f x')) :=
    SurjectiveOnStalks.mono_of_injective (Y.fromSpecStalk (f x')).isEmbedding.injective
  have key := Spec.map_injective ((cancel_mono _).1 hs)
  exact ⟨φ.hom, hφ, congrArg CommRingCat.Hom.hom key⟩

theorem pow_ne_top {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    maximalIdeal A ^ (n + 1) ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self n.succ_ne_zero))

theorem isLocalRing_quot {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
  haveI := Ideal.Quotient.nontrivial_iff.2 (pow_ne_top (A := A) n)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

theorem map_maximalIdeal_quot {A : Type} [CommRing A] [IsLocalRing A] (J : Ideal A)
    [IsLocalRing (A ⧸ J)] :
    (maximalIdeal A).map (Ideal.Quotient.mk J) = maximalIdeal (A ⧸ J) :=
  IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

theorem isArtinianRing_quot {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1)) := by
  haveI := isLocalRing_quot (A := A) n
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n + 1, ?_⟩
  rw [← map_maximalIdeal_quot, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

theorem exists_retraction : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → ∀ (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))], Function.Surjective (f.residueFieldMap x).hom → ∀ n : ℕ, ∃ ψ : X.presheaf.stalk x →+* Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1), ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ := by
  intro X Y f H x _ hs n
  suffices h : ∃ ψ : X.presheaf.stalk x →+*
      Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1),
      IsLocalHom ψ ∧ ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ from
    let ⟨ψ, _, h⟩ := h; ⟨ψ, h⟩
  induction n with
  | zero =>
    let e : ResidueField (Y.presheaf.stalk (f x)) ≃+* ResidueField (X.presheaf.stalk x) :=
      RingEquiv.ofBijective (f.residueFieldMap x).hom ⟨(f.residueFieldMap x).hom.injective, hs⟩
    let q : (Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (0 + 1)) ≃+*
        ResidueField (Y.presheaf.stalk (f x)) :=
      Ideal.quotEquivOfEq (by rw [zero_add, pow_one])
    let r := (q.trans e).symm
    haveI := isLocalRing_quot (A := Y.presheaf.stalk (f x)) 0
    refine ⟨r.toRingHom.comp (residue _), ?_, ?_⟩
    · have : IsLocalHom r.toRingHom := IsLocalHom.of_surjective _ r.surjective
      infer_instance
    · ext a
      change r (residue _ ((f.stalkMap x).hom a)) = _
      rw [RingEquiv.symm_apply_eq]
      rfl
  | succ n ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    set A := Y.presheaf.stalk (f x) with hA
    haveI := isLocalRing_quot (A := A) n
    haveI := isLocalRing_quot (A := A) (n + 1)
    haveI := isArtinianRing_quot (A := A) (n + 1)
    have hle : maximalIdeal A ^ (n + 1 + 1) ≤ maximalIdeal A ^ (n + 1) :=
      Ideal.pow_le_pow_right (Nat.le_succ _)
    let I : Ideal (A ⧸ maximalIdeal A ^ (n + 1 + 1)) :=
      (maximalIdeal A ^ (n + 1)).map (Ideal.Quotient.mk _)
    let r : (A ⧸ maximalIdeal A ^ (n + 1)) ≃+* ((A ⧸ maximalIdeal A ^ (n + 1 + 1)) ⧸ I) :=
      (DoubleQuot.quotQuotEquivQuotOfLE hle).symm
    haveI : IsLocalRing ((A ⧸ maximalIdeal A ^ (n + 1 + 1)) ⧸ I) := r.isLocalRing
    have h1 : I ≤ maximalIdeal _ := by
      rw [← map_maximalIdeal_quot]
      exact Ideal.map_mono (Ideal.pow_le_self n.succ_ne_zero)
    have h2 : maximalIdeal _ * I = ⊥ := by
      rw [← map_maximalIdeal_quot, ← Ideal.map_mul, ← pow_succ', Ideal.map_quotient_self]
    have : IsLocalHom r.toRingHom := IsLocalHom.of_surjective _ r.surjective
    have hl : IsLocalHom (r.toRingHom.comp ψ) := inferInstance
    let π : A →+* A ⧸ maximalIdeal A ^ (n + 1 + 1) := Ideal.Quotient.mk _
    refine @step X Y f x _ _ _ I _ (H _ I h1 h2) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (r.toRingHom.comp ψ)) hl ?_
    change (r.toRingHom.comp ψ).comp _ = _
    rw [RingHom.comp_assoc, h]
    ext a
    rfl

end GlobalTheory.SmallLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardBasisExtensionDetNeZero
section
open Module Submodule

namespace GlobalTheory

theorem extend_linearIndependent_rows_by_standard_basis
    {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K) :
    LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧
      (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by
  intro hv
  set std : Fin n → (Fin n → K) := fun i => Pi.single i (1 : K) with hstd
  set W : Submodule K (Fin n → K) := span K (Set.range v) with hWdef
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (W.mkQ ∘ std)
  classical
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hW : finrank K W = Fintype.card J := finrank_span_eq_card hv
  have hQ := Submodule.finrank_quotient_add_finrank W
  have hfin : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hκ : Fintype.card κ ≤ finrank K ((Fin n → K) ⧸ W) := hli.fintype_card_le_finrank

  let C := {i : Fin n // i ∉ Set.range a}
  have hC : Fintype.card C = n - Fintype.card κ := by
    have h1 : Fintype.card C = Fintype.card (Fin n) - Fintype.card (Set.range a) := by
      simp only [C]
      rw [Fintype.card_subtype_compl]
    rw [h1, Fintype.card_fin, Set.card_range_of_injective ha]
  have hJC : Fintype.card J ≤ Fintype.card C := by omega
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hJC
  let e : J → Fin n := fun j => (φ j).1
  have he : Function.Injective e := fun x y h => φ.injective (Subtype.ext h)
  have heC : ∀ j, e j ∉ Set.range a := fun j => (φ j).2
  refine ⟨e, he, ?_⟩
  set f := Function.extend e v std with hf
  have hfe : ∀ j, f (e j) = v j := fun j => he.extend_apply v std j
  have hfa : ∀ k, f (a k) = std (a k) := by
    intro k
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    exact heC j ⟨k, hj.symm⟩

  have hstdspan : span K (Set.range std) = ⊤ := by
    have := (Pi.basisFun K (Fin n)).span_eq
    convert this using 2
    ext i
    simp [std, Pi.basisFun_apply]
  have hspanf : span K (Set.range f) = ⊤ := by
    have hWle : W ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨e j, hfe j⟩
    have hAle : span K (Set.range (std ∘ a)) ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact subset_span ⟨a k, hfa k⟩
    have htop : W ⊔ span K (Set.range (std ∘ a)) = ⊤ := by
      rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
      have : (W.mkQ ∘ std ∘ a) = (W.mkQ ∘ std) ∘ a := rfl
      rw [← Function.comp_assoc] at *
      rw [hspan, Set.range_comp, ← Submodule.map_span, hstdspan, Submodule.map_top, LinearMap.range_eq_top]
      exact W.mkQ_surjective
    exact eq_top_iff.mpr (htop ▸ sup_le hWle hAle)
  have hlin : LinearIndependent K f := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanf, finrank_top, hfin,
      Fintype.card_fin]
  have hunit : IsUnit (Matrix.of f) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hlin
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStripFinitelyManyPrimeFactors
section
namespace GlobalTheory

theorem strip_prime_factors (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ}
    (π : Fin n → R) (J : Finset (Fin n)) (x : R) (hx : x ≠ 0) :
    ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧
      ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by
  induction J using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, x, by simp, by simp⟩
  | @insert j J hj ih =>
    obtain ⟨m, y, hxy, hy⟩ := ih
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hxy)
    by_cases hp : Prime (π j)
    · obtain ⟨y', hy', hnd⟩ :=
        (FiniteMultiplicity.of_not_isUnit hp.not_unit hy0).exists_eq_pow_mul_and_not_dvd
      refine ⟨Function.update m j (multiplicity (π j) y), y', ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self]
        have hJ : ∏ i ∈ J, π i ^ Function.update m j (multiplicity (π j) y) i
            = ∏ i ∈ J, π i ^ m i := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
        rw [hJ, hxy]
        conv_lhs => rw [hy']
        ring
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hnd hdvd
        · exact hy i hi hpi (hdvd.trans (Dvd.intro_left _ hy'.symm))
    · refine ⟨Function.update m j 0, y, ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self, pow_zero, one_mul]
        rw [hxy]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hp hpi
        · exact hy i hi hpi hdvd

theorem strip_prime_factors_target : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y :=
  fun R _ _ _ _ π J x hx => strip_prime_factors R π J x hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjLocalizationMvPolynomialOfEssFiniteTyp
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_surj_localization_mvPolynomial_of_essFiniteType :
    ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R]
      [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime)
      (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by
  intro Λ R _ _ _ _ h
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff Λ R).mp h
  let y : Fin σ.card → R := fun i => (σ.equivFin.symm i : R)
  let φ₀ : MvPolynomial (Fin σ.card) Λ →ₐ[Λ] R := MvPolynomial.aeval y
  have hrange : Algebra.adjoin Λ (σ : Set R) = φ₀.range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨σ.equivFin ⟨x, hx⟩, by simp [y]⟩
    · rintro ⟨i, rfl⟩
      exact (σ.equivFin.symm i).2
  let P : Ideal (MvPolynomial (Fin σ.card) Λ) := (maximalIdeal R).comap φ₀
  have hunit : ∀ b : P.primeCompl, IsUnit (φ₀ b) := by
    intro b
    by_contra hb
    exact b.2 ((mem_maximalIdeal _).mpr hb)
  refine ⟨σ.card, P, inferInstance, IsLocalization.liftAlgHom (M := P.primeCompl) (f := φ₀) hunit, ?_⟩
  intro r
  obtain ⟨t, ht, htu, hrt⟩ := hσ r
  rw [hrange] at ht hrt
  obtain ⟨b, rfl⟩ := ht
  obtain ⟨a, ha⟩ := hrt
  have hb : b ∈ P.primeCompl := fun hbP => (mem_maximalIdeal _).mp hbP htu
  refine ⟨IsLocalization.mk' (Localization.AtPrime P) a ⟨b, hb⟩, ?_⟩
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
  change φ₀ a = φ₀ b * r
  exact ha.trans (mul_comm _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPowEq
section
open Polynomial IsLocalRing

namespace GlobalTheory.UnitPowerExistence

theorem exists_unit_pow_eq (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (IsLocalRing.ResidueField O)] (q : ℕ) (hq : IsUnit (q : O)) (hpos : 0 < q)
    (w : Oˣ) : ∃ v : Oˣ, v ^ q = w := by
  have hq0 : (q : ResidueField O) ≠ 0 := by
    have h := hq.map (residue O)
    rw [map_natCast] at h
    exact h.ne_zero
  have hw : residue O (w : O) ≠ 0 := (w.isUnit.map (residue O)).ne_zero
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (X ^ q - C (residue O (w : O)))
    (by rw [degree_X_pow_sub_C hpos]; exact_mod_cast hpos.ne') (separable_X_pow_sub_C _ hq0 hw)
  obtain ⟨b, rfl⟩ := residue_surjective a₀
  have hb : b ^ q - (w : O) ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_sub, map_pow]
    simpa [IsRoot] using ha₀
  have hbu : IsUnit b := by
    by_contra hb'
    have h2 : b ^ q ∈ maximalIdeal O := Ideal.pow_mem_of_mem _ ((mem_maximalIdeal b).2 hb') q hpos
    have h3 : (w : O) ∈ maximalIdeal O := by simpa using sub_mem h2 hb
    exact (mem_maximalIdeal _).1 h3 w.isUnit
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ q - C (w : O)) (monic_X_pow_sub_C _ hpos.ne') b
    (by simpa using hb) (by
      rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X]
      exact hq.mul (hbu.pow (q - 1)))
  have hapow : a ^ q = w := by simpa [IsRoot, sub_eq_zero] using ha
  have hau : IsUnit a := (isUnit_pow_iff hpos.ne').1 (hapow ▸ w.isUnit)
  exact ⟨hau.unit, Units.ext (by simpa using hapow)⟩

end GlobalTheory.UnitPowerExistence
end

