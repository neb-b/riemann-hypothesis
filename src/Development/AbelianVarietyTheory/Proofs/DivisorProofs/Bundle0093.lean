module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiolaIdentityAdjugateDivergenceFree
section
namespace GlobalTheory.PiolaAlg

open Finset Matrix

variable {K R : Type} [CommRing K] [CommRing R] [Algebra K R]

theorem derivation_prod {ι : Type} [DecidableEq ι] (D : Derivation K R R) (f : ι → R) (s : Finset ι) :
    D (∏ i ∈ s, f i) = ∑ k ∈ s, ∏ i ∈ s, Function.update f k (D (f k)) i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha, prod_insert ha, Function.update_self,
      prod_congr rfl (fun i hi => Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _)]
    simp only [smul_eq_mul, mul_sum]
    rw [add_comm, mul_comm (∏ i ∈ s, f i)]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [prod_insert ha, Function.update_of_ne (ne_of_mem_of_not_mem hk ha).symm]

theorem derivation_det {ι : Type} [Fintype ι] [DecidableEq ι] (D : Derivation K R R)
    (A : Matrix ι ι R) :
    D A.det = ∑ k, (A.updateRow k fun l => D (A k l)).det := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [det_apply, map_sum]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
  · simp only [h, one_smul, Units.neg_smul, map_neg, sum_neg_distrib, neg_inj]
    rw [derivation_prod]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine sum_congr rfl fun k _ => prod_congr rfl fun i _ => ?_
    by_cases hik : i = k
    · subst hik; simp [updateRow_apply]
    · rw [Function.update_of_ne hik, updateRow_apply, if_neg (σ.injective.ne hik)]

theorem piola {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R)
    (M : Matrix ι ι R) (hM : ∀ h i j, δ h (M i j) = δ i (M h j)) (j : ι) :
    ∑ i, δ i (M.adjugate j i) = 0 := by
  set f : ι × ι → R := fun p =>
    ((M.updateRow p.1 (Pi.single j 1)).updateRow p.2
      fun l => δ p.1 ((M.updateRow p.1 (Pi.single j 1)) p.2 l)).det with hf
  have hS : ∑ i, δ i (M.adjugate j i) = ∑ p ∈ univ ×ˢ univ, f p := by
    rw [sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [adjugate_apply, derivation_det]
  have hdiag : ∀ i, f (i, i) = 0 := by
    intro i
    refine det_eq_zero_of_row_eq_zero i fun l => ?_
    simp only [updateRow_self]
    by_cases hl : l = j
    · subst hl; simp
    · simp [Pi.single_apply, hl]
  have hpair : ∀ i k, i ≠ k → f (i, k) + f (k, i) = 0 := by
    intro i k hik
    set D : ι → R := fun l => δ i (M k l) with hD
    have h1 : f (i, k) = ((M.updateRow i (Pi.single j 1)).updateRow k D).det := by
      simp only [hf]
      congr 2
      funext l
      rw [updateRow_ne (Ne.symm hik)]
    have h2 : f (k, i) = (((M.updateRow i (Pi.single j 1)).updateRow k D).submatrix
        (Equiv.swap i k) id).det := by
      simp only [hf]
      congr 1
      ext a b
      simp only [submatrix_apply, id, updateRow_apply, updateRow_ne hik, hD]
      by_cases hai : a = i
      · subst hai; simp [Equiv.swap_apply_left, hik, Ne.symm hik, hM]
      · by_cases hak : a = k
        · subst hak; simp [Equiv.swap_apply_right, hik, Ne.symm hik]
        · rw [Equiv.swap_apply_of_ne_of_ne hai hak]; simp [hai, hak]
    rw [h1, h2, det_permute, Equiv.Perm.sign_swap hik]
    simp
  rw [hS]
  refine sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · rintro ⟨i, k⟩ _
    by_cases hik : i = k
    · subst hik; simp [hdiag]
    · exact hpair i k hik
  · rintro ⟨i, k⟩ _ hne heq
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    rw [heq.1] at hne
    exact hne (hdiag i)
  · intro p _; simp
  · intro p _; simp

theorem piola_identity : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (δ : ι → Derivation K R R) (M : Matrix ι ι R),
    (∀ h i j, δ h (M i j) = δ i (M h j)) → ∀ j, ∑ i, δ i (M.adjugate j i) = 0 :=
  fun δ M hM j => piola δ M hM j

end GlobalTheory.PiolaAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsGroup
section
open TensorProduct WithConv

namespace GlobalTheory.HopfShear

variable {R A B X Y : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R X] [Algebra R Y]


open Algebra.TensorProduct Bialgebra HopfAlgebra in
@[reducible] noncomputable def pointsGroup : Group (WithConv (A →ₐ[R] X)) where
  __ := (inferInstance : Monoid (WithConv (A →ₐ[R] X)))
  inv f := toConv <| f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)
  inv_mul_cancel f := by
    have H : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
    trans toConv <|
      ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
        (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (Bialgebra.comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp
      (toConv (HopfAlgebra.antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A →ₗ[R] X)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

attribute [local instance] pointsGroup

noncomputable def pre (f : B →ₐc[R] A) : WithConv (A →ₐ[R] X) →* WithConv (B →ₐ[R] X) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (x.ofConv.comp (f : B →ₐ[R] A))) fun x y => by
    rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv]

noncomputable def post (h : X →ₐ[R] Y) : WithConv (A →ₐ[R] X) →* WithConv (A →ₐ[R] Y) :=
  MonoidHom.mk' (fun x : WithConv (A →ₐ[R] X) => toConv (h.comp x.ofConv)) fun x y => by
    rw [AlgHom.comp_convMul_distrib, toConv_ofConv]

theorem pre_apply (f : B →ₐc[R] A) (x : WithConv (A →ₐ[R] X)) (b : B) :
    (pre f x).ofConv b = x.ofConv (f b) := rfl

theorem conv_ext {x y : WithConv (A →ₐ[R] X)} (h : ∀ a, x.ofConv a = y.ofConv a) : x = y :=
  ofConv_injective (AlgHom.ext h)

theorem shear (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A]
    [HopfAlgebra R B] (f : B →ₐc[R] A) :
    Nonempty ((TensorProduct (AlgHom.range (f : B →ₐ[R] A)) A A) ≃ₗ[A]
      TensorProduct R A (A ⧸ Ideal.map (f : B →ₐ[R] A)
        (RingHom.ker (Bialgebra.counitAlgHom R B)))) := by
  set S := AlgHom.range (f : B →ₐ[R] A) with hS
  set I : Ideal A := Ideal.map (f : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B)) with hI
  let l : WithConv (A →ₐ[R] A ⊗[S] A) := toConv (IsScalarTower.toAlgHom R A (A ⊗[S] A))
  let r : WithConv (A →ₐ[R] A ⊗[S] A) :=
    toConv ((Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A).restrictScalars R)
  let l' : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) := toConv (IsScalarTower.toAlgHom R A _)
  let p : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) :=
    toConv ((Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).comp
      (Ideal.Quotient.mkₐ R I))
  have hl : ∀ a, l.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hr : ∀ a, r.ofConv a = 1 ⊗ₜ a := fun a => rfl
  have hl' : ∀ a, l'.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hp : ∀ a, p.ofConv a = 1 ⊗ₜ Ideal.Quotient.mk I a := fun a => rfl
  have hlr : pre f l = pre f r := conv_ext fun b => by
    rw [pre_apply, pre_apply, hl, hr]
    have := TensorProduct.smul_tmul (R := S) (⟨f b, ⟨b, rfl⟩⟩ : S) (1 : A) (1 : A)
    simpa [Subalgebra.smul_def] using this
  have hpf : pre f p = 1 := conv_ext fun b => by
    rw [pre_apply, hp]
    have hb : b - algebraMap R B (Coalgebra.counit b) ∈
        RingHom.ker (Bialgebra.counitAlgHom R B) := by
      simp [RingHom.mem_ker]
    have h1 : Ideal.Quotient.mk I (f b) = algebraMap R _ (Coalgebra.counit b) := by
      have h2 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem (f : B →ₐ[R] A) hb)
      rw [map_sub, map_sub, sub_eq_zero, AlgHom.commutes] at h2
      exact h2
    rw [h1]
    exact (Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).commutes _
  let g : A →ₐ[S] A ⊗[R] (A ⧸ I) :=
    { (l' * p).ofConv.toRingHom with
      commutes' := by
        rintro ⟨_, b, rfl⟩
        have h : pre f (l' * p) = pre f l' := by rw [map_mul, hpf, mul_one]
        have h2 : (l' * p).ofConv (f b) = f b ⊗ₜ 1 := congrArg (fun x => x.ofConv b) h
        exact h2 }
  let Φ : A ⊗[S] A →ₐ[A] A ⊗[R] (A ⧸ I) :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) g fun _ _ => Commute.all _ _
  have hk : ∀ a ∈ I, (l⁻¹ * r).ofConv a = 0 := by
    have h : pre f (l⁻¹ * r) = 1 := by rw [map_mul, map_inv, hlr, inv_mul_cancel]
    have : I ≤ RingHom.ker (l⁻¹ * r).ofConv := by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro b hb
      have h2 : (l⁻¹ * r).ofConv (f b) = algebraMap R _ (Coalgebra.counit b) :=
        congrArg (fun x => x.ofConv b) h
      have h3 : Coalgebra.counit (R := R) b = 0 := hb
      rw [h3, map_zero] at h2
      exact h2
    exact fun a ha => this ha
  let k : (A ⧸ I) →ₐ[R] A ⊗[S] A := Ideal.Quotient.liftₐ I (l⁻¹ * r).ofConv hk
  let Ψ : A ⊗[R] (A ⧸ I) →ₐ[A] A ⊗[S] A :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) k fun _ _ => Commute.all _ _
  have hΦl : post (Φ.restrictScalars R) l = l' := conv_ext fun a => Φ.commutes a
  have hΦr : post (Φ.restrictScalars R) r = l' * p := conv_ext fun a => by
    change Φ (1 ⊗ₜ a) = g a
    simp [Φ, ← Algebra.TensorProduct.one_def]
  have hΨl : post (Ψ.restrictScalars R) l' = l := conv_ext fun a => Ψ.commutes a
  have hΨp : post (Ψ.restrictScalars R) p = l⁻¹ * r := conv_ext fun a => by
    change Ψ (1 ⊗ₜ Ideal.Quotient.mk I a) = k (Ideal.Quotient.mk I a)
    simp [Ψ, ← Algebra.TensorProduct.one_def]
  have h1 : ∀ a, Φ (Ψ (p.ofConv a)) = p.ofConv a := fun a => by
    have h : post (Φ.restrictScalars R) (post (Ψ.restrictScalars R) p) = p := by
      rw [hΨp, map_mul, map_inv, hΦl, hΦr, inv_mul_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  have h2 : ∀ a, Ψ (Φ (r.ofConv a)) = r.ofConv a := fun a => by
    have h : post (Ψ.restrictScalars R) (post (Φ.restrictScalars R) r) = r := by
      rw [hΦr, map_mul, hΨl, hΨp, mul_inv_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  refine ⟨(AlgEquiv.ofAlgHom Φ Ψ ?_ ?_).toLinearEquiv⟩
  · refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun c => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact h1 a
  · exact Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => h2 a)

end GlobalTheory.HopfShear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsOfSchemeOverArtinianFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.PinchPoints

theorem ring_lift_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (a : R₁) (b : R₂)
    (hab : g₁ a = g₂ b) : ∃ x : P, f₁ x = a ∧ f₂ x = b :=
  ((Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))).2.2 a b hab

theorem ring_ext_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (x y : P)
    (h₁ : f₁ x = f₁ y) (h₂ : f₂ x = f₂ y) : x = y :=
  ((Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))).2.1 x y ⟨h₁, h₂⟩

theorem scheme_exists_of_isPullback {X Y Z W : Scheme.{0}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y) (hxy : f x = g y) :
    ∃ w, fst w = x ∧ snd w = y := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]

theorem closedImmersion_of_isPullback {W X Y Z : Scheme.{0}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [IsClosedImmersion g] :
    IsClosedImmersion fst :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance

theorem spec_subsingleton_of_artinian (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P] :
    Subsingleton (Spec P) :=
  ⟨fun a b => PrimeSpectrum.ext
    ((IsLocalRing.eq_maximalIdeal (@IsArtinianRing.isMaximal_of_isPrime P _ a.asIdeal a.isPrime _)).trans
      (IsLocalRing.eq_maximalIdeal (@IsArtinianRing.isMaximal_of_isPrime P _ b.asIdeal b.isPrime _)).symm)⟩

theorem spec_nonempty_iff (R : CommRingCat.{0}) : Nonempty (Spec R) ↔ Nontrivial R := by
  rw [← not_isEmpty_iff, ← not_subsingleton_iff_nontrivial]
  exact not_congr (PrimeSpectrum.isEmpty_iff_subsingleton (R := R))

theorem points_of_pinch : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y Y₁ Y₂ Y₀ : Scheme.{0}) (p : Y ⟶ Spec P) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback j₁ p₁ p (Spec.map f₁) → IsPullback j₂ p₂ p (Spec.map f₂) → IsPullback i₁ p₀ p₁ (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) ∧ ∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → ∃ y₀ : Y₀, i₁ y₀ = y₁ ∧ i₂ y₀ = y₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y Y₁ Y₂ Y₀ p p₁ p₂ p₀ j₁ j₂ i₁ i₂ h₁ h₂ h₀ hcomm
  have hf₁ : Function.Surjective f₁ := fun a => by
    obtain ⟨b, hb⟩ := hg₂ (g₁ a)
    obtain ⟨x, hx, -⟩ := ring_lift_of_isPullback hP a b hb.symm
    exact ⟨x, hx⟩
  have hf₂ : Function.Surjective f₂ := fun b => by
    obtain ⟨a, ha⟩ := hg₁ (g₂ b)
    obtain ⟨x, -, hx⟩ := ring_lift_of_isPullback hP a b ha
    exact ⟨x, hx⟩
  haveI := IsClosedImmersion.spec_of_surjective f₁ hf₁
  haveI := IsClosedImmersion.spec_of_surjective f₂ hf₂
  haveI : IsClosedImmersion j₁ := closedImmersion_of_isPullback h₁
  haveI : IsClosedImmersion j₂ := closedImmersion_of_isPullback h₂
  haveI : Subsingleton (Spec P) := spec_subsingleton_of_artinian P
  haveI : Subsingleton (Spec R₁) := (Spec.map f₁).isClosedEmbedding.injective.subsingleton
  have lift₁ : Nontrivial R₁ → ∀ y : Y, ∃ y₁, j₁ y₁ = y := fun hn y => by
    obtain ⟨s⟩ := (spec_nonempty_iff R₁).2 hn
    obtain ⟨y₁, hy, -⟩ := scheme_exists_of_isPullback h₁ y s (Subsingleton.elim _ _)
    exact ⟨y₁, hy⟩
  have lift₂ : Nontrivial R₂ → ∀ y : Y, ∃ y₂, j₂ y₂ = y := fun hn y => by
    obtain ⟨s⟩ := (spec_nonempty_iff R₂).2 hn
    obtain ⟨y₂, hy, -⟩ := scheme_exists_of_isPullback h₂ y s (Subsingleton.elim _ _)
    exact ⟨y₂, hy⟩
  refine ⟨fun y => ?_, fun y₁ y₂ hy => ?_⟩
  · by_cases hn : Nontrivial R₁
    · exact Or.inl (lift₁ hn y)
    · by_cases hn₂ : Nontrivial R₂
      · exact Or.inr (lift₂ hn₂ y)
      · exfalso
        rw [not_nontrivial_iff_subsingleton] at hn hn₂
        exact one_ne_zero (ring_ext_of_isPullback hP (1 : P) 0 (Subsingleton.elim _ _)
          (Subsingleton.elim _ _))
  · have hn₁ : Nontrivial R₁ := (spec_nonempty_iff R₁).1 ⟨p₁ y₁⟩
    have hn₂ : Nontrivial R₂ := (spec_nonempty_iff R₂).1 ⟨p₂ y₂⟩
    have hn₀ : Nontrivial R₀ := by
      by_contra hc
      rw [not_nontrivial_iff_subsingleton] at hc
      obtain ⟨e, he₁, he₂⟩ := ring_lift_of_isPullback hP (1 : R₁) (0 : R₂) (Subsingleton.elim _ _)
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
      · have h' := hu.map f₂.hom
        rw [show f₂.hom e = 0 from he₂] at h'
        exact not_isUnit_zero h'
      · have h' := hu.map f₁.hom
        rw [map_sub, map_one, show f₁.hom e = 1 from he₁, sub_self] at h'
        exact not_isUnit_zero h'
    obtain ⟨s₀⟩ := (spec_nonempty_iff R₀).2 hn₀
    obtain ⟨y₀, hy₀, -⟩ := scheme_exists_of_isPullback h₀ y₁ s₀ (Subsingleton.elim _ _)
    refine ⟨y₀, hy₀, j₂.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply, hy₀, hy]

end GlobalTheory.PinchPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyGrowthSpreadOfIntegralMonodromy
section
open Filter Topology

namespace GlobalTheory

lemma intMatrix_smul_sum_norm_le {m g : ℕ} (M : Fin m → Fin m → ℤ) (x y : Fin m → Fin g → ℂ)
    (h : ∀ j, y j = ∑ i, M j i • x i) :
    ‖y‖ ≤ (∑ j, ∑ i, ‖M j i‖) * ‖x‖ := by
  have hS : 0 ≤ ∑ j, ∑ i, ‖M j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hS (norm_nonneg x))).2 fun j => ?_
  rw [h j]
  calc ‖∑ i, M j i • x i‖ ≤ ∑ i, ‖M j i • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖M j i‖ * ‖x‖ := Finset.sum_le_sum fun i _ =>
        (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _))
    _ = (∑ i, ‖M j i‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j, ∑ i, ‖M j i‖) * ‖x‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun j => ∑ i, ‖M j i‖)
          (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _) (Finset.mem_univ j)) (norm_nonneg x)

theorem polyGrowth_spread_of_integral_monodromy : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ) (P Q : Fin m → Fin m → ℤ), (∀ s : ℂ, s.re < 0 → ∀ j, lam (s + 2 * Real.pi * Complex.I) j = ∑ i, P j i • lam s i) → (∀ s : ℂ, s.re < 0 → ∀ j, lam s j = ∑ i, Q j i • lam (s + 2 * Real.pi * Complex.I) i) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  intro g m lam C k P Q h1 h2 h3 R
  set τ : ℂ := 2 * Real.pi * Complex.I with hτ
  have hτre : τ.re = 0 := by simp [hτ]
  have hτim : τ.im = 2 * Real.pi := by simp [hτ]
  have hτn : ‖τ‖ = 2 * Real.pi := by simp [hτ, abs_of_pos Real.pi_pos]
  have hexp : ∀ s, Complex.exp (s + τ) = Complex.exp s := by
    intro s; rw [Complex.exp_add, hτ, Complex.exp_two_pi_mul_I, mul_one]
  have hSP : 0 ≤ ∑ j, ∑ i, ‖P j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  have hSQ : 0 ≤ ∑ j, ∑ i, ‖Q j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  set A : ℝ := 1 + ∑ j, ∑ i, ‖P j i‖ + ∑ j, ∑ i, ‖Q j i‖ with hA
  have hA1 : 1 ≤ A := by linarith
  have hPA : ∀ s : ℂ, s.re < 0 → ‖lam (s + τ)‖ ≤ A * ‖lam s‖ := fun s hs =>
    (intMatrix_smul_sum_norm_le P _ _ (h1 s hs)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hQA : ∀ s : ℂ, s.re < 0 → ‖lam s‖ ≤ A * ‖lam (s + τ)‖ := fun s hs =>
    (intMatrix_smul_sum_norm_le Q _ _ (h2 s hs)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  set B : ℝ := A * (1 + 2 * Real.pi) ^ k with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ (by linarith [Real.pi_pos]))
  have hgrow : ∀ s t : ℂ, ‖t‖ ≤ ‖s‖ + 2 * Real.pi →
      (1 + ‖t‖) ^ k ≤ (1 + 2 * Real.pi) ^ k * (1 + ‖s‖) ^ k := by
    intro s t h
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [norm_nonneg s, Real.pi_pos]
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have key : ∀ n : ℕ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 →
      |s.im| ≤ Real.pi + 2 * Real.pi * n → ‖lam s‖ ≤ max C 0 * B ^ n * (1 + ‖s‖) ^ k := by
    intro n
    induction n with
    | zero =>
      intro s hs he hi
      have hX : 0 ≤ (1 + ‖s‖) ^ k := by positivity
      calc ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := h3 s hs he (by simpa using hi)
        _ ≤ max C 0 * B ^ 0 * (1 + ‖s‖) ^ k := by
          rw [pow_zero, mul_one]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    | succ n ih =>
      intro s hs he hi
      have hX : 0 ≤ (1 + ‖s‖) ^ k := by positivity
      have hBn : 1 ≤ B ^ (n + 1) := one_le_pow₀ hB1
      by_cases hsm : |s.im| ≤ Real.pi
      · calc ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := h3 s hs he hsm
          _ ≤ max C 0 * B ^ (n + 1) * (1 + ‖s‖) ^ k := by
            apply mul_le_mul_of_nonneg_right _ hX
            calc C ≤ max C 0 := le_max_left _ _
              _ = max C 0 * 1 := (mul_one _).symm
              _ ≤ max C 0 * B ^ (n + 1) := mul_le_mul_of_nonneg_left hBn hM
      · push_neg at hsm
        have hn0 : (0 : ℝ) ≤ 2 * Real.pi * n := by positivity
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hi
        obtain ⟨hi1, hi2⟩ := abs_le.mp hi
        obtain ⟨t, hlt, htre, hte, htn, hti⟩ : ∃ t : ℂ, ‖lam s‖ ≤ A * ‖lam t‖ ∧ t.re = s.re ∧
            Complex.exp t = Complex.exp s ∧ ‖t‖ ≤ ‖s‖ + 2 * Real.pi ∧
            |t.im| ≤ Real.pi + 2 * Real.pi * n := by
          rcases lt_abs.mp hsm with hpos | hneg
          · refine ⟨s - τ, ?_, ?_, ?_, ?_, ?_⟩
            · have := hPA (s - τ) (by simp [Complex.sub_re, hτre, hs])
              rwa [sub_add_cancel] at this
            · simp [hτre]
            · have := hexp (s - τ); rw [sub_add_cancel] at this; exact this.symm
            · calc ‖s - τ‖ ≤ ‖s‖ + ‖τ‖ := norm_sub_le _ _
                _ = ‖s‖ + 2 * Real.pi := by rw [hτn]
            · rw [Complex.sub_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]
          · refine ⟨s + τ, hQA s hs, ?_, hexp s, ?_, ?_⟩
            · simp [hτre]
            · calc ‖s + τ‖ ≤ ‖s‖ + ‖τ‖ := norm_add_le _ _
                _ = ‖s‖ + 2 * Real.pi := by rw [hτn]
            · rw [Complex.add_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]
        have hIH := ih t (by rw [htre]; exact hs) (by rw [hte]; exact he) hti
        calc ‖lam s‖ ≤ A * ‖lam t‖ := hlt
          _ ≤ A * (max C 0 * B ^ n * (1 + ‖t‖) ^ k) :=
            mul_le_mul_of_nonneg_left hIH (by linarith)
          _ ≤ A * (max C 0 * B ^ n * ((1 + 2 * Real.pi) ^ k * (1 + ‖s‖) ^ k)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hgrow s t htn)
                (mul_nonneg hM (pow_nonneg (by linarith) n))) (by linarith)
          _ = max C 0 * B ^ (n + 1) * (1 + ‖s‖) ^ k := by rw [hB]; ring
  refine ⟨max C 0 * B ^ ⌈R / (2 * Real.pi)⌉₊, fun s hs he hi => key _ s hs he (hi.trans ?_)⟩
  have hc : R / (2 * Real.pi) ≤ (⌈R / (2 * Real.pi)⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ (by positivity)] at hc
  linarith [Real.pi_pos]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowApplyEqZeroOfStrictUpper
section
namespace GlobalTheory.StrictUpperNilpotent

theorem pow_apply_eq_zero_of_strictUpper {L : Type} [inst : Field L] {n : ℕ}
    {y : Matrix (Fin n) (Fin n) L} (hy : ∀ (i j : Fin n), j ≤ i → y i j = (0 : L)) :
    ∀ (k : ℕ) (i j : Fin n), (↑j : ℕ) < (↑i : ℕ) + k → (y ^ k) i j = (0 : L) := by
  intro k
  induction k with
  | zero =>
    intro i j h
    have hne : i ≠ j := by
      rintro rfl
      simp at h
    rw [pow_zero, Matrix.one_apply_ne hne]
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < (i : ℕ) + k
    · rw [ih i l hl, zero_mul]
    · have hjl : j ≤ l := by
        rw [Fin.le_def]
        omega
      rw [hy l j hjl, mul_zero]

end GlobalTheory.StrictUpperNilpotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteType
section
namespace GlobalTheory

theorem residueField_localization_atPrime_isSepClosed_of_finiteType :
    ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
      (P : Ideal B) [P.IsMaximal],
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  intro k B _ _ _ _ _ P _
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  haveI : Algebra.IsIntegral k (B ⧸ P) := inferInstance
  let f : k ≃+* (B ⧸ P) := RingEquiv.ofBijective (algebraMap k (B ⧸ P))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed (B ⧸ P) := IsAlgClosed.of_ringEquiv k (B ⧸ P) f
  let e : (B ⧸ P) ≃+* IsLocalRing.ResidueField (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)).toRingEquiv
  haveI : IsAlgClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) :=
    IsAlgClosed.of_ringEquiv _ _ e
  infer_instance

end GlobalTheory
end

