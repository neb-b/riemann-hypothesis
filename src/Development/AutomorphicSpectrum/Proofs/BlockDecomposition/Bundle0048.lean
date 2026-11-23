module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOrthogonalIdempotentSum
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
open CategoryTheory.Limits

namespace GlobalTheory.CompanionTheory.SecAdd

variable {S : Type} [CommRing S]

theorem away_self_eq_one {e : S} (he : IsIdempotentElem e) :
    algebraMap S (Localization.Away e) e = 1 := by
  have hu : IsUnit (algebraMap S (Localization.Away e) e) := IsLocalization.Away.algebraMap_isUnit e
  have h : algebraMap S (Localization.Away e) e * algebraMap S (Localization.Away e) e
      = algebraMap S (Localization.Away e) e * 1 := by
    rw [← map_mul, he.eq, mul_one]
  exact hu.mul_left_cancel h

theorem away_orth_eq_zero {e x : S} (he : IsIdempotentElem e) (h : e * x = 0) :
    algebraMap S (Localization.Away e) x = 0 := by
  have := congrArg (algebraMap S (Localization.Away e)) h
  rwa [map_mul, away_self_eq_one he, one_mul, map_zero] at this

theorem away_surj {e : S} (he : IsIdempotentElem e) :
    Function.Surjective (algebraMap S (Localization.Away e)) := by
  intro b
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers e) b
  obtain ⟨n, hn⟩ := s.2
  refine ⟨x, ?_⟩
  have : algebraMap S (Localization.Away e) (s : S) = 1 := by
    rw [← hn, map_pow, away_self_eq_one he, one_pow]
  simp only [this, mul_one] at hx
  exact hx.symm

theorem away_ker {e x : S} (he : IsIdempotentElem e)
    (h : algebraMap S (Localization.Away e) x = 0) : e * x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers e) _ x).1 h
  rcases n with _ | n
  · simp at hc
    simp [hc]
  · have : e ^ (n + 1) = e := he.pow_succ_eq n
    simpa [this] using hc

theorem isIdempotentElem_add {e e' : S} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e * e' = 0) : IsIdempotentElem (e + e') := by
  have h' : e' * e = 0 := by rw [mul_comm, h]
  unfold IsIdempotentElem
  rw [add_mul, mul_add, mul_add, h, h', he.eq, he'.eq, add_zero, zero_add]

theorem isLocalization_prod {e e' : S} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e * e' = 0) :
    IsLocalization.Away (e + e') (Localization.Away e × Localization.Away e') := by
  have h' : e' * e = 0 := by rw [mul_comm, h]
  have key : ∀ z : S, algebraMap S (Localization.Away e × Localization.Away e') z = 0 ↔
      (e + e') * z = 0 := by
    intro z
    constructor
    · intro hz
      have h1 : algebraMap S (Localization.Away e) z = 0 := congrArg Prod.fst hz
      have h2 : algebraMap S (Localization.Away e') z = 0 := congrArg Prod.snd hz
      rw [add_mul, away_ker he h1, away_ker he' h2, add_zero]
    · intro hz
      have h1 : e * z = 0 := by
        have := congrArg (e * ·) hz
        simp only [mul_zero] at this
        rw [← this, ← mul_assoc, mul_add, he.eq, h, add_zero]
      have h2 : e' * z = 0 := by
        have := congrArg (e' * ·) hz
        simp only [mul_zero] at this
        rw [← this, ← mul_assoc, mul_add, he'.eq, h', zero_add]
      exact Prod.ext (away_orth_eq_zero he h1) (away_orth_eq_zero he' h2)
  refine IsLocalization.away_of_isIdempotentElem_of_mul (isIdempotentElem_add he he' h) ?_ ?_
  · intro x y
    rw [← sub_eq_zero, ← map_sub, key, mul_sub, sub_eq_zero]
  · rintro ⟨b, c⟩
    obtain ⟨x, rfl⟩ := away_surj he b
    obtain ⟨y, rfl⟩ := away_surj he' c
    refine ⟨e * x + e' * y, Prod.ext ?_ ?_⟩
    · change algebraMap S (Localization.Away e) (e * x + e' * y) = _
      have : algebraMap S (Localization.Away e) e' = 0 := away_orth_eq_zero he h
      rw [map_add (f := _), map_mul, map_mul, away_self_eq_one he, this, one_mul, zero_mul, add_zero]
    · change algebraMap S (Localization.Away e') (e * x + e' * y) = _
      have : algebraMap S (Localization.Away e') e = 0 := away_orth_eq_zero he' h'
      rw [map_add (f := _), map_mul, map_mul, away_self_eq_one he', this, one_mul, zero_mul, zero_add]

theorem secOn_add : ∀ {S : Type} [CommRing S] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' →
    e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := by
  intro S _ Y f e e' he he' h ⟨s, hs⟩ ⟨s', hs'⟩
  haveI := isLocalization_prod he he' h
  let B := Localization.Away e
  let C := Localization.Away e'
  let A := Localization.Away (e + e')
  let φ : (B × C) ≃ₐ[S] A :=
    IsLocalization.algEquiv (Submonoid.powers (e + e')) (B × C) A
  let t : Spec (CommRingCat.of (B × C)) ⟶ Y := inv (coprodSpec B C) ≫ coprod.desc s s'
  have ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (B × C))) := by
    rw [← cancel_epi (coprodSpec B C)]
    simp only [t, Category.assoc, IsIso.hom_inv_id_assoc]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, hs, coprodSpec_inl_assoc, ← Spec.map_comp]
      rfl
    · rw [coprod.inr_desc_assoc, hs', coprodSpec_inr_assoc, ← Spec.map_comp]
      rfl
  refine ⟨Spec.map (CommRingCat.ofHom (φ : B × C →+* A)) ≫ t, ?_⟩
  rw [Category.assoc, ht, ← Spec.map_comp]
  congr 1
  ext x
  exact φ.commutes x

end GlobalTheory.CompanionTheory.SecAdd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleOfPerm
section
open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.ShuffleWords

variable {T : Type u}

theorem interleave_exchange {u v w : List T} (h : Interleave u v w) :
    ∀ {u' x : List T}, Interleave u' x v →
      ∃ v', Interleave u' v' w ∧ Interleave u x v' := by
  induction h with
  | nil =>
    intro u' x h'
    cases h'
    exact ⟨[], Interleave.nil, Interleave.nil⟩
  | @left a u v w _ ih =>
    intro u' x h'
    obtain ⟨v', h₁, h₂⟩ := ih h'
    exact ⟨a :: v', Interleave.right h₁, Interleave.left h₂⟩
  | @right a u v w _ ih =>
    intro u' x h'
    cases h' with
    | left h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨v', Interleave.left h₁, h₂⟩
    | right h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨a :: v', Interleave.right h₁, Interleave.right h₂⟩

theorem shuffle_swap {a b : List T} {us : List (List T)} {w : List T}
    (h : Shuffle (a :: b :: us) w) : Shuffle (b :: a :: us) w := by
  cases h with
  | cons hv hw =>
    cases hv with
    | cons hx hv =>
      obtain ⟨v', h₁, h₂⟩ := interleave_exchange hw hv
      exact Shuffle.cons (Shuffle.cons hx h₂) h₁

theorem shuffle_perm {T : Type u} (us us' : List (List T)) (w : List T)
    (h : Shuffle us w) (hp : us.Perm us') : Shuffle us' w := by
  induction hp generalizing w with
  | nil => exact h
  | cons a _ ih =>
    cases h with
    | cons hv hw => exact Shuffle.cons (ih _ hv) hw
  | swap a b l => exact shuffle_swap h
  | trans _ _ ih₁ ih₂ => exact ih₂ _ (ih₁ _ h)

end GlobalTheory.CompanionTheory.ShuffleWords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlatten
section
open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.Comb

theorem interleave_perm_append {T : Type u} {u v w : List T} (h : Interleave u v w) :
    w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm

theorem shuffle_perm_flatten {T : Type u} (us : List (List T)) (w : List T)
    (h : Shuffle us w) : w.Perm us.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons _ hi ih =>
    rw [List.flatten_cons]
    exact (interleave_perm_append hi).trans (ih.append_left _)

end GlobalTheory.CompanionTheory.Comb
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial

namespace GlobalTheory.CompanionTheory.SmoothSpread

section Witness

variable {T S ι σ : Type} [CommRing T] [CommRing S] [Algebra T S]

theorem exists_witness [Algebra.FormallySmooth T S] (Q : Algebra.Presentation T S ι σ) :
    ∃ h : ι → Q.Ring, (∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation)) ∧
      ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2 := by
  let f : Q.Ring →ₐ[T] S := IsScalarTower.toAlgHom _ _ _
  have hkerf : RingHom.ker f = Ideal.span (.range Q.relation) :=
    Q.span_range_relation_eq_ker.symm
  obtain ⟨(τ : S →ₐ[T] MvPolynomial _ T ⧸ RingHom.ker f ^ 2), hsig⟩ :=
    (Algebra.FormallySmooth.iff_split_surjection f Q.algebraMap_surjective).mp inferInstance
  have hex (i : _) := Ideal.Quotient.mk_surjective (τ <| Q.val i)
  choose h hh using hex
  have hdiag : (Ideal.Quotient.mkₐ _ _).comp (aeval h) = τ.comp (aeval Q.val) :=
    algHom_ext (by simp [hh])
  refine ⟨h, fun i ↦ ?_, fun j ↦ ?_⟩
  · have hs : f (h i) = Q.val i := by
      rw [← AlgHom.kerSquareLift_mk]
      exact hh i ▸ congr($hsig (Q.val i))
    rw [← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero, hs]
    simp [f]
  · have ho : Ideal.Quotient.mk (RingHom.ker f ^ 2) (aeval h (Q.relation j)) = 0 := by
      suffices ho : τ (aeval Q.val (Q.relation j)) = 0 by
        convert! ho
        exact congr($hdiag _)
      simp
    rwa [Ideal.Quotient.eq_zero_iff_mem, hkerf] at ho

theorem formallySmooth_of_witness (Q : Algebra.Presentation T S ι σ) (h : ι → Q.Ring)
    (h1 : ∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation))
    (h2 : ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2) :
    Algebra.FormallySmooth T S := by
  let f : Q.Ring →ₐ[T] S := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Surjective f := Q.algebraMap_surjective
  have hkerf : RingHom.ker f = Ideal.span (.range Q.relation) :=
    Q.span_range_relation_eq_ker.symm
  let g₀ : Q.Ring →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.mkₐ T _).comp (aeval h)
  have hg₀ : ∀ a ∈ RingHom.ker f.toRingHom, g₀ a = 0 := by
    intro a ha
    have ha' : a ∈ Ideal.span (Set.range Q.relation) := hkerf ▸ ha
    have : Ideal.span (Set.range Q.relation) ≤ RingHom.ker g₀ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      change Ideal.Quotient.mk _ _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have := h2 j
      rw [← hkerf] at this
      exact this
    exact this ha'
  let g : S →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.liftₐ (RingHom.ker f.toRingHom) g₀ hg₀).comp
      (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
  refine Algebra.FormallySmooth.of_split f g ?_
  rw [← AlgHom.cancel_right hf]
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  have hgf : g (f (X i)) = Ideal.Quotient.mk _ (h i) := by
    have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i)) = Ideal.Quotient.mk _ (X i) := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change (Ideal.Quotient.liftₐ _ g₀ hg₀)
      ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i))) = _
    rw [this]
    change Ideal.Quotient.mk _ (aeval h (X i)) = _
    rw [aeval_X]
  have hfx : f (h i) = f (X i) := by
    have := h1 i
    rw [← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  simp only [AlgHom.comp_apply, hgf, AlgHom.id_apply]
  rw [AlgHom.kerSquareLift_mk, hfx]

end Witness

section Spread

variable {R₀ R B : Type} [CommRing R₀] [CommRing R] [CommRing B] [Algebra R₀ R] [Algebra R₀ B]

theorem span_range_sq {P : Type} [CommRing P] {σ : Type} (g : σ → P) :
    Ideal.span (Set.range g) ^ 2 = Ideal.span (Set.range fun p : σ × σ ↦ g p.1 * g p.2) := by
  rw [pow_two, Ideal.span_mul_span']
  congr 1
  ext x
  simp only [Set.mem_mul, Set.mem_range, Prod.exists]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩

theorem exists_finite_smooth [Algebra.FinitePresentation R₀ B] [Algebra.Smooth R (R ⊗[R₀] B)] :
    ∃ s : Set R, s.Finite ∧ ∀ A : Subalgebra R₀ R, s ⊆ A → Algebra.Smooth A (A ⊗[R₀] B) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R₀ B
  let Q := P.baseChange R
  obtain ⟨h, h1, h2⟩ := exists_witness Q
  simp_rw [span_range_sq] at h2
  simp_rw [Ideal.mem_span_range_iff_exists_fun] at h1 h2
  choose c hc using h1
  choose d hd using h2
  refine ⟨(⋃ i, ((h i).coeffs : Set R)) ∪ (⋃ i, ⋃ j, ((c i j).coeffs : Set R)) ∪
    (⋃ i, ⋃ j, ((d i j).coeffs : Set R)), ?_, fun A hA ↦ ?_⟩
  · refine .union (.union ?_ ?_) ?_
    · exact Set.finite_iUnion fun i ↦ Finset.finite_toSet _
    · exact Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦ Finset.finite_toSet _
    · exact Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦ Finset.finite_toSet _
  let M {ι : Type} : MvPolynomial ι A →+* MvPolynomial ι R := MvPolynomial.map (algebraMap A R)
  have hM {ι : Type} : Function.Injective (M (ι := ι)) :=
    MvPolynomial.map_injective _ Subtype.val_injective
  have hMX {ι : Type} (i : ι) : M (X i) = (X i : MvPolynomial ι R) := MvPolynomial.map_X _ _
  have lift {ι : Type} (p : MvPolynomial ι R) (hp : (p.coeffs : Set R) ⊆ A) : ∃ q, M q = p := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun x hx ↦ ?_
    exact ⟨⟨x, hp hx⟩, rfl⟩
  have hh' (i) : ∃ q, M q = h i := lift _ fun x hx ↦
    hA (.inl (.inl (Set.mem_iUnion.mpr ⟨i, hx⟩)))
  have hc' (i j) : ∃ q, M q = c i j := lift _ fun x hx ↦
    hA (.inl (.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩)))
  have hd' (i j) : ∃ q, M q = d i j := lift _ fun x hx ↦
    hA (.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩))
  choose h' hh' using hh'
  choose c' hc' using hc'
  choose d' hd' using hd'
  let Q' := P.baseChange A
  have hrel (j) : M (Q'.relation j) = Q.relation j := by
    simp [Q, Q', M, Algebra.Presentation.baseChange_relation, MvPolynomial.map_map,
      ← IsScalarTower.algebraMap_eq]
  have : Algebra.FormallySmooth A (A ⊗[R₀] B) := by
    refine formallySmooth_of_witness Q' h' (fun i ↦ ?_) (fun j ↦ ?_)
    · rw [Ideal.mem_span_range_iff_exists_fun]
      refine ⟨c' i, hM ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, map_sub, hc', hrel, hh', hMX]
      exact hc i
    · rw [span_range_sq, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨d' j, hM ?_⟩
      have hMa (q : MvPolynomial _ A) : M (aeval h' q) = aeval h (M q) := by
        induction q using MvPolynomial.induction_on with
        | C a => simp [M, MvPolynomial.algebraMap_apply]
        | add p q hp hq => simp only [map_add (f := _), hp, hq]
        | mul_X p i hp =>
          simp only [map_mul, aeval_X, hp, hh', hMX]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hd', hrel, hMa, hd j]
  exact ⟨inferInstance, inferInstance⟩

end Spread

section Schemes

theorem smooth_iff_of_isPullback {R₀ T B : Type} [CommRing R₀] [CommRing T] [CommRing B] [Algebra R₀ T]
    [Algebra R₀ B] {U W : Scheme.{0}} (g : U ⟶ Spec (CommRingCat.of R₀)) (e : U ≅ Spec (CommRingCat.of B))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = g)
    {p : W ⟶ U} {q : W ⟶ Spec (CommRingCat.of T)}
    (H : IsPullback p q g (Spec.map (CommRingCat.ofHom (algebraMap R₀ T)))) :
    Smooth q ↔ Algebra.Smooth T (T ⊗[R₀] B) := by
  have sq := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R₀ T B)).flip
  have H' : IsPullback (p ≫ e.hom) q (Spec.map (CommRingCat.ofHom (algebraMap R₀ B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R₀ T))) :=
    H.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [he]) (by simp)
  have hq : (H'.isoIsPullback _ _ sq).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[R₀] B)) = q :=
    IsPullback.isoIsPullback_hom_snd ..
  have : MorphismProperty.RespectsIso @Smooth.{0} := by
    first
      | exact inferInstance
      | exact HasRingHomProperty.respectsIso
      | exact MorphismProperty.IsStableUnderBaseChange.respectsIso
      | exact (HasRingHomProperty.isLocal_ringHomProperty (P := @Smooth.{0})).respectsIso.arrow
  rw [← hq, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{0}), HasRingHomProperty.Spec_iff (P := @Smooth.{0})]
  exact RingHom.smooth_algebraMap (R := T) (S := T ⊗[R₀] B)

theorem exists_finite_chart {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R₀ R] {Y Y₀ U : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)} {π : Y ⟶ Y₀}
    (hlfp : LocallyOfFinitePresentation f₀)
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))))
    (hf : Smooth f) [IsAffine U] (j : U ⟶ Y₀) [IsOpenImmersion j] :
    ∃ s : Set R, s.Finite ∧ ∀ (A : Subalgebra R₀ R), s ⊆ A → ∀ {W : Scheme.{0}} {p : W ⟶ U}
      {q : W ⟶ Spec (CommRingCat.of A)},
      IsPullback p q (j ≫ f₀) (Spec.map (CommRingCat.ofHom (algebraMap R₀ A))) → Smooth q := by
  let B : Type := Γ(U, ⊤)
  let e : U ≅ Spec (CommRingCat.of B) := U.isoSpec
  let α : CommRingCat.of R₀ ⟶ CommRingCat.of B := Spec.preimage (e.inv ≫ j ≫ f₀)
  have hα : Spec.map α = e.inv ≫ j ≫ f₀ := Spec.map_preimage _
  letI : Algebra R₀ B := α.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = e.inv ≫ j ≫ f₀ := hα
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = j ≫ f₀ := by
    rw [hmap, Iso.hom_inv_id_assoc]
  have hfp : Algebra.FinitePresentation R₀ B := by
    have : LocallyOfFinitePresentation (Spec.map α) := by
      rw [hα]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation.{0})] at this
    exact this
  have hsm : Algebra.Smooth R (R ⊗[R₀] B) := by
    refine (smooth_iff_of_isPullback (j ≫ f₀) e he
      ((IsPullback.of_hasPullback j π).paste_vert hpb)).mp ?_
    infer_instance
  obtain ⟨s, hs, H⟩ := exists_finite_smooth (R₀ := R₀) (R := R) (B := B)
  refine ⟨s, hs, fun A hA W p q hW ↦ ?_⟩
  have := H A hA
  exact (smooth_iff_of_isPullback (j ≫ f₀) e he hW).mpr this

end Schemes

theorem smooth_spreads : GlobalTheory.SpreadingModels.Spreads (fun _ _ f ↦ Smooth f) := by
  intro R R₀ _ _ φ Y Y₀ f f₀ π ⟨hfg, hlfp, hqc, hqs, hpb⟩ hsm
  letI : Algebra R₀ R := φ.toAlgebra
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  let 𝒰 := Y₀.affineCover.finiteSubcover
  have hch (i : 𝒰.I₀) := exists_finite_chart (R := R) (R₀ := R₀) hlfp hpb hsm (𝒰.f i)
  choose s hs H using hch
  have : Finite 𝒰.I₀ := by
    change Finite Y₀.affineCover.finiteSubcover.I₀
    infer_instance
  let A : Subalgebra R₀ R := Algebra.adjoin R₀ (⋃ i, s i)
  have hAfg : A.FG := ⟨(Set.finite_iUnion hs).toFinset, by simp [A]⟩
  have hft : Algebra.FiniteType R₀ A := (Subalgebra.fg_iff_finiteType A).mp hAfg
  refine ⟨A, inferInstance, algebraMap R₀ A, algebraMap A R, rfl, Algebra.FiniteType.trans hfg hft, ?_⟩
  have hloc : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0})
    (𝒰.pullback₁ (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap R₀ A))))) fun i ↦ ?_
  exact H i A (fun x hx ↦ Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, hx⟩))
    ((IsPullback.of_hasPullback _ (𝒰.f i)).flip.paste_vert (IsPullback.of_hasPullback _ _))

end GlobalTheory.CompanionTheory.SmoothSpread
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectivePreservesClosednessComparability
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.SurjPass

theorem aic_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Aic (S := S)) : Aic (S := T) := by
  intro P hP hdeg
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨Q, hQ, hQdeg, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts P).mpr fun n => hφ (P.coeff n)) hP
  obtain ⟨x, hx⟩ := h Q hQm (hQdeg ▸ hdeg)
  refine ⟨φ x, ?_⟩
  rw [← hQ, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, hx.eq_zero, map_zero]

theorem comparable_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Val0 (S := S)) : Val0 (S := T) := by
  intro f g
  obtain ⟨f', rfl⟩ := hφ f
  obtain ⟨g', rfl⟩ := hφ g
  obtain ⟨e, he, h1, h2⟩ := h f' g'
  refine ⟨φ e, ?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [← map_mul, he.eq]
  · rw [Ideal.mem_span_singleton] at h1 ⊢
    rw [← map_mul]
    exact map_dvd φ h1
  · rw [Ideal.mem_span_singleton] at h2 ⊢
    rw [← map_one φ, ← map_sub, ← map_mul]
    exact map_dvd φ h2

theorem absolutely_closed_comparable_surjective : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T),
    Function.Surjective φ → (Aic (S := S) → Aic (S := T)) ∧ (Val0 (S := S) → Val0 (S := T)) := by
  intro S _ T _ φ hφ
  exact ⟨aic_of_surjective φ hφ, comparable_of_surjective φ hφ⟩

end GlobalTheory.CompanionTheory.SurjPass
end

