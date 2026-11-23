module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitelyManyIsoClassesProjectiveNumberField
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.ProjModFinIso

variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem finrank_prod_eq (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R (M × N) = Module.finrank R M + Module.finrank R N := by
  have h1 := (TensorProduct.isBaseChange R (M × N) (FractionRing R)).finrank_eq
  have h2 := (TensorProduct.isBaseChange R M (FractionRing R)).finrank_eq
  have h2' := (TensorProduct.isBaseChange R N (FractionRing R)).finrank_eq
  have h3 := (TensorProduct.prodRight R (FractionRing R) (FractionRing R) M N).finrank_eq
  rw [← h1, h3, Module.finrank_prod, h2, h2']

theorem projective_of_isTorsionFree (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Projective R M :=
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  Module.Flat.projective_of_finitePresentation

theorem finrank_ideal (I : Ideal R) (h : I ≠ ⊥) : Module.finrank R I = 1 := by
  have h1 : Module.finrank R I ≤ 1 := by simpa using Submodule.finrank_le I
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr h
  have h2 := Module.finrank_pos (R := R) (M := I)
  omega

theorem nonempty_equiv_of_mk0_eq {I J : (Ideal R)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    Nonempty ((I : Ideal R) ≃ₗ[R] (J : Ideal R)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  have key : ∀ (z : R), z ≠ 0 → ∀ K : Ideal R, Nonempty (K ≃ₗ[R] ↥(Ideal.span {z} * K)) := by
    intro z hz K
    have hinj : Function.Injective (LinearMap.mulLeft R z) := fun a b hab => mul_left_cancel₀ hz hab
    refine ⟨(Submodule.equivMapOfInjective _ hinj K).trans (LinearEquiv.ofEq _ _ ?_)⟩
    ext w
    rw [Submodule.mem_map, Ideal.mem_span_singleton_mul]
    constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩
  exact ⟨(key x hx I).some.trans ((LinearEquiv.ofEq _ _ hxy).trans (key y hy J).some.symm)⟩

theorem exists_split (X : Type) [AddCommGroup X] [Module R X] [Module.Projective R X]
    [Nontrivial X] :
    ∃ (I : (Ideal R)⁰) (K : Submodule R X), Nonempty (X ≃ₗ[R] K × (I : Ideal R)) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R X)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hsx : s x ≠ 0 := by
    intro h
    apply hx
    have := LinearMap.congr_fun hs x
    simp only [LinearMap.comp_apply, h, map_zero, LinearMap.id_apply] at this
    exact this.symm
  obtain ⟨a, ha⟩ : ∃ a, s x a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hsx (Finsupp.ext h)
  let f : X →ₗ[R] R := Finsupp.lapply a ∘ₗ s
  have hI : LinearMap.range f ≠ ⊥ := by
    intro h
    have hm : f x ∈ LinearMap.range f := LinearMap.mem_range_self f x
    rw [h, Submodule.mem_bot] at hm
    exact ha hm
  let I : (Ideal R)⁰ := ⟨LinearMap.range f, mem_nonZeroDivisors_of_ne_zero hI⟩
  let g := f.rangeRestrict
  haveI := projective_of_isTorsionFree (R := R) (LinearMap.range f)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id f.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv (LinearMap.ker g).injective_subtype ⟨l, hl⟩
  exact ⟨I, LinearMap.ker g, ⟨e⟩⟩

theorem exists_equiv_pi (r : ℕ) : ∀ (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.IsTorsionFree R X], Module.finrank R X = r →
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → (Ideal R)⁰), Fintype.card ι = r ∧
      Nonempty (X ≃ₗ[R] ((i : ι) → ((I i : Ideal R)))) := by
  induction r with
  | zero =>
    intro X _ _ _ _ h
    have : Subsingleton X := by
      by_contra hne
      rw [not_subsingleton_iff_nontrivial] at hne
      have := Module.finrank_pos (R := R) (M := X)
      omega
    exact ⟨Empty, inferInstance, Empty.elim, by simp, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | succ r ih =>
    intro X _ _ _ _ h
    have : Nontrivial X := Module.nontrivial_of_finrank_pos (R := R) (by omega)
    haveI := projective_of_isTorsionFree (R := R) X
    obtain ⟨I, K, ⟨e⟩⟩ := exists_split (R := R) X
    have hK : Module.finrank R K = r := by
      have h1 := e.finrank_eq
      rw [finrank_prod_eq, finrank_ideal _ (by simpa using nonZeroDivisors.ne_zero I.2)] at h1
      omega
    obtain ⟨ι, _, J, hcard, ⟨eK⟩⟩ := ih K hK
    refine ⟨Option ι, inferInstance, fun o => o.elim I J, by simp [hcard], ⟨?_⟩⟩
    exact e ≪≫ₗ LinearEquiv.prodComm R _ _ ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.refl R _) eK ≪≫ₗ
      (LinearEquiv.piOptionEquivProd R (M := fun o => ((o.elim I J : (Ideal R)⁰) : Ideal R))).symm

theorem exists_finite_reps [Finite (ClassGroup R)] (q : ℕ) :
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} R), ∀ (X : Type) [AddCommGroup X] [Module R X]
      [Module.Finite R X] [Module.Projective R X], Module.finrank R X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[R] Y k) := by
  let rep : ClassGroup R → Ideal R := fun c => ((ClassGroup.mk0_surjective c).choose : Ideal R)
  have hrep : ∀ c : ClassGroup R, ClassGroup.mk0 (ClassGroup.mk0_surjective c).choose = c :=
    fun c => (ClassGroup.mk0_surjective c).choose_spec
  let S := Σ r : Fin (q + 1), (Fin r → ClassGroup R)
  let Y' : S → ModuleCat.{0} R := fun s => ModuleCat.of R ((b : Fin s.1) → rep (s.2 b))
  obtain ⟨n, ⟨eS⟩⟩ := Finite.exists_equiv_fin S
  refine ⟨n, fun k => Y' (eS.symm k), ?_⟩
  intro X _ _ _ _ hX
  obtain ⟨ι, _, I, hcard, ⟨e⟩⟩ := exists_equiv_pi (R := R) (Module.finrank R X) X rfl
  let eι := Fintype.equivFin ι
  let s : S := ⟨⟨Fintype.card ι, by omega⟩, fun b => ClassGroup.mk0 (I (eι.symm b))⟩
  refine ⟨eS s, ?_⟩
  show Nonempty (X ≃ₗ[R] Y' (eS.symm (eS s)))
  rw [Equiv.symm_apply_apply]
  have hI : ∀ i, Nonempty ((I i : Ideal R) ≃ₗ[R] rep (ClassGroup.mk0 (I i))) := fun i =>
    nonempty_equiv_of_mk0_eq (hrep _).symm
  exact ⟨e ≪≫ₗ LinearEquiv.piCongrRight (fun i => (hI i).some) ≪≫ₗ
    LinearEquiv.piCongrLeft' R (fun i => ↥(rep (ClassGroup.mk0 (I i)))) eι⟩

theorem finitely_many_iso_classes : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ),
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} (𝓞 E)), ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
      [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[𝓞 E] Y k) := by
  intro E _ _ q
  exact exists_finite_reps q

end GlobalTheory.ProjModFinIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanImage
section
open Module

noncomputable section

namespace GlobalTheory.RatSpan

section Lin

variable {K' V' W : Type} [Field K'] [AddCommGroup V'] [Module K' V'] [AddCommGroup W] [Module ℂ W]
  {σ' : K' →+* ℂ} (j' : V' →ₛₗ[σ'] W)

private theorem span_range_le_comap_span_image {κ : Type} (x : κ → V') :
    Submodule.span K' (Set.range x) ≤ (Submodule.span ℂ (Set.range fun k => j' (x k))).comap j' := by
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact Submodule.subset_span ⟨k, rfl⟩

private theorem linearIndependent_image_basis_of_linearIndependent {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V')
    (hb : LinearIndependent ℂ fun i => j' (b' i)) {κ : Type} [Fintype κ] (c : Basis κ K' V') :
    LinearIndependent ℂ fun k => j' (c k) := by
  have := Module.Finite.of_basis b'
  have hcard : Fintype.card ι' = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis c]
  have hle : Submodule.span ℂ (Set.range fun i => j' (b' i)) ≤
      Submodule.span ℂ (Set.range fun k => j' (c k)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : b' i ∈ Submodule.span K' (Set.range c) := by rw [c.span_eq]; trivial
    exact span_range_le_comap_span_image j' c hi
  have : Module.Finite ℂ (Submodule.span ℂ (Set.range fun k => j' (c k))) :=
    Module.Finite.span_of_finite ℂ (Set.finite_range _)
  rw [linearIndependent_iff_card_eq_finrank_span]
  apply le_antisymm
  · rw [← hcard, linearIndependent_iff_card_eq_finrank_span.mp hb]
    exact Submodule.finrank_mono hle
  · exact finrank_range_le_card _

theorem linInd_comp {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V') (hb : LinearIndependent ℂ fun i => j' (b' i))
    {κ : Type} {x : κ → V'} (hx : LinearIndependent K' x) : LinearIndependent ℂ fun k => j' (x k) := by
  have := Module.Finite.of_basis b'
  have hs : LinearIndepOn K' id (Set.range x) := (linearIndepOn_id_range_iff hx.injective).mpr hx
  have : Fintype (hs.extend (Set.subset_univ _)) := by
    have := Module.Finite.finite_basis (Basis.extend hs)
    exact Fintype.ofFinite _
  have he := linearIndependent_image_basis_of_linearIndependent j' b' hb (Basis.extend hs)
  let g : κ → hs.extend (Set.subset_univ _) := fun k => ⟨x k, Basis.subset_extend hs ⟨k, rfl⟩⟩
  have hg : Function.Injective g := fun a b h => hx.injective (congrArg Subtype.val h)
  have h2 := he.comp g hg
  simpa [g, Function.comp_def, Basis.coe_extend] using h2

end Lin

section Main

variable {K K' V V' W : Type} [Field K] [Field K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {σ : K →+* ℂ} {σ' : K' →+* ℂ}

theorem finrank_span_image (j' : V' →ₛₗ[σ'] W) {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V')
    (hb : LinearIndependent ℂ fun i => j' (b' i)) (X : Submodule K' V') :
    finrank ℂ (Submodule.span ℂ (j' '' X)) = finrank K' X := by
  have := Module.Finite.of_basis b'
  let e := Module.finBasis K' X
  let x : Fin (finrank K' X) → V' := fun i => (e i : V')
  have hx : LinearIndependent K' x := e.linearIndependent.map' X.subtype X.ker_subtype
  have hjx := linInd_comp j' b' hb hx
  have hspan : Submodule.span ℂ (j' '' X) = Submodule.span ℂ (Set.range fun i => j' (x i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      have hvx : v ∈ Submodule.span K' (Set.range x) := by
        have h1 : (⟨v, hv⟩ : X) ∈ Submodule.span K' (Set.range e) := by rw [e.span_eq]; trivial
        have h2 := Submodule.mem_map_of_mem (f := X.subtype) h1
        rw [Submodule.map_span, ← Set.range_comp] at h2
        exact h2
      exact span_range_le_comap_span_image j' x hvx
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨x i, (e i).2, rfl⟩
  rw [hspan, finrank_span_eq_card hjx, Fintype.card_fin]

theorem comap_eq_span (j : V →ₛₗ[σ] W) (j' : V' →ₛₗ[σ'] W) (ι : V → V') (hj : ∀ v, j' (ι v) = j v)
    {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V') (hb : LinearIndependent ℂ fun i => j' (b' i))
    (U : Submodule ℂ W) (hU : U ≤ Submodule.span ℂ (j '' (U.comap j))) :
    U.comap j' = Submodule.span K' (ι '' (U.comap j)) := by
  have := Module.Finite.of_basis b'
  have hle : Submodule.span K' (ι '' (U.comap j)) ≤ U.comap j' := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show j' (ι v) ∈ U
    rw [hj]
    exact hv
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [← finrank_span_image j' b' hb, ← finrank_span_image j' b' hb]
  calc finrank ℂ (Submodule.span ℂ (j' '' (U.comap j'))) ≤ finrank ℂ U := by
        apply Submodule.finrank_mono
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        exact hv
    _ ≤ finrank ℂ (Submodule.span ℂ (j' '' (Submodule.span K' (ι '' (U.comap j))))) := by
        apply Submodule.finrank_mono
        refine hU.trans (Submodule.span_mono ?_)
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨ι v, Submodule.subset_span ⟨v, hv, rfl⟩, hj v⟩

end Main

end GlobalTheory.RatSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatMapColonIdeal
section
open IsLocalRing

namespace GlobalTheory

private lemma mem_colon_span_range_iff {B : Type*} [CommRing B] {P : Ideal B} {ι : Type*}
    (g : ι → B) (r : B) :
    r ∈ P.colon (Ideal.span (Set.range g) : Set B) ↔ ∀ i, r * g i ∈ P := by
  rw [Ideal.colon_span, Submodule.mem_colon]
  simp only [Set.forall_mem_range, smul_eq_mul]

theorem _root_.GlobalTheory.ideal_map_colon_eq_of_flat : ∀ {A R : Type} [CommRing A] [IsNoetherianRing A] [CommRing R]
    (φ : A →+* R), φ.Flat → ∀ I J : Ideal A, (I.colon J).map φ = (I.map φ).colon (J.map φ) := by
  intro A R _ _ _ φ hφ I J
  obtain ⟨n, a, hJ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  obtain ⟨m, b, hI⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  replace hJ : Ideal.span (Set.range a) = J := hJ
  replace hI : Ideal.span (Set.range b) = I := hI
  subst hJ hI
  rw [Ideal.map_span φ (Set.range a), ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_colon_span_range_iff]
    rw [mem_colon_span_range_iff] at hr
    intro i
    simpa [map_mul] using Ideal.mem_map_of_mem φ (hr i)
  · intro s hs
    rw [mem_colon_span_range_iff] at hs
    have hmapI : (Ideal.span (Set.range b)).map φ = Ideal.span (Set.range (φ ∘ b)) := by
      rw [Ideal.map_span, ← Set.range_comp]
    choose c hc using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hmapI ▸ hs i)
    letI := φ.toAlgebra
    haveI : Module.Flat A R := hφ
    let f : (Fin n → A) →ₗ[A] A × (Fin n × Fin m → A) :=
      LinearMap.prod (Fintype.linearCombination A a)
        (LinearMap.pi fun p => -(b p.2) • LinearMap.proj p.1)
    let x : A × (Fin n × Fin m → A) →ₗ[A] R :=
      LinearMap.coprod (LinearMap.toSpanSingleton A R s)
        (Fintype.linearCombination A fun p => c p.1 p.2)
    have hxf : x ∘ₗ f = 0 := by
      refine LinearMap.ext fun v => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp [f, x, Algebra.smul_def, Fintype.sum_prod_type, Fintype.linearCombination_apply,
        LinearMap.pi_apply, map_sum, Finset.sum_mul]
      rw [← sub_eq_add_neg, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : ∑ j, algebraMap A R (b j) * algebraMap A R (v i) * c i j
          = algebraMap A R (v i) * ∑ j, c i j * (φ ∘ b) j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
        ring
      rw [e, hc i]
      simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
      ring
    obtain ⟨k, g, y, hxy, hgf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
    have hdec : ∀ w : A × (Fin n × Fin m → A), g w = w.1 • g (1, 0) +
        ∑ p, w.2 p • g (0, fun q => if p = q then 1 else 0) := by
      intro w
      have hw : w = w.1 • ((1 : A), (0 : Fin n × Fin m → A)) + ((0 : A), w.2) := by
        ext <;> simp
      conv_lhs => rw [hw]
      rw [map_add (f := _), map_smul]
      congr 1
      exact LinearMap.pi_apply_eq_sum_univ (g ∘ₗ LinearMap.inr A A (Fin n × Fin m → A)) w.2
    have key : ∀ q, g (1, 0) q ∈
        (Ideal.span (Set.range b)).colon (Ideal.span (Set.range a) : Set A) := by
      intro q
      rw [mem_colon_span_range_iff]
      intro i
      set w := f (fun j => if i = j then 1 else 0) with hw
      have hw1 : w.1 = a i := by simp [hw, f, Fintype.linearCombination_apply]
      have hw2 : ∀ p, w.2 p ∈ Ideal.span (Set.range b) := by
        intro p
        simp only [hw, f, LinearMap.prod_apply, Function.prod, LinearMap.pi_apply, LinearMap.smul_apply,
          LinearMap.proj_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ (neg_mem (Ideal.subset_span ⟨p.2, rfl⟩))
      have h0 := DFunLike.congr_fun (hdec w) q
      rw [show g w = 0 from LinearMap.congr_fun hgf _] at h0
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply] at h0
      have h1 : g (1, 0) q * a i = -∑ p, w.2 p * g (0, fun q => if p = q then 1 else 0) q := by
        rw [← hw1]
        linear_combination -h0
      rw [h1]
      exact neg_mem (Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hw2 p))
    have hs' : s = x (1, 0) := by simp [x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs', hxy, LinearMap.comp_apply, ← Finsupp.univ_sum_single (g (1, 0)), map_sum]
    refine Ideal.sum_mem _ fun q _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ (key q))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatTensorEmbedsTensorFractionFields
section
open TensorProduct

namespace GlobalTheory

theorem flat_tensor_embeds_tensor_fractionFields
    (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C]
    [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F]
    [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L]
    [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L]
    [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Flat T U] :
    ∃ φ : U ⊗[T] C →+* L ⊗[F] K, Function.Injective φ ∧
      ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c := by
  have hF : Module.Flat T F := IsLocalization.flat F (nonZeroDivisors T)
  have hK : Module.Flat T K := Module.Flat.trans T F K
  let f : U →ₐ[T] L := IsScalarTower.toAlgHom T U L
  let g : C →ₐ[T] K := IsScalarTower.toAlgHom T C K
  let e : L ⊗[F] K ≃ₐ[F] L ⊗[T] K :=
    IsLocalization.algebraTensorEquiv (nonZeroDivisors T) F L K
  refine ⟨(e.symm.toRingHom : L ⊗[T] K →+* L ⊗[F] K).comp
    (Algebra.TensorProduct.map f g).toRingHom, ?_, ?_⟩
  · have hf : Function.Injective f.toLinearMap := IsFractionRing.injective U L
    have hg : Function.Injective g.toLinearMap := IsFractionRing.injective C K
    have h1 : Function.Injective (LinearMap.lTensor U g.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hg
    have h2 : Function.Injective (LinearMap.rTensor K f.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hf
    have h3 : Function.Injective (TensorProduct.map f.toLinearMap g.toLinearMap) := by
      rw [← LinearMap.rTensor_comp_lTensor]
      exact h2.comp h1
    intro x y hxy
    apply h3
    exact e.symm.injective hxy
  · intro u c
    show e.symm (f u ⊗ₜ g c) = _
    rw [AlgEquiv.symm_apply_eq]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianPairingMomentAlgebra
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem gaussian_pairing_moment_algebra :
    ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ)
      (t f : ℂ) (p q : σ → ℂ) (m n : Matrix σ σ ℂ),
      Sᵀ = S → Tᵀ = T → IsUnit (1 - (t ^ 2) • (T * S)).det →
      p = t • (f • y + T *ᵥ q) → q = t • (f • x + S *ᵥ p) →
      m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q + t • (T * n) →
      n = t • vecMulVec x q + t • (S * m) →
      (let w : σ → ℂ := (1 - (t ^ 2) • (T * S))⁻¹ *ᵥ (y + t • T *ᵥ x)
       let u : σ → ℂ := x + t • S *ᵥ w
       f * (x ⬝ᵥ y) + x ⬝ᵥ T *ᵥ q + y ⬝ᵥ S *ᵥ p + (S * m * Tᵀ).trace =
         f * (u ⬝ᵥ w + t * (T * S * (1 - (t ^ 2) • (T * S))⁻¹).trace)) := by
  intro σ _ _ S T x y t f p q m n hS hT hA hp hq hm hn w u
  set A : Matrix σ σ ℂ := 1 - (t ^ 2) • (T * S) with hAdef
  have hKA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hAK : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hAv : ∀ v : σ → ℂ, A *ᵥ v = v - (t ^ 2) • T *ᵥ (S *ᵥ v) := by
    intro v
    rw [hAdef, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hAp : A *ᵥ p = (t * f) • (y + t • T *ᵥ x) := by
    have h1 : p = t • (f • y + T *ᵥ (t • (f • x + S *ᵥ p))) := by rw [← hq]; exact hp
    rw [hAv]
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul] at h1
    rw [sub_eq_iff_eq_add]
    refine h1.trans ?_
    module
  have hpw : p = (t * f) • w := by
    have : p = A⁻¹ *ᵥ (A *ᵥ p) := by rw [Matrix.mulVec_mulVec, hKA, Matrix.one_mulVec]
    rw [this, hAp, Matrix.mulVec_smul]
  have hqu : q = (t * f) • u := by
    rw [hq, hpw, Matrix.mulVec_smul]
    simp only [u]
    module
  have hAw : A *ᵥ w = y + t • T *ᵥ x := by
    simp only [w]
    rw [Matrix.mulVec_mulVec, hAK, Matrix.one_mulVec]
  have hw : w = y + t • T *ᵥ u := by
    rw [hAv, sub_eq_iff_eq_add] at hAw
    refine hAw.trans ?_
    simp only [u]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  have hAm : A * m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec (y + t • T *ᵥ x) q := by
    have h1 : m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q
        + t • (T * (t • vecMulVec x q + t • (S * m))) := by rw [← hn]; exact hm
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_vecMulVec,
      ← Matrix.mul_assoc] at h1
    rw [hAdef, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_eq_iff_eq_add,
      Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
    refine h1.trans ?_
    module
  have hmK : m = (t * f) • A⁻¹ + t • vecMulVec w q := by
    have : m = A⁻¹ * (A * m) := by rw [← Matrix.mul_assoc, hKA, Matrix.one_mul]
    rw [this, hAm, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_vecMulVec]
  have htr : (S * m * Tᵀ).trace
      = (t * f) * (T * S * A⁻¹).trace + t * ((S *ᵥ w) ⬝ᵥ (T *ᵥ q)) := by
    rw [hmK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Matrix.vecMul_transpose,
      hT, Matrix.trace_mul_comm (S * A⁻¹) T, Matrix.mul_assoc T S, smul_eq_mul, smul_eq_mul]
  have huw : u ⬝ᵥ w = x ⬝ᵥ y + t * (x ⬝ᵥ T *ᵥ u) + t * (y ⬝ᵥ S *ᵥ w)
      + t ^ 2 * ((S *ᵥ w) ⬝ᵥ (T *ᵥ u)) := by
    have h1 : u ⬝ᵥ w = (x + t • S *ᵥ w) ⬝ᵥ (y + t • T *ᵥ u) := by rw [← hw]
    rw [h1]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (S *ᵥ w) y]
    ring
  rw [htr, huw, hqu, hpw]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

end GlobalTheory
end

