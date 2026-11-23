module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301

@[expose] public section

open CategoryTheory Limits TensorProduct GlobalTheory.FiniteColim MvPolynomial

noncomputable section
namespace GlobalTheory.SplitColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}} {c : Cocone F}

theorem eventually_map_eq_zero (hc : IsColimit c) {k : J} (x : F.obj k)
    (hx : (c.ι.app k).hom x = 0) :
    ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k'), (F.map (f₀ ≫ f)).hom x = 0 := by
  have hc' := isColimitOfPreserves (forget _) hc
  have h0 : (c.ι.app k).hom x = (c.ι.app k).hom 0 := by rw [hx, map_zero]
  obtain ⟨k₀, f₀, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' x 0).1 (by exact h0)
  refine ⟨k₀, f₀, fun k' f => ?_⟩
  have e' : (F.map f₀).hom x = 0 := by simpa using e
  rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]

theorem eventually_map_eq_zero_finite (hc : IsColimit c) {k : J} {κ : Type} [Fintype κ]
    (x : κ → F.obj k) (hx : ∀ i, (c.ι.app k).hom (x i) = 0) :
    ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k') (i : κ), (F.map (f₀ ≫ f)).hom (x i) = 0 := by
  classical
  suffices H : ∀ S : Finset κ, ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k'),
      ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (x i) = 0 by
    obtain ⟨k₀, f₀, h⟩ := H Finset.univ
    exact ⟨k₀, f₀, fun k' f i => h k' f i (Finset.mem_univ i)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a S _ ih =>
    obtain ⟨k₀, f₀, h⟩ := GlobalTheory.TorsorColim.eventually_and
      (fun k' (g : k ⟶ k') => (F.map g).hom (x a) = 0)
      (fun k' (g : k ⟶ k') => ∀ i ∈ S, (F.map g).hom (x i) = 0)
      (eventually_map_eq_zero hc (x a) (hx a)) ih
    refine ⟨k₀, f₀, fun k' f i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (h k' f).1
    · exact (h k' f).2 i hi

theorem exists_stage_rep (hc : IsColimit c) (k₁ : J) {ι : Type} [Finite ι] (t : ι → c.pt) :
    ∃ (K : J) (h : k₁ ⟶ K) (u : ι → F.obj K), ∀ i, (c.ι.app K).hom (u i) = t i := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose jx x hx using fun i : ι => Types.jointly_surjective_of_isColimit hc' (t i)
  haveI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (insert k₁ (Finset.univ.image jx))
  obtain ⟨h⟩ := hK (Finset.mem_insert_self k₁ _)
  have hm : ∀ i, Nonempty (jx i ⟶ K) := fun i =>
    hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ i)))
  refine ⟨K, h, fun i => (F.map (hm i).some).hom (x i), fun i => ?_⟩
  have h1 := hx i
  have h2 := congr(($(c.w (hm i).some)).hom (x i))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2]
  exact h1

end GlobalTheory.SplitColim

namespace GlobalTheory.SplitColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}} {c : Cocone F}

theorem exists_late_solution (hc : IsColimit c) (k₁ : J) {ι κ : Type} [Finite ι] [Fintype κ]
    (P : κ → MvPolynomial ι (F.obj k₁)) (t : ι → c.pt)
    (ht : ∀ i, MvPolynomial.eval₂ (c.ι.app k₁).hom t (P i) = 0) :
    ∃ (k₀ : J) (f₀ : k₁ ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ u : ι → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom u (P i) = 0 := by
  obtain ⟨K, h, u, hu⟩ := exists_stage_rep hc k₁ t
  have hx : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (P i)) = 0 := by
    intro i
    rw [MvPolynomial.eval₂_comp_left]
    have e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app k₁).hom := by
      rw [← CommRingCat.hom_comp, c.w h]
    have e2 : ⇑(c.ι.app K).hom ∘ u = t := funext hu
    rw [e1, e2]; exact ht i
  obtain ⟨k₀, f₀, h0⟩ := eventually_map_eq_zero_finite hc _ hx
  refine ⟨k₀, h ≫ f₀, fun k f => ⟨fun a => (F.map (f₀ ≫ f)).hom (u a), fun i => ?_⟩⟩
  have := h0 k f i
  rw [MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp] at this
  rw [Category.assoc]
  exact this

theorem exists_late_linear (hc : IsColimit c) (k₁ : J) (M : Type) [AddCommGroup M]
    [Module (F.obj k₁) M] [Module.FinitePresentation (F.obj k₁) M] (m : M) :
    letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
    ∀ σ : M →ₗ[F.obj k₁] c.pt, σ m = 1 →
    ∃ (k₀ : J) (f₀ : k₁ ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
      ∃ σk : M →ₗ[F.obj k₁] F.obj k, σk m = 1 := by
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  intro σ hσ
  classical
  obtain ⟨s, hs, K, hK⟩ := Module.FinitePresentation.out (R := F.obj k₁) (M := M)
  set π := Finsupp.linearCombination (F.obj k₁) (Subtype.val : s → M) with hπdef
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, hπdef, Finsupp.range_linearCombination, Subtype.range_coe_subtype]
    simpa using hs
  obtain ⟨e, he⟩ := hπ m
  have hπapp : ∀ {T : Type} [AddCommGroup T] [Module (F.obj k₁) T] (g : M →ₗ[F.obj k₁] T)
      (v : s →₀ F.obj k₁), g (π v) = ∑ x, v x • g x := by
    intro T _ _ g v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hπdef, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp), map_sum]
    simp
  let lin : (s →₀ F.obj k₁) → MvPolynomial s (F.obj k₁) :=
    fun v => ∑ x, MvPolynomial.C (v x) * MvPolynomial.X x
  have evlin : ∀ {T : Type} [CommRing T] (φ : F.obj k₁ →+* T) (u : s → T) (v : s →₀ F.obj k₁),
      MvPolynomial.eval₂ φ u (lin v) = ∑ x, φ (v x) * u x := by
    intro T _ φ u v; simp [lin, MvPolynomial.eval₂_sum]
  let P : Option K → MvPolynomial s (F.obj k₁) := fun o => o.elim (lin e - 1) (fun v => lin v.1)
  have hKker : ∀ v ∈ K, π v = 0 := fun v hv => by
    have : v ∈ Submodule.span (F.obj k₁) (K : Set (s →₀ F.obj k₁)) := Submodule.subset_span hv
    rw [hK] at this
    exact this
  obtain ⟨k₀, f₀, hsol⟩ := exists_late_solution hc k₁ P (fun x => σ x) (by
    intro o
    cases o with
    | none =>
      change MvPolynomial.eval₂ _ _ (lin e - 1) = 0
      rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, evlin, sub_eq_zero, ← hσ, ← he, hπapp σ e]
      rfl
    | some v =>
      change MvPolynomial.eval₂ _ _ (lin v.1) = 0
      rw [evlin]
      have := hπapp σ v.1
      rw [hKker v.1 v.2, map_zero] at this
      rw [this]
      rfl)
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  obtain ⟨u, hu⟩ := hsol k f
  let φ := Finsupp.linearCombination (F.obj k₁) u
  have hφ : ∀ v : s →₀ F.obj k₁, φ v = MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom u (lin v) := by
    intro v
    rw [evlin, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · rfl
    · intro i; simp
  have hle : LinearMap.ker π ≤ LinearMap.ker φ := by
    rw [← hK, Submodule.span_le]
    intro v hv
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [hφ]
    exact hu (some ⟨v, hv⟩)
  refine ⟨((LinearMap.ker π).liftQ φ hle).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, ?_⟩
  have hq : (π.quotKerEquivOfSurjective hπ).symm m = Submodule.Quotient.mk e := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk, he]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.liftQ_apply, hφ]
  have := hu none
  change MvPolynomial.eval₂ _ _ (lin e - 1) = 0 at this
  rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, sub_eq_zero] at this
  exact this

end GlobalTheory.SplitColim

namespace GlobalTheory.SplitColim

theorem exists_late_split_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧
        ∃ τ : (c.pt ⊗[F.obj j] A) →ₗ[c.pt] c.pt, τ 1 = 1) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      ∃ τ : (F.obj k ⊗[F.obj j] A) →ₗ[F.obj k] F.obj k, τ 1 = 1 := by
  intro J _ _ F c hc j A _ _ hfp h
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨hfin, τ, hτ⟩ := h
  have hbase : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Finite (F.obj k) (F.obj k ⊗[F.obj j] A) := by
    classical
    obtain ⟨n, φ, hφ, hfg⟩ := hfp.out
    obtain ⟨s, hs⟩ := hfg
    let rel : s → MvPolynomial (Fin n) (F.obj j) := fun x => x
    have hker : RingHom.ker φ = Ideal.span (Set.range rel) := by
      have : Set.range rel = (s : Set (MvPolynomial (Fin n) (F.obj j))) := by
        ext x; simp [rel]
      rw [this, hs]
      rfl
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
    haveI : Algebra.IsIntegral c.pt (c.pt ⊗[F.obj j] A) := Algebra.IsIntegral.of_finite _ _
    have hint : ∀ i, IsIntegral c.pt (bcPres (S := c.pt) φ (X i)) :=
      fun i => Algebra.IsIntegral.isIntegral _
    choose p hpm hp0 using hint
    have hcomb : ∀ i, ∃ G : s → MvPolynomial (Fin n) c.pt,
        ∑ l, G l * MvPolynomial.map (algebraMap (F.obj j) c.pt) (rel l) =
          Polynomial.aeval (X i : MvPolynomial (Fin n) c.pt) (p i) := by
      intro i
      refine exists_comb_of_bcPres_eq_zero φ hφ rel hker _ ?_
      rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def]
      exact hp0 i
    choose G hG using hcomb
    let T : Finset c.pt := Finset.univ.biUnion (fun i => (p i).support.image (p i).coeff) ∪
      Finset.univ.biUnion (fun i => Finset.univ.biUnion (fun l => (G i l).coeffs))
    obtain ⟨k₁, f₁, hk₁⟩ := exists_stage_range hc j T
    have hlp : ∀ i, ∃ q : Polynomial (F.obj k₁), q.map (c.ι.app k₁).hom = p i ∧ q.Monic := by
      intro i
      have hl : p i ∈ Polynomial.lifts (c.ι.app k₁).hom := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro m
        by_cases hm : m ∈ (p i).support
        · exact hk₁ _ (Finset.mem_union_left _ (Finset.mem_biUnion.2
            ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hm⟩))
        · rw [Polynomial.notMem_support_iff.1 hm]; exact ⟨0, map_zero _⟩
      obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm i)
      exact ⟨q, hq, hqm⟩
    choose q hq hqm using hlp
    have hlG : ∀ i l, ∃ H, MvPolynomial.map (c.ι.app k₁).hom H = G i l := by
      intro i l
      have : G i l ∈ Set.range (MvPolynomial.map (σ := Fin n) (c.ι.app k₁).hom) := by
        rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
        intro y hy
        exact hk₁ _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
          Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hy⟩⟩))
      exact this
    choose H hH using hlG
    let E : Fin n → MvPolynomial (Fin n) (F.obj k₁) := fun i =>
      Polynomial.aeval (X i) (q i) - ∑ l, H i l * MvPolynomial.map (F.map f₁).hom (rel l)
    have hE : ∀ i, MvPolynomial.map (c.ι.app k₁).hom (E i) = 0 := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [E, map_sub, map_sum, map_mul, map_aeval_X, hq, hH, MvPolynomial.map_map]
      rw [← CommRingCat.hom_comp, c.w f₁, sub_eq_zero, ← hG i]
      rfl
    let U : Finset (F.obj k₁) := Finset.univ.biUnion (fun i => (E i).coeffs)
    obtain ⟨k₂, g₂, hg₂⟩ := exists_stage_zero hc U (by
      intro x hx
      obtain ⟨i, -, hx⟩ := Finset.mem_biUnion.1 hx
      obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hx
      have := congrArg (AddMonoidAlgebra.coeff · m) (hE i)
      rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this)
    have hE2 : ∀ i, MvPolynomial.map (F.map g₂).hom (E i) = 0 := by
      intro i
      ext m
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
      by_cases hm : m ∈ (E i).support
      · exact hg₂ _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
          MvPolynomial.coeff_mem_coeffs _ (MvPolynomial.mem_support_iff.1 hm)⟩)
      · simp [MvPolynomial.notMem_support_iff.1 hm]
    refine ⟨k₂, f₁ ≫ g₂, fun k f => ?_⟩
    letI : Algebra (F.obj j) (F.obj k) := (F.map ((f₁ ≫ g₂) ≫ f)).hom.toAlgebra
    have hrel : ∀ l, φ (rel l) = 0 := fun l =>
      (RingHom.mem_ker).1 (hker ▸ Ideal.subset_span ⟨l, rfl⟩ : rel l ∈ RingHom.ker φ)
    refine finite_of_relations φ hφ rel hrel (fun i => (q i).map (F.map (g₂ ≫ f)).hom)
      (fun i => (hqm i).map _) (fun i l => MvPolynomial.map (F.map (g₂ ≫ f)).hom (H i l)) (fun i => ?_)
    have halg : algebraMap (F.obj j) (F.obj k) = (F.map (g₂ ≫ f)).hom.comp (F.map f₁).hom := by
      change (F.map ((f₁ ≫ g₂) ≫ f)).hom = _
      rw [Category.assoc, Functor.map_comp, CommRingCat.hom_comp]
    have h3 : MvPolynomial.map (F.map (g₂ ≫ f)).hom (E i) = 0 := by
      rw [Functor.map_comp, CommRingCat.hom_comp, ← MvPolynomial.map_map, hE2, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E, map_sub, map_sum, map_mul, map_aeval_X, MvPolynomial.map_map, sub_eq_zero] at h3
    rw [halg]
    exact h3
  obtain ⟨k₁, f₁, hk₁⟩ := hbase
  have hfin₁ := hk₁ k₁ (𝟙 k₁)
  rw [Category.comp_id] at hfin₁
  letI : Algebra (F.obj j) (F.obj k₁) := (F.map f₁).hom.toAlgebra
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app j).hom x = (c.ι.app k₁).hom ((F.map f₁).hom x)
    rw [← c.w f₁]; rfl)
  haveI : Module.Finite (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) := hfin₁
  haveI : Module.FinitePresentation (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite _ _).2 inferInstance
  let g : A →ₗ[F.obj j] c.pt :=
    (τ.restrictScalars (F.obj j)).comp (TensorProduct.mk (F.obj j) c.pt A 1)
  let σ : (F.obj k₁ ⊗[F.obj j] A) →ₗ[F.obj k₁] c.pt := LinearMap.liftBaseChange (F.obj k₁) g
  have hσ : σ 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, LinearMap.liftBaseChange_tmul, one_smul]
    change τ (1 ⊗ₜ 1) = 1
    rw [← Algebra.TensorProduct.one_def]; exact hτ
  obtain ⟨k₀, f₀, hk₀⟩ := exists_late_linear hc k₁ _ (1 : F.obj k₁ ⊗[F.obj j] A) σ hσ
  refine ⟨k₀, f₁ ≫ f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map ((f₁ ≫ f₀) ≫ f)).hom.toAlgebra
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) (F.obj k) := IsScalarTower.of_algebraMap_eq (fun x => by
    change (F.map ((f₁ ≫ f₀) ≫ f)).hom x = (F.map (f₀ ≫ f)).hom ((F.map f₁).hom x)
    rw [Category.assoc, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply])
  obtain ⟨σk, hσk⟩ := hk₀ k f
  refine ⟨LinearMap.liftBaseChange (F.obj k)
    ((σk.restrictScalars (F.obj j)).comp (TensorProduct.mk (F.obj j) (F.obj k₁) A 1)), ?_⟩
  rw [Algebra.TensorProduct.one_def, LinearMap.liftBaseChange_tmul, one_smul]
  change σk (1 ⊗ₜ 1) = 1
  rw [← Algebra.TensorProduct.one_def]; exact hσk

end GlobalTheory.SplitColim
