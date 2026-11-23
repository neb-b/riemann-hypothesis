module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgHomEqOfReductionEqOfCoordsEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem algHom_eq_of_reduction_eq_of_coords_eq :
    ∀ (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [Algebra.FiniteType O B] (s s' : B →ₐ[O] O) (g : ℕ) (u : Fin g → B), (∀ b, s b - s' b ∈ IsLocalRing.maximalIdeal O) → (∀ i, s (u i) = s' (u i)) → (∀ b, s b = 0 → ∃ t : B, IsUnit (s t) ∧ t * b ∈ Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ⊔ (IsLocalRing.maximalIdeal O).map (algebraMap O B)) → s = s' := by
  intro O B _ _ _ _ hft s s' g u hred hu hgen
  classical
  obtain ⟨S, hS⟩ := hft.out
  let N : Ideal O := Ideal.span ((S.image fun b => s' b - s b : Finset O) : Set O)
  have hNfg : N.FG := ⟨_, rfl⟩
  have h1 : ∀ b, s' b - s b ∈ N := by
    intro b
    have hb : b ∈ Algebra.adjoin O (S : Set B) := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      exact Ideal.subset_span (by
        simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
    | algebraMap r => simp
    | add x y _ _ hx hy =>
      have : s' (x + y) - s (x + y) = (s' x - s x) + (s' y - s y) := by
        simp only [map_add (f := _)]; ring
      rw [this]; exact N.add_mem hx hy
    | mul x y _ _ hx hy =>
      have : s' (x * y) - s (x * y) = s' x * (s' y - s y) + s y * (s' x - s x) := by
        simp only [map_mul]; ring
      rw [this]; exact N.add_mem (N.mul_mem_left _ hy) (N.mul_mem_left _ hx)
  have h2 : ∀ y ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O B),
      ∀ c : B, s' (c * y) - s (c * y) ∈ IsLocalRing.maximalIdeal O * N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      have : s' (c * algebraMap O B a) - s (c * algebraMap O B a) = a * (s' c - s c) := by
        simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]; ring
      rw [this]; exact Ideal.mul_mem_mul ha (h1 c)
    | zero => intro c; simp
    | add x y _ _ hx hy =>
      intro c
      have : s' (c * (x + y)) - s (c * (x + y))
          = (s' (c * x) - s (c * x)) + (s' (c * y) - s (c * y)) := by
        simp only [map_add (f := _), map_mul]; ring
      rw [this]; exact Ideal.add_mem _ (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      have := hx (c * a)
      rwa [_root_.mul_assoc] at this
  have h3 : ∀ j ∈ Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))),
      s j = 0 ∧ s' j = 0 := by
    intro j hj
    have a1 : Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ≤
        RingHom.ker (s : B →+* O) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    have a2 : Ideal.span (Set.range fun i => u i - algebraMap O B (s (u i))) ≤
        RingHom.ker (s' : B →+* O) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker, hu i]
    exact ⟨a1 hj, a2 hj⟩
  have h4 : ∀ x, s' x - s x ∈ IsLocalRing.maximalIdeal O * N := by
    intro x
    have hb : s (x - algebraMap O B (s x)) = 0 := by simp
    have hb' : s' (x - algebraMap O B (s x)) = s' x - s x := by simp
    obtain ⟨t, ht, hmem⟩ := hgen _ hb
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 hmem
    have ht' : IsUnit (s' t) := by
      by_contra hn
      have m1 : s' t ∈ IsLocalRing.maximalIdeal O := hn
      have m2 := Ideal.add_mem _ (hred t) m1
      rw [sub_add_cancel] at m2
      exact m2 ht
    obtain ⟨j1, j2⟩ := h3 j hj
    have e1 := congrArg s hjy
    have e2 := congrArg s' hjy
    rw [map_add (f := _), map_mul, hb, j1] at e1
    rw [map_add (f := _), map_mul, hb', j2] at e2
    have h5 := h2 y hy 1
    rw [_root_.one_mul] at h5
    have : s' y - s y = s' t * (s' x - s x) := by
      linear_combination e2 - e1
    rw [this] at h5
    exact (Ideal.unit_mul_mem_iff_mem _ ht').1 h5
  have hN : N = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) N hNfg ?_ ?_
    · rw [Ideal.span_le]
      intro z hz
      simp only [Finset.coe_image] at hz
      obtain ⟨x, _, rfl⟩ := hz
      exact h4 x
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  ext b
  have := h1 b
  rw [hN, Ideal.mem_bot, sub_eq_zero] at this
  exact this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenDisjointImageOfIsConstructible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem interior_closure_eq_empty_of_isConstructible_of_disjoint_dense
    {Y : Type*} [TopologicalSpace Y] {D Sg : Set Y} (hD : Topology.IsConstructible D)
    (hSg : Dense Sg) (h : Disjoint D Sg) : interior (closure D) = ∅ := by
  have h1 : interior (frontier D) = ∅ :=
    interior_frontier_preimage_of_isConstructible (f := id) continuous_id hD
  have h2 : interior D = ∅ :=
    interior_eq_empty_iff_dense_compl.2 (hSg.mono h.subset_compl_left)
  rwa [frontier, h2, Set.diff_empty] at h1

theorem exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense :
    ∀ (X S : Scheme.{0}) [IsIntegral S] [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (C : Set X) (Sg : Set S), Topology.IsConstructible C → Dense Sg → Disjoint (f '' C) Sg → ∃ V : S.Opens, (V : Set S).Nonempty ∧ IsAffineOpen V ∧ Disjoint (f '' C) V := by
  intro X S _ _ f _ _ C Sg hC hSg h
  have hD : Topology.IsConstructible (f '' C) := f.isConstructible_image hC
  have h1 := interior_closure_eq_empty_of_isConstructible_of_disjoint_dense hD hSg h
  obtain ⟨x, hx⟩ : ((closure (f '' C))ᶜ).Nonempty :=
    (interior_eq_empty_iff_dense_compl.1 h1).nonempty
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hx isClosed_closure.isOpen_compl
  refine ⟨V, ⟨x, hxV⟩, hV, ?_⟩
  exact Set.disjoint_left.2 fun y hy hyV => hVU hyV (subset_closure hy)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem hom_ext_of_geometricPoints_dense {X Y S : Scheme.{0}} [IsReduced X] (t : Y ⟶ S)
    [IsSeparated t] (f g : X ⟶ Y) (h : f ≫ t = g ≫ t) (D : Set X) (hD : Dense D)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.range x ⊆ D →
      x ≫ f = x ≫ g) : f = g := by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated t h (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨Dense.mono (fun x hx ↦ ?_) hD⟩
  let K := AlgebraicClosure (X.residueField x)
  let y : Sp K ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫ X.fromSpecResidueField x
  have hy : ∀ p, y p = x := fun p ↦ Scheme.fromSpecResidueField_apply x _
  have hxy : y ≫ f = y ≫ g := H K y (by rintro _ ⟨p, rfl⟩; rwa [hy])
  have p : Sp K := IsLocalRing.closedPoint K
  refine ⟨equalizer.lift y hxy p, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι, hy]

theorem exists_lift_closedImmersion_of_dense {X Y Z : Scheme.{0}} [IsReduced X] (i : Z ⟶ Y)
    [IsClosedImmersion i] (f : X ⟶ Y) (D : Set X) (hD : Dense D)
    (H : ∀ x ∈ D, f x ∈ Set.range i) : ∃ f' : X ⟶ Z, f' ≫ i = f := by
  have : IsDominant (pullback.snd i f) := ⟨Dense.mono (fun x hx ↦ by
    rw [Scheme.Pullback.range_snd]; exact H x hx) hD⟩
  have : Surjective (pullback.snd i f) :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i f)
  refine ⟨inv (pullback.snd i f) ≫ pullback.fst i f, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

theorem dense_fibres_ext :
    ∀ (X S : Scheme.{0}) [IsReduced X] (s : X ⟶ S) [Flat s] [LocallyOfFinitePresentation s]
      (Sg : Set S), Dense Sg → Dense (s ⁻¹' Sg) ∧
      (∀ (Y : Scheme.{0}) (t : Y ⟶ S) [IsSeparated t] (f g : X ⟶ Y), f ≫ t = s → g ≫ t = s →
        (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
          Set.range (x ≫ s) ⊆ Sg → x ≫ f = x ≫ g) → f = g) ∧
      (∀ (Y Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y),
        (∀ x : X, s x ∈ Sg → f x ∈ Set.range i) → ∃ f' : X ⟶ Z, f' ≫ i = f) := by
  intro X S _ s _ _ Sg hSg
  have hD : Dense (s ⁻¹' Sg) := hSg.preimage s.isOpenMap
  refine ⟨hD, fun Y t _ f g hf hg H ↦ ?_, fun Y Z i _ f H ↦ ?_⟩
  · refine hom_ext_of_geometricPoints_dense t f g (hf.trans hg.symm) _ hD fun K _ _ x hx ↦ ?_
    refine H K x ?_
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hx ⟨p, rfl⟩
  · exact exists_lift_closedImmersion_of_dense i f _ hD H

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalCoordinates
section
open TensorProduct

namespace GlobalTheory.LocalCoord

theorem exists_frobenius (k A : Type) [Field k] [Finite k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (m : Ideal A) (hm : m.IsMaximal) :
    ∃ F : A →ₐ[k] A, (∀ a, a - F a ∈ m) ∧ ∀ a, ∃ c, F a = a * a * c := by
  letI := Fintype.ofFinite k
  letI := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  haveI : Finite (A ⧸ m) := Module.finite_of_finite k
  letI := Fintype.ofFinite (A ⧸ m)
  have hpow : ∀ (n : ℕ) (a : A),
      (FiniteField.frobeniusAlgHom k A ^ n) a = a ^ (Fintype.card k ^ n) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom, pow_succ, pow_mul]
  have hc : Fintype.card (A ⧸ m) = Fintype.card k ^ Module.finrank k (A ⧸ m) :=
    Module.card_eq_pow_finrank
  refine ⟨FiniteField.frobeniusAlgHom k A ^ Module.finrank k (A ⧸ m), fun a => ?_, fun a => ?_⟩
  · rw [hpow, ← hc, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, FiniteField.pow_card,
      sub_self]
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Fintype.one_lt_card (α := A ⧸ m))
    exact ⟨a ^ d, by rw [hpow, ← hc, hd]; ring⟩

theorem span_of_derivation {k A K B W : Type} [Field k] [PerfectField k] [CommRing A]
    [Algebra k A] [Field K] [Algebra k K] [CommRing B] [Algebra K B] [AddCommGroup W]
    [Module K W] [Module k W] [IsScalarTower k K W]
    (φ : K ⊗[k] A →ₐ[K] B) (χ : B →ₐ[K] K) {g : ℕ}
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≤ nilradical _)
    (t : Fin g → B) (s : B) (hs : χ s ≠ 0) (ht : ∀ i, χ (t i) = 0)
    (hb : ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t))
    (D : A →ₗ[k] W)
    (hD : ∀ a b, D (a * b) = χ (φ (1 ⊗ₜ a)) • D b + χ (φ (1 ⊗ₜ b)) • D a)
    (hN : ∀ a ∈ nilradical A, D a = 0) :
    ∃ w : Fin g → W, ∀ a, χ (φ (1 ⊗ₜ a)) = 0 → D a ∈ Submodule.span K (Set.range w) := by
  classical
  let E : K ⊗[k] A →ₗ[K] W := D.liftBaseChange K
  have hψ : ∀ (c : K) (a : A), χ (φ (c ⊗ₜ a)) = c * χ (φ (1 ⊗ₜ a)) := by
    intro c a
    rw [← smul_eq_mul, ← map_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hE : ∀ x y, E (x * y) = χ (φ x) • E y + χ (φ y) • E x := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [add_mul, map_add (f := _), h, h', add_smul, smul_add]; abel
    | tmul c a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [mul_add, map_add (f := _), h, h', add_smul, smul_add]; abel
      | tmul d b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hψ c, hψ d]
        simp only [E, LinearMap.liftBaseChange_tmul, hD, smul_add, smul_smul]
        congr 2 <;> ring
  have hEN : ∀ x ∈ nilradical (K ⊗[k] A), E x = 0 := by
    intro x hx
    haveI : IsReduced (A ⧸ nilradical A) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    haveI := GlobalTheory.ReducedAlg.isReduced_field_tensor (k := k) K (A ⧸ nilradical A)
    let π := Algebra.TensorProduct.map (AlgHom.id k K) (Ideal.Quotient.mkₐ k (nilradical A))
    have h0 : π x = 0 := ((mem_nilradical.mp hx).map π).eq_zero
    let D' : (A ⧸ nilradical A) →ₗ[k] W :=
      (((nilradical A).restrictScalars k).liftQ D (fun a ha => hN a ha)).comp
        (Submodule.Quotient.restrictScalarsEquiv k (nilradical A)).symm.toLinearMap
    have key : ∀ y, E y = D'.liftBaseChange K (π y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add (f := _), h, h']
      | tmul d b => rfl
    rw [key, h0, map_zero]
  choose l hl using hφ
  refine ⟨fun i => E (l (t i)), fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hb _ ha)
  have h1 : E (l s * 1 ⊗ₜ a - ∑ i, l (c i) * l (t i)) = 0 := by
    refine hEN _ (hker ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, map_mul, map_sum]
    simp only [map_mul, hl, hc, sub_self]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, sub_eq_zero] at h1
  simp only [hE, hl, ha, ht, zero_smul, add_zero] at h1
  have h2 : E (1 ⊗ₜ a) = D a := by simp [E]
  rw [h2] at h1
  rw [← Submodule.smul_mem_iff _ hs, h1]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_local_coordinates :
    ∀ (k A K B : Type) [Field k] [Finite k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] [CommRing B] [Algebra K B] (φ : TensorProduct k K A →ₐ[K] B) (χ : B →ₐ[K] K) (g : ℕ) (m : Ideal A), Function.Surjective φ → RingHom.ker φ ≤ nilradical _ → (∀ a : A, a ∈ m ↔ χ (φ (1 ⊗ₜ a)) = 0) → m.IsMaximal → (∃ (t : Fin g → B) (s : B), χ s ≠ 0 ∧ (∀ i, χ (t i) = 0) ∧ ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t)) → IsReduced B → ∃ (u : Fin g → A) (s : A), s ∉ m ∧ (∀ i, u i ∈ m) ∧ ∀ a ∈ m, s * a ∈ Ideal.span (Set.range u) ⊔ nilradical A := by
  intro k A K B _ _ _ _ _ _ _ _ _ φ χ g m hφ hker hm hmax ⟨t, s, hs, ht, hb⟩ _
  classical
  letI := Ideal.Quotient.field m
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨F, hF, hF2⟩ := exists_frobenius k A m hmax
  let ι : A →ₐ[k] K := ((χ.comp φ).restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hι : ∀ a, ι a = χ (φ (1 ⊗ₜ a)) := fun a => rfl
  let ι' : (A ⧸ m) →+* K := Ideal.Quotient.lift m ι fun a ha => (hm a).mp ha
  let N' : Submodule (A ⧸ m) m.Cotangent :=
    Submodule.span _ {y | ∃ x : m, (x : A) ∈ nilradical A ∧ m.toCotangent x = y}
  haveI : Module.Finite A m.Cotangent :=
    Module.Finite.of_surjective m.toCotangent m.toCotangent_surjective
  haveI : Module.Finite (A ⧸ m) m.Cotangent := Module.Finite.of_restrictScalars_finite A _ _
  let r := Module.finrank (A ⧸ m) (m.Cotangent ⧸ N')
  let b := Module.finBasis (A ⧸ m) (m.Cotangent ⧸ N')
  let p : m → m.Cotangent ⧸ N' := fun x => N'.mkQ (m.toCotangent x)
  have hpadd : ∀ x y, p (x + y) = p x + p y := fun x y => by simp only [p, map_add (f := _)]
  have hpsmul : ∀ (a : A) x, p (a • x) = Ideal.Quotient.mk m a • p x := fun a x => by
    simp only [p, map_smul]; rfl
  have hpsurj : Function.Surjective p := N'.mkQ_surjective.comp m.toCotangent_surjective
  let L : m → Fin r → K := fun x j => ι' (b.repr (p x) j)
  have hLadd : ∀ x y, L (x + y) = L x + L y := fun x y => by
    ext j; simp only [L, hpadd, map_add (f := _), Finsupp.add_apply, Pi.add_apply]
  have hLsmul : ∀ (a : A) x, L (a • x) = ι a • L x := fun a x => by
    ext j
    simp only [L, hpsmul, map_smul, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    rfl
  let D : A →ₗ[k] Fin r → K :=
    { toFun := fun a => L ⟨a - F a, hF a⟩
      map_add' := fun a a' => by
        rw [← hLadd]; congr 1; ext; simp only [map_add (f := _), Submodule.coe_add]; ring
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← algebraMap_smul K c (L _), ← ι.commutes, ← hLsmul]
        congr 1; ext
        change c • a - F (c • a) = algebraMap k A c * (a - F a)
        rw [map_smul, ← Algebra.smul_def, smul_sub] }
  have hιF : ∀ a, ι (F a) = ι a := fun a => by
    have := (hm _).mp (hF a)
    rw [← hι, map_sub, sub_eq_zero] at this
    exact this.symm
  obtain ⟨w, hw⟩ := span_of_derivation φ χ hφ hker t s hs ht hb D (fun a a' => by
      change L _ = ι a • L _ + ι a' • L _
      rw [← hιF a', ← hLsmul, ← hLsmul, ← hLadd]
      congr 1; ext
      simp only [map_mul, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
      ring) (fun a ha => by
      have : p ⟨a - F a, hF a⟩ = 0 := by
        refine (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨_, ?_, rfl⟩)
        exact sub_mem ha ((mem_nilradical.mp ha).map F)
      change L _ = 0
      ext j
      simp [L, this])
  choose v hv using hpsurj
  have hDL : ∀ x : m, D x = L x := fun x => by
    obtain ⟨c, hc⟩ := hF2 x
    have h1 : L x = L ⟨x - F x, hF x⟩ + L ((x * c : A) • x) := by
      rw [← hLadd]; congr 1; ext
      simp only [hc, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
      ring
    rw [h1, hLsmul, map_mul, hι, (hm _).mp x.2, zero_mul, zero_smul, add_zero]
    rfl
  have hrg : r ≤ g := by
    have htop : Submodule.span K (Set.range w) = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have : Pi.basisFun K (Fin r) j = D (v (b j)) := by
        rw [hDL]
        ext i
        simp only [L, hv, Module.Basis.repr_self, Pi.basisFun_apply, Finsupp.single_apply,
          Pi.single_apply]
        by_cases h : j = i
        · simp [h]
        · simp [h, Ne.symm h]
      rw [this]
      exact hw _ ((hm _).mp (v (b j)).2)
    have := finrank_range_le_card (R := K) w
    rwa [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at this
  let u : Fin g → A := fun i => if h : i.1 < r then (v (b ⟨i.1, h⟩) : A) else 0
  have hu : ∀ j : Fin r, (v (b j) : A) ∈ Ideal.span (Set.range u) := fun j =>
    Ideal.subset_span ⟨⟨j.1, lt_of_lt_of_le j.2 hrg⟩, by simp [u]⟩
  have hle : m ≤ (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m := by
    set J := (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m with hJ
    have hk : ∀ y ∈ N', ∀ x : m, m.toCotangent x = y → (x : A) ∈ J := by
      intro y hy
      have : ∃ z : m, (z : A) ∈ nilradical A ∧ m.toCotangent z = y := by
        induction hy using Submodule.span_induction with
        | mem y h => exact h
        | zero => exact ⟨0, zero_mem _, map_zero _⟩
        | add y y' _ _ h h' =>
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨z', hz', rfl⟩ := h'
          exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
        | smul c y _ h =>
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact ⟨c • z, Ideal.mul_mem_left _ _ hz, by rw [map_smul]; rfl⟩
      obtain ⟨z, hz, rfl⟩ := this
      intro x hx
      have h2 := m.toCotangent_eq.mp hx
      have : (x : A) = z + (x - z) := by ring
      rw [this]
      refine add_mem (Ideal.mem_sup_left (Ideal.mem_sup_right hz)) (Ideal.mem_sup_right ?_)
      rwa [pow_two] at h2
    have hall : ∀ y : m.Cotangent ⧸ N', ∃ z : m, (z : A) ∈ J ∧ p z = y := by
      intro y
      have hy : y ∈ Submodule.span (A ⧸ m) (Set.range b) := by rw [b.span_eq]; trivial
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨j, rfl⟩ := h
        exact ⟨v (b j), Ideal.mem_sup_left (Ideal.mem_sup_left (hu j)), hv _⟩
      | zero => exact ⟨0, zero_mem _, by simp [p]⟩
      | add y y' _ _ h h' =>
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨z', hz', rfl⟩ := h'
        exact ⟨z + z', add_mem hz hz', hpadd _ _⟩
      | smul c y _ h =>
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨c • z, Ideal.mul_mem_left _ _ hz, hpsmul _ _⟩
    intro a ha
    obtain ⟨z, hz, hp⟩ := hall (p ⟨a, ha⟩)
    have h3 := hk _ ((Submodule.Quotient.eq N').mp hp.symm) (⟨a, ha⟩ - z) (map_sub _ _ _)
    have : a = (a - z) + z := by ring
    rw [this]
    exact add_mem h3 hz
  obtain ⟨c, hc, hcle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (IsNoetherian.noetherian m) le_rfl hle
  refine ⟨u, c, fun h => hmax.ne_top ?_, fun i => ?_, fun a ha => ?_⟩
  · rw [Ideal.eq_top_iff_one]
    have := sub_mem h hc
    rwa [sub_sub_cancel] at this
  · simp only [u]
    split_ifs
    · exact Subtype.prop _
    · exact zero_mem _
  · exact hcle (Submodule.smul_mem_pointwise_smul a c m ha)

end GlobalTheory.LocalCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPairAvoidingSmallSets
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_notMem_of_ncard_lt_card {H : Type} [Finite H] (S : Set H)
    (h : S.ncard < Nat.card H) : ∃ x : H, x ∉ S := by
  by_contra hx
  have hS : S = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    by_contra hx'
    exact hx ⟨x, hx'⟩
  rw [hS, Set.ncard_univ] at h
  exact lt_irrefl _ h

theorem exists_pair_avoiding_small_sets :
    ∀ (H : Type) [CommGroup H] [Finite H] (B₀ B₁ : Set H), 6 * Nat.card B₀ < Nat.card H →
      6 * Nat.card B₁ < Nat.card H →
      ∃ b c : H, b ∉ B₀ ∧ c ∉ B₀ ∧ b * c ∉ B₀ ∧ b ∉ B₁ ∧ c ∉ B₁ ∧ b * c ∉ B₁ := by
  intro H _ _ B₀ B₁ h₀ h₁
  rw [Nat.card_coe_set_eq] at h₀ h₁
  have hS : (B₀ ∪ B₁).ncard ≤ B₀.ncard + B₁.ncard := Set.ncard_union_le _ _
  obtain ⟨b, hb⟩ := exists_notMem_of_ncard_lt_card (B₀ ∪ B₁) (by omega)
  have hT : ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤ (B₀ ∪ B₁).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have hU : ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤
      (B₀ ∪ B₁).ncard + ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard := Set.ncard_union_le _ _
  obtain ⟨c, hc⟩ := exists_notMem_of_ncard_lt_card
    ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)) (by omega)
  have hbc : b * c ∉ B₀ ∪ B₁ := fun h => hc (Or.inr ⟨b * c, h, by simp⟩)
  exact ⟨b, c, fun h => hb (Or.inl h), fun h => hc (Or.inl (Or.inl h)), fun h => hbc (Or.inl h),
    fun h => hb (Or.inr h), fun h => hc (Or.inl (Or.inr h)), fun h => hbc (Or.inr h)⟩

end GlobalTheory
end

