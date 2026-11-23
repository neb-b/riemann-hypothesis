module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSymmCommutantKroneckerLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SymmCommutant



end GlobalTheory.ZM.SymmCommutant

namespace GlobalTheory.ZM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma entry_eq_sum_of_mul_eq_mul_kronecker (K : Type) [Field K] (h : ℕ)
    (Ei Em : Matrix (Fin 8) (Fin 8) ℤ) (Θ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)
    (hΘ : ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K))
      (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v
      (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose)
    (v c : Fin 8) (i j : Fin h) :
    Θ (v, i) (c, j) = (Ei c v : K) * ∑ d, Θ (0, i) (d, j) * (Em 0 d : K) := by
  have hX : ∀ u v : Fin 8, (Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map
      (Int.cast : ℤ → K) = Matrix.of fun c d => (Ei c v : K) * (Em u d : K) := by
    intro u v; ext c d
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply, Finset.sum_ite_eq',
      Finset.sum_ite_eq, ite_and]
  have hA : ∀ u v : Fin 8, (Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K) =
      Matrix.single u v (1 : K) := by
    intro u v; ext a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs <;> simp
  have e := congrFun (congrFun (hΘ 0 v) (0, i)) (c, j)
  rw [hA, hX] at e
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Matrix.of_apply, Fintype.sum_prod_type, Matrix.single_apply, Matrix.one_apply] at e
  simpa [Finset.mul_sum, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc] using e


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.ZM.finrank_symm_commutant_le : ∀ (K : Type) [Field K] (h : ℕ) (Em Ei : Matrix (Fin 8) (Fin 8) ℤ) (V : Submodule K (Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)), Em.IsSymm → Ei * Em = 1 → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose) → Module.finrank K V ≤ h * (h + 1) / 2 := by
  intro K _ h Em Ei V hEm hEiEm hV
  let B : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K → Fin h → Fin h → K :=
    fun Θ i j => ∑ d, Θ (0, i) (d, j) * (Em 0 d : K)
  have key : ∀ Θ ∈ V, ∀ v c i j, Θ (v, i) (c, j) = (Ei c v : K) * B Θ i j :=
    fun Θ hΘ v c i j => entry_eq_sum_of_mul_eq_mul_kronecker K h Ei Em Θ (hV Θ hΘ).2 v c i j
  have hsum : ∑ d, (Ei 0 d : K) * (Em 0 d : K) = 1 := by
    have e := congrFun (congrFun hEiEm 0) 0
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at e
    have e' : ∑ d, Ei 0 d * Em 0 d = 1 := by
      rw [← e]; exact Finset.sum_congr rfl fun d _ => by rw [hEm.apply 0 d]
    have e'' := congrArg (Int.cast : ℤ → K) e'
    push_cast at e''
    exact e''
  have symmB : ∀ Θ ∈ V, ∀ i j, B Θ i j = B Θ j i := by
    intro Θ hΘ i j
    calc B Θ i j = ∑ d, (Ei 0 d : K) * B Θ j i * (Em 0 d : K) :=
          Finset.sum_congr rfl fun d _ => by
            rw [← key Θ hΘ d 0 j i, (hV Θ hΘ).1.apply (0, i) (d, j)]
      _ = B Θ j i * ∑ d, (Ei 0 d : K) * (Em 0 d : K) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
      _ = B Θ j i := by rw [hsum, _root_.mul_one]
  let L : V →ₗ[K] (Sym2 (Fin h) → K) :=
    { toFun := fun Θ s => B Θ (Quot.out s).1 (Quot.out s).2
      map_add' := by
        intro x y; funext s
        simp [B, Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro r x; funext s
        simp [B, Finset.mul_sum, _root_.mul_assoc] }
  have inj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro Θ hΘ0
    have hB : ∀ i j, B Θ i j = 0 := by
      intro i j
      have hs := congrFun hΘ0 s(i, j)
      have hout : s((Quot.out s(i, j)).1, (Quot.out s(i, j)).2) = s(i, j) := Quot.out_eq _
      rcases Sym2.eq_iff.1 hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rwa [h1, h2] at this
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rw [h1, h2] at this
        rwa [symmB Θ Θ.2] at this
    apply Subtype.ext
    ext ⟨v, i⟩ ⟨c, j⟩
    rw [key Θ Θ.2, hB]
    simp
  calc Module.finrank K V ≤ Module.finrank K (Sym2 (Fin h) → K) :=
        LinearMap.finrank_le_finrank_of_injective inj
    _ = h * (h + 1) / 2 := by
        rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin, Nat.choose_two_right,
          Nat.add_sub_cancel, mul_comm]

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.IsGaloisCover

theorem exists_algClosed_point (T : Scheme.{0}) (p : T) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : Sp K ⟶ T), p ∈ Set.range j := by
  let k := T.residueField p
  let K := AlgebraicClosure k
  let i : Spec (CommRingCat.of K) ⟶ Spec k := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine ⟨K, inferInstance, inferInstance, i ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨z, ?_⟩
  have hz : (T.fromSpecResidueField p) (i z) ∈ Set.range (T.fromSpecResidueField p) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at hz
  rw [Scheme.Hom.comp_apply]
  exact Set.mem_singleton_iff.mp hz

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}

theorem exists_local_geom (h : IsGaloisCover Ga ρ π) {T : Scheme.{0}} (x x' : T ⟶ X) (hx : x ≫ π = x' ≫ π) (p : T) :
    ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  have := h.etale
  let D := pullback.diagonal π
  let m : Ga → (T ⟶ pullback π π) := fun a =>
    pullback.lift (x ≫ ρ a) x' (by rw [Category.assoc, h.inv a, hx])
  obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point T p
  obtain ⟨a, ha, -⟩ := h.fibre K (j ≫ x) (j ≫ x') (by simp only [Category.assoc, hx])
  have hm1 : m a ≫ pullback.fst π π = x ≫ ρ a := pullback.lift_fst _ _ _
  have hm2 : m a ≫ pullback.snd π π = x' := pullback.lift_snd _ _ _
  have hjm : j ≫ m a = j ≫ x' ≫ D := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm1, Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      simpa only [Category.assoc] using ha
    · rw [Category.assoc, hm2, Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  let V : T.Opens := (m a) ⁻¹ᵁ D.opensRange
  have hpV : p ∈ V := by
    show (m a) p ∈ Set.range D
    rw [← hz]
    refine ⟨x' (j z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjm]
  have hsub : Set.range (V.ι ≫ m a) ⊆ Set.range D := by
    rintro _ ⟨w, rfl⟩
    have hw : V.ι w ∈ (V : Set T) := by
      rw [← Scheme.Opens.range_ι V]
      exact ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hw
  let l := IsOpenImmersion.lift D (V.ι ≫ m a) hsub
  have hl : l ≫ D = V.ι ≫ m a := IsOpenImmersion.lift_fac _ _ _
  refine ⟨V, a, hpV, ?_⟩
  have e1 : V.ι ≫ x ≫ ρ a = l := by
    have h1 : l ≫ D ≫ pullback.fst π π = l := by rw [pullback.diagonal_fst, Category.comp_id]
    rw [← h1, ← Category.assoc l, hl, Category.assoc, hm1]
  have e2 : V.ι ≫ x' = l := by
    have h2 : l ≫ D ≫ pullback.snd π π = l := by rw [pullback.diagonal_snd, Category.comp_id]
    rw [← h2, ← Category.assoc l, hl, Category.assoc, hm2]
  rw [e1, e2]

theorem existsUnique_desc (h : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} (f : X ⟶ Z) (hf : ∀ a, ρ a ≫ f = f) :
    ∃! f' : Y ⟶ Z, π ≫ f' = f := by
  have := h.fin
  have := h.etale
  have := h.onto
  have key : ∀ {W : Scheme.{0}} (g₁ g₂ : W ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ f = g₂ ≫ f := by
    intro W g₁ g₂ hg
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h.exists_local_geom g₁ g₂ hg p
    refine ⟨V, hp, ?_⟩
    calc V.ι ≫ g₁ ≫ f = V.ι ≫ g₁ ≫ ρ a ≫ f := by rw [hf]
      _ = (V.ι ≫ g₁ ≫ ρ a) ≫ f := by simp only [Category.assoc]
      _ = V.ι ≫ g₂ ≫ f := by rw [hV, Category.assoc]
  refine ⟨EffectiveEpi.desc π f key, EffectiveEpi.fac π f key, ?_⟩
  intro f' hf'
  apply (cancel_epi π).1
  rw [hf', EffectiveEpi.fac]

variable {X' Y' : Scheme.{0}} {π' : X' ⟶ Y'} {ρ' : Ga → (X' ⟶ X')} {u : X' ⟶ X} {v : Y' ⟶ Y}

private theorem existsUnique_act_of_isPullback_isGaloisCover (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v)
    (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a) (hπ : ∀ a, ρ' a ≫ π' = π') (K : Type) [Field K] [IsAlgClosed K]
    (y y' : Sp K ⟶ X') (hy : y ≫ π' = y' ≫ π') : ∃! a, y ≫ ρ' a = y' := by
  have hyu : (y ≫ u) ≫ π = (y' ≫ u) ≫ π := by
    simp only [Category.assoc, hp.w, reassoc_of% hy]
  obtain ⟨a, ha, hauniq⟩ := h.fibre K (y ≫ u) (y' ≫ u) hyu
  refine ⟨a, ?_, ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, hu, ← Category.assoc, ha]
    · rw [Category.assoc, hπ, hy]
  · intro b hb
    apply hauniq
    rw [Category.assoc, ← hu, ← Category.assoc, hb]

theorem isPullback (h : IsGaloisCover Ga ρ π) (h' : IsGaloisCover Ga ρ' π') (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (w : u ≫ π = π' ≫ v) : IsPullback u π' π v := by
  have := h.fin
  have := h.etale
  have := h.onto
  have := h'.fin
  have := h'.etale
  let ρP : Ga → (pullback π v ⟶ pullback π v) := fun a =>
    pullback.map π v π v (ρ a) (𝟙 Y') (𝟙 Y) (by rw [Category.comp_id, h.inv]) (by rw [Category.comp_id, Category.id_comp])
  have huP : ∀ a, ρP a ≫ pullback.fst π v = pullback.fst π v ≫ ρ a := fun a => pullback.lift_fst _ _ _
  have hπP : ∀ a, ρP a ≫ pullback.snd π v = pullback.snd π v := fun a => by
    rw [← Category.comp_id (pullback.snd π v)]
    exact pullback.lift_snd _ _ _
  let φ : X' ⟶ pullback π v := pullback.lift u π' w
  have hφ1 : φ ≫ pullback.fst π v = u := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd π v = π' := pullback.lift_snd _ _ _
  have hφeq : ∀ a, φ ≫ ρP a = ρ' a ≫ φ := fun a => by
    apply pullback.hom_ext
    · simp only [Category.assoc, huP, hφ1, reassoc_of% hφ1, hu]
    · simp only [Category.assoc, hπP, hφ2, h'.inv]
  have hmono : Mono φ := by
    constructor
    intro T g₁ g₂ hg
    have hg1 : g₁ ≫ u = g₂ ≫ u := by rw [← hφ1, reassoc_of% hg]
    have hg2 : g₁ ≫ π' = g₂ ≫ π' := by rw [← hφ2, reassoc_of% hg]
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h'.exists_local_geom g₁ g₂ hg2 p
    refine ⟨V, hp, ?_⟩
    have e : V.ι ≫ g₁ ≫ u ≫ ρ a = V.ι ≫ g₁ ≫ u := by
      rw [← hu, hg1]
      simpa only [Category.assoc] using congrArg (· ≫ u) hV
    obtain ⟨K, _, _, j, -⟩ := exists_algClosed_point V.toScheme ⟨p, hp⟩
    have ha : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ a = j ≫ V.ι ≫ g₁ ≫ u := by
      simp only [Category.assoc] at e ⊢
      rw [e]
    have h1 : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ 1 = j ≫ V.ι ≫ g₁ ≫ u := by
      rw [h.one, Category.comp_id]
    have ha1 : a = 1 := (h.fibre K _ _ rfl).unique ha h1
    rw [← hV, ha1, h'.one, Category.comp_id]
  have hsurj : Surjective φ := by
    constructor
    intro q
    obtain ⟨y, hy⟩ := h'.onto.surj (pullback.snd π v q)
    obtain ⟨r, hr1, hr2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd π v)
      (g := pullback.snd π v) (φ y) q (by rw [← Scheme.Hom.comp_apply, hφ2, hy])
    obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point _ r
    obtain ⟨a, ha, -⟩ := existsUnique_act_of_isPullback_isGaloisCover h (IsPullback.of_hasPullback π v) huP hπP K
      (j ≫ pullback.fst _ _) (j ≫ pullback.snd _ _)
      (by simp only [Category.assoc, pullback.condition])
    refine ⟨ρ' a y, ?_⟩
    have hz' := congrArg (fun m : Sp K ⟶ _ => m z) ha
    simp only [Scheme.Hom.comp_apply, hz, hr1, hr2] at hz'
    rw [← Scheme.Hom.comp_apply, ← hφeq, Scheme.Hom.comp_apply]
    exact hz'
  have : Etale φ := by
    have : Etale (φ ≫ pullback.snd π v) := by rw [hφ2]; exact h'.etale
    exact Etale.of_comp (f := φ) (pullback.snd π v)
  have : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ pullback.snd π v) := by rw [hφ2]; infer_instance
    exact MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) φ
      (pullback.snd π v) inferInstance this
  have : IsIso φ := Flat.isIso_of_surjective_of_mono φ
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2

theorem of_isPullback (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (hπ : ∀ a, ρ' a ≫ π' = π') : IsGaloisCover Ga ρ' π' := by
  refine ⟨h.finite, ?_, ?_, hπ, ?_, ?_, ?_, existsUnique_act_of_isPullback_isGaloisCover h hp hu hπ⟩
  · apply hp.hom_ext
    · rw [hu 1, h.one, Category.id_comp, Category.comp_id]
    · rw [hπ 1, Category.id_comp]
  · intro a c
    apply hp.hom_ext
    · rw [hu, h.mul, Category.assoc, hu c, reassoc_of% (hu a)]
    · rw [hπ, Category.assoc, hπ c, hπ a]
  · exact MorphismProperty.of_isPullback hp h.fin
  · exact MorphismProperty.of_isPullback hp h.etale
  · exact MorphismProperty.of_isPullback hp h.onto

end GlobalTheory.ZM.IsGaloisCover

namespace GlobalTheory.ZM

theorem galoisCover_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  intro X Y π Ga _ ρ h
  refine ⟨fun Z f hf => h.existsUnique_desc f hf, fun T x x' hx p => h.exists_local_geom x x' hx p, ?_⟩
  intro X' Y' π' ρ' u v hu w
  exact ⟨fun h' => h.isPullback h' hu w, fun hp hπ => h.of_isPullback hp hu hπ⟩

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorIsoExtendFromOpenContainingCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.GenPush

variable {X Y : Scheme.{0}}

private theorem gm_res_eq_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} {h : V ≤ U} (hy : f y ∈ V)
    (a : Γ(X, U)ˣ) : gm f y V (res h a) = gm f y U a := by
  apply Units.ext
  rw [← gs_unit f y V hy, ← gs_unit f y U (h hy)]
  exact gs_res f y h hy a.val

private theorem gm_id_pullU_eq_gm {X Y : Scheme.{0}} (c : Y ⟶ X) (y : Y) {U : X.Opens} (hy : c y ∈ U)
    (a : Γ(X, U)ˣ) : gm (𝟙 Y) y (c ⁻¹ᵁ U) (pullU c U a) = gm c y U a := by
  have hy' : (𝟙 Y ≫ c) y ∈ U := by simpa using hy
  apply Units.ext
  rw [← gs_unit (𝟙 Y) y (c ⁻¹ᵁ U) (by simpa using hy), ← gs_unit c y U hy]
  have e := gs_pull (𝟙 Y) c y U (by simpa using hy) a.val
  rw [Category.id_comp] at e
  exact e

private theorem mem_pull_U_of_mem {X Y : Scheme.{0}} (N : LB X) (c : Y ⟶ X) {y : Y} {a : N.ι} (ha : c y ∈ N.U a) :
    y ∈ (N.pull c).U (fun _ => a) := by
  unfold LB.pull LB.LinComb LB.wchart
  exact Set.mem_iInter.2 fun _ => ha

private theorem gm_id_pull_g_eq_gm_g {X Y : Scheme.{0}} (N : LB X) (c : Y ⟶ X) (y : Y) {a b : N.ι} (ha : c y ∈ N.U a)
    (hb : c y ∈ N.U b) :
    gm (𝟙 Y) y ((N.pull c).U (fun _ => a) ⊓ (N.pull c).U (fun _ => b)) ((N.pull c).g (fun _ => a) (fun _ => b)) =
      gm c y (N.U a ⊓ N.U b) (N.g a b) := by
  have hm : (𝟙 Y) y ∈ (N.pull c).U (fun _ => a) ⊓ (N.pull c).U (fun _ => b) :=
    ⟨mem_pull_U_of_mem N c (by simpa using ha), mem_pull_U_of_mem N c (by simpa using hb)⟩
  revert hm
  unfold LB.pull LB.LinComb
  dsimp only
  intro hm
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
  exact (gm_res_eq_gm (𝟙 Y) y hm _).trans (gm_id_pullU_eq_gm c y (show c y ∈ N.U a ⊓ N.U b from ⟨ha, hb⟩) _)

private theorem gm_div_g_eq_mul_inv {X Y : Scheme.{0}} (A B : LB X) (f : Y ⟶ X) (y : Y) (p q : (A.div B).ι)
    (hp : f y ∈ A.U p.1 ⊓ B.U p.2) (hq : f y ∈ A.U q.1 ⊓ B.U q.2) :
    gm f y ((A.div B).U p ⊓ (A.div B).U q) ((A.div B).g p q) =
      gm f y (A.U p.1 ⊓ A.U q.1) (A.g p.1 q.1) * (gm f y (B.U p.2 ⊓ B.U q.2) (B.g p.2 q.2))⁻¹ := by
  unfold LB.div
  dsimp only
  rw [map_mul, map_inv, gm_res_eq_gm f y (V := (A.U p.1 ⊓ B.U p.2) ⊓ (A.U q.1 ⊓ B.U q.2)) ⟨hp, hq⟩,
    gm_res_eq_gm f y (V := (A.U p.1 ⊓ B.U p.2) ⊓ (A.U q.1 ⊓ B.U q.2)) ⟨hp, hq⟩]

theorem exists_gen_of_units (c : Y ⟶ X) [IsOpenImmersion c] (N : LB X) (hN : ∀ a, N.U a ≤ c.opensRange)
    (V : N.ι → Y.Opens) (hV : ∀ a y, c y ∈ N.U a → y ∈ V a) (s : ∀ a, Γ(Y, V a)ˣ)
    (hs : ∀ (y : Y) a b, c y ∈ N.U a → c y ∈ N.U b →
      gm (𝟙 Y) y (V a) (s a) = gm c y (N.U a ⊓ N.U b) (N.g a b) * gm (𝟙 Y) y (V b) (s b)) :
    ∃ t : N.Gen, t.IsGen := by
  have hW : ∀ a, c ⁻¹ᵁ N.U a ≤ V a := fun a y hy => hV a y hy
  choose b hb using fun a => exists_ext_unit c (c ⁻¹ᵁ N.U a) (res (hW a) (s a))
  have hE : ∀ a, N.U a ≤ c ''ᵁ (c ⁻¹ᵁ N.U a) := by
    intro a x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range c := hN a hx
    exact ⟨y, hx, rfl⟩
  have key : ∀ (y : Y) a, c y ∈ N.U a → gm c y (c ''ᵁ (c ⁻¹ᵁ N.U a)) (b a) = gm (𝟙 Y) y (V a) (s a) := by
    intro y a ha
    have e := hb a Y (𝟙 Y) y (by simpa using ha)
    rw [Category.id_comp] at e
    rw [e, gm_res_eq_gm (𝟙 Y) y (by simpa using ha)]
  refine ⟨⟨fun a => res (hE a) (b a)⟩, ?_⟩
  unfold LB.Gen.IsGen
  intro a a'
  apply Units.ext
  apply fn_ext
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range c := hN a hx.1
  have hx' : (𝟙 X) (c y) ∈ N.U a ⊓ N.U a' := by simpa using hx
  rw [gs_unit (𝟙 X) (c y) _ hx', gs_unit (𝟙 X) (c y) _ hx']
  congr 1
  apply gm_inj c y hx hx
  rw [map_mul, gm_res_eq_gm c y hx, gm_res_eq_gm c y hx.1, gm_res_eq_gm c y hx, gm_res_eq_gm c y hx.2,
    key y a hx.1, key y a' hx.2]
  exact hs y a a' hx.1 hx.2

theorem gen_stalk {N : LB Y} {t : N.Gen} (ht : t.IsGen) (y : Y) (i j : N.ι) (hi : y ∈ N.U i) (hj : y ∈ N.U j) :
    gm (𝟙 Y) y (N.U i) (t.s i) = gm (𝟙 Y) y (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) y (N.U j) (t.s j) := by
  unfold LB.Gen.IsGen at ht
  have hm : (𝟙 Y) y ∈ N.U i ⊓ N.U j := by simpa using (⟨hi, hj⟩ : y ∈ N.U i ⊓ N.U j)
  have e := congrArg (gm (𝟙 Y) y (N.U i ⊓ N.U j)) (ht i j)
  rw [map_mul, gm_res_eq_gm (𝟙 Y) y hm, gm_res_eq_gm (𝟙 Y) y hm] at e
  exact e

theorem gen_iso_of_charts_le_range : ∀ (X Y : Scheme.{0}) (c : Y ⟶ X) [IsOpenImmersion c], (∀ N : LB X, (∀ a, N.U a ≤ c.opensRange) → (∃ t : (N.pull c).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen) ∧ ∀ M M' : LB X, (∀ a b, M.U a ⊓ M'.U b ≤ c.opensRange) → LBIso (M.pull c) (M'.pull c) → LBIso M M' := by
  intro X Y c _
  refine ⟨fun N hN ⟨t, ht⟩ => ?_, fun M M' hM ⟨w, hw⟩ => ?_⟩
  · refine exists_gen_of_units c N hN (fun a => (N.pull c).U (fun _ => a)) (fun a y hy => mem_pull_U_of_mem N c hy)
      (fun a => t.s (fun _ => a)) ?_
    intro y a b ha hb
    rw [gen_stalk ht y (fun _ => a) (fun _ => b) (mem_pull_U_of_mem N c ha) (mem_pull_U_of_mem N c hb),
      gm_id_pull_g_eq_gm_g N c y ha hb]
  · have hN : ∀ p : (M'.div M).ι, (M'.div M).U p ≤ c.opensRange := by
      intro p
      show M'.U p.1 ⊓ M.U p.2 ≤ _
      rw [inf_comm]
      exact hM p.2 p.1
    have hV : ∀ (p : (M'.div M).ι) (y : Y), c y ∈ (M'.div M).U p →
        y ∈ ((M'.pull c).div (M.pull c)).U ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι) :=
      fun p y hy => ⟨mem_pull_U_of_mem M' c hy.1, mem_pull_U_of_mem M c hy.2⟩
    obtain ⟨t, ht⟩ := exists_gen_of_units c (M'.div M) hN
      (fun p => ((M'.pull c).div (M.pull c)).U ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι)) hV
      (fun p => w.s ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι)) (by
        intro y p q hp hq
        rw [gen_stalk hw y _ _ (hV p y hp) (hV q y hq)]
        congr 1
        have m1 : (𝟙 Y) y ∈ (M'.pull c).U (fun _ => p.1) ⊓ (M.pull c).U (fun _ => p.2) := by
          have h : y ∈ (M'.pull c).U (fun _ => p.1) ⊓ (M.pull c).U (fun _ => p.2) := hV p y hp
          simpa using h
        have m2 : (𝟙 Y) y ∈ (M'.pull c).U (fun _ => q.1) ⊓ (M.pull c).U (fun _ => q.2) := by
          have h : y ∈ (M'.pull c).U (fun _ => q.1) ⊓ (M.pull c).U (fun _ => q.2) := hV q y hq
          simpa using h
        have e1 := gm_div_g_eq_mul_inv (M'.pull c) (M.pull c) (𝟙 Y) y
          ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι)
          ((fun _ => q.1, fun _ => q.2) : (M'.pull c).ι × (M.pull c).ι) m1 m2
        have e2 := gm_div_g_eq_mul_inv M' M c y p q hp hq
        refine e1.trans (Eq.trans ?_ e2.symm)
        dsimp only
        rw [gm_id_pull_g_eq_gm_g M' c y hp.1 hq.1, gm_id_pull_g_eq_gm_g M c y hp.2 hq.2])
    exact ⟨t, ht⟩

end GlobalTheory.GenPush
end
end

