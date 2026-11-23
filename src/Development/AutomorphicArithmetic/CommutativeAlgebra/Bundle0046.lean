module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ClopenCondOfIsClosedSubgroupLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem clopen_forall {S : Scheme.{0}} (X F : Over S) [IsFinite F.hom] [Etale F.hom]
    (W : (X ⊗ F).left.Opens) (hW : IsClosed (W : Set (X ⊗ F).left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ F),
      Set.range (lift (t ≫ h) a).left ⊆ W) := by
  have hWo : IsOpen ((W : Set (X ⊗ F).left)ᶜ) := hW.isOpen_compl
  have hWc : IsClosed ((W : Set (X ⊗ F).left)ᶜ) := W.isOpen.isClosed_compl
  have hKc : IsClosed (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isClosedMap _ hWc
  have hKo : IsOpen (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isOpenMap _ hWo
  refine ⟨⟨(pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ)ᶜ, hKc.isOpen_compl⟩,
    hKo.isClosed_compl, ?_⟩
  intro T h
  constructor
  · intro H
    rintro _ ⟨x, rfl⟩ ⟨z, hz, hzx⟩
    obtain ⟨q, hq1, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := h.left) (g := pullback.fst X.hom F.hom) x z hzx.symm
    let T' : Over S := Over.mk (pullback.fst h.left (pullback.fst X.hom F.hom) ≫ T.hom)
    let t : T' ⟶ T := Over.homMk (pullback.fst h.left (pullback.fst X.hom F.hom)) rfl
    have ha : (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ≫ F.hom
        = T'.hom := by
      simp only [T', Over.mk_hom, Category.assoc]
      rw [← pullback.condition (f := X.hom) (g := F.hom), ← Category.assoc,
        ← pullback.condition (f := h.left) (g := pullback.fst X.hom F.hom), Category.assoc, Over.w h]
    let a : T' ⟶ F :=
      Over.homMk (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ha
    have hl : (lift (t ≫ h) a).left = pullback.snd h.left (pullback.fst X.hom F.hom) := by
      apply pullback.hom_ext
      · change (lift (t ≫ h) a ≫ fst X F).left = _
        rw [lift_fst]
        exact pullback.condition
      · change (lift (t ≫ h) a ≫ snd X F).left = _
        rw [lift_snd]
        rfl
    apply hz
    have hmem := H T' t a ⟨q, rfl⟩
    rw [hl, hq2] at hmem
    exact hmem
  · intro H T' t a
    rintro _ ⟨y, rfl⟩
    by_contra hy
    have e : (lift (t ≫ h) a).left ≫ pullback.fst X.hom F.hom = t.left ≫ h.left := by
      change (lift (t ≫ h) a ≫ fst X F).left = _
      rw [lift_fst]
      rfl
    apply H ⟨t.left y, rfl⟩
    refine ⟨(lift (t ≫ h) a).left y, hy, ?_⟩
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]

private theorem clopen_pre {S : Scheme.{0}} {X Y : Over S} (e : X ⟶ Y) (U : Y.left.Opens)
    (hU : IsClosed (U : Set Y.left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => Set.range (h ≫ e).left ⊆ U) := by
  refine ⟨e.left ⁻¹ᵁ U, hU.preimage e.left.continuous, ?_⟩
  intro T h
  simp only [Over.comp_left, Set.range_subset_iff, Scheme.Hom.comp_apply, Scheme.Hom.mem_preimage, SetLike.mem_coe]

theorem UpperTheory.clopenCond_of_isClosed_subgroupLocus :
    ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [IsFinite G.hom] [Etale G.hom] (U : (X ⊗ G).left.Opens), IsClosed (U : Set (X ⊗ G).left) → GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T), Set.range (lift (t ≫ h) (1 : T' ⟶ G)).left ⊆ U ∧ ∀ a b : T' ⟶ G, Set.range (lift (t ≫ h) a).left ⊆ U → Set.range (lift (t ≫ h) b).left ⊆ U → Set.range (lift (t ≫ h) (a * b⁻¹)).left ⊆ U) := by
  intro S G X _ _ _ U hU
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).1
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).2
  have hUo : IsOpen (U : Set (X ⊗ G).left) := U.isOpen
  let m1 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ fst G G)
  let m2 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ snd G G)
  let m3 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ (fst G G * (snd G G)⁻¹))
  let Ws : Set (X ⊗ (G ⊗ G)).left :=
    (m1.left ⁻¹' U ∩ m2.left ⁻¹' U)ᶜ ∪ m3.left ⁻¹' U
  have hWo : IsOpen Ws :=
    ((hU.preimage m1.left.continuous).inter (hU.preimage m2.left.continuous)).isOpen_compl.union
      (hUo.preimage m3.left.continuous)
  have hWc : IsClosed Ws :=
    ((hUo.preimage m1.left.continuous).inter (hUo.preimage m2.left.continuous)).isClosed_compl.union
      (hU.preimage m3.left.continuous)
  have h1 := clopen_pre (lift (𝟙 X) (1 : X ⟶ G)) U hU
  have h2 := clopen_forall X (G ⊗ G) ⟨Ws, hWo⟩ hWc
  refine (h1.and h2).congr ?_
  intro T h
  have k0 : ∀ (T' : Over S) (t : T' ⟶ T),
      lift (t ≫ h) (1 : T' ⟶ G) = t ≫ h ≫ lift (𝟙 X) (1 : X ⟶ G) := by
    intro T' t
    simp [comp_lift]
  have k1 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m1 = lift u (c ≫ fst G G) := by
    intro T' u c
    simp [m1, comp_lift]
  have k2 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m2 = lift u (c ≫ snd G G) := by
    intro T' u c
    simp [m2, comp_lift]
  have k3 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m3 = lift u ((c ≫ fst G G) * (c ≫ snd G G)⁻¹) := by
    intro T' u c
    simp [m3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv]
  have pt : ∀ {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (y : A.left),
      (f ≫ g).left y = g.left (f.left y) := by
    intro A B C f g y
    rw [Over.comp_left, Scheme.Hom.comp_apply]
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · have := (H T (𝟙 T)).1
      rw [k0, Category.id_comp] at this
      exact this
    · intro T' t c
      rintro _ ⟨y, rfl⟩
      change (lift (t ≫ h) c).left y ∈ Ws
      by_cases hy : (lift (t ≫ h) c).left y ∈ m1.left ⁻¹' U ∩ m2.left ⁻¹' U
      · right
        let V : T'.left.Opens :=
          (lift (t ≫ h) c ≫ m1).left ⁻¹ᵁ U ⊓ (lift (t ≫ h) c ≫ m2).left ⁻¹ᵁ U
        have hyV : y ∈ V := by
          refine ⟨?_, ?_⟩
          · change (lift (t ≫ h) c ≫ m1).left y ∈ (U : Set _)
            rw [pt]
            exact hy.1
          · change (lift (t ≫ h) c ≫ m2).left y ∈ (U : Set _)
            rw [pt]
            exact hy.2
        have hVw : ∀ w, V.ι w ∈ V := by
          intro w
          have hw : V.ι w ∈ Set.range V.ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at hw
        let T'' : Over S := Over.mk (V.ι ≫ T'.hom)
        let j : T'' ⟶ T' := Over.homMk V.ι rfl
        have eq1 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ fst G G) = j ≫ (lift (t ≫ h) c ≫ m1) := by
          rw [k1, comp_lift, Category.assoc]
        have eq2 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ snd G G) = j ≫ (lift (t ≫ h) c ≫ m2) := by
          rw [k2, comp_lift, Category.assoc]
        have eq3 : lift ((j ≫ t) ≫ h) ((j ≫ c ≫ fst G G) * (j ≫ c ≫ snd G G)⁻¹)
            = j ≫ (lift (t ≫ h) c ≫ m3) := by
          rw [k3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
        have hA := (H T'' (j ≫ t)).2 (j ≫ c ≫ fst G G) (j ≫ c ≫ snd G G)
          (by
            rw [eq1]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).1)
          (by
            rw [eq2]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).2)
        obtain ⟨y', hy'⟩ : y ∈ Set.range V.ι := by
          rw [Scheme.Opens.range_ι]
          exact hyV
        have := hA ⟨y', rfl⟩
        rw [eq3, pt] at this
        change m3.left ((lift (t ≫ h) c).left y) ∈ (U : Set _)
        rw [← pt, ← hy']
        exact this
      · left
        exact hy
  · rintro ⟨H1, H2⟩ T' t
    refine ⟨?_, ?_⟩
    · rw [k0]
      rintro _ ⟨y, rfl⟩
      rw [pt]
      exact H1 ⟨t.left y, rfl⟩
    · intro a b ha hb
      rintro _ ⟨y, rfl⟩
      have hz : (lift (t ≫ h) (lift a b)).left y ∈ Ws := H2 T' t (lift a b) ⟨y, rfl⟩
      have e3 := k3 T' (t ≫ h) (lift a b)
      rw [lift_fst, lift_snd] at e3
      rw [← e3, pt]
      rcases hz with hz | hz
      · exfalso
        apply hz
        refine ⟨?_, ?_⟩
        · change (m1.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k1, lift_fst]
          exact ha ⟨y, rfl⟩
        · change (m2.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k2, lift_snd]
          exact hb ⟨y, rfl⟩
      · exact hz
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsNoetherianBaseLink
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

namespace UpperTheory.BaseNoeth

private theorem exists_ratHom {A : Type} [CommRing A] (h : ∀ k : ℕ, k ≠ 0 → IsUnit (k : A)) :
    Nonempty (ℚ →+* A) := by
  have hu : ∀ y : nonZeroDivisors ℤ, IsUnit (Int.castRingHom A y) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hn := h y.natAbs (Int.natAbs_ne_zero.mpr hy0)
    rcases Int.natAbs_eq y with e | e
    · have : Int.castRingHom A y = (y.natAbs : A) := by
        conv_lhs => rw [e]
        simp
      simpa [this] using hn
    · have : Int.castRingHom A y = -(y.natAbs : A) := by
        conv_lhs => rw [e]
        simp
      simpa [this] using hn.neg
  exact ⟨IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) hu⟩

variable {p : ℕ} [Fact p.Prime]

private theorem units_of {A : Type} [CommRing A] (hp : IsUnit ((p : ℕ) : A))
    (hu : ∀ k : ℕ, k.Coprime p → IsUnit (k : A)) (k : ℕ) (hk : k ≠ 0) : IsUnit (k : A) := by
  have pp : p.Prime := Fact.out
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p pp.ne_one
  have hcop : m.Coprime p := ((Nat.Prime.coprime_iff_not_dvd pp).mpr hm).symm
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (hp.pow e).mul (hu m hcop)

private theorem core (D : Datum p) {A : Type} [CommRing A] (hp : IsUnit ((p : ℕ) : A))
    (hu : ∀ k : ℕ, k.Coprime p → IsUnit (k : A)) (ρ : A) (hρ : ρ ^ 2 - D.tr * ρ + D.nm = 0)
    (t : Fin D.a → (𝓞 D.F →+* A)) (hω : ∀ i, t i D.ω = ρ)
    (hc : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) :
    ∃ (R₁ : Subring A) (_ : IsNoetherianRing R₁) (b₁ : Base D R₁), IsUnit ((p : ℕ) : R₁) ∧
      ((b₁.ρ : R₁) : A) = ρ ∧ ∀ i c, ((b₁.t i c : R₁) : A) = t i c := by
  classical
  obtain ⟨f⟩ := exists_ratHom (units_of hp hu)
  letI : Algebra ℚ A := f.toAlgebra

  obtain ⟨G, hG⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 D.F)).FG)

  have hw : ∀ ij : Fin D.a × Fin D.a, ∃ c : 𝓞 D.F →₀ A, ij.1 ≠ ij.2 →
      (c.sum fun x a => a * (t ij.1 x - t ij.2 x)) = 1 := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨0, fun h => absurd hij h⟩
    · have h1 : (1 : A) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [hc i j hij]; trivial
      obtain ⟨c, hc'⟩ := (Finsupp.mem_ideal_span_range_iff_exists_finsupp).mp h1
      exact ⟨c, fun _ => hc'⟩
  choose w hw using hw

  let T : Finset A := insert ρ ((Finset.univ.biUnion fun i : Fin D.a => G.image (t i)) ∪
    (Finset.univ.biUnion fun ij : Fin D.a × Fin D.a => (w ij).support.image (w ij)))
  let B : Subalgebra ℚ A := Algebra.adjoin ℚ (T : Set A)
  have hfg : B.FG := Subalgebra.fg_adjoin_finset T
  haveI : Algebra.FiniteType ℚ B := (Subalgebra.fg_iff_finiteType B).mp hfg
  haveI hN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℚ B
  have hTB : ∀ a ∈ T, a ∈ B := fun a ha => Algebra.subset_adjoin (by exact_mod_cast ha)
  have hρB : ρ ∈ B := hTB _ (Finset.mem_insert_self _ _)
  have htB : ∀ i c, t i c ∈ B := by
    intro i c
    have hcG : c ∈ Submodule.span ℤ (G : Set (𝓞 D.F)) := by rw [hG]; trivial
    induction hcG using Submodule.span_induction with
    | mem x hx =>
      refine hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (by exact_mod_cast hx)⟩
    | zero => simpa using B.zero_mem
    | add x y _ _ hx hy => simpa using B.add_mem hx hy
    | smul a x _ hx =>
      have : t i (a • x) = (a : A) * t i x := by simp
      rw [this]
      exact B.mul_mem (by simpa using B.toSubring.intCast_mem a) hx
  have hwB : ∀ ij x, w ij x ∈ B := by
    intro ij x
    by_cases hx : x ∈ (w ij).support
    · refine hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
      exact Finset.mem_biUnion.mpr ⟨ij, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩
    · rw [Finsupp.notMem_support_iff.mp hx]; exact B.zero_mem
  have hun : ∀ k : ℕ, k ≠ 0 → IsUnit ((k : ℕ) : B.toSubring) := by
    intro k hk
    have h := (IsUnit.mk0 (k : ℚ) (by exact_mod_cast hk)).map (algebraMap ℚ B)
    simpa using h
  let t₁ : Fin D.a → (𝓞 D.F →+* B.toSubring) := fun i => (t i).codRestrict B.toSubring (htB i)
  let ρ₁ : B.toSubring := ⟨ρ, hρB⟩
  have pp : p.Prime := Fact.out
  have hpu : IsUnit ((p : ℕ) : B.toSubring) := hun p pp.ne_zero
  refine ⟨B.toSubring, hN, ?_⟩
  refine ⟨⟨fun k hk => hun k ?_, ρ₁, ?_, t₁, ?_, ?_, ?_⟩, hpu, rfl, fun i c => rfl⟩
  · rintro rfl
    have := (Nat.coprime_zero_left p).mp hk
    exact pp.ne_one this
  · apply Subtype.ext
    simpa [ρ₁] using hρ
  · intro i
    exact Subtype.ext (hω i)
  · intro i j hij
    rw [Ideal.eq_top_iff_one]
    have key : ((((w (i, j)).support.sum fun x =>
        (⟨w (i, j) x, hwB _ x⟩ : B.toSubring) * (t₁ i x - t₁ j x)) : B.toSubring)) = 1 := by
      apply Subtype.ext
      have := hw (i, j) hij
      rw [Finsupp.sum] at this
      simpa [t₁] using this
    rw [← key]
    exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)
  · intro i j _ k _ _ β
    exfalso
    have h1 := hpu.map β
    simp at h1

private theorem gam_toSpecΓ {S : Scheme.{0}} {R₁ : Type} [CommRing R₁] (f : R₁ →+* Γ(S, ⊤)) (a : R₁) :
    gam (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) : S ⟶ Sp R₁) a = f a := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv ≫
      (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)).appTop = CommRingCat.ofHom f := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Scheme.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun g => CommRingCat.Hom.hom g a) h

end UpperTheory.BaseNoeth

open UpperTheory.BaseNoeth in
theorem UpperTheory.exists_noetherian_base_link :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0}) (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsNoetherianRing R₁) (b₁ : Base D R₁) (s₁ : S ⟶ Sp R₁), IsUnit ((p : ℕ) : R₁) ∧ Link b b₁ s s₁ := by
  intro p _ D R _ b S s hp
  let g : R →+* Γ(S, ⊤) := gam s
  obtain ⟨R₁, hN, b₁, hpu, h1, h2⟩ := core D (A := Γ(S, ⊤)) hp
    (fun k hk => by simpa using (b.unit k hk).map g) (g b.ρ)
    (by simpa using congrArg g b.ρ_root)
    (fun i => g.comp (b.t i)) (fun i => by simp [b.t_ω])
    (fun i j hij => by
      have h := congrArg (Ideal.map g) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
      simpa [Function.comp_def] using h)
  refine ⟨R₁, inferInstance, hN, b₁, S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom R₁.subtype), hpu, ?_, ?_⟩
  · rw [gam_toSpecΓ]
    exact h1.symm
  · intro i c
    rw [gam_toSpecΓ]
    exact (h2 i c).symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionOfEtaleClopenGeomPointUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

theorem UpperTheory.exists_section_of_etale_clopen_geomPoint_unique :
    ∀ (S : Scheme.{0}) (Y : Over S), IsFinite Y.hom → Etale Y.hom → ∀ (W : Set Y.left), IsOpen W → IsClosed W → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ y : Sp k ⟶ Y.left, y ≫ Y.hom = x ∧ Set.range y.base ⊆ W) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y₁ y₂ : Sp k ⟶ Y.left), y₁ ≫ Y.hom = y₂ ≫ Y.hom → Set.range y₁.base ⊆ W → Set.range y₂.base ⊆ W → y₁ = y₂) → ∃ σ : S ⟶ Y.left, σ ≫ Y.hom = 𝟙 S ∧ Set.range σ.base ⊆ W := by
  intro S Y hfin het W hWo hWc hex huniq
  let U : Y.left.Opens := ⟨W, hWo⟩
  have hrange : Set.range U.ι.base = W := U.range_ι
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [hrange]; exact hWc)
  haveI : IsFinite (U.ι ≫ Y.hom) := inferInstance
  haveI : Etale (U.ι ≫ Y.hom) := inferInstance
  have hiso : IsIso (U.ι ≫ Y.hom) := by
    rw [GlobalTheory.FinEt.isIso_iff_bijective_algClosed]
    intro k _ _
    constructor
    · intro z₁ z₂ h
      apply (cancel_mono U.ι).mp
      apply huniq k (z₁ ≫ U.ι) (z₂ ≫ U.ι)
      · simpa [Category.assoc] using h
      · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange.symm]
        exact Set.image_subset_range _ _
      · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange.symm]
        exact Set.image_subset_range _ _
    · intro x
      obtain ⟨y, hy, hyW⟩ := hex k x
      refine ⟨IsOpenImmersion.lift U.ι y (by rw [hrange]; exact hyW), ?_⟩
      simp only
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hy]
  refine ⟨inv (U.ι ≫ Y.hom) ≫ U.ι, ?_, ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hrange]
    exact Set.image_subset_range _ _
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LevDefs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace UpperTheory.Lev

variable {G : GDatum}

def MN (n : ℕ) (a b : G.La) : Prop := ∃ c : G.La, a = b + n • c

structure IsLSim (n : ℕ) (f : G.La → G.La) (ν : ℤ) : Prop where
  add : ∀ x y, MN n (f (x + y)) (f x + f y)
  lin : ∀ (c : G.O) x, MN n (f (c • x)) (c • f x)
  inj : ∀ x, MN n (f x) 0 → MN n x 0
  surj : ∀ y, ∃ x, MN n (f x) y
  cop : IsCoprime ν (n : ℤ)
  isom : ∀ x y, (n : ℤ) ∣ 2 * G.EF (f x) (f y) - ν * (2 * G.EF x y)

structure GSim (G : GDatum) where
  f : ℕ → G.La → G.La
  ν : ℕ → ℤ
  sim : ∀ n, 0 < n → IsLSim n (f n) (ν n)
  tower : ∀ n m : ℕ, 0 < n → 0 < m → ∀ x, MN n (f (n * m) x) (f n x)
  νtower : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n

variable {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}}

end UpperTheory.Lev
end
end

