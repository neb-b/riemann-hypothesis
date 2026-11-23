module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0034
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0002
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmul
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def pK (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    Submodule (𝓞 K) K :=
  locF 𝔭 (Submodule.map (Algebra.linearMap (𝓞 K) K) (extP K 𝔭 ^ k))

def glSub (A : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {X | Formalism.HermitianLatticesTheory.gmap X A = A}
  one_mem' := autSub_gmap_one A
  mul_mem' := by
    intro a b ha hb
    show Formalism.HermitianLatticesTheory.gmap (a * b) A = A
    rw [autSub_gmap_mul, show Formalism.HermitianLatticesTheory.gmap b A = A from hb, show Formalism.HermitianLatticesTheory.gmap a A = A from ha]
  inv_mem' := by
    intro a ha
    show Formalism.HermitianLatticesTheory.gmap a⁻¹ A = A
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.gmap a A = A from ha]
    rw [← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem mem_glSub {A : Submodule (𝓞 K) V} {X : V ≃ₗ[K] V} :
    X ∈ glSub A ↔ Formalism.HermitianLatticesTheory.gmap X A = A := Iff.rfl

theorem apply_mem {A : Submodule (𝓞 K) V} {X : V ≃ₗ[K] V} (hX : X ∈ glSub A) {x : V} (hx : x ∈ A) :
    X x ∈ A := by
  have hX' : Formalism.HermitianLatticesTheory.gmap X A = A := hX
  rw [← hX']
  exact Submodule.mem_map_of_mem hx

theorem apply_mem_smul {A : Submodule (𝓞 K) V} {X : V ≃ₗ[K] V} (hX : X ∈ glSub A) (I : Ideal (𝓞 K))
    {x : V} (hx : x ∈ I • A) : X x ∈ I • A := by
  have h2 : A.map ((X : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hX
  have h1 : X x ∈ (I • A).map ((X : V →ₗ[K] V).restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hx
  rwa [Submodule.map_smul'', h2] at h1

def sSub (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {X | X ∈ glSub A ∧ ∀ x ∈ A, ∀ y ∈ A, h (X x) (X y) - h x y ∈ pK K 𝔭 k}
  one_mem' := ⟨one_mem _, fun x _ y _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx y hy => ?_⟩
    have := (pK K 𝔭 k).add_mem (ha' _ (apply_mem hb hx) _ (apply_mem hb hy)) (hb' x hx y hy)
    simpa using this
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx y hy => ?_⟩
    have := (pK K 𝔭 k).neg_mem (ha' _ (apply_mem (inv_mem ha) hx) _ (apply_mem (inv_mem ha) hy))
    have e : ∀ z : V, a (a⁻¹ z) = z := fun z => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    simpa [e] using this

def nSub (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Subgroup (V ≃ₗ[K] V) where
  carrier := {X | X ∈ glSub A ∧ ∀ x ∈ A, X x - x ∈ extP K 𝔭 ^ k • A}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    have := (extP K 𝔭 ^ k • A).add_mem (apply_mem_smul ha _ (hb' x hx)) (ha' x hx)
    simpa using this
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have := (extP K 𝔭 ^ k • A).neg_mem (apply_mem_smul (inv_mem ha) _ (ha' x hx))
    have e : ∀ z : V, a⁻¹ (a z) = z := fun z => by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    simpa [e] using this

theorem mem_sSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    {X : V ≃ₗ[K] V} : X ∈ sSub h A 𝔭 k ↔
      X ∈ glSub A ∧ ∀ x ∈ A, ∀ y ∈ A, h (X x) (X y) - h x y ∈ pK K 𝔭 k := Iff.rfl

theorem mem_nSub {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {X : V ≃ₗ[K] V} :
    X ∈ nSub A 𝔭 k ↔ X ∈ glSub A ∧ ∀ x ∈ A, X x - x ∈ extP K 𝔭 ^ k • A := Iff.rfl

def endL (A A' : Submodule (𝓞 K) V) : AddSubgroup (V →ₗ[K] V) where
  carrier := {D | ∀ x ∈ A, D x ∈ A'}
  zero_mem' := fun x _ => by simp
  add_mem' := fun ha hb x hx => A'.add_mem (ha x hx) (hb x hx)
  neg_mem' := fun ha x hx => A'.neg_mem (ha x hx)

def sesqL (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    AddSubgroup (V →ₗ⋆[K] V →ₗ[K] K) where
  carrier := {s | ∀ x ∈ A, ∀ y ∈ A, s x y ∈ pK K 𝔭 k}
  zero_mem' := fun x _ y _ => by simp
  add_mem' := fun ha hb x hx y hy => (pK K 𝔭 k).add_mem (ha x hx y hy) (hb x hx y hy)
  neg_mem' := fun ha x hx y hy => (pK K 𝔭 k).neg_mem (ha x hx y hy)

def hermL (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    AddSubgroup (V →ₗ⋆[K] V →ₗ[K] K) where
  carrier := {s | (∀ x y, star (s x y) = s y x) ∧ ∀ x ∈ A, ∀ y ∈ A, s x y ∈ pK K 𝔭 k}
  zero_mem' := ⟨fun x y => by simp, fun x _ y _ => by simp⟩
  add_mem' := fun ha hb => ⟨fun x y => by simp [ha.1 x y, hb.1 x y],
    fun x hx y hy => (pK K 𝔭 k).add_mem (ha.2 x hx y hy) (hb.2 x hx y hy)⟩
  neg_mem' := fun ha => ⟨fun x y => by simp [ha.1 x y],
    fun x hx y hy => (pK K 𝔭 k).neg_mem (ha.2 x hx y hy)⟩

def nO (𝔭 : Ideal (𝓞 F)) (z : K) : ℕ :=
  ((pK K 𝔭 0).toAddSubgroup.map (AddMonoidHom.mulLeft z)).relIndex (pK K 𝔭 0).toAddSubgroup

end Formalism.HermitianLattices.Ext.L3.D2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocReps
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrB

section One

variable {K V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem finite_between {N D : Submodule (𝓞 K) V} (hN : Submodule.IsFullLattice K N)
    (hD : Submodule.IsLattice K D) (hND : N ≤ D) :
    {Λ : Submodule (𝓞 K) V | N ≤ Λ ∧ Λ ≤ D}.Finite := by
  have h1 := Formalism.HermitianLatticesTheory.finIntermediate V N.toAddSubgroup D.toAddSubgroup hND ?_
  · refine Set.Finite.of_finite_image (f := Submodule.toAddSubgroup) (h1.subset ?_)
      (Submodule.toAddSubgroup_injective.injOn)
    rintro _ ⟨Λ, ⟨h2, h3⟩, rfl⟩
    exact ⟨h2, h3⟩
  · have f1 : Module.Finite (𝓞 K) D := Module.Finite.iff_fg.mpr hD.fg
    have f2 : Module.Finite ℤ D := Module.Finite.trans (𝓞 K) D
    have f3 : AddGroup.FG D.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
    obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hD hN
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact hnx _ q.2

end One

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem finite_fibG (hs : h.IsSymm) (hd : IsTotPosDef h) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {Λ' : Submodule (𝓞 K) V'} (hΛ' : Submodule.IsLattice K Λ') : (fibG S L Λ').Finite := by
  by_cases hne : (fibG S L Λ').Nonempty
  · obtain ⟨Λ, hΛ⟩ := hne
    have hCut := StabilizerLattices.isFullLattice_cut S hΛ.1.1
    rw [hΛ.2.2] at hCut
    have hN : Submodule.IsFullLattice K (S.adjoin Λ') := by
      refine { toIsLattice := (S.isLattice_adjoin_iff Λ').2 hΛ', span_eq_top := ?_ }
      rw [eq_top_iff]
      intro v _
      obtain ⟨c, a, rfl⟩ := S.cover v
      refine add_mem (Submodule.smul_mem _ c (Submodule.subset_span (S.x₀_mem_adjoin Λ'))) ?_
      have hle : Submodule.map S.ι (Submodule.span K (Λ' : Set V')) ≤
          Submodule.span K (S.adjoin Λ' : Set V) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨b, hb, rfl⟩
        exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hb)
      have ha : a ∈ Submodule.span K (Λ' : Set V') := by
        rw [hCut.span_eq_top]
        exact Submodule.mem_top
      exact hle (Submodule.mem_map_of_mem ha)
    have hD := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs
      (UnimodularLocalization.nondegenerate hd)
      Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range _ hN).1
    have key : ∀ Λ ∈ fibG S L Λ', S.adjoin Λ' ≤ Λ ∧ Λ ≤ Formalism.HermitianLatticesTheory.dual h (S.adjoin Λ') := by
      rintro Λ ⟨hg, hx, hc⟩
      have hΛi : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ :=
        ((Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range).2.2 L Λ hL.fg hg.1.fg
          hg.2).2.mp hLi
      have := S.le_dual_of_mem hs hΛi hx
      rwa [hc] at this
    exact (finite_between hN hD.toIsLattice ((key Λ hΛ).1.trans (key Λ hΛ).2)).subset key
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

theorem good_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {B : Submodule (𝓞 K) V}
    (hB : Submodule.IsFullLattice K B) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) (hx : S.x₀ ∈ B) :
    GoodGenusOrbits.Good F S B (S.cut B) := by
  let hc := StabilizerLattices.isFullLattice_cut S hB
  refine ⟨inferInstance, fun 𝔮 h0 => ?_⟩
  have h1 := card_fibG_eq_prod (F := F) (L := B) (Λ' := S.cut B)
    hK hF hs hd S inferInstance hBi inferInstance
  rw [tprod_of_exists_eq_zero ⟨𝔮, by rw [h0]; simp⟩] at h1
  have hfin := finite_fibG hs hd S hB.toIsLattice hBi hc.toIsLattice
  have hmem : B ∈ fibG S B (S.cut B) :=
    ⟨⟨hB, (Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range).1.refl B⟩, hx, rfl⟩
  have : Nat.card (fibG S B (S.cut B)) ≠ 0 := by
    have := hfin.to_subtype
    have : Nonempty (fibG S B (S.cut B)) := ⟨⟨B, hmem⟩⟩
    exact Nat.card_pos.ne'
  exact this (by exact_mod_cast h1)

def scaleSplit (S : VecSplit h h') (c : K) (hc : c ≠ 0) : VecSplit h h' where
  x₀ := c • S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := by
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_ne_zero hc (mul_ne_zero ((map_ne_zero _).mpr hc) S.hx₀)
  isom := S.isom
  orth := fun a => by
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, S.orth, smul_zero]
  cover := fun v => by
    obtain ⟨d, a, rfl⟩ := S.cover v
    exact ⟨d / c, a, by rw [smul_smul, div_mul_cancel₀ _ hc]⟩

theorem fibLoc_scale (S : VecSplit h h') (L : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsPrime) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {t : 𝓞 F} (ht : t ∉ 𝔭)
    (hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0) (T : Submodule (𝓞 K) V') :
    fibLoc (scaleSplit S _ hc) (Formalism.HermitianLatticesTheory.gmap g L) 𝔭 T = fibLoc S L 𝔭 T := by
  unfold fibLoc
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Λ => ?_)
  refine and_congr_right fun hΛ => and_congr ?_ (and_congr_left fun _ => ?_)
  · rw [← LocalizedFibreSets.gmap_locF]
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g' * g, Subgroup.mul_mem _ hg' hg, autSub_gmap_mul _ _ _⟩
    · rintro ⟨g', hg', rfl⟩
      refine ⟨g' * g⁻¹, Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hg), ?_⟩
      rw [← autSub_gmap_mul, mul_assoc, inv_mul_cancel, mul_one]
  · change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ Λ ↔ _
    rw [algebraMap_smul]
    constructor
    · intro hx
      rw [← hΛ]
      exact (LocF.mem_locF_iff h𝔭 Λ _).mpr ⟨t, ht, hx⟩
    · exact fun hx => Λ.smul_mem _ hx

theorem exists_locReps' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ s, IsLocReps S L 𝔭 s := by
  by_cases H : ∀ T, fibLoc S L 𝔭 T = 0
  · exact ⟨∅, fun T hT => absurd hT (Finset.notMem_empty T), fun T _ _ h3 => absurd (H T) h3⟩
  · push Not at H
    obtain ⟨T₁, hT₁⟩ := H
    obtain ⟨g, hg, hx, -⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hT₁
    obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).mp hx
    have hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      intro e
      have e1 : algebraMap (𝓞 F) (𝓞 K) t = 0 := Formalism.HermitianLatticesTheory.genusCovol_hinj (by rw [e, map_zero])
      have e2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [e1, map_zero])
      exact ht (e2 ▸ 𝔭.zero_mem)
    let hB : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
      refine { toIsLattice := LocalizedFibreSets.isLattice_gmap g hL, span_eq_top := ?_ }
      change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
      rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
      exact g.surjective
    have hBi := UnimodularLocalization.isIntegralLat_gmap hg hLi
    have hgood := good_cut (F := F) hK hF hs hd (scaleSplit S _ hc) hB hBi
      (by change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ _
          rw [algebraMap_smul]; exact hx)
    obtain ⟨s, hs1⟩ := GoodGenusOrbits.exists_locReps (L := Formalism.HermitianLatticesTheory.gmap g L)
      hK hF hs hd (scaleSplit S _ hc) inferInstance hBi hgood ⟨𝔭, h𝔭⟩
    refine ⟨s, ?_⟩
    unfold IsLocReps at hs1 ⊢
    simpa only [fibLoc_scale S L h𝔭.isPrime hg ht hc] using hs1

end Formalism.HermitianLattices.Ext.L3.BrB
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLatticeOfFibReps
section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalFactorEquality

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits

theorem finite_vF_ne_zero {n : 𝓞 F} (hn : n ≠ 0) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | vF 𝔭.1 n ≠ 0}.Finite := by
  have hnF : ¬ IsField (𝓞 F) := NumberField.RingOfIntegers.not_isField F
  have hI : Ideal.span {n} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  let f : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    fun 𝔭 => ⟨𝔭.1, 𝔭.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 hnF⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h)
  refine ((Ideal.finite_factors hI).preimage hf.injOn).subset ?_
  intro 𝔭 h𝔭
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at h𝔭 ⊢
  show 𝔭.1 ∣ Ideal.span {n}
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply h𝔭
  unfold vF

  have hset : {e : ℕ | n ∈ 𝔭.1 ^ e} = {0} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro he
      by_contra h0
      exact hmem (Ideal.pow_le_self h0 he)
    · rintro rfl
      simp
  rw [hset, csSup_singleton]

theorem psiP_eq (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (hex : ∃ s, IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ hex.choose, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  unfold psiP
  rw [dite_eq_left hex]

theorem psiP_eq_zero (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (H : ∀ T, fibLoc S L 𝔭 T = 0) : psiP S L 𝔭 = 0 := by
  unfold psiP
  split_ifs with hs
  · simp [H]
  · rfl

theorem card_fibG_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsFullLattice K Λ') (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (H : fibLoc S L 𝔭.1 Λ' = 0) : (Nat.card (fibG S L Λ') : ℝ) = 0 := by
  letI := hL
  letI := hΛ'
  rw [card_fibG_eq_prod (L := L) (Λ' := Λ') hK hF hs hd S inferInstance hLi inferInstance]
  exact tprod_of_exists_eq_zero ⟨𝔭, by rw [H]; simp⟩

theorem isFullLattice_of_fibReps (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s') {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Λ' ∈ s') : Submodule.IsFullLattice K Λ' := by
  obtain ⟨Λ, hΛ, -, rfl⟩ := hs'.1 Λ' hΛ'
  exact StabilizerLattices.isFullLattice_cut S hΛ.1

theorem exists_norm_eq (hF : IsFixF K F) (hs : h.IsSymm) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∃ T, fibLoc S L 𝔭.1 T ≠ 0) :
    ∃ n : 𝓞 F, h S.x₀ S.x₀ = algebraMap F K (n : F) := by

  have hloc : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      h S.x₀ S.x₀ ∈ locF 𝔭.1 (1 : Submodule (𝓞 K) K) := by
    intro 𝔭
    obtain ⟨T, hT⟩ := H 𝔭
    obtain ⟨g, hg, hx, -⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hT
    exact GoodPrimeTerms.isIntegralAt_locF 𝔭.2.isPrime hF (UnimodularLocalization.isIntegralLat_gmap hg hLi) _ hx _ hx
  have h1 : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K)]
    exact Submodule.mem_iInf _ |>.mpr hloc
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp h1

  have hc : conjO K y = y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [BallB.algebraMap_conjO, hy]
    simpa [starRingEnd_apply] using hs.eq S.x₀ S.x₀
  obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF y).mp hc
  exact ⟨t, by rw [← hy, ← ht]; rfl⟩


open Classical in
theorem sum_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsLattice K A) (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h' A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hZ1 : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A = 1) (hZ2 : ∀ 𝔭 ∉ Z, vd h' A 𝔭.1 = 0)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) (hMA : ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A) :
    ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
        (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
      c * ∏ 𝔭 ∈ Z, ((fibLoc S L 𝔭.1 (locF 𝔭.1 M) : ℝ) * lamP h' (locF 𝔭.1 M) 𝔭.1) := by
  have hs2 := S.isSymm hs
  have hd2 := S.isTotPosDef hd
  letI := hL
  have hMi := hM.integral hF hL.toIsLattice hLi
  have hMfull := hM.isFullLattice hL
  have hmass : Formalism.HermitianLatticesTheory.mass h' M = ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
      ((Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℕ) : ℝ)⁻¹ :=
    (Formalism.HermitianLatticesTheory.massBasic K V' h' hs2 (StabilizerLattices.trace_pos hd2) M hMfull).2.1 _
      (isClassReps_filter (L := L) hK hF hs hd S inferInstance hLi hs' hM)
  have hfr : finrank K V' = finrank K V - 1 := by
    have := S.finrank_add_one
    omega
  have hmc := hc V' h' M hs2 hd2 hfr hMfull hMi
  have e1 : ∀ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
      (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
        (∏ 𝔭 ∈ Z, (fibLoc S L 𝔭.1 (locF 𝔭.1 M) : ℝ)) *
          ((Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℕ) : ℝ)⁻¹ := by
    intro Λ' hΛ'
    rw [Finset.mem_filter] at hΛ'
    letI := isFullLattice_of_fibReps S hs' hΛ'.1
    rw [card_fibG_eq_prod (F := F) (L := L) (Λ' := Λ') hK hF hs hd S inferInstance hLi inferInstance,
      div_eq_mul_inv]
    congr 1
    have e2 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        fibLoc S L 𝔭.1 Λ' = fibLoc S L 𝔭.1 (locF 𝔭.1 M) := fun 𝔭 => by
      rw [fibLoc_eq_of_rel hs S L ((sameGenus_iff hK hF M Λ').mp hΛ'.2 𝔭), fibLoc_locF]
    simp only [e2]
    apply tprod_eq_prod
    intro 𝔭 h𝔭
    rw [fibLoc_locF, fibLoc_congr S L (hMA 𝔭 h𝔭), hZ1 𝔭 h𝔭, Nat.cast_one]
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← hmass, hmc, Finset.prod_mul_distrib]
  have e3 : lamG F h' M = ∏ 𝔭 ∈ Z, lamP h' (locF 𝔭.1 M) 𝔭.1 := by
    unfold lamG
    have e4 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        lamP h' M 𝔭.1 = lamP h' (locF 𝔭.1 M) 𝔭.1 := fun 𝔭 =>
      (localFactor_localField hK hF hs2 hd2 hM.1 hMi 𝔭.2).symm
    simp only [e4]
    apply tprod_eq_prod
    intro 𝔭 h𝔭
    rw [← e4 𝔭]
    apply localMassFactor_of_valuation_eq_zero hK hF hs2 hd2 hMfull hMi 𝔭.2
    rw [← vd_locF hK hF hs2 hd2 hM.1 hMi 𝔭.2, hMA 𝔭 h𝔭,
      vd_locF hK hF hs2 hd2 hA hAi 𝔭.2, hZ2 𝔭 h𝔭]
  rw [e3]
  ring

end Formalism.HermitianLattices.Ext.L3.LocalFactorEquality
end
end

