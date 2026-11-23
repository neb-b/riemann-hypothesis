module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSchemeLatticeTorsionHomPrimitiveRoot
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsRootParam


open Polynomial in
abbrev CycRing (n : ℕ) : Type := AdjoinRoot (cyclotomic n ℤ)

open Polynomial in
theorem root_pow (n : ℕ) : AdjoinRoot.root (cyclotomic n ℤ) ^ n = 1 := by
  have h := (AdjoinRoot.mk_eq_zero (f := cyclotomic n ℤ)).mpr (cyclotomic.dvd_X_pow_sub_one n ℤ)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact sub_eq_zero.mp h


open Polynomial in
def cycUnit {n : ℕ} (hn : 0 < n) : (CycRing n)ˣ :=
  Units.ofPowEqOne (AdjoinRoot.root (cyclotomic n ℤ)) n (root_pow n) hn.ne'

open Polynomial in
theorem cycUnit_val {n : ℕ} (hn : 0 < n) : (cycUnit hn : CycRing n) = AdjoinRoot.root (cyclotomic n ℤ) := rfl

theorem cycUnit_pow {n : ℕ} (hn : 0 < n) : cycUnit hn ^ n = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, cycUnit_val, root_pow, Units.val_one]

open Polynomial in
theorem isPrimitiveRoot_map {n : ℕ} (hn : 0 < n) {K : Type} [Field K] (hK : (n : K) ≠ 0) (β : CycRing n →+* K) :
    IsPrimitiveRoot (Units.map β.toMonoidHom (cycUnit hn)) n := by
  have : NeZero (n : K) := ⟨hK⟩
  have hr : (cyclotomic n K).IsRoot (β (AdjoinRoot.root (cyclotomic n ℤ))) := by
    have h := congrArg β (AdjoinRoot.eval₂_root (cyclotomic n ℤ))
    rw [Polynomial.hom_eval₂, map_zero, RingHom.ext_int (β.comp (AdjoinRoot.of _)) (Int.castRingHom K),
      ← Polynomial.eval_map, Polynomial.map_cyclotomic_int] at h
    exact h
  rw [← IsPrimitiveRoot.coe_units_iff]
  have hv : ((Units.map β.toMonoidHom (cycUnit hn) : Kˣ) : K) = β (AdjoinRoot.root (cyclotomic n ℤ)) := by
    simp [cycUnit_val]
  rw [hv]
  exact (Polynomial.isRoot_cyclotomic_iff).mp hr

open Polynomial in
theorem exists_map_eq {n : ℕ} (hn : 0 < n) {K : Type} [Field K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) :
    ∃ β : CycRing n →+* K, Units.map β.toMonoidHom (cycUnit hn) = ζ := by
  have h : (cyclotomic n ℤ).eval₂ (Int.castRingHom K) (ζ : K) = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int]
    exact (IsPrimitiveRoot.coe_units_iff.mpr hζ).isRoot_cyclotomic hn
  refine ⟨AdjoinRoot.lift (Int.castRingHom K) (ζ : K) h, Units.ext ?_⟩
  simp [cycUnit_val]

open Polynomial in
theorem isFinite_cyc (n : ℕ) : IsFinite (spMap (algebraMap ℤ (CycRing n))) := by
  have hf : Module.Finite ℤ (CycRing n) := (AdjoinRoot.powerBasis' (cyclotomic.monic n ℤ)).finite
  dsimp only [spMap]
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr hf

theorem isUnit_natCast_of_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {n : ℕ} (h : IsUnit (n : Γ(Y, ⊤))) :
    IsUnit (n : Γ(X, ⊤)) := by
  have h' := h.map f.appTop.hom
  rwa [map_natCast] at h'

theorem natCast_ne_zero_of_isUnit {K : Type} [Field K] {n : ℕ} (h : IsUnit (n : Γ(Sp K, ⊤))) : (n : K) ≠ 0 := by
  have h' := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast] at h'
  exact h'.ne_zero

theorem isUnit_natCast_basicOpen (S : Scheme.{0}) (n : ℕ) :
    IsUnit (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) := by
  have h : IsUnit (n : Γ(S, S.basicOpen (n : Γ(S, ⊤)))) := by
    have h0 := S.toRingedSpace.isUnit_res_basicOpen (n : Γ(S, ⊤))
    rwa [map_natCast] at h0
  have e : (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) =
      (S.basicOpen (n : Γ(S, ⊤))).topIso.inv.hom (n : Γ(S, S.basicOpen (n : Γ(S, ⊤)))) :=
    (map_natCast _ n).symm
  rw [e]
  exact h.map _

theorem range_subset_basicOpen {S : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ} (hK : (n : K) ≠ 0) :
    Set.range x ⊆ Set.range (S.basicOpen (n : Γ(S, ⊤))).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hK' : IsUnit (n : Γ(Sp K, ⊤)) := by
    have h1 := (Ne.isUnit hK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [map_natCast] at h1
  have hu : IsUnit (x.app ⊤ (n : Γ(S, ⊤))) := by
    rw [map_natCast]
    have h1 := hK'.map ((Sp K).presheaf.map (homOfLE (le_top : x ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
    rwa [map_natCast] at h1
  have h := Scheme.preimage_basicOpen x (n : Γ(S, ⊤))
  rw [(Sp K).basicOpen_of_isUnit hu] at h
  show y ∈ x ⁻¹ᵁ S.basicOpen (n : Γ(S, ⊤))
  rw [h]
  trivial

theorem unitOn_inj {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := by
  intro a b h
  apply Units.ext
  have h1 := congrArg (fun u : Γ(Sp k, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (u : Γ(Sp k, ⊤))) h
  simpa [unitOn] using h1

private theorem exists_lift_of_range_subset_closure_image_finite {W U S : Scheme.{0}} (q : W ⟶ U) [IsFinite q] (f : U ⟶ S) [IsOpenImmersion f]
    {C : Set W} (hC : IsClosed C) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ U)
    (hx : Set.range (x ≫ f) ⊆ closure ((q ≫ f) '' C)) : ∃ w : Sp K ⟶ W, w ≫ q = x ∧ Set.range w ⊆ C := by
  let pt : Sp K := IsLocalRing.closedPoint K
  obtain ⟨c, hcC, hc⟩ : ∃ c ∈ C, q c = x pt := by
    have h1 : (x ≫ f) pt ∈ closure ((q ≫ f) '' C) := hx ⟨pt, rfl⟩
    have e : (q ≫ f) '' C = f '' (q '' C) := by
      ext y
      simp
    rw [e] at h1
    have h2 : x pt ∈ closure (q '' C) := by
      rw [f.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
      simpa [Scheme.Hom.comp_apply] using h1
    rw [(q.isClosedMap C hC).closure_eq] at h2
    exact h2
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback c pt hc
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q x)
  have hS : IsClosed ((pullback.fst q x) ⁻¹' C) := hC.preimage (pullback.fst q x).continuous
  obtain ⟨z', hz'C, hz'⟩ := hS.exists_closed_singleton ⟨z, by simpa [Set.mem_preimage, hz1] using hcC⟩
  refine ⟨pointOfClosedPoint (pullback.snd q x) z' hz' ≫ pullback.fst q x, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  · rintro _ ⟨a, rfl⟩
    simpa [Scheme.Hom.comp_apply] using hz'C

private theorem lift_lemma' {S : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ} (hK : (n : K) ≠ 0) :
    ∃ xU : Sp K ⟶ (S.basicOpen (n : Γ(S, ⊤)) : Scheme.{0}), xU ≫ (S.basicOpen (n : Γ(S, ⊤))).ι = x :=
  ⟨_, IsOpenImmersion.lift_fac _ x (range_subset_basicOpen x hK)⟩

set_option maxHeartbeats 1000000 in
private theorem main_lemma_3 : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  intro S G _ _ n La _ _ _ hG hn
  have hU : IsUnit (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) := isUnit_natCast_basicOpen S n
  have hGU : IsAbelianScheme ((Over.pullback (S.basicOpen (n : Γ(S, ⊤))).ι).obj G) :=
    Out.TLinPf.isAb_pullback _ G hG
  have hP := isGrpPullback_pullback G (S.basicOpen (n : Γ(S, ⊤))).ι
  obtain ⟨Z₀, et₀, hfin, -, hadd₀, hpow₀, huniv₀⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom _ ((Over.pullback (S.basicOpen (n : Γ(S, ⊤))).ι).obj G) n La hGU hU
  have hcyc := isFinite_cyc n
  have hp1 : IsFinite (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n)))) :=
    by infer_instance
  let ZU : Over (S.basicOpen (n : Γ(S, ⊤)) : Scheme.{0}) :=
    Over.mk (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n))) ≫ Z₀.hom)
  let r : ZU ⟶ Z₀ := Over.homMk (pullback.fst _ _)
  have hWu : IsUnit (n : Γ(ZU.left, ⊤)) := isUnit_natCast_of_hom ZU.hom hU
  refine ⟨Over.mk (ZU.hom ≫ (S.basicOpen (n : Γ(S, ⊤))).ι), fun a => GlobalTheory.ObjPull.pushEquiv hP ZU (r ≫ et₀ a),
    Units.map (GlobalTheory.LevCover.fnOn (pullback.snd (specZIsTerminal.from Z₀.left)
      (spMap (algebraMap ℤ (CycRing n))))).toMonoidHom (cycUnit hn), hWu, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a'
    dsimp only
    rw [hadd₀, comp_mul, map_mul]
  · intro a
    dsimp only
    rw [← map_pow, ← comp_pow, hpow₀]
    simp
  · rw [← map_pow, cycUnit_pow, map_one]
  · intro K _ h ζ hζ
    obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (h ≫ pullback.snd _ _)
    rw [GlobalTheory.LevCover.map_fnOn _ h β hβ] at hζ
    rw [← unitOn_inj hζ]
    exact isPrimitiveRoot_map hn (natCast_ne_zero_of_isUnit (isUnit_natCast_of_hom h hWu)) β
  · intro K _ x et' ζ hK hadd hpow hζ
    obtain ⟨xU, hxU⟩ := lift_lemma' (S := S) (K := K) (n := n) x hK
    let e : Over.mk ((Over.mk xU).hom ≫ (S.basicOpen (n : Γ(S, ⊤))).ι) ⟶ Over.mk x :=
      Over.homMk (𝟙 _) (by simpa using hxU.symm)
    obtain ⟨h₀, hh₀, -⟩ := huniv₀ (Over.mk xU) (fun a => (GlobalTheory.ObjPull.pushEquiv hP _).symm (e ≫ et' a))
      (fun a a' => by rw [hadd, comp_mul, map_mul])
      (fun a => by rw [← map_pow, ← comp_pow, hpow]; simp)
    obtain ⟨β, hβ⟩ := exists_map_eq hn hζ
    let hW : Sp K ⟶ ZU.left := pullback.lift h₀.left (spMap β) (specZIsTerminal.hom_ext _ _)
    have hW1 : hW ≫ pullback.fst _ _ = h₀.left := pullback.lift_fst _ _ _
    have hW2 : hW ≫ pullback.snd _ _ = spMap β := pullback.lift_snd _ _ _
    refine ⟨Over.homMk hW ?_, ?_, ?_⟩
    · show hW ≫ (pullback.fst _ _ ≫ Z₀.hom) ≫ _ = x
      rw [← Category.assoc, ← Category.assoc, hW1, Over.w h₀]
      exact hxU
    · intro a
      apply Over.OverMorphism.ext
      have h1 := GlobalTheory.ObjPull.pushEquiv_symm_left hP _ (e ≫ et' a)
      rw [← hh₀ a] at h1
      have h2 : (e ≫ et' a).left = (et' a).left := by simp [e]
      show hW ≫ (GlobalTheory.ObjPull.pushEquiv hP ZU (r ≫ et₀ a)).left = (et' a).left
      rw [GlobalTheory.ObjPull.pushEquiv_left, ← h2, ← h1, Over.comp_left, Over.comp_left, ← hW1]
      simp only [Category.assoc]
      rfl
    · show Units.map hW.appTop.hom.toMonoidHom _ = _
      rw [GlobalTheory.LevCover.map_fnOn _ hW β hW2, hβ]
  · intro C hC K _ _ x hK hcl
    obtain ⟨xU, hxU⟩ := lift_lemma' (S := S) (K := K) (n := n) x hK
    have : IsFinite Z₀.hom := hfin
    have : IsFinite ZU.hom := by
      show IsFinite (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n))) ≫ Z₀.hom)
      infer_instance
    obtain ⟨w, hw, hwC⟩ := exists_lift_of_range_subset_closure_image_finite ZU.hom (S.basicOpen (n : Γ(S, ⊤))).ι hC xU
      (by rw [hxU]; exact hcl)
    refine ⟨Over.homMk w ?_, hwC⟩
    show w ≫ ZU.hom ≫ _ = x
    rw [← Category.assoc, hw, hxU]

end GlobalTheory.TorsRootParam

namespace GlobalTheory


open TorsRootParam in
theorem exists_latticeTorsionHom_primitiveRoot_param : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  exact main_lemma_3

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionTheta

theorem ptMap_comp_ptMap {O : Type} [CommRing O] {A B C : Type} [CommRing A] [Algebra O A]
    [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] (φ : A →ₐ[O] B) (ψ : B →ₐ[O] C) :
    ptMap ψ ≫ ptMap φ = ptMap (ψ.comp φ) := by
  unfold ptMap
  ext1
  simp only [Over.comp_left, Over.homMk_left]
  rw [← Spec.map_comp]
  rfl

theorem tmul_one_ne_zero {O : Type} [CommRing O] [IsLocalRing O] {H : Type} [CommRing H]
    [Algebra O H] [Module.Finite O H] [Module.Free O H] (l : H)
    (hl : l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H))
    (K : Type) [Field K] [Algebra O K] : l ⊗ₜ[O] (1 : K) ≠ 0 := by
  classical
  intro h0
  let b := Module.Free.chooseBasis O H
  have hex : ∃ i, IsUnit (b.repr l i) := by
    by_contra hne
    push Not at hne
    apply hl
    rw [← b.sum_repr l]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i)))
  obtain ⟨i, hi⟩ := hex
  have h1 := congrArg (fun x => TensorProduct.lid O K (TensorProduct.map (b.coord i) LinearMap.id x)) h0
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_zero,
    Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, _root_.mul_one] at h1
  exact (hi.map (algebraMap O K)).ne_zero h1

private lemma ptMap_comp_comp {O : Type} [CommRing O] {A B C : Type} [CommRing A] [Algebra O A]
    [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] {X : Over (Sp O)} (φ : A →ₐ[O] B)
    (ψ : B →ₐ[O] C) (f : specO O A ⟶ X) : ptMap (ψ.comp φ) ≫ f = ptMap ψ ≫ ptMap φ ≫ f := by
  rw [← ptMap_comp_ptMap, Category.assoc]

theorem exists_theta : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G), y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O) (l : H) (c : O), ptMap ε ≫ y = 1 → (∀ h, ε h = 0 → h * l = 0) → ε l = c → l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) → ∃ Θ : H ⊗[O] H, (∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0 := by
  intro O _ _ G _ _ n H _ _ _ _ y hy hU ε l c hε hann hεl hlm
  have tors : ∀ (S : Type) [CommRing S] [Algebra O S] (f : specO O S ⟶ specO O H), (f ≫ y) ^ n = 1 := by
    intro S _ _ f
    rw [← comp_pow, hy, comp_one]
  have uniq : ∀ (S : Type) [CommRing S] [Algebra O S] (φ₁ φ₂ : H →ₐ[O] S),
      ptMap φ₁ ≫ y = ptMap φ₂ ≫ y → φ₁ = φ₂ := by
    intro S _ _ φ₁ φ₂ h
    obtain ⟨φ, -, hφ⟩ := hU S (ptMap φ₂ ≫ y) (tors S _)
    exact (hφ φ₁ h).trans (hφ φ₂ rfl).symm
  let iL : H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.includeLeft
  let iR : H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.includeRight
  obtain ⟨d, hd, -⟩ := hU (H ⊗[O] H) (ptMap iL ≫ y * (ptMap iR ≫ y)⁻¹)
    (by rw [mul_pow, inv_pow, tors, tors, inv_one, _root_.mul_one])
  obtain ⟨m, hm, -⟩ := hU (H ⊗[O] H) (ptMap iL ≫ y * ptMap iR ≫ y)
    (by rw [mul_pow, tors, tors, _root_.mul_one])
  let eH : H →ₐ[O] H := (Algebra.ofId O H).comp ε
  have heH : ptMap eH ≫ y = 1 := by
    rw [ptMap_comp_comp, hε, comp_one]

  have hmd : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp d = eH := by
    apply uniq
    rw [ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, heH]
    have h1 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iL = AlgHom.id O H := by
      ext x; simp [iL]
    have h2 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iR = AlgHom.id O H := by
      ext x; simp [iR]
    rw [h1, h2, mul_inv_cancel]
  refine ⟨d l, ?_, ?_, ?_⟩
  ·
    have hl' : ∀ a : H, a * l = algebraMap O H (ε a) * l := by
      intro a
      have := hann (a - algebraMap O H (ε a)) (by simp)
      rwa [sub_mul, sub_eq_zero] at this
    let e2 : H ⊗[O] H →ₐ[O] H := Algebra.TensorProduct.lift eH (AlgHom.id O H) (fun _ _ => Commute.all _ _)
    have hkey : ∀ x : H ⊗[O] H, x * (l ⊗ₜ[O] (1 : H)) = (l ⊗ₜ[O] (1 : H)) * ((1 : H) ⊗ₜ[O] e2 x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [e2, eH, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
          _root_.one_mul, hl' a, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply]
        rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
      | add x x' hx hx' => rw [add_mul, hx, hx', map_add (f := _), TensorProduct.tmul_add, mul_add]
    let ψ : H ⊗[O] H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.lift d iR (fun _ _ => Commute.all _ _)
    have hψL : ψ.comp iL = d := by ext x; simp [ψ, iL]
    have hψR : ψ.comp iR = iR := by ext x; simp [ψ, iR]
    have he2L : e2.comp iL = eH := by ext x; simp [e2, iL]
    have he2R : e2.comp iR = AlgHom.id O H := by ext x; simp [e2, iR]
    have he2m : e2.comp m = AlgHom.id O H := by
      apply uniq
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, he2L, he2R, heH, _root_.one_mul]
    have hψm : ψ.comp m = iL := by
      apply uniq
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hψL, hψR, hd,
        inv_mul_cancel_right]
    intro h
    have a1 : h ⊗ₜ[O] (1 : H) = ψ (m h) := by
      rw [← AlgHom.comp_apply, hψm]; rfl
    have a2 : d l = ψ (l ⊗ₜ[O] (1 : H)) := by simp [ψ]
    have a3 : (1 : H) ⊗ₜ[O] h = ψ ((1 : H) ⊗ₜ[O] h) := by simp [ψ, iR]
    have a4 : e2 (m h) = h := by rw [← AlgHom.comp_apply, he2m]; rfl
    rw [a1, a2, ← map_mul, hkey, a4, map_mul, ← a3, ← a2, _root_.mul_comm]
  · have := DFunLike.congr_fun hmd l
    rw [AlgHom.comp_apply] at this
    rw [this]
    simp [eH, hεl]
  · intro K _ _ _ _ ga
    let jL : H →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.includeLeft
    let jR : K →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.includeRight
    let κ : H ⊗[O] H →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.map (AlgHom.id O H) ga
    let Sg : H →ₐ[O] H ⊗[O] K := κ.comp m
    let MainNotions : H ⊗[O] K →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.lift Sg jR (fun _ _ => Commute.all _ _)
    have hκL : κ.comp iL = jL := by ext x; simp [κ, iL, jL]
    have hκR : κ.comp iR = jR.comp ga := by ext x; simp [κ, iR, jR]
    have hSL : (MainNotions.comp κ).comp iL = Sg := by ext x; simp [MainNotions, κ, iL]
    have hSR : (MainNotions.comp κ).comp iR = jR.comp ga := by ext x; simp [MainNotions, κ, iR, jR]
    have hSg : ptMap Sg ≫ y = ptMap jL ≫ y * ptMap (jR.comp ga) ≫ y := by
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hκL, hκR]
    have hback : (MainNotions.comp κ).comp d = jL := by
      apply uniq
      rw [ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, hSL, hSR, hSg,
        mul_inv_cancel_right]
    intro h0
    apply tmul_one_ne_zero l hlm K
    have := DFunLike.congr_fun hback l
    simp only [AlgHom.comp_apply] at this
    change MainNotions (κ (d l)) = l ⊗ₜ[O] (1 : K) at this
    rw [← this]
    change MainNotions (Algebra.TensorProduct.map (AlgHom.id O H) ga (d l)) = 0
    rw [h0, map_zero]

end GlobalTheory.TorsionTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImportsBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnitBallVal

theorem dvd_of_norm_le {C O : Type} [NormedField C] [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C))
    (hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x) {a b : O}
    (h : ‖algebraMap O C b‖ ≤ ‖algebraMap O C a‖) : a ∣ b := by
  by_cases ha : algebraMap O C a = 0
  · have hb : algebraMap O C b = 0 := by
      rw [ha, norm_zero] at h
      exact norm_le_zero_iff.mp h
    have hb0 : b = 0 := hinj (by rw [hb, map_zero])
    rw [hb0]
    exact dvd_zero a
  · obtain ⟨y, hy⟩ := hsurj (algebraMap O C b / algebraMap O C a) (by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr ha)).mpr h)
    refine ⟨y, hinj ?_⟩
    rw [map_mul, hy]
    field_simp

theorem main : ∀ (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CommRing O] [Algebra O C], IsUnitBall O C → ∃ (_ : IsDomain O), ValuationRing O ∧ Ring.DimensionLEOne O ∧ IsFractionRing O C := by
  intro C O _ _ _ _ hO
  obtain ⟨hinj, hball⟩ := hO
  have hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x := fun x hx => (hball x).mpr hx
  have hle : ∀ y : O, ‖algebraMap O C y‖ ≤ 1 := fun y => (hball _).mp ⟨y, rfl⟩
  have hdom : IsDomain O := hinj.isDomain (algebraMap O C)

  have hunit : ∀ y : O, ‖algebraMap O C y‖ = 1 → IsUnit y := fun y hy =>
    isUnit_of_dvd_one (dvd_of_norm_le hinj hsurj (by rw [map_one, norm_one, hy]))
  refine ⟨hdom, { cond' := fun a b => ?_ }, ⟨fun {P} hP0 hP => ?_⟩, ?_⟩
  · rcases le_total ‖algebraMap O C b‖ ‖algebraMap O C a‖ with h | h
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inl hc.symm⟩
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inr hc.symm⟩
  ·
    obtain ⟨p, hpP, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    have hp' : algebraMap O C p ≠ 0 := fun h0 => hp0 (hinj (by rw [h0, map_zero]))
    have key : ∀ m : O, m ∉ P → IsUnit m := by
      intro m hm
      apply hunit
      refine le_antisymm (hle m) (not_lt.mp fun hlt => hm ?_)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hp') hlt
      obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj (a := p) (b := m ^ n)
        (by rw [map_pow, norm_pow]; exact hn.le)
      refine hP.mem_of_pow_mem n ?_
      rw [hc]
      exact P.mul_mem_right c hpP
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    have hMP : M ≤ P := fun m hm => by
      by_contra hmP
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M hm (key m hmP))
    rwa [le_antisymm hPM hMP]
  · refine (isLocalization_iff (nonZeroDivisors O) C).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact IsUnit.mk0 _ fun h0 => nonZeroDivisors.ne_zero hy (hinj (by rw [h0, map_zero]))
    · intro z
      by_cases hz : ‖z‖ ≤ 1
      · obtain ⟨y, hy⟩ := hsurj z hz
        exact ⟨⟨y, 1⟩, by simp [hy]⟩
      · rw [not_le] at hz
        have hz0 : z ≠ 0 := by
          rintro rfl
          rw [norm_zero] at hz
          linarith
        obtain ⟨y, hy⟩ := hsurj z⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz.le)
        have hy0 : y ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero (by
          rintro rfl
          rw [map_zero] at hy
          exact inv_ne_zero hz0 hy.symm)
        exact ⟨⟨1, ⟨y, hy0⟩⟩, by simp [hy, hz0]⟩
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩

end GlobalTheory.UnitBallVal
end

