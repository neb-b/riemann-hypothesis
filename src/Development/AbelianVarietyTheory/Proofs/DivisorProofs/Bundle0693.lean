module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentConstPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackCompSpreadToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrpMulSpread

attribute [local instance] Over.cartesianMonoidalCategory

theorem isPullback_pullbackMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (cart : IsPullback F G'.hom G.hom f) :
    IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm)
      (G' ⊗ G').hom (G ⊗ G).hom f := by
  have p : IsPullback (pullback.snd G.hom G.hom) (pullback.fst G.hom G.hom) G.hom G.hom :=
    (IsPullback.of_hasPullback G.hom G.hom).flip
  have p' : IsPullback (pullback.snd G'.hom G'.hom) (pullback.fst G'.hom G'.hom) G'.hom G'.hom :=
    (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have c₁ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.fst G.hom G.hom =
      pullback.fst G'.hom G'.hom ≫ F := pullback.lift_fst _ _ _
  have c₂ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.snd G.hom G.hom =
      pullback.snd G'.hom G'.hom ≫ F := pullback.lift_snd _ _ _
  have q : IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫
      pullback.snd G.hom G.hom) (pullback.fst G'.hom G'.hom) G.hom (F ≫ G.hom) := by
    rw [c₂, cart.w]
    exact p'.paste_horiz cart
  exact (IsPullback.of_right q c₁ p).paste_vert cart

theorem pullbackMap_comp {S₁ S₀ Y : Scheme.{0}} {A₁ : Over S₁} {D : Over S₀} {U : Over Y} {k : S₁ ⟶ S₀}
    {h₀ : S₀ ⟶ Y} {φ : A₁.left ⟶ D.left} {ψ : D.left ⟶ U.left} (hφ : IsPullback φ A₁.hom D.hom k)
    (cart : IsPullback ψ D.hom U.hom h₀) :
    pullback.map A₁.hom A₁.hom D.hom D.hom φ φ k hφ.w.symm hφ.w.symm ≫
        pullback.map D.hom D.hom U.hom U.hom ψ ψ h₀ cart.w.symm cart.w.symm =
      pullback.map A₁.hom A₁.hom U.hom U.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
        (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

theorem isGrpPullback_comp_spread_to_subring :
    ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → IsGrpPullback e.A d₀.A (spMap R₀.subtype) j → IsGrpPullback e.A u.A (spMap R₀.subtype ≫ h₀) (j ≫ ψ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ₁ : A₁.left ⟶ d₀.A.left), IsGrpPullback A₁ d₀.A (spMap (Subring.inclusion hle)) φ₁ → IsGrpPullback A₁ u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j cart hj hjψ
  haveI := d₀.ab.proper
  haveI := u.ab.smooth
  haveI hqc : QuasiCompact (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom) := inferInstance
  haveI hlft : LocallyOfFiniteType (pullback.snd u.A.hom h₀) := inferInstance
  set f₀ : pullback d₀.A.hom d₀.A.hom ⟶ Sp R₀ := pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom with hf₀
  have hμd : (μ[d₀.A]).left ≫ d₀.A.hom = f₀ := Over.w μ[d₀.A]
  have hμu : (μ[u.A]).left ≫ u.A.hom = pullback.fst u.A.hom u.A.hom ≫ u.A.hom := Over.w μ[u.A]
  set mψ := pullback.map d₀.A.hom d₀.A.hom u.A.hom u.A.hom ψ ψ h₀ cart.w.symm cart.w.symm with hmψ
  have w₁ : ((μ[d₀.A]).left ≫ ψ) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, cart.w, ← Category.assoc, hμd]
  have w₂ : (mψ ≫ (μ[u.A]).left) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, hμu, ← Category.assoc, hmψ, pullback.lift_fst, Category.assoc, cart.w, hf₀,
      Category.assoc]
  let a : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₁
  let b : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₂
  have key : ∀ {S₁ : Scheme.{0}} {A₁ : Over S₁} [GrpObj A₁] {k : S₁ ⟶ Sp R₀} {φ : A₁.left ⟶ d₀.A.left}
      (hφ : IsPullback φ A₁.hom d₀.A.hom k),
      pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ φ k hφ.w.symm hφ.w.symm ≫ mψ =
        pullback.map A₁.hom A₁.hom u.A.hom u.A.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
          (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
    intro S₁ A₁ _ k φ hφ
    exact pullbackMap_comp hφ cart
  have hab : pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ a =
      pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ b := by
    have m₁ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hj.1).1 hj
    have m₂ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hjψ.1).1 hjψ
    apply pullback.hom_ext
    · simp only [a, b, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, ← m₁, Category.assoc, m₂]
      exact (congrArg (· ≫ (μ[u.A]).left) (key hj.1).symm).trans (Category.assoc _ _ _)
    · simp only [a, b, Category.assoc, pullback.lift_snd]
  obtain ⟨F, hF⟩ := GlobalTheory.morphisms_eq_spread_to_subring S R₀ (pullback e.A.hom e.A.hom)
    (pullback d₀.A.hom d₀.A.hom) (pullback u.A.hom h₀) (e.A ⊗ e.A).hom f₀ (pullback.snd u.A.hom h₀)
    (pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm) a b
    (isPullback_pullbackMap hj.1) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) hab
  refine ⟨F, fun R₁ hle hFs A₁ _ φ₁ hφ ↦ ?_⟩
  have cart₁ := hφ.1.paste_horiz cart
  refine (GlobalTheory.PullDegCompare.isGrpPullback_iff cart₁).2 ?_
  have H := hF R₁ hle hFs (pullback A₁.hom A₁.hom) (A₁ ⊗ A₁).hom
    (pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ₁ φ₁ _ hφ.1.w.symm hφ.1.w.symm)
    (isPullback_pullbackMap hφ.1)
  have H' := congrArg (· ≫ pullback.fst u.A.hom h₀) H
  simp only [a, b, Category.assoc, pullback.lift_fst] at H'
  have m := (GlobalTheory.PullDegCompare.isGrpPullback_iff hφ.1).1 hφ
  rw [← Category.assoc, m, Category.assoc, H']
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (μ[u.A]).left) (key hφ.1))

end GlobalTheory.GrpMulSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReduction
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

open CategoryTheory.Limits
open scoped TensorProduct

namespace GlobalTheory.NilThickIso

theorem appTop_spMap_eq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) :
    (spMap π).appTop = (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom π ≫
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc]; simp

theorem surjective_appTop_spMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) : Function.Surjective (spMap π).appTop := by
  rw [appTop_spMap_eq]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso _).2.comp hπ).comp
    (ConcreteCategory.bijective_of_isIso _).2

theorem isNilpotent_ker_appTop_spMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hn : IsNilpotent (RingHom.ker π)) : IsNilpotent (RingHom.ker (spMap π).appTop.hom) := by
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  rw [appTop_spMap_eq]
  simp only [CommRingCat.hom_comp]
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have hk : RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom.comp
      (CommRingCat.ofHom π).hom).comp e) = (RingHom.ker π).comap e := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    constructor
    · intro h
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom h
      simpa using this
    · intro h; simp [h]
  rw [hk, Ideal.zero_eq_bot, ← le_bot_iff]
  refine (Ideal.le_comap_pow _ n).trans ?_
  rw [hn, Ideal.zero_eq_bot]
  intro x hx
  simp only [Ideal.mem_comap, Ideal.mem_bot] at hx ⊢
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    (by rw [map_zero]; exact hx)

theorem surjective_of_sub_mem_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] (φ : B →ₐ[A] C) (I : Ideal A) (hI : IsNilpotent I)
    (h : ∀ c : C, ∃ b : B, c - φ b ∈ I.map (algebraMap A C)) : Function.Surjective φ := by
  obtain ⟨n, hn⟩ := hI
  let N : Submodule A C := LinearMap.range φ.toLinearMap
  have h1 : (⊤ : Submodule A C) ≤ N ⊔ I • ⊤ := by
    intro c _
    obtain ⟨b, hb⟩ := h c
    have hm : c - φ b ∈ I • (⊤ : Submodule A C) := by
      rw [Ideal.smul_top_eq_map]; exact hb
    have := Submodule.add_mem_sup (LinearMap.mem_range_self φ.toLinearMap b) hm
    simpa using this
  have h2 : ∀ k : ℕ, (⊤ : Submodule A C) ≤ N ⊔ I ^ k • ⊤ := by
    intro k
    induction k with
    | zero => exact le_sup_of_le_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul])
    | succ k ih =>
      calc ⊤ ≤ N ⊔ I ^ k • ⊤ := ih
        _ ≤ N ⊔ I ^ k • (N ⊔ I • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl h1) _
        _ = N ⊔ (I ^ k • N ⊔ I ^ (k + 1) • ⊤) := by
          rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
        _ ≤ N ⊔ I ^ (k + 1) • ⊤ := by
          rw [← sup_assoc]
          exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _
  have h3 := h2 n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at h3
  intro c
  obtain ⟨b, hb⟩ := h3 (Submodule.mem_top (x := c))
  exact ⟨b, hb⟩

theorem injective_of_flat_of_ker_le_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Flat A C] (φ : B →ₐ[A] C) (I : Ideal A) (hI : IsNilpotent I)
    (hs : Function.Surjective φ) (h : ∀ b : B, φ b = 0 → b ∈ I.map (algebraMap A B)) :
    Function.Injective φ := by
  obtain ⟨n, hn⟩ := hI
  set K := LinearMap.ker φ.toLinearMap with hKdef
  let mB : I ⊗[A] B →ₗ[A] B := (TensorProduct.lid A B).toLinearMap ∘ₗ I.subtype.rTensor B
  let mC : I ⊗[A] C →ₗ[A] C := (TensorProduct.lid A C).toLinearMap ∘ₗ I.subtype.rTensor C
  have hmC : Function.Injective mC := (TensorProduct.lid A C).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hcomm : ∀ t, φ (mB t) = mC (φ.toLinearMap.lTensor I t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mB, mC]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hex := lTensor_exact I (LinearMap.exact_subtype_ker_map φ.toLinearMap) hs
  have hrange : ∀ b ∈ I • (⊤ : Submodule A B), ∃ t, mB t = b := by
    intro b hb
    refine Submodule.smul_induction_on (p := fun b ↦ ∃ t, mB t = b) hb ?_ ?_
    · intro a ha x _
      exact ⟨⟨a, ha⟩ ⊗ₜ x, by simp [mB]⟩
    · rintro x y ⟨t, rfl⟩ ⟨s, rfl⟩
      exact ⟨t + s, map_add _ _ _⟩
  have hK : ∀ s : I ⊗[A] K, mB (K.subtype.lTensor I s) ∈ I • K := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [mB, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.lid_tmul, Submodule.subtype_apply]
      exact Submodule.smul_mem_smul a.2 x.2
    | add x y hx hy =>
      simp only [map_add]
      exact add_mem hx hy
  have hle : K ≤ I • K := by
    intro k hk
    have hk' : k ∈ I • (⊤ : Submodule A B) := by rw [Ideal.smul_top_eq_map]; exact h k hk
    obtain ⟨t, rfl⟩ := hrange k hk'
    have h0 : φ.toLinearMap.lTensor I t = 0 := hmC (by rw [← hcomm, map_zero]; exact hk)
    obtain ⟨s, rfl⟩ := (hex t).mp h0
    exact hK s
  have hle' : ∀ k : ℕ, K ≤ I ^ k • K := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ k ih =>
      calc K ≤ I ^ k • K := ih
        _ ≤ I ^ k • (I • K) := Submodule.smul_mono le_rfl hle
        _ = I ^ (k + 1) • K := by rw [pow_succ, Submodule.mul_smul]
  have h3 := hle' n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul] at h3
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro b hb
  exact (Submodule.mem_bot A).mp (h3 hb)

theorem ring_step {A A₀ B C B₀ C₀ : CommRingCat.{0}} (ψ : A ⟶ A₀) (β : A ⟶ B) (ρ : A ⟶ C)
    (φ : B ⟶ C) (πB : B ⟶ B₀) (πC : C ⟶ C₀) (β₀ : A₀ ⟶ B₀) (ρ₀ : A₀ ⟶ C₀) (φ₀ : B₀ ⟶ C₀)
    (hψ : Function.Surjective ψ) (hn : IsNilpotent (RingHom.ker ψ.hom))
    (hB : IsPushout β ψ πB β₀) (hC : IsPushout ρ ψ πC ρ₀) (hflat : ρ.hom.Flat)
    (w : β ≫ φ = ρ) (w₀ : φ ≫ πC = πB ≫ φ₀) (hφ₀ : IsIso φ₀) : IsIso φ := by
  have hkB := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout hB hψ
  have hkC := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout hC hψ
  have hπB : Function.Surjective πB := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout hB, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨y, rfl⟩
    · obtain ⟨a, rfl⟩ := hψ y
      exact ⟨β a, congr($(hB.w).hom a)⟩
  have hφ₀ := ConcreteCategory.bijective_of_isIso φ₀
  have hw₀ (b : B) : πC (φ b) = φ₀ (πB b) := congr($(w₀).hom b)
  algebraize [β.hom, ρ.hom]
  let φA : B →ₐ[A] C := { φ.hom with commutes' := fun a ↦ congr($(w).hom a) }
  have hs : Function.Surjective φA := by
    refine surjective_of_sub_mem_map φA (RingHom.ker ψ.hom) hn fun c ↦ ?_
    obtain ⟨y, hy⟩ := hφ₀.2 (πC c)
    obtain ⟨b, rfl⟩ := hπB y
    refine ⟨b, ?_⟩
    have h0 : πC (c - φ b) = 0 := by rw [map_sub, hw₀, hy, sub_self]
    have h1 : c - φ b ∈ RingHom.ker πC.hom := h0
    rw [hkC] at h1
    exact h1
  have hi : Function.Injective φA := by
    refine injective_of_flat_of_ker_le_map φA (RingHom.ker ψ.hom) hn hs fun b hb ↦ ?_
    have h0 : πB b = 0 := hφ₀.1 (by rw [← hw₀, show φ b = 0 from hb, map_zero, map_zero])
    rw [← RingHom.mem_ker, hkB] at h0
    exact h0
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr ⟨hi, hs⟩

theorem affine_case (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) {X Y X₀ Y₀ : Scheme.{0}}
    (p : X ⟶ Sp R) (q : Y ⟶ Sp R) (p₀ : X₀ ⟶ Sp R₀) (q₀ : Y₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (j : Y₀ ⟶ Y)
    (hX : IsPullback i p₀ p (spMap π)) (hY : IsPullback j q₀ q (spMap π)) [Flat p] [IsAffine Y]
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (w : f ≫ q = p) (w₀ : i ≫ f = f₀ ≫ j) [IsIso f₀] : IsIso f := by
  have : IsAffine Y₀ := IsAffine.of_isPullback hY
  have : IsAffine X₀ := IsAffine.of_isIso f₀
  have : IsAffine X := GlobalTheory.AffineThickening.isAffine_of_isPullback_of_isNilpotent (RingHom.ker π) hn
    (CommRingCat.ofHom π) hπ rfl hX this
  have hψ := surjective_appTop_spMap π hπ
  have hψn := isNilpotent_ker_appTop_spMap π hn
  have hfl : (p.appTop).hom.Flat := HasRingHomProperty.iff_of_isAffine.mp ‹Flat p›
  have key : IsIso f.appTop := ring_step (spMap π).appTop q.appTop p.appTop f.appTop j.appTop i.appTop
    q₀.appTop p₀.appTop f₀.appTop hψ hψn (isPushout_appTop_of_isPullback hY)
    (isPushout_appTop_of_isPullback hX) hfl (by rw [← w]; simp) (by
      rw [← Scheme.Hom.comp_appTop, w₀, Scheme.Hom.comp_appTop]) ⟨⟨(inv f₀).appTop, by rw [← Scheme.Hom.comp_appTop]; simp, by rw [← Scheme.Hom.comp_appTop]; simp⟩⟩
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop))))

theorem general (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) {X Y X₀ Y₀ : Scheme.{0}}
    (p : X ⟶ Sp R) (q : Y ⟶ Sp R) (p₀ : X₀ ⟶ Sp R₀) (q₀ : Y₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (j : Y₀ ⟶ Y)
    (hX : IsPullback i p₀ p (spMap π)) (hY : IsPullback j q₀ q (spMap π)) [Flat p]
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (w : f ≫ q = p) (w₀ : i ≫ f = f₀ ≫ j) [IsIso f₀] : IsIso f := by
  refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    Y.affineCover (fun k ↦ ?_)
  change IsIso (pullback.snd f (Y.affineCover.f k))
  set u := Y.affineCover.f k
  have hU : IsPullback (pullback.snd j u) (pullback.fst j u ≫ q₀) (u ≫ q) (spMap π) :=
    (IsPullback.of_hasPullback j u).flip.paste_vert hY
  have hX' : IsPullback (pullback.snd i (pullback.fst f u)) (pullback.fst i (pullback.fst f u) ≫ p₀)
      (pullback.fst f u ≫ p) (spMap π) :=
    (IsPullback.of_hasPullback i (pullback.fst f u)).flip.paste_vert hX
  have hP : IsPullback (pullback.fst i (pullback.fst f u))
      (pullback.snd i (pullback.fst f u) ≫ pullback.snd f u) (i ≫ f) u :=
    (IsPullback.of_hasPullback i (pullback.fst f u)).paste_vert (IsPullback.of_hasPullback f u)
  have hP' : IsPullback (pullback.fst i (pullback.fst f u) ≫ f₀)
      (pullback.snd i (pullback.fst f u) ≫ pullback.snd f u) j u :=
    IsPullback.of_iso hP (Iso.refl _) (asIso f₀) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [w₀]) (by simp)
  exact affine_case R R₀ π hπ hn (pullback.fst f u ≫ p) (u ≫ q) _ _ _ _ hX' hU (pullback.snd f u)
    hP'.isoPullback.hom (by rw [← w, pullback.condition_assoc]) (by simp)

theorem isIso_of_flat_of_isIso_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X Y : Over (Sp R)) (X₀ Y₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left) (j : Y₀.left ⟶ Y.left),
    IsPullback i X₀.hom X.hom (spMap π) → IsPullback j Y₀.hom Y.hom (spMap π) → Flat X.hom →
    ∀ (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀), i ≫ f.left = f₀.left ≫ j → IsIso f₀ → IsIso f := by
  intro R R₀ _ _ π hπ hn X Y X₀ Y₀ i j hX hY hfl f f₀ w₀ hf₀
  have : IsIso f₀.left := (Over.forget _).map_isIso f₀
  have : IsIso f.left := general R R₀ π hπ hn X.hom Y.hom X₀.hom Y₀.hom i j hX hY f.left f₀.left
    (Over.w f) w₀
  have : IsIso ((Over.forget _).map f) := this
  exact isIso_of_reflects_iso f (Over.forget _)

end GlobalTheory.NilThickIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfSubsingletonPoints
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ConnConstSplit

open IsLocalRing

theorem isLocalRing_of_subsingleton_points (O : Type) [CommRing O] [IsLocalRing O]
    [IsAlgClosed (ResidueField O)] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Subsingleton (A →ₐ[O] ResidueField O)] (c₀ : A →ₐ[O] ResidueField O) : IsLocalRing A := by
  have key : ∀ M : Ideal A, M.IsMaximal → M = RingHom.ker c₀ := by
    intro M hM
    have hu : (M.under O).IsMaximal := Ideal.IsMaximal.under O M
    have hum : M.under O = maximalIdeal O := IsLocalRing.eq_maximalIdeal hu
    letI : Field (A ⧸ M) := Ideal.Quotient.field M
    let g : O →+* A ⧸ M := (Ideal.Quotient.mk M).comp (algebraMap O A)
    haveI : IsLocalHom g := ⟨fun x hx => by
      by_contra h
      have hxm : x ∈ M.under O := by rw [hum]; exact h
      have h0 : g x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hxm
      exact hx.ne_zero h0⟩
    let f : ResidueField O →+* A ⧸ M := ResidueField.lift g
    letI : Algebra (ResidueField O) (A ⧸ M) := f.toAlgebra
    have hf : ∀ x : O, f (residue O x) = g x := fun x => rfl
    haveI : Algebra.IsIntegral (ResidueField O) (A ⧸ M) := ⟨fun y => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨P, hPm, hPa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
      refine ⟨P.map (residue O), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have h1 : (algebraMap (ResidueField O) (A ⧸ M)).comp (residue O) = g := RingHom.ext hf
      rw [h1]
      have h2 := Polynomial.hom_eval₂ P (algebraMap O A) (Ideal.Quotient.mk M) a
      rw [hPa, map_zero] at h2
      exact h2.symm⟩
    have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField O) (K := A ⧸ M)).2
    let e : ResidueField O ≃+* A ⧸ M := RingEquiv.ofBijective f ⟨f.injective, hsurj⟩
    let c : A →ₐ[O] ResidueField O :=
      { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk M)
        commutes' := fun x => by
          change e.symm (Ideal.Quotient.mk M (algebraMap O A x)) = algebraMap O (ResidueField O) x
          rw [RingEquiv.symm_apply_eq]
          exact (hf x).symm }
    have hc : c = c₀ := Subsingleton.elim _ _
    ext a
    rw [← hc, RingHom.mem_ker]
    change a ∈ M ↔ e.symm (Ideal.Quotient.mk M a) = 0
    rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  haveI : Nontrivial A := c₀.toRingHom.domain_nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' => (key M' hM').trans (key M hM).symm⟩

theorem comp_add_app {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {B : Type} [CommRing B]
    [Algebra O B] {G H : PDivGroup p O} (f g : G ⟶ H) (n : ℕ) (x : G.A n →ₐ[O] B) :
    x.comp ((f + g).app n : H.A n →ₐ[O] G.A n) = WithConv.ofConv
      (WithConv.toConv (x.comp (f.app n : H.A n →ₐ[O] G.A n)) *
        WithConv.toConv (x.comp (g.app n : H.A n →ₐ[O] G.A n))) :=
  congrArg WithConv.ofConv
    (map_mul ((GlobalTheory.PDiv.ptsPush (H.A n) x).comp GlobalTheory.PDiv.toPts) (f.conv n) (g.conv n))

theorem eq_one_of_mul_self_of_pow {M : Type*} [Monoid M] {y : M} (hy : y * y = y) {m : ℕ}
    (hm : 1 ≤ m) (h : y ^ m = 1) : y = 1 := by
  have hk : ∀ k : ℕ, y ^ (k + 1) = y := by
    intro k
    induction k with
    | zero => exact pow_one y
    | succ k ih => rw [pow_succ, ih, hy]
  rw [← h, ← Nat.sub_add_cancel hm, hk]

end GlobalTheory.ConnConstSplit

namespace GlobalTheory.ConnConstSplit

open IsLocalRing

theorem exists_isSum_conn_const : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, ∃ G₁ G₂ : PDivGroup p O, IsSum G G₁ G₂ ∧ PDivLat.IsConn G₁ ∧ IsConst G₂ := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  haveI := ValuationRing.of_integers v hv
  haveI := hv.isFractionRing
  haveI : IsAlgClosed (ResidueField O) :=
    GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O C
  obtain ⟨u, huu, hfix, hrange⟩ := GlobalTheory.ConstPart.exists_idempotent_constPart p C v O hv G
  obtain ⟨G₂, i₂, q₂, h₂1, h₂2⟩ := GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G u huu
  have h1u : (𝟙 G - u) ≫ (𝟙 G - u) = 𝟙 G - u := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id, huu]
    abel
  obtain ⟨G₁, i₁, q₁, h₁1, h₁2⟩ := GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G (𝟙 G - u) h1u
  have hl₁ : ∀ n (b : G₁.A n), i₁.app n (q₁.app n b) = b := fun n b => by
    have h := congrArg (fun f : G₁ ⟶ G₁ => f.app n b) h₁1
    simpa using h
  have hl₂ : ∀ n (b : G₂.A n), i₂.app n (q₂.app n b) = b := fun n b => by
    have h := congrArg (fun f : G₂ ⟶ G₂ => f.app n b) h₂1
    simpa using h
  have hu₂ : ∀ n (a : G.A n), u.app n a = q₂.app n (i₂.app n a) := fun n a => by
    rw [← h₂2]; rfl
  refine ⟨G₁, G₂, ⟨i₁, i₂, q₁, q₂, h₁1, h₂1, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have e1 : i₁ ≫ q₂ = i₁ ≫ ((q₁ ≫ i₁) ≫ (q₂ ≫ i₂)) ≫ q₂ := by
      simp only [Category.assoc]
      rw [h₂1, Category.comp_id, reassoc_of% h₁1]
    rw [e1, h₁2, h₂2, Preadditive.sub_comp, Category.id_comp, huu, sub_self,
      Limits.zero_comp, Limits.comp_zero]
  · have e1 : i₂ ≫ q₁ = i₂ ≫ ((q₂ ≫ i₂) ≫ (q₁ ≫ i₁)) ≫ q₁ := by
      simp only [Category.assoc]
      rw [h₁1, Category.comp_id, reassoc_of% h₂1]
    rw [e1, h₁2, h₂2, Preadditive.comp_sub, Category.comp_id, huu, sub_self,
      Limits.zero_comp, Limits.comp_zero]
  · rw [h₁2, h₂2, sub_add_cancel]
  · intro n
    let c₀ : G₁.A n →ₐ[O] ResidueField O :=
      (Algebra.ofId O (ResidueField O)).comp (Bialgebra.counitAlgHom O (G₁.A n))
    have hall : ∀ c : G₁.A n →ₐ[O] ResidueField O, c = c₀ := by
      intro c
      set x : G.A n →ₐ[O] ResidueField O := c.comp (i₁.app n : G.A n →ₐ[O] G₁.A n) with hxdef
      have hx1 : x.comp (u.app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext (hfix n x)
      have hx2 : x.comp ((q₁ ≫ i₁).app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext fun a => by
        change c (i₁.app n (q₁.app n (i₁.app n a))) = c (i₁.app n a)
        rw [hl₁]
      have hsum : q₁ ≫ i₁ + u = 𝟙 G := by rw [h₁2, sub_add_cancel]
      have hid : x.comp ((𝟙 G : G ⟶ G).app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext fun a => rfl
      have hmul := comp_add_app (q₁ ≫ i₁) u n x
      rw [hsum, hid, hx2, hx1] at hmul
      have hyy : WithConv.toConv x * WithConv.toConv x = WithConv.toConv x := by
        exact (congrArg WithConv.toConv hmul).symm
      have hx : WithConv.toConv x = 1 :=
        eq_one_of_mul_self_of_pow hyy (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
          (G.pts_pow_self n (WithConv.toConv x))
      ext b
      have hb : c b = x (q₁.app n b) := by
        change c b = c (i₁.app n (q₁.app n b)); rw [hl₁]
      rw [hb]
      have hx' : x = WithConv.ofConv (1 : WithConv (G.A n →ₐ[O] ResidueField O)) := by
        rw [← hx]
      rw [hx', AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]
      rfl
    haveI : Subsingleton (G₁.A n →ₐ[O] ResidueField O) :=
      ⟨fun a b => (hall a).trans (hall b).symm⟩
    exact isLocalRing_of_subsingleton_points O (G₁.A n) c₀
  · intro n
    obtain ⟨N, ⟨e⟩⟩ := hrange n
    have hinj : Function.Injective (q₂.app n : G₂.A n →ₐ[O] G.A n) := fun a b h => by
      rw [← hl₂ n a, ← hl₂ n b]
      exact congrArg (i₂.app n) h
    have hrng : (u.app n : G.A n →ₐ[O] G.A n).range = (q₂.app n : G₂.A n →ₐ[O] G.A n).range := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨i₂.app n a, (hu₂ n a).symm⟩
      · rintro ⟨b, rfl⟩
        refine ⟨q₂.app n b, ?_⟩
        change u.app n (q₂.app n b) = q₂.app n b
        rw [hu₂, hl₂]
    let e' : G₂.A n ≃ₐ[O] (Fin N → O) :=
      (AlgEquiv.ofInjective _ hinj).trans ((Subalgebra.equivOfEq _ _ hrng.symm).trans e)
    have hN : N = p ^ (n * G₂.height) := by
      have h1 := G₂.rank_eq n ⟨maximalIdeal O, inferInstance⟩
      rw [Module.rankAtStalk_eq_of_equiv e'.toLinearEquiv, Module.rankAtStalk_eq_finrank_of_free,
        Module.finrank_fin_fun] at h1
      simpa using h1
    exact ⟨hN ▸ e'⟩

end GlobalTheory.ConnConstSplit
end

