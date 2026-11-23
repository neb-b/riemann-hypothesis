module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAvgK
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pAvgK :
    ∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out := by
  intro X V _ _ _ K K₀ hle hidx Ψ hΨ
  haveI : Finite (K ⧸ K₀.subgroupOf K) := Nat.finite_of_card_ne_zero hidx
  haveI : Fintype (K ⧸ K₀.subgroupOf K) := Fintype.ofFinite _
  let e := Subgroup.quotientEquivProdOfLE hle
  let F : X ⧸ K → V := fun y => Ψ y.out
  have he : ∀ x : X ⧸ K₀, Ψ x.out = F (e x).1 := by
    intro x
    have h1 : (e x).1 = ((x.out : X) : X ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' x]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x.out
    simp only [F, h1, hk, hΨ k k.2]
  have hcard : Fintype.card (K ⧸ K₀.subgroupOf K) = K₀.relIndex K := by
    rw [Fintype.card_eq_nat_card]
    rfl
  have h2 : ∑ᶠ x : X ⧸ K₀, Ψ x.out = ∑ᶠ p : (X ⧸ K) × (K ⧸ K₀.subgroupOf K), F p.1 :=
    (finsum_congr he).trans (finsum_comp_equiv e (f := fun p => F p.1))
  rw [h2]
  by_cases hfin : (Function.support F).Finite
  · have hG : Function.HasFiniteSupport (fun p : (X ⧸ K) × (K ⧸ K₀.subgroupOf K) => F p.1) := by
      refine (hfin.prod (Set.finite_univ (α := K ⧸ K₀.subgroupOf K))).subset ?_
      intro p hp
      exact ⟨hp, trivial⟩
    rw [finsum_curry _ hG, smul_finsum]
    refine finsum_congr fun a => ?_
    show ∑ᶠ _ : K ⧸ K₀.subgroupOf K, Ψ a.out = _
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, hcard, Nat.cast_smul_eq_nsmul ℂ]
  · have h3 : ∑ᶠ y : X ⧸ K, Ψ y.out = 0 := finsum_of_infinite_support hfin
    rw [h3, smul_zero]
    apply finsum_of_infinite_support
    intro hG
    apply hfin
    refine (hG.image Prod.fst).subset ?_
    intro a ha
    exact ⟨(a, ((1 : K) : K ⧸ K₀.subgroupOf K)), ha, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvRing
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pConvRing :
    ConvRing := by
  intro X _ K hK f hf f' hf'
  refine ⟨Formalism.UG.Final.HeckeConvMem X K ℂ hK f hf f' hf', fun f'' hf'' => ?_⟩
  exact Formalism.UG.Final.HeckeAssoc X K ℂ hK f hf f' hf' f'' hf''
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvSupp
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms
open scoped Classical

namespace UpperTheory.Gal.W2.Seed

theorem pConvSupp : ConvSupp := by
  intro X _ K f f' g h
  by_contra hne
  push_neg at hne
  apply h
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  by_contra hq
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hq
  exact hne _ _ h1 h2 (mul_inv_cancel_left _ _).symm

end UpperTheory.Gal.W2.Seed
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetCosets
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem mul_mem_doubleCoset_iff_of_mem {X : Type} [Group X] (K : Subgroup X) (a g k : X) (hk : k ∈ K) :
    g * k ∈ DoubleCoset.doubleCoset a (K : Set X) K ↔ g ∈ DoubleCoset.doubleCoset a (K : Set X) K := by
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y * k⁻¹, K.mul_mem hy (K.inv_mem hk), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y * k, K.mul_mem hy hk, by rw [h, mul_assoc]⟩

private theorem loc_mem_doubleCoset_loc_iff {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X)
    (Kw : Subgroup M') (hF : L'.Fact K Kw) (t z : M') :
    L'.loc z ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K ↔
      z ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw := by
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    refine ⟨L'.pr x, hF.2 x hx, L'.pr y, hF.2 y hy, ?_⟩
    have h' := congrArg L'.pr h
    simpa [map_mul, L'.pr_loc] using h'
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨L'.loc x, hF.1 x hx, L'.loc y, hF.1 y hy, by rw [h, map_mul, map_mul]⟩

theorem UpperTheory.Gal.W2.Seed.pDosetCosets :
    ∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := by
  intro X M' _ _ L' K Kw hF t V _ _ Ψ hΨ
  set f : X ⧸ K → V := fun y => dosetInd ℂ K (L'.loc t) y.out • Ψ y.out with hf
  let φ : M' ⧸ Kw → X ⧸ K := fun x => ((L'.loc x.out : X) : X ⧸ K)
  have hφ : Function.Injective φ := by
    intro x x' h
    simp only [φ, QuotientGroup.eq] at h
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x', QuotientGroup.eq]
    have h2 := hF.2 _ h
    simpa [map_mul, map_inv, L'.pr_loc] using h2
  have hφf : ∀ x, f (φ x) = dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (L'.loc x.out)
    simp only [hf, φ, hk]
    rw [hΨ k k.2]
    simp only [dosetInd, Set.indicator, mul_mem_doubleCoset_iff_of_mem K _ _ _ k.2, loc_mem_doubleCoset_loc_iff L' K Kw hF,
      Pi.one_apply]
  have hsupp : Function.support f ⊆ Set.range φ := by
    intro y hy
    rw [Function.mem_support] at hy
    have hmem : y.out ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K := by
      by_contra hn
      apply hy
      simp [hf, dosetInd, hn]
    rw [DoubleCoset.mem_doubleCoset] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    refine ⟨((L'.pr a * t : M') : M' ⧸ Kw), ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Kw (L'.pr a * t)
    simp only [φ, hk]
    rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
    set n := a * (L'.loc (L'.pr a))⁻¹ with hn
    have hn1 : L'.pr n = 1 := by simp [hn, L'.pr_loc]
    have hnK : n ∈ K := K.mul_mem ha (K.inv_mem (hF.1 _ (hF.2 a ha)))
    have hy' : y.out = L'.loc (L'.pr a * t) * (n * b) := by
      calc y.out = a * L'.loc t * b := hab
        _ = n * L'.loc (L'.pr a * t) * b := by simp [hn, map_mul, mul_assoc]
        _ = L'.loc (L'.pr a * t) * n * b := by rw [L'.comm _ n hn1]
        _ = _ := mul_assoc _ _ _
    rw [hy', map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact K.mul_mem (K.inv_mem (hF.1 _ k.2)) (K.mul_mem hnK hb)
  calc ∑ᶠ y : X ⧸ K, f y = ∑ᶠ y ∈ Set.range φ, f y := by
        rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp]
    _ = ∑ᶠ x, f (φ x) := finsum_mem_range hφ
    _ = _ := finsum_congr hφf
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetIff
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem loc_split {X M' : Type} [Group X] [Group M'] (L' : Loc X M') {K : Subgroup X} {Kw : Subgroup M'}
    (hF : L'.Fact K Kw) {k : X} (hk : k ∈ K) :
    ∃ a ∈ Kw, ∃ k₀ ∈ K, L'.pr k₀ = 1 ∧ k = L'.loc a * k₀ := by
  refine ⟨L'.pr k, hF.2 k hk, (L'.loc (L'.pr k))⁻¹ * k, K.mul_mem (K.inv_mem (hF.1 _ (hF.2 k hk))) hk, ?_, by group⟩
  simp [L'.pr_loc]

private theorem loc_key {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (a t b : M') {k₀ r k₁ : X}
    (h₀ : L'.pr k₀ = 1) (hr : L'.pr r = 1) (h₁ : L'.pr k₁ = 1) :
    L'.loc a * k₀ * (L'.loc t * r) * (k₁ * L'.loc b) = L'.loc (a * t * b) * (k₀ * r * k₁) := by
  have hprod : L'.pr (k₀ * r * k₁) = 1 := by simp [map_mul, h₀, hr, h₁]
  have e1 := L'.comm t k₀ h₀
  have e2 := L'.comm b (k₀ * r * k₁) hprod
  rw [map_mul, map_mul]
  calc L'.loc a * k₀ * (L'.loc t * r) * (k₁ * L'.loc b)
      = L'.loc a * (k₀ * L'.loc t) * r * k₁ * L'.loc b := by group
    _ = L'.loc a * (L'.loc t * k₀) * r * k₁ * L'.loc b := by rw [e1]
    _ = L'.loc a * L'.loc t * ((k₀ * r * k₁) * L'.loc b) := by group
    _ = L'.loc a * L'.loc t * L'.loc b * (k₀ * r * k₁) := by rw [← e2]; group

theorem UpperTheory.Gal.W2.Seed.pDosetIff :
    ∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K := by
  intro X M' _ _ L' K Kw hF t r hr g
  constructor
  · intro hg
    rw [DoubleCoset.mem_doubleCoset] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    obtain ⟨a, ha, k₀, hk₀, h₀, rfl⟩ := loc_split L' hF hx
    obtain ⟨b, hb, k₁, hk₁, h₁, rfl⟩ := loc_split L' hF hy
    have hc : L'.loc b * k₁ = k₁ * L'.loc b := L'.comm b k₁ h₁
    rw [hc, loc_key L' a t b h₀ hr h₁]
    have hpr : L'.pr (L'.loc (a * t * b) * (k₀ * r * k₁)) = a * t * b := by
      simp [map_mul, h₀, hr, h₁, L'.pr_loc]
    rw [hpr]
    refine ⟨?_, ?_⟩
    · rw [DoubleCoset.mem_doubleCoset]
      exact ⟨a, ha, b, hb, rfl⟩
    · rw [DoubleCoset.mem_doubleCoset, inv_mul_cancel_left]
      exact ⟨k₀, hk₀, k₁, hk₁, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [DoubleCoset.mem_doubleCoset] at h1 h2 ⊢
    obtain ⟨a, ha, b, hb, hab⟩ := h1
    obtain ⟨k₀, hk₀, k₁, hk₁, hk⟩ := h2
    have hg : g = L'.loc (L'.pr g) * (k₀ * r * k₁) := by
      rw [← hk]
      group
    have hpg := congrArg L'.pr hg
    simp only [map_mul, L'.pr_loc, hr, mul_one] at hpg
    have hpk : L'.pr k₀ * L'.pr k₁ = 1 := by
      calc L'.pr k₀ * L'.pr k₁ = (L'.pr g)⁻¹ * (L'.pr g * (L'.pr k₀ * L'.pr k₁)) := by group
        _ = 1 := by rw [← hpg]; group
    have hcr := L'.comm (L'.pr k₀) r hr
    have hk0 : L'.pr (k₀ * (L'.loc (L'.pr k₀))⁻¹) = 1 := by
      simp [map_mul, map_inv, L'.pr_loc]
    have hk1 : L'.pr (L'.loc (L'.pr k₀) * k₁) = 1 := by
      rw [map_mul, L'.pr_loc, hpk]
    have hsplit : k₀ * r * k₁ =
        k₀ * (L'.loc (L'.pr k₀))⁻¹ * r * (L'.loc (L'.pr k₀) * k₁) := by
      calc k₀ * r * k₁ = k₀ * (L'.loc (L'.pr k₀))⁻¹ * (L'.loc (L'.pr k₀) * r) * k₁ := by group
        _ = _ := by rw [hcr]; group
    refine ⟨L'.loc a * (k₀ * (L'.loc (L'.pr k₀))⁻¹), ?_, L'.loc (L'.pr k₀) * k₁ * L'.loc b, ?_, ?_⟩
    · exact K.mul_mem (hF.1 a ha) (K.mul_mem hk₀ (K.inv_mem (hF.1 _ (hF.2 _ hk₀))))
    · exact K.mul_mem (K.mul_mem (hF.1 _ (hF.2 _ hk₀)) hk₁) (hF.1 b hb)
    · rw [loc_key L' a t b hk0 hr hk1, ← hab, ← hsplit]
      exact hg
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PExtP
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pExtP :
    ExtP := by
  intro Γ X X₂ V _ _ _ _ _ ι K K₂ ξ φ h1 h2
  let F : X × X₂ → V := fun p =>
    if h : ∃ γ : Γ, (ι γ).2⁻¹ * p.2 ∈ K₂ then ξ h.choose (φ ((ι h.choose).1⁻¹ * p.1)) else 0
  have key : ∀ (γ : Γ) (g : X) (g₂ : X₂), (ι γ).2⁻¹ * g₂ ∈ K₂ →
      F (g, g₂) = ξ γ (φ ((ι γ).1⁻¹ * g)) := by
    intro γ g g₂ hγ
    have h : ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂ := ⟨γ, hγ⟩
    dsimp only [F]
    rw [dite_eq_left h]
    have hδ := h.choose_spec
    generalize h.choose = δ at hδ ⊢
    have hε : (ι (δ⁻¹ * γ)).2 ∈ K₂ := by
      have e : (ι (δ⁻¹ * γ)).2 = ((ι δ).2⁻¹ * g₂) * ((ι γ).2⁻¹ * g₂)⁻¹ := by
        simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv]
        group
      rw [e]
      exact K₂.mul_mem hδ (K₂.inv_mem hγ)
    have e2 : (ι (δ⁻¹ * γ)).1 * ((ι γ).1⁻¹ * g) = (ι δ).1⁻¹ * g := by
      simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv]
      group
    rw [← e2, h1 _ hε, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have zero : ∀ (g : X) (g₂ : X₂), (¬ ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂) → F (g, g₂) = 0 := by
    intro g g₂ h
    dsimp only [F]
    rw [dite_eq_right h]
  have mem : F ∈ forms ι (K.prod K₂) ξ := by
    refine ⟨fun γ p => ?_, fun k hk p => ?_⟩
    · obtain ⟨g, g₂⟩ := p
      have e : ι γ * (g, g₂) = ((ι γ).1 * g, (ι γ).2 * g₂) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι (γ * δ)).2⁻¹ * ((ι γ).2 * g₂) ∈ K₂ := by
          simpa [map_mul, mul_assoc] using hδ
        rw [key δ g g₂ hδ, key (γ * δ) _ _ hs, ← Module.End.mul_apply, ← map_mul]
        congr 2
        simp [mul_assoc]
      · rw [zero g g₂ h, map_zero]
        apply zero
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨γ⁻¹ * δ, ?_⟩
        simpa [map_mul, mul_assoc] using hδ
    · obtain ⟨g, g₂⟩ := p
      obtain ⟨k1, k2⟩ := k
      rw [Subgroup.mem_prod] at hk
      have hk1 : k1 ∈ K := hk.1
      have hk2 : k2 ∈ K₂ := hk.2
      have e : (g, g₂) * (k1, k2) = (g * k1, g₂ * k2) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι δ).2⁻¹ * (g₂ * k2) ∈ K₂ := by
          rw [← mul_assoc]
          exact K₂.mul_mem hδ hk2
        rw [key δ g g₂ hδ, key δ (g * k1) (g₂ * k2) hs, ← mul_assoc, h2 k1 hk1]
      · rw [zero g g₂ h, zero]
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ, ?_⟩
        have := K₂.mul_mem hδ (K₂.inv_mem hk2)
        simpa [mul_assoc] using this
  refine ⟨⟨F, mem⟩, fun g => ?_, fun g₂ => ?_⟩
  · show F (g, 1) = φ g
    rw [key 1 g 1 (by simp)]
    simp
  · by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
    · obtain ⟨δ, hδ⟩ := h
      exact Or.inr ⟨δ, fun g => key δ g g₂ hδ⟩
    · exact Or.inl fun g => zero g g₂ h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAct
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem typeFunction_mul_mem {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a b : M) (hb : b ∈ J) :
    tyFn J ψ (a * b) = tyFn J ψ a * (((ψ ⟨b, hb⟩)⁻¹ : ℂˣ) : ℂ) := by
  unfold tyFn
  by_cases ha : a ∈ J
  · have hab : a * b ∈ J := J.mul_mem ha hb
    rw [dite_eq_left ha, dite_eq_left hab]
    have : (⟨a * b, hab⟩ : J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, mul_inv, Units.val_mul]
  · have hab : a * b ∉ J := fun h => ha (by simpa using J.mul_mem h (J.inv_mem hb))
    rw [dite_eq_right ha, dite_eq_right hab, zero_mul]

private theorem typeFunction_one {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) : tyFn J ψ 1 = 1 := by
  unfold tyFn
  rw [dite_eq_left J.one_mem]
  have : (⟨1, J.one_mem⟩ : J) = 1 := rfl
  rw [this, map_one, inv_one, Units.val_one]

private theorem doubleCosetIndicator_central {X : Type} [Group X] (K : Subgroup X) (a z w : X) (hz : ∀ g, z * g = g * z) :
    dosetInd ℂ K (a * z) (z * w) = dosetInd ℂ K a w := by
  have key : z * w ∈ DoubleCoset.doubleCoset (a * z) (K : Set X) (K : Set X) ↔
      w ∈ DoubleCoset.doubleCoset a (K : Set X) (K : Set X) := by
    simp only [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y, hy, ?_⟩
      have e' : z * w = z * (x * a * y) := by
        rw [e, hz (x * a * y)]
        have h1 : x * (a * z) * y = x * a * (z * y) := by group
        rw [h1, hz y]
        group
      exact mul_left_cancel e'
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y, hy, ?_⟩
      rw [e, hz (x * a * y)]
      have h1 : x * (a * z) * y = x * a * (z * y) := by group
      rw [h1, hz y]
      group
  unfold dosetInd
  by_cases hw : w ∈ DoubleCoset.doubleCoset a (K : Set X) (K : Set X)
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (key.mpr hw)]; rfl
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw (key.mp h))]

theorem UpperTheory.Gal.W2.Seed.pTfAct :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out)) → TfAdm → TfAct := by
  intro hidx hfac hadm X M M' _ _ _ T L' Kw hF hAp t z hz V _ _ Φ hΦ g
  have hh : T.L.pr (L'.loc t * z) = 1 := by rw [map_mul, hAp.1 t, hz.2, one_mul]
  obtain ⟨-, hinv⟩ := hadm X M T _ hh
  have hc0 : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr T.idx
  have h0 : ∀ k ∈ T.K, ∀ x, T.tf (L'.loc t * z) (x * k) • Φ (g * (x * k)) =
      T.tf (L'.loc t * z) x • Φ (g * x) := by
    intro k hk x
    rw [(hinv k hk x).2, ← mul_assoc, hΦ k hk, smul_smul, mul_right_comm, Units.inv_mul, one_mul]
  let F : X → V := fun y =>
    (tyFn T.J T.ψ (T.L.pr y) * dosetInd ℂ T.K (L'.loc t * z) y) • Φ (g * y)
  have hF1 : ∀ y, ((T.K₀.relIndex T.K : ℕ) : ℂ) • (T.tf (L'.loc t * z) y • Φ (g * y)) = F y := by
    intro y
    simp only [F, TyLev.tf]
    rw [smul_smul, mul_assoc, mul_inv_cancel_left₀ hc0]
  have hFinv : ∀ (y : X) (k : T.K), F (y * k) = F y := by
    intro y k
    rw [← hF1, ← hF1, h0 k k.2 y]
  let Ψ : X → V := fun y => tyFn T.J T.ψ (T.L.pr y) • Φ (g * z * y)
  have hΨ : ∀ k ∈ T.K, ∀ y, Ψ (y * k) = Ψ y := by
    intro k hk y
    simp only [Ψ]
    rw [map_mul, typeFunction_mul_mem T.J T.ψ _ _ (T.fact.2 k hk), ← mul_assoc, hΦ k hk, smul_smul,
      mul_assoc, Units.inv_mul, mul_one]
  have e1 := hidx X V T.K T.K₀ T.le T.idx (fun x => T.tf (L'.loc t * z) x • Φ (g * x)) h0
  have e2 := hfac X M' L' T.K Kw hF t V Ψ hΨ
  calc hAct T.K₀ (T.tf (L'.loc t * z)) Φ g
      = ((T.K₀.relIndex T.K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ T.K, T.tf (L'.loc t * z) y.out • Φ (g * y.out) := e1
    _ = ∑ᶠ y : X ⧸ T.K, F y.out := by
        rw [smul_finsum]
        exact finsum_congr fun y => hF1 _
    _ = ∑ᶠ y : X ⧸ T.K, F (z * y.out) := (Formalism.UG.P.finsum_out_mul T.K z F hFinv).symm
    _ = ∑ᶠ y : X ⧸ T.K, dosetInd ℂ T.K (L'.loc t) y.out • Ψ y.out := by
        refine finsum_congr fun y => ?_
        simp only [F, Ψ]
        rw [doubleCosetIndicator_central T.K _ z _ hz.1, map_mul, hz.2, one_mul, smul_smul, ← mul_assoc g z,
          mul_comm]
    _ = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := e2
    _ = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Φ (g * z * L'.loc x.out) := by
        refine finsum_congr fun x => ?_
        simp only [Ψ]
        rw [hAp.1, typeFunction_one, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfCen
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfCen :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → TfAdm → TfCen := by
  intro hsum hadm X M _ _ T z hz V _ _ Φ hΦ g
  have hidx : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr T.idx
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : X → V, ∀ x, Ψ x = T.tf z x • Φ (g * x) := ⟨_, fun _ => rfl⟩
  have hinv : ∀ k ∈ T.K, ∀ x, Ψ (x * k) = Ψ x := by
    intro k hk x
    have h1 := ((hadm X M T z hz.2).2 k hk x).2
    have h2 := hΦ k hk (g * x)
    rw [hΨ, hΨ, h1, ← mul_assoc, h2, smul_smul, mul_right_comm, Units.inv_mul, one_mul]
  have hsingle : ∑ᶠ y : X ⧸ T.K, Ψ y.out = Ψ z := by
    rw [finsum_eq_single _ (QuotientGroup.mk z : X ⧸ T.K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul T.K z
      rw [hk]
      exact hinv k k.2 z
    · intro y hy
      have h0 : dosetInd ℂ T.K z y.out = 0 := by
        apply Set.indicator_of_notMem
        intro hm
        obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.mp hm
        have e' : y.out = z * (a * b) := by
          rw [e, ← hz.1 a, mul_assoc]
        have h2 : ((y.out : X) : X ⧸ T.K) = (z : X ⧸ T.K) := by
          rw [e']
          exact QuotientGroup.mk_mul_of_mem z (T.K.mul_mem ha hb)
        exact hy ((QuotientGroup.out_eq' y).symm.trans h2)
      rw [hΨ, TyLev.tf, h0, mul_zero, zero_smul]
  have hty : tyFn T.J T.ψ 1 = 1 := by
    unfold tyFn
    rw [dite_eq_left T.J.one_mem]
    have h1 : (⟨1, T.J.one_mem⟩ : T.J) = 1 := rfl
    rw [h1, map_one]
    simp
  have hdz : dosetInd ℂ T.K z z = 1 := by
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.mpr ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩)]
    rfl
  have hzz : T.tf z z = ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ := by
    rw [TyLev.tf, hz.2, hty, hdz, mul_one, mul_one]
  have hs := hsum X V T.K T.K₀ T.le T.idx Ψ hinv
  unfold hAct
  simp only [hΨ] at hs hsingle
  rw [hs, hsingle, hzz, smul_smul, mul_inv_cancel₀ hidx, one_smul]
end

