module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0040

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ALocEqRoL
section
open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def aLoc (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (n : 𝓞 F) : ℝ :=
  alphaN h L 𝔭.1 n / eFac K (finrank K V) 𝔭.1


open scoped Classical in
def roL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (j : ℕ) : ℝ :=
  if 𝔭 ∈ S then 1 else aLoc h L 𝔭 (exists_vF_eq 𝔭.2 j).choose

variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
  {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
  (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
  {S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}}
  (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S)

include hK hF hs hd hL hLi hS

theorem aLoc_eq_roL {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (h𝔭 : 𝔭 ∉ S) {n : 𝓞 F} (hn : n ≠ 0) :
    aLoc h L 𝔭 n = roL h L S 𝔭 (valF n 𝔭) := by
  have hv : vd h L 𝔭.1 = 0 := by
    by_contra hne
    exact h𝔭 (hS 𝔭 hne)
  obtain ⟨hn', hvn'⟩ := (exists_vF_eq 𝔭.2 (valF n 𝔭)).choose_spec
  rw [roL, if_neg h𝔭]
  unfold aLoc
  rw [alphaN_eq_of_vF_eq hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi 𝔭.2 hv hn hn' (by rw [hvn', valF_apply hn])]

include hm

theorem roL_zero (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) : roL h L S 𝔭 0 = 1 := by
  by_cases h𝔭 : 𝔭 ∈ S
  · rw [roL, if_pos h𝔭]
  · have hv : vd h L 𝔭.1 = 0 := by
      by_contra hne
      exact h𝔭 (hS 𝔭 hne)
    obtain ⟨hn', hvn'⟩ := (exists_vF_eq 𝔭.2 0).choose_spec
    have hn𝔭 : (exists_vF_eq 𝔭.2 0).choose ∉ 𝔭.1 := by
      intro hmem
      have := (mem_pow_iff_le_vF 𝔭.2 hn' 1).mp (by rw [pow_one]; exact hmem)
      omega
    rw [roL, if_neg h𝔭]
    unfold aLoc
    rw [unitaryAbsoluteValueBounds.alphaN_unit hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi 𝔭.2 hv (by omega) hn𝔭]
    have he := eFac_pos (K := K) 𝔭.2 (m := finrank K V) (by omega)
    unfold eFac at he ⊢
    exact div_self he.ne'

theorem roL_diff (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (j : ℕ) :
    |roL h L S 𝔭 (j + 1) - roL h L S 𝔭 j| ≤
      8 * ((j : ℝ) + 2) ^ 2 / (Ideal.absNorm 𝔭.1 : ℝ) := by
  by_cases h𝔭 : 𝔭 ∈ S
  · have h1 : ∀ i, roL h L S 𝔭 i = 1 := fun i => by rw [roL, if_pos h𝔭]
    rw [h1, h1, sub_self, abs_zero]
    positivity
  · have hv : vd h L 𝔭.1 = 0 := by
      by_contra hne
      exact h𝔭 (hS 𝔭 hne)
    have hro : ∀ i, roL h L S 𝔭 i = aLoc h L 𝔭 (exists_vF_eq 𝔭.2 i).choose := fun i => by
      rw [roL, if_neg h𝔭]
    obtain ⟨hn1, hv1⟩ := (exists_vF_eq 𝔭.2 (j + 1)).choose_spec
    obtain ⟨hn0, hv0⟩ := (exists_vF_eq 𝔭.2 j).choose_spec
    rw [hro, hro]
    unfold aLoc eFac
    have hb := alphaN_rho_diff_bound hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm 𝔭.2 hv hn1 hn0 (by rw [hv1, hv0])
    refine hb.trans ?_
    rw [hv1]

    have key : ∀ e : ℕ, 1 ≤ e → 8 * (((j + 1 : ℕ) : ℝ) + 1) ^ 2 *
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(e : ℤ)) ≤ 8 * ((j : ℝ) + 2) ^ 2 / (Ideal.absNorm 𝔭.1 : ℝ) := by
      intro e he
      have hj : (((j + 1 : ℕ) : ℝ) + 1) = (j : ℝ) + 2 := by push_cast; ring
      rw [hj, div_eq_mul_inv]
      rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔭.1) with h0 | hpos
      · rw [h0, Nat.cast_zero, zero_zpow _ (by omega), inv_zero]
      · have hx : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast hpos
        have hz : (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(e : ℤ)) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ hx (by omega)
        rw [zpow_neg_one] at hz
        exact mul_le_mul_of_nonneg_left hz (by positivity)
    exact key _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))

omit hm in
theorem prod_aLoc {U : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (hU : S ⊆ U) {n : 𝓞 F}
    (hn : n ≠ 0) :
    ∏ 𝔭 ∈ U, aLoc h L 𝔭 n = (∏ 𝔭 ∈ S, aLoc h L 𝔭 n) * ∏ 𝔭 ∈ U, roL h L S 𝔭 (valF n 𝔭) := by
  rw [← Finset.prod_sdiff hU (f := fun 𝔭 => aLoc h L 𝔭 n),
    ← Finset.prod_sdiff hU (f := fun 𝔭 => roL h L S 𝔭 (valF n 𝔭))]
  have h1 : ∏ 𝔭 ∈ S, roL h L S 𝔭 (valF n 𝔭) = 1 :=
    Finset.prod_eq_one fun 𝔭 h𝔭 => by rw [roL, if_pos h𝔭]
  have h2 : ∏ 𝔭 ∈ U \ S, aLoc h L 𝔭 n = ∏ 𝔭 ∈ U \ S, roL h L S 𝔭 (valF n 𝔭) :=
    Finset.prod_congr rfl fun 𝔭 h𝔭 =>
      aLoc_eq_roL (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) (Finset.mem_sdiff.mp h𝔭).2 hn
  rw [h1, h2, mul_one, mul_comm]

theorem singS_eq {n : 𝓞 F} (hn : n ≠ 0) :
    singS F h L n = (∏ 𝔭 ∈ S, aLoc h L 𝔭 n) * (valF n).prod (roL h L S) := by
  classical
  have hz : ∀ 𝔭, roL h L S 𝔭 0 = 1 := fun 𝔭 => roL_zero (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hm := hm) (hS := hS) 𝔭
  have e1 : singS F h L n = ∏' 𝔭, aLoc h L 𝔭 n := rfl
  have hsup : (valF n).support ⊆ S ∪ (valF n).support := Finset.subset_union_right
  rw [e1, tprod_eq_prod (s := S ∪ (valF n).support) ?_,
    prod_aLoc (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) Finset.subset_union_left hn,
    Finsupp.prod_of_support_subset _ hsup _ (fun 𝔭 _ => hz 𝔭)]
  intro 𝔭 h𝔭
  rw [Finset.mem_union, not_or] at h𝔭
  have h0 : valF n 𝔭 = 0 := by
    by_contra hne
    exact h𝔭.2 (Finsupp.mem_support_iff.mpr hne)
  rw [aLoc_eq_roL (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) h𝔭.1 hn, h0, hz]

omit hS in
theorem prodS_bound (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ C : ℝ, ∀ n : 𝓞 F, n ≠ 0 →
      0 ≤ ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ∧ ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ≤ C := by
  have hm1 : 1 ≤ finrank K V := by omega
  choose C hC using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    alphaN_bound hK hF hs hd hL hLi hm 𝔭.2
  refine ⟨∏ 𝔭 ∈ S, C 𝔭 / eFac K (finrank K V) 𝔭.1, fun n hn => ?_⟩
  have hpos : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 0 < eFac K (finrank K V) 𝔭.1 :=
    fun 𝔭 => eFac_pos 𝔭.2 hm1
  have h0 : ∀ 𝔭 ∈ S, 0 ≤ aLoc h L 𝔭 n := fun 𝔭 _ => div_nonneg (hC 𝔭 n hn).1 (hpos 𝔭).le
  refine ⟨Finset.prod_nonneg h0, Finset.prod_le_prod₀ h0 fun 𝔭 _ => ?_⟩
  exact div_le_div_of_nonneg_right (hC 𝔭 n hn).2 (hpos 𝔭).le

end Formalism.HermitianLattices.Ext.L3.A5
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CoeMemOfMemSmulTop
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

theorem relIndex_eq_card_image {G α : Type*} [Group G] (H S : Subgroup G) (f : G → α)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b ↔ a⁻¹ * b ∈ H) :
    H.relIndex S = Nat.card {c : α // ∃ a ∈ S, f a = c} := by
  classical
  show Nat.card (S ⧸ H.subgroupOf S) = _
  apply Nat.card_congr
  refine Equiv.ofBijective (fun q => Quotient.liftOn' q
    (fun a : S => (⟨f a, a, a.2, rfl⟩ : {c : α // ∃ a ∈ S, f a = c})) ?_) ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    show f a = f b
    have hab' : a⁻¹ * b ∈ H.subgroupOf S := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab'
    exact (hf a a.2 b b.2).mpr hab'
  · intro q₁ q₂ e
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    have e' : f a = f b := congrArg Subtype.val e
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hf a a.2 b b.2).mp e'
  · rintro ⟨c, a, ha, rfl⟩
    exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (a b : V ≃ₗ[K] V) (B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap a B = Formalism.HermitianLatticesTheory.gmap b B ↔ a⁻¹ * b ∈ glSub B := by
  rw [mem_glSub]
  constructor
  · intro e
    rw [autSub_gmap_mul, ← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro e
    rw [show b = a * (a⁻¹ * b) from (mul_inv_cancel_left a b).symm, autSub_gmap_mul a, e]

theorem autSub_le_sSub (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    autSub h A ≤ sSub h A 𝔭 k := fun X hX => ⟨hX.2, fun x _ y _ => by
  rw [hX.1 x y, sub_self]
  exact Submodule.zero_mem _⟩

theorem coe_mem_of_mem_smul_top (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) {u : ↥A}
    (hu : u ∈ (I • ⊤ : Submodule (𝓞 K) ↥A)) : (u : V) ∈ I • A := by
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) hu
  rwa [Submodule.map_smul'', Submodule.map_subtype_top] at h2

theorem exists_autSub_mul_nSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k) {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), g⁻¹ * X ∈ nSub (locF 𝔭 A₀) 𝔭 (k - eA h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨hXg, hXh⟩ := hX
  set A := locF 𝔭 A₀ with hA
  let f : ↥A →ₗ[𝓞 K] ↥A :=
    (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).domRestrict A).codRestrict A
      (fun x => apply_mem hXg x.2)
  have hf : ∀ x : ↥A, ((f x : ↥A) : V) = X x := fun x => rfl
  let Xb : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
    Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)
  have key : ∀ x x' : ↥A, Submodule.Quotient.mk x' = Xb (Submodule.Quotient.mk x) →
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
    intro x x' hx
    have h1 : x' - f x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
      rw [← Submodule.Quotient.eq]
      exact hx
    exact coe_mem_of_mem_smul_top _ _ h1
  have h0 : ∀ {z : V}, z ∈ A → z ∈ extP K 𝔭 ^ 0 • A := fun hz => by rwa [pow_zero_smul]
  let := hA₀
  obtain ⟨g, hg, hgX⟩ := exists_isom_lift hK hF hs hd (A₀ := A₀) inferInstance hA₀i h𝔭 hk Xb (by
    intro x y x' y' hx hy
    rw [congrP_algebraMap_iff_sub_mem h𝔭]
    have hu := key x x' hx
    have hv := key y y' hy
    have e1 : h (x' : V) (y' : V) - h (x : V) (y : V) =
        (h (X x) (X y) - h (x : V) (y : V)) + h ((x' : V) - X x) (y' : V)
          + h (X x) ((y' : V) - X y) := by
      simp only [map_sub, LinearMap.sub_apply]
      ring
    rw [e1]
    refine add_mem (add_mem (hXh x x.2 y y.2) ?_) ?_
    · simpa using form_mem_pK hF hA₀i h𝔭 hu (h0 y'.2)
    · simpa using form_mem_pK hF hA₀i h𝔭 (h0 (apply_mem hXg x.2)) hv)
  refine ⟨g, hg, mul_mem (inv_mem hg.2) hXg, fun x hx => ?_⟩
  have h1 := hgX ⟨x, hx⟩ (f ⟨x, hx⟩) rfl
  have h2 := apply_mem_smul (inv_mem (show g ∈ glSub A from hg.2)) _ ((Submodule.neg_mem _ h1))
  have e : ∀ z : V, g⁻¹ (g z) = z := fun z => by
    rw [← mul_apply_eq_comp, inv_mul_cancel]
    rfl
  simpa [e, hf] using h2

theorem relIndex_inf_glSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) =
      orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) := by
  let := hA₀
  let := hB₀
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub (A₀ := A₀) (B₀ := B₀) inferInstance inferInstance h𝔭
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1 + k₁, fun k hk => ?_⟩
  rw [Subgroup.inf_relIndex_left,
    relIndex_eq_card_image _ _ (fun X => Formalism.HermitianLatticesTheory.gmap X (locF 𝔭 B₀))
      (fun a _ b _ => gmap_eq_iff a b _)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ⟨?_, ?_⟩)
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨g, hg, hY⟩ := exists_autSub_mul_nSub hK hF hs hd hA₀ hA₀i h𝔭 (by omega) hX
    exact ⟨g, hg.1, hg.2, (gmap_eq_iff g X _).2 (hk₁ _ (by omega) hY)⟩
  · rintro ⟨g, hg, hgA, rfl⟩
    exact ⟨g, autSub_le_sSub h _ 𝔭 k ⟨hg, hgA⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.D2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulSpanIff
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

open LocalSpans in
theorem exists_smith {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀)
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (a b : Basis (Fin (finrank K V)) K V) (e : Fin (finrank K V) → 𝓞 K) (c : 𝓞 K),
      c ≠ 0 ∧ (∀ i, e i ≠ 0) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) = locF 𝔭 A₀ ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 B₀ ∧ ∀ i, c • b i = e i • a i := by
  have : 𝔭.IsPrime := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := fun h => RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h ▸ h𝔭))
  have : IsDedekindDomain (RP K 𝔭) := IsLocalization.isDedekindDomain (𝓞 K) (sF_le 𝔭) _
  have : IsPrincipalIdealRing (RP K 𝔭) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) 𝔭 hp0
  obtain ⟨a0, -, ha0⟩ := exists_basis_locF hA₀ h𝔭
  obtain ⟨b0, -, hb0⟩ := exists_basis_locF hB₀ h𝔭

  obtain ⟨⟨c, hc⟩, hcint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun p : Fin (finrank K V) × Fin (finrank K V) => a0.repr (b0 p.1) p.2)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by
    simpa using hc0
  let MA : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (Set.range a0)
  let MB : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (Set.range b0)
  let μ : V →ₗ[RP K 𝔭] V := ((algebraMap (𝓞 K) K c) • (LinearMap.id : V →ₗ[K] V)).restrictScalars (RP K 𝔭)
  have hμ : ∀ x, μ x = algebraMap (𝓞 K) K c • x := fun x => rfl
  have hμi : Function.Injective μ := fun x y hxy => by
    rw [hμ, hμ] at hxy
    exact smul_right_injective V hcK hxy
  let N' : Submodule (RP K 𝔭) V := MB.map μ
  have hN' : N' ≤ MA := by
    show Submodule.map μ (Submodule.span _ _) ≤ MA
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hμ, ← a0.sum_repr (b0 i), Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨z, hz⟩ := hcint (i, j)
    rw [smul_smul]
    have : algebraMap (𝓞 K) K c * a0.repr (b0 i) j = algebraMap (𝓞 K) K z := by
      rw [hz, Algebra.smul_def]
    rw [this, algebraMap_smul, ← algebraMap_smul (RP K 𝔭)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hliA : LinearIndependent (RP K 𝔭) a0 := a0.linearIndependent.restrict_scalars' (RP K 𝔭)
  have hliB : LinearIndependent (RP K 𝔭) b0 := b0.linearIndependent.restrict_scalars' (RP K 𝔭)
  have hfA : finrank (RP K 𝔭) MA = finrank K V := by
    rw [finrank_span_eq_card hliA, Fintype.card_fin]
  have hfB : finrank (RP K 𝔭) MB = finrank K V := by
    rw [finrank_span_eq_card hliB, Fintype.card_fin]
  let N : Submodule (RP K 𝔭) MA := N'.comap MA.subtype
  have hfN : finrank (RP K 𝔭) N = finrank (RP K 𝔭) MA := by
    rw [hfA, ← hfB, (Submodule.comapSubtypeEquivOfLe hN').finrank_eq,
      (Submodule.equivMapOfInjective μ hμi MB).finrank_eq]
  obtain ⟨b', α, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq (Basis.span hliA) hfN
  have hlatA : Submodule.IsFullLattice K MA :=
    { toIsLattice := Submodule.IsLattice.of_fg K (Submodule.fg_span (Set.finite_range _))
      span_eq_top := by
        change Submodule.span K (Submodule.span (RP K 𝔭) (Set.range a0) : Set V) = ⊤
        rw [Submodule.span_span_of_tower, a0.span_eq] }
  let a := b'.extendOfIsLattice K
  have ha : ∀ i, a i = (b' i : V) := fun i => Basis.extendOfIsLattice_apply K b' i
  have hα0 : ∀ i, α i ≠ 0 := fun i h0 => by
    have h1 := hab i
    rw [h0, zero_smul] at h1
    exact ab'.ne_zero i (Subtype.ext h1)
  have hα : ∀ i, ∃ (z : 𝓞 K) (t : 𝓞 F), t ∉ 𝔭 ∧ (α i : K) =
      algebraMap (𝓞 K) K z * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ := fun i => by
    obtain ⟨z, s, ⟨t, ht, rfl⟩, hz⟩ := (α i).2
    exact ⟨z, t, ht, hz⟩
  choose e t ht he using hα
  have ht0 : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) ≠ 0 := by
    intro i h0
    have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
    have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
    exact ht i (h2 ▸ 𝔭.zero_mem)
  have he0 : ∀ i, e i ≠ 0 := fun i h0 => hα0 i (Subtype.ext (by rw [he, h0]; simp))
  have heK : ∀ i, algebraMap (𝓞 K) K (e i) ≠ 0 := fun i => by
    simpa using he0 i
  let b := a.unitsSMul fun i => Units.mk0 (algebraMap (𝓞 K) K (e i) * (algebraMap (𝓞 K) K c)⁻¹)
    (mul_ne_zero (heK i) (inv_ne_zero hcK))
  have hb : ∀ i, b i = (algebraMap (𝓞 K) K (e i) * (algebraMap (𝓞 K) K c)⁻¹) • a i := fun i => by
    rw [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hcb : ∀ i, algebraMap (𝓞 K) K c • b i = algebraMap (𝓞 K) K (e i) • a i := fun i => by
    rw [hb, smul_smul, mul_comm, mul_assoc, inv_mul_cancel₀ hcK, mul_one]
  have habV : ∀ i, (((ab' i : N) : MA) : V) = (α i : K) • a i := fun i => by
    rw [hab, ha]
    rfl
  have hτ : ∀ i, μ (b i) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) • (((ab' i : N) : MA) : V) :=
    fun i => by
      rw [hμ, hcb, habV, he, smul_smul, mul_comm, mul_assoc, inv_mul_cancel₀ (ht0 i), mul_one]
  have hsA : Submodule.span (RP K 𝔭) (Set.range a) = MA := by
    have h1 : Set.range a = MA.subtype '' Set.range b' := by
      rw [← Set.range_comp]
      exact congrArg _ (funext ha)
    rw [h1, ← Submodule.map_span, b'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsN : Submodule.span (RP K 𝔭) (Set.range fun i => (((ab' i : N) : MA) : V)) = N' := by
    have h1 : (Set.range fun i => (((ab' i : N) : MA) : V)) =
        MA.subtype '' (N.subtype '' Set.range ab') := by
      rw [← Set.range_comp, ← Set.range_comp]
      rfl
    rw [h1, ← Submodule.map_span, ← Submodule.map_span, ab'.span_eq, Submodule.map_top,
      Submodule.range_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hN']
  have hsB : Submodule.span (RP K 𝔭) (Set.range b) = MB := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨y, hy, hyx⟩ : (((ab' i : N) : MA) : V) ∈ N' := (ab' i).2
      have h1 : μ (b i) = μ (algebraMap (𝓞 F) (𝓞 K) (t i) • y) := by
        rw [hτ, ← hyx, hμ, hμ, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t i)), smul_comm]
      rw [hμi h1, ← algebraMap_smul (RP K 𝔭)]
      exact Submodule.smul_mem _ _ hy
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h1 : μ (b0 j) ∈ N' := ⟨b0 j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
      have h2 : N' ≤ (Submodule.span (RP K 𝔭) (Set.range b)).map μ := by
        rw [← hsN, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        let u : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)))⁻¹,
          ⟨1, _, ⟨t i, ht i, rfl⟩, by simp⟩⟩
        refine ⟨u • b i, Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
        rw [map_smul, hτ, Subalgebra.smul_def, smul_smul, inv_mul_cancel₀ (ht0 i), one_smul]
      obtain ⟨y, hy, hyx⟩ := h2 h1
      exact hμi hyx ▸ hy
  refine ⟨a, b, e, c, hc0, he0, ?_, ?_, fun i => ?_⟩
  · rw [← ha0]
    ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Submodule.span_span_of_tower, hsA]
  · rw [← hb0]
    ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Submodule.span_span_of_tower, hsB]
  · rw [← algebraMap_smul K, ← algebraMap_smul K (e i), hcb]

theorem basis_mem_locF {κ : Type} (a : Basis κ K V) (𝔭 : Ideal (𝓞 F)) (i : κ) :
    a i ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) :=
  LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)

theorem repr_mem_pK_zero {κ : Type} (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {x : V} (hx : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) (i : κ) :
    a.repr x i ∈ pK K 𝔭 0 := by
  obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).1 hx
  obtain ⟨z, hz⟩ := (a.mem_span_iff_repr_mem (𝓞 K) _).1 hx i
  refine (mem_pK h𝔭).2 ⟨t, ht, z, by simp, ?_⟩
  rw [hz, ← algebraMap_smul K, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rfl

theorem mem_smul_span_iff {κ : Type} [Fintype κ] (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (x : V) :
    x ∈ extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) ↔
      ∀ i, a.repr x i ∈ pK K 𝔭 k := by
  constructor
  · intro hx i
    induction hx using Submodule.smul_induction_on' with
    | smul r hr n hn =>
      have h1 : algebraMap (𝓞 K) K r ∈ pK K 𝔭 k := LocF.le_locF 𝔭 _ ⟨r, hr, rfl⟩
      have h2 := mul_mem_pK h𝔭 h1 (repr_mem_pK_zero a h𝔭 hn i)
      rw [← algebraMap_smul K, map_smul, Finsupp.smul_apply, smul_eq_mul]
      simpa using h2
    | add x _ y _ hx hy =>
      rw [map_add (f := _), Finsupp.add_apply]
      exact (pK K 𝔭 k).add_mem hx hy
  · intro hx
    rw [← a.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h0 : a i ∈ extP K 𝔭 ^ 0 • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) := by
      rw [pow_zero_smul]
      exact basis_mem_locF a 𝔭 i
    simpa using smul_mem_smul h𝔭 _ (hx i) h0

theorem mem_endL_iff {κ : Type} [Fintype κ] [DecidableEq κ] (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (D : V →ₗ[K] V) :
    D ∈ endL (locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)))
        (extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) ↔
      ∀ i j, LinearMap.toMatrix a a D i j ∈ pK K 𝔭 k := by
  constructor
  · intro hD i j
    rw [LinearMap.toMatrix_apply]
    exact (mem_smul_span_iff a h𝔭 k _).1 (hD _ (basis_mem_locF a 𝔭 j)) i
  · intro hD x hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← a.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    have h1 : D (a j) ∈ extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) :=
      (mem_smul_span_iff a h𝔭 k _).2 fun i => by
        rw [← LinearMap.toMatrix_apply]
        exact hD i j
    simpa using smul_mem_smul h𝔭 _ (repr_mem_pK_zero a h𝔭 hx j) h1

theorem mem_sesqL_iff (hF : IsFixF K F) {κ : Type} [Fintype κ] (a : Basis κ K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (s : V →ₗ⋆[K] V →ₗ[K] K) :
    s ∈ sesqL (locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) 𝔭 k ↔
      ∀ i j, s (a i) (a j) ∈ pK K 𝔭 k := by
  constructor
  · intro hs i j
    exact hs _ (basis_mem_locF a 𝔭 i) _ (basis_mem_locF a 𝔭 j)
  · intro hs x hx y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← a.sum_repr x, ← a.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    have h1 := mul_mem_pK h𝔭 (repr_mem_pK_zero a h𝔭 hy j)
      (mul_mem_pK h𝔭 (star_mem_pK hF h𝔭 (repr_mem_pK_zero a h𝔭 hx i)) (hs i j))
    rw [zero_add, zero_add] at h1
    exact h1

end Formalism.HermitianLattices.Ext.L3.D2
end
end

