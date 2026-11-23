module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomFrame
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0011
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsRepsOfCover
section
open Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbSum

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

theorem exists_reps_of_cover (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (C : Set X)
    (hC : C.Finite) (hCA : ∀ c ∈ C, c ∈ A) (hcov : ∀ x ∈ A, ∃ c ∈ C, ∃ g : G, g • c = x) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let rep : X → X := fun x => (Quotient.mk (MulAction.orbitRel G X) x).out
  have hrep : ∀ x, ∃ g : G, g • x = rep x := fun x => by
    have h1 : Quotient.mk (MulAction.orbitRel G X) (rep x) = Quotient.mk _ x := Quotient.out_eq _
    have h2 : rep x ∈ MulAction.orbit G x := Quotient.exact h1
    exact MulAction.mem_orbit_iff.1 h2
  have hrepA : ∀ x ∈ A, rep x ∈ A := fun x hx => by
    obtain ⟨g, hg⟩ := hrep x
    rw [← hg]
    exact hA g x hx
  have hrep_eq : ∀ x y : X, ∀ g : G, g • y = x → rep y = rep x := fun x y g hg => by
    show (Quotient.mk (MulAction.orbitRel G X) y).out = (Quotient.mk (MulAction.orbitRel G X) x).out
    congr 1
    apply Quotient.sound
    show y ∈ MulAction.orbit G x
    rw [MulAction.mem_orbit_iff]
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  refine ⟨hC.toFinset.image rep, ?_, ?_⟩
  · intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ht
    exact hrepA c (hCA c (hC.mem_toFinset.1 hc))
  · intro x hx
    obtain ⟨c, hc, g, hg⟩ := hcov x hx
    obtain ⟨g', hg'⟩ := hrep c
    refine ⟨rep c, ⟨Finset.mem_image.2 ⟨c, hC.mem_toFinset.2 hc, rfl⟩, ⟨g * g'⁻¹, ?_⟩⟩, ?_⟩
    · rw [← hg', mul_smul, inv_smul_smul, hg]
    · rintro t ⟨ht, h, hh⟩
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨g'', hg''⟩ := hrep c'
      have e1 : rep c' = rep x := (hrep_eq (rep c') c' g'' hg'').trans (hrep_eq x (rep c') h hh)
      have e2 : rep c = rep x := hrep_eq x c g hg
      rw [e1, e2]

theorem card_stab_smul (g : G) (x : X) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_stab_sub (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : X) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G (π x)) x) =
      Nat.card (MulAction.stabilizer G x) := Nat.card_congr
  { toFun := fun h => ⟨h.1.1, h.2⟩
    invFun := fun g => ⟨⟨g.1, by
      show g.1 • π x = π x
      rw [← hπ]
      exact congrArg π g.2⟩, g.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem sum_orbits_on (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (B : Set Y)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (hAB : ∀ x ∈ A, π x ∈ B)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ t ∈ sX, t ∈ A) (hsY : ∀ u ∈ sY, u ∈ B)
    (hX : ∀ x ∈ A, ∃! t : X, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ B, ∃! t : Y, t ∈ sY ∧ ∃ g : G, g • t = y)
    (hfinY : ∀ y ∈ B, (MulAction.stabilizer G y : Set G).Finite) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer G t) : ℕ) : ℝ)⁻¹ =
      ∑ u ∈ sY, (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) /
        (Nat.card (MulAction.stabilizer G u) : ℝ) := by
  classical
  have key : ∀ t : X, ∃ (u : Y) (g : G), t ∈ A → (u ∈ sY ∧ g • u = π t) := by
    intro t
    by_cases ht : t ∈ A
    · obtain ⟨u, ⟨hu, g, hg⟩, -⟩ := hY (π t) (hAB t ht)
      exact ⟨u, g, fun _ => ⟨hu, hg⟩⟩
    · exact ⟨π t, 1, fun h => absurd h ht⟩
  choose U γ hU using key
  have hπ' : ∀ t ∈ A, π ((γ t)⁻¹ • t) = U t := by
    intro t ht
    rw [hπ, ← (hU t ht).2, inv_smul_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := sX) (t := sY) (g := U)
    (fun t ht => (hU t (hsX t ht)).1)]
  refine Finset.sum_congr rfl fun u hu => ?_
  set T : Finset X := (sX.filter (fun t => U t = u)).image (fun t => (γ t)⁻¹ • t) with hTdef
  have hinj : Set.InjOn (fun t => (γ t)⁻¹ • t) (sX.filter (fun t => U t = u) : Set X) := by
    intro t₁ h₁ t₂ h₂ e
    have h₁' := (Finset.mem_filter.mp h₁).1
    have h₂' := (Finset.mem_filter.mp h₂).1
    exact (hX _ (hA (γ t₁)⁻¹ t₁ (hsX t₁ h₁'))).unique ⟨h₁', _, rfl⟩ ⟨h₂', _, e.symm⟩
  have hstab : ∀ g : MulAction.stabilizer G u, ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      g • x ∈ {x : X | x ∈ A ∧ π x = u} := by
    rintro ⟨g, hg⟩ x ⟨hx1, hx2⟩
    refine ⟨hA g x hx1, ?_⟩
    change π (g • x) = u
    rw [hπ, hx2]
    exact MulAction.mem_stabilizer_iff.mp hg
  have hTA : ∀ t ∈ T, t ∈ {x : X | x ∈ A ∧ π x = u} := by
    intro t ht
    obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h₁, rfl⟩ := Finset.mem_filter.mp h₀
    exact ⟨hA _ _ (hsX t₀ h₁), hπ' t₀ (hsX t₀ h₁)⟩
  have hT : ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      ∃! t, t ∈ T ∧ ∃ g : MulAction.stabilizer G u, g • t = x := by
    rintro x ⟨hx1, hx2⟩
    obtain ⟨t, ⟨ht, g, hg⟩, huniq⟩ := hX x hx1
    have htA := hsX t ht
    have e1 : (g * γ t) • U t = u := by
      rw [mul_smul, (hU t htA).2, ← hπ, hg, hx2]
    have hUt : U t = u :=
      (hY u (hsY u hu)).unique ⟨(hU t htA).1, _, e1⟩ ⟨hu, 1, one_smul _ _⟩
    refine ⟨(γ t)⁻¹ • t, ⟨Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hUt⟩, rfl⟩,
      ⟨g * γ t, MulAction.mem_stabilizer_iff.mpr (by rw [← hUt] at e1 ⊢; exact e1)⟩, ?_⟩, ?_⟩
    · change (g * γ t) • (γ t)⁻¹ • t = x
      rw [mul_smul, smul_inv_smul, hg]
    · rintro t' ⟨ht', ⟨g', hg'm⟩, hg'⟩
      obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht'
      have h₀' := (Finset.mem_filter.mp h₀).1
      have : t₀ = t := huniq t₀ ⟨h₀', g' * (γ t₀)⁻¹, by rw [mul_smul]; exact hg'⟩
      rw [this]
  have hfinG : Finite (MulAction.stabilizer G u) := (hfinY u (hsY u hu)).to_subtype
  have hfinA : Finite ↥{x : X | x ∈ A ∧ π x = u} := by
    apply Set.Finite.to_subtype
    refine ((T : Set X).toFinite.biUnion
      (fun t _ => Set.finite_range (fun g : MulAction.stabilizer G u => g • t))).subset ?_
    intro x hx
    obtain ⟨t, ⟨ht, g, hg⟩, -⟩ := hT x hx
    exact Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨g, hg⟩
  have main := sum_inv_card_stab (G := MulAction.stabilizer G u) {x : X | x ∈ A ∧ π x = u}
    hstab T hTA hT
  have e0 : (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) =
      (Nat.card ↥{x : X | x ∈ A ∧ π x = u} : ℝ) := rfl
  rw [e0, main, hTdef, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨ht1, rfl⟩ := Finset.mem_filter.mp ht
  have := card_stab_sub π hπ ((γ t)⁻¹ • t)
  rw [hπ' t (hsX t ht1)] at this
  rw [this, card_stab_smul]

end OrbSum

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_loc {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) {m : V} (hm : m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    a • m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).mp ha
  obtain ⟨t, ht, htm⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hm
  refine Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s * t, mul_mem hs ht, ?_⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have : (s * t) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • m) = r • (t • m) := by
    rw [← algebraMap_smul K (s * t), ← algebraMap_smul K r, ← algebraMap_smul K t, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp
  rw [this]
  exact L.smul_mem r htm

theorem isSelfDualMod_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) {p : Ideal (𝓞 K)} (hp : p.IsPrime)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    IsSelfDualMod (locRing p) h (Formalism.HermitianLatticesTheory.loc (K := K) p L).toAddSubgroup := by
  have hu' : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L ↔
      ∀ y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L, h y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
    intro x
    rw [← Formalism.HermitianLatticesTheory.locDual_mem_dualAt]
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hu
    rw [hu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    exact smul_mem_loc hp ha hm
  · intro x hx y hy
    exact (hu' y).mp hy x hx
  · intro x hx
    exact (hu' x).mpr hx
  · intro x
    obtain ⟨n, hn, hnx⟩ := Formalism.HermitianLatticesTheory.traceReal_mult L hL x
    refine ⟨(n : K), by exact_mod_cast hn, ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ L hnx

end Formalism.HermitianLattices.Ext.L3.WA
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtAdjoinIff
section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

structure VecSplit (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) where
  x₀ : V
  ι : V' →ₗ[K] V
  inj : Function.Injective ι
  hx₀ : h x₀ x₀ ≠ 0
  isom : ∀ a b, h (ι a) (ι b) = h' a b
  orth : ∀ a, h x₀ (ι a) = 0
  cover : ∀ v, ∃ (c : K) (a : V'), v = c • x₀ + ι a

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def VecSplit.adjoin (S : VecSplit h h') (L' : Submodule (𝓞 K) V') : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) {S.x₀} ⊔ L'.map (S.ι.restrictScalars (𝓞 K))

def VecSplit.cut (S : VecSplit h h') (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V' :=
  L.comap (S.ι.restrictScalars (𝓞 K))

namespace VecSplit

variable (S : VecSplit h h')

theorem h_x₀_comb (c : K) (a : V') : h S.x₀ (c • S.x₀ + S.ι a) = c * h S.x₀ S.x₀ := by
  rw [map_add (f := _), map_smul, S.orth a, smul_eq_mul, add_zero]

theorem comb_eq_iff {c c' : K} {a a' : V'} :
    c • S.x₀ + S.ι a = c' • S.x₀ + S.ι a' ↔ c = c' ∧ a = a' := by
  constructor
  · intro he
    have hc : c = c' := by
      have := congrArg (h S.x₀) he
      rw [S.h_x₀_comb, S.h_x₀_comb] at this
      exact mul_right_cancel₀ S.hx₀ this
    subst hc
    exact ⟨rfl, S.inj (add_left_cancel he)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem x₀_not_mem_range (a : V') : S.ι a ≠ S.x₀ := by
  intro he
  apply S.hx₀
  have := S.orth a
  rwa [he] at this

theorem mem_adjoin_iff (L' : Submodule (𝓞 K) V') (v : V) :
    v ∈ S.adjoin L' ↔ ∃ (r : 𝓞 K) (a : V'), a ∈ L' ∧ v = (algebraMap (𝓞 K) K r) • S.x₀ + S.ι a := by
  unfold VecSplit.adjoin
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
    exact ⟨r, a, ha, by simp only [algebraMap_smul, LinearMap.coe_restrictScalars]⟩
  · rintro ⟨r, a, ha, rfl⟩
    exact ⟨r • S.x₀, Submodule.mem_span_singleton.mpr ⟨r, rfl⟩, S.ι a,
      Submodule.mem_map.mpr ⟨a, ha, rfl⟩, by simp only [algebraMap_smul, LinearMap.coe_restrictScalars]⟩

theorem x₀_mem_adjoin' (L' : Submodule (𝓞 K) V') : S.x₀ ∈ S.adjoin L' := by
  unfold VecSplit.adjoin
  exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)

theorem mem_cut_iff (L : Submodule (𝓞 K) V) (a : V') : a ∈ S.cut L ↔ S.ι a ∈ L := Iff.rfl

theorem cut_adjoin' (L' : Submodule (𝓞 K) V') : S.cut (S.adjoin L') = L' := by
  ext a
  rw [S.mem_cut_iff, S.mem_adjoin_iff]
  constructor
  · rintro ⟨r, b, hb, he⟩
    have h0 : (0 : K) • S.x₀ + S.ι a = (algebraMap (𝓞 K) K r) • S.x₀ + S.ι b := by
      rw [zero_smul, zero_add]
      exact he
    rw [(S.comb_eq_iff.mp h0).2]
    exact hb
  · intro ha
    exact ⟨0, a, ha, by simp⟩

theorem adjoin_cut' (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L) : S.adjoin (S.cut L) = L := by
  apply le_antisymm
  · unfold VecSplit.adjoin VecSplit.cut
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) (Submodule.map_comap_le _ _)
  · intro v hv
    obtain ⟨c, a, rfl⟩ := S.cover v
    have hc : c ∈ (1 : Submodule (𝓞 K) K) := by
      have := hL S.x₀ hx _ hv
      rwa [S.h_x₀_comb, h1, mul_one] at this
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
    rw [S.mem_adjoin_iff]
    refine ⟨r, a, ?_, by rw [hr]⟩
    rw [S.mem_cut_iff]
    have e : S.ι a = (c • S.x₀ + S.ι a) - (algebraMap (𝓞 K) K r) • S.x₀ := by
      rw [hr]
      abel
    rw [e]
    refine L.sub_mem hv ?_
    rw [algebraMap_smul]
    exact L.smul_mem r hx

end VecSplit

namespace VecSplit

variable (S : VecSplit h h')

theorem orth' (hs : h.IsSymm) (a : V') : h (S.ι a) S.x₀ = 0 := by
  rw [← hs.eq S.x₀ (S.ι a), S.orth a, map_zero]

theorem h_comb (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1) (d c : K) (b a : V') :
    h (d • S.x₀ + S.ι b) (c • S.x₀ + S.ι a) = starRingEnd K d * c + h' b a := by
  simp [S.orth, S.orth' hs, S.isom, h1]

theorem star_alg_mem_one (r : 𝓞 K) : starRingEnd K (algebraMap (𝓞 K) K r) ∈ (1 : Submodule (𝓞 K) K) := by
  refine Submodule.mem_one.mpr ⟨⟨starRingEnd K (algebraMap (𝓞 K) K r), ?_⟩, rfl⟩
  exact (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom

theorem isLattice_adjoin_iff' (L' : Submodule (𝓞 K) V') :
    Submodule.IsLattice K (S.adjoin L') ↔ Submodule.IsLattice K L' := by
  constructor
  · intro hL
    have hFG : (L'.map (S.ι.restrictScalars (𝓞 K))).FG :=
      hL.fg.of_le (by unfold VecSplit.adjoin; exact le_sup_right)
    refine ⟨Submodule.fg_of_fg_map_injective (S.ι.restrictScalars (𝓞 K)) S.inj hFG, ?_⟩
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · intro hL
    refine ⟨?_, ?_⟩
    · unfold VecSplit.adjoin
      exact (Submodule.fg_span_singleton _).sup (hL.fg.map _)
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isIntegralLat_adjoin_iff' (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1) (L' : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsIntegralLat h' L' := by
  unfold Formalism.HermitianLatticesTheory.IsIntegralLat
  constructor
  · intro H b hb a ha
    have hb' : S.ι b ∈ S.adjoin L' := (S.mem_adjoin_iff L' _).mpr ⟨0, b, hb, by simp⟩
    have ha' : S.ι a ∈ S.adjoin L' := (S.mem_adjoin_iff L' _).mpr ⟨0, a, ha, by simp⟩
    rw [← S.isom]
    exact H _ hb' _ ha'
  · intro H x hx y hy
    obtain ⟨r, b, hb, rfl⟩ := (S.mem_adjoin_iff L' x).mp hx
    obtain ⟨r', a, ha, rfl⟩ := (S.mem_adjoin_iff L' y).mp hy
    rw [S.h_comb hs h1]
    refine Submodule.add_mem _ ?_ (H b hb a ha)
    obtain ⟨u, hu⟩ := Submodule.mem_one.mp (star_alg_mem_one r)
    exact Submodule.mem_one.mpr ⟨u * r', by rw [map_mul, hu]⟩

end VecSplit

namespace VecSplit

variable (S : VecSplit h h')

theorem smul_comb (s : 𝓞 K) (c : K) (a : V') :
    s • (c • S.x₀ + S.ι a) = (s • c) • S.x₀ + S.ι (s • a) := by
  rw [smul_add, smul_assoc, ← LinearMap.map_smul_of_tower]

theorem comb_mem_adjoin_iff (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ S.adjoin L' ↔ c ∈ (1 : Submodule (𝓞 K) K) ∧ a ∈ L' := by
  rw [S.mem_adjoin_iff]
  constructor
  · rintro ⟨r, b, hb, he⟩
    obtain ⟨rfl, rfl⟩ := S.comb_eq_iff.mp he
    exact ⟨Submodule.mem_one.mpr ⟨r, rfl⟩, hb⟩
  · rintro ⟨hc, ha⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    exact ⟨r, a, ha, rfl⟩

theorem comb_mem_loc_adjoin_iff (p : Ideal (𝓞 K)) (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L') ↔
      c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ∧ a ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L' := by
  simp only [Formalism.HermitianLatticesTheory.locR, Formalism.HermitianLatticesTheory.loc, Formalism.HermitianLatticesTheory.locS, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, hmem⟩
    rw [S.smul_comb, S.comb_mem_adjoin_iff] at hmem
    exact ⟨⟨s, hs, hmem.1⟩, ⟨s, hs, hmem.2⟩⟩
  · rintro ⟨⟨s₁, hs₁, h₁⟩, ⟨s₂, hs₂, h₂⟩⟩
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂, ?_⟩
    rw [S.smul_comb, S.comb_mem_adjoin_iff]
    refine ⟨?_, ?_⟩
    · rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ s₂ h₁
    · rw [mul_smul]
      exact L'.smul_mem s₁ h₂

end VecSplit

theorem VecSplit.cut_adjoin (S : VecSplit h h') (L' : Submodule (𝓞 K) V') :
    S.cut (S.adjoin L') = L' := S.cut_adjoin' L'

theorem VecSplit.adjoin_cut (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L) : S.adjoin (S.cut L) = L := S.adjoin_cut' h1 hL hx

theorem VecSplit.x₀_mem_adjoin (S : VecSplit h h') (L' : Submodule (𝓞 K) V') :
    S.x₀ ∈ S.adjoin L' := S.x₀_mem_adjoin' L'

theorem VecSplit.isLattice_adjoin_iff (S : VecSplit h h') (L' : Submodule (𝓞 K) V') :
    Submodule.IsLattice K (S.adjoin L') ↔ Submodule.IsLattice K L' := S.isLattice_adjoin_iff' L'

theorem VecSplit.isIntegralLat_adjoin_iff (hs : h.IsSymm) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1)
    (L' : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsIntegralLat h' L' := S.isIntegralLat_adjoin_iff' hs h1 L'

end Formalism.HermitianLattices.Ext.L3
end
end

