module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0012
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ConjOMemHcompl
section
open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.SplitA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjO_mem_hcompl (p : Ideal (𝓞 K)) {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have hle : Formalism.HermitianLatticesTheory.hcompl (K := K) p ≤
      (Formalism.HermitianLatticesTheory.hcompl (K := K) p).comap (conjO K).toMonoidHom := by
    unfold Formalism.HermitianLatticesTheory.hcompl
    rw [Submonoid.closure_le]
    rintro s ⟨hs1, hs2⟩
    rw [SetLike.mem_coe, Submonoid.mem_comap]
    apply Submonoid.subset_closure
    refine ⟨hs2 _ rfl, fun t ht => ?_⟩
    have hts : t = s := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [ht]
      exact star_star _
    rw [hts]; exact hs1
  exact hle hs

theorem one_mem_locR (p : Ideal (𝓞 K)) : (1 : K) ∈ Formalism.HermitianLatticesTheory.locR (K := K) p :=
  ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩

theorem star_mem_locR (p : Ideal (𝓞 K)) {c : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) :
    starRingEnd K c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  obtain ⟨s, hs, hc⟩ := hc
  refine ⟨conjO K s, conjO_mem_hcompl p hs, ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
  refine Submodule.mem_one.mpr ⟨conjO K r, ?_⟩
  rw [Algebra.smul_def] at hr ⊢
  show starRingEnd K (algebraMap (𝓞 K) K r) = _
  rw [hr, map_mul]
  rfl

theorem mul_mem_locR (p : Ideal (𝓞 K)) {c d : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hd : d ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) : c * d ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  obtain ⟨s, hs, hc⟩ := hc
  obtain ⟨t, ht, hd⟩ := hd
  refine ⟨s * t, Submonoid.mul_mem _ hs ht, ?_⟩
  obtain ⟨r₁, hr₁⟩ := Submodule.mem_one.mp hc
  obtain ⟨r₂, hr₂⟩ := Submodule.mem_one.mp hd
  refine Submodule.mem_one.mpr ⟨r₁ * r₂, ?_⟩
  rw [Algebra.smul_def] at hr₁ hr₂ ⊢
  rw [map_mul, hr₁, hr₂, map_mul]
  ring

theorem mem_dualAt_iff' {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (g : W →ₗ⋆[K] W →ₗ[K] K) (p : Ideal (𝓞 K))
    (M : Submodule (𝓞 K) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.dualAt g p M ↔ ∀ y ∈ M, g y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  unfold Formalism.HermitianLatticesTheory.dualAt
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

end Formalism.HermitianLattices.Ext.L3.SplitA
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomMapOfEq
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace WittTransvections

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def transv (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (ξ : K) : V →ₗ[K] V :=
  LinearMap.id - ξ • (h u).smulRight u

theorem transv_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (ξ : K) (v : V) :
    transv h u ξ v = v - (ξ * h u v) • u := by
  simp [transv, LinearMap.smulRight_apply, smul_smul]

theorem transv_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {ξ η : K}
    (hξ : ξ + η = ξ * η * h u u) : transv h u η ∘ₗ transv h u ξ = LinearMap.id := by
  ext v
  rw [LinearMap.comp_apply, transv_apply, transv_apply, LinearMap.id_apply]
  have e1 : h u (v - (ξ * h u v) • u) = h u v - ξ * h u v * h u u := by
    rw [map_sub, map_smul, smul_eq_mul, mul_assoc]
  rw [e1, sub_sub, ← add_smul]
  have hc : ξ * h u v + η * (h u v - ξ * h u v * h u u) = 0 := by linear_combination (h u v) * hξ
  rw [hc, zero_smul, sub_zero]

def transvEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (transv h u ξ) (transv h u (star ξ))
    (transv_comp h u (by rw [add_comm, mul_comm (star ξ)]; exact hξ)) (transv_comp h u hξ)

theorem transvEquiv_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) (v : V) :
    transvEquiv h u hξ v = v - (ξ * h u v) • u := transv_apply h u ξ v

theorem transvEquiv_isom {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {ξ : K}
    (hξ : ξ + star ξ = ξ * star ξ * h u u) (v w : V) :
    h (transvEquiv h u hξ v) (transvEquiv h u hξ w) = h v w := by
  rw [transvEquiv_apply, transvEquiv_apply]
  have h1 : star (h u v) = h v u := by rw [← starRingEnd_apply]; exact hs.eq u v
  simp only [map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    map_mul, starRingEnd_apply, star_mul', h1]
  linear_combination (-(h v u * h u w)) * hξ

end WittTransvections

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_isom_map_of_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : IsTotPosDef h) {x y : V} (hx : x ≠ 0) (hxy : h x x = h y y) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, g x = y := by
  by_cases hxy' : x = y
  · exact ⟨1, Subgroup.one_mem _, by rw [hxy']; rfl⟩
  have hu0 : x - y ≠ 0 := sub_ne_zero.2 hxy'
  have hsym : ∀ a b, starRingEnd K (h a b) = h b a := fun a b => hs.eq a b
  have hnz : ∀ v : V, v ≠ 0 → h v v ≠ 0 := by
    intro v hv h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd v hv φ
    rw [h0, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  have huu : h (x - y) (x - y) = starRingEnd K (h (x - y) x) + h (x - y) x := by
    rw [hsym]
    simp only [map_sub, LinearMap.sub_apply]
    rw [← hxy]
    ring
  have hux : h (x - y) x ≠ 0 := by
    intro h0
    apply hnz _ hu0
    rw [huu, h0, map_zero, add_zero]
  have hξ : (h (x - y) x)⁻¹ + star (h (x - y) x)⁻¹ =
      (h (x - y) x)⁻¹ * star (h (x - y) x)⁻¹ * h (x - y) (x - y) := by
    have hs' : star (h (x - y) x) ≠ 0 := by
      intro h0; exact hux (by simpa using congrArg star h0)
    have hs'' : starRingEnd K (h (x - y) x) ≠ 0 := by rwa [starRingEnd_apply]
    rw [huu, ← starRingEnd_apply, map_inv₀]
    field_simp
    try ring
  refine ⟨WittTransvections.transvEquiv h (x - y) hξ, fun v w => WittTransvections.transvEquiv_isom hs _ hξ v w, ?_⟩
  rw [WittTransvections.transvEquiv_apply, inv_mul_cancel₀ hux, one_smul, sub_sub_cancel]

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem sum_inv_card_stab {G X : Type*} [Group G] [Finite G] [MulAction G X] (A : Set X)
    [Finite A] (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (T : Finset X) (hTA : ∀ t ∈ T, t ∈ A)
    (hT : ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x) :
    (Nat.card A : ℝ) / (Nat.card G : ℝ) =
      ∑ t ∈ T, ((Nat.card (MulAction.stabilizer G t) : ℕ) : ℝ)⁻¹ := by
  classical
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hos : ∀ t : X, (Nat.card (MulAction.orbit G t) : ℝ) =
      Nat.card G / Nat.card (MulAction.stabilizer G t) := by
    intro t
    have h1 := (MulAction.stabilizer G t).card_mul_index
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h1
    have hs : (0 : ℝ) < Nat.card (MulAction.stabilizer G t) := by exact_mod_cast Nat.card_pos
    rw [eq_div_iff hs.ne', ← Nat.cast_mul, mul_comm, h1]
  obtain ⟨A', hA'⟩ : ∃ A' : Finset X, ∀ x, x ∈ A' ↔ x ∈ A :=
    ⟨(Set.toFinite A).toFinset, fun x => Set.Finite.mem_toFinset _⟩
  have hAeq : A = ↑A' := Set.ext fun x => (hA' x).symm
  have hcover : A' = T.biUnion (fun t => A'.filter (fun x => ∃ g : G, g • t = x)) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hx
      obtain ⟨t, ⟨htT, g, hg⟩, -⟩ := hT x ((hA' x).mp hx)
      exact ⟨t, htT, hx, g, hg⟩
    · rintro ⟨t, -, hx, -⟩
      exact hx
  have hdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ →
      Disjoint (A'.filter (fun x => ∃ g : G, g • t₁ = x)) (A'.filter (fun x => ∃ g : G, g • t₂ = x)) := by
    intro t₁ h₁ t₂ h₂ hne
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2
    obtain ⟨t, -, huniq⟩ := hT x ((hA' x).mp hx1.1)
    exact hne ((huniq t₁ ⟨h₁, hx1.2⟩).trans (huniq t₂ ⟨h₂, hx2.2⟩).symm)
  have hcard : ∀ t ∈ T, ((A'.filter (fun x => ∃ g : G, g • t = x)).card : ℝ) =
      Nat.card (MulAction.orbit G t) := by
    intro t ht
    have hset : MulAction.orbit G t = ↑(A'.filter (fun x => ∃ g : G, g • t = x)) := by
      ext x
      simp only [MulAction.mem_orbit_iff, Finset.coe_filter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨(hA' _).mpr (hA g t (hTA t ht)), g, rfl⟩
      · rintro ⟨-, g, rfl⟩
        exact ⟨g, rfl⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hsum : (A'.card : ℝ) = ∑ t ∈ T, (Nat.card (MulAction.orbit G t) : ℝ) := by
    rw [hcover, Finset.card_biUnion hdisj, Nat.cast_sum]
    exact Finset.sum_congr rfl hcard
  rw [hAeq, Nat.card_coe_set_eq, Set.ncard_coe_finset, hsum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [hos t, div_div, mul_comm, ← div_div, div_self hGpos.ne', one_div]

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem autSub_gmap_one (L : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  simp [Submodule.mem_map]

theorem autSub_gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  simp [Submodule.mem_map]

def autSub (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := Formalism.ThetaLiftIndependence.autL h L
  one_mem' := ⟨one_mem _, autSub_gmap_one L⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨mul_mem ha.1 hb.1, by rw [autSub_gmap_mul, hb.2, ha.2]⟩
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem ha.1, ?_⟩
    conv_lhs => rw [← ha.2]
    rw [← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnimodularOfMemGenusOrtho
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem loc_gmap (g : V ≃ₗ[K] V) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.loc (K := K) p (Formalism.HermitianLatticesTheory.gmap g L) = Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p L) := by
  have hsm : ∀ (s : 𝓞 K) (v : V), g (s • v) = s • g v := fun s v => by
    rw [← algebraMap_smul K s v, ← algebraMap_smul K s (g v), map_smul]
  unfold Formalism.HermitianLatticesTheory.loc Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.locS
  ext x
  simp only [Submodule.mem_map, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨s, hs, y, hy, hyx⟩
    refine ⟨g.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have e : s • g.symm x = y := g.injective (by rw [hsm, g.apply_symm_apply]; exact hyx.symm)
    rw [e]; exact hy
  · rintro ⟨z, ⟨s, hs, hz⟩, rfl⟩
    exact ⟨s, hs, s • z, hz, hsm s z⟩

theorem gmap_injective (g : V ≃ₗ[K] V) :
    Function.Injective (Formalism.HermitianLatticesTheory.gmap g : Submodule (𝓞 K) V → Submodule (𝓞 K) V) := by
  intro L M hLM
  unfold Formalism.HermitianLatticesTheory.gmap at hLM
  exact Submodule.map_injective_of_injective (f := (g : V →ₗ[K] V).restrictScalars (𝓞 K))
    (fun a b h => g.injective h) hLM

theorem isUnimodularAt_of_loc_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (p : Ideal (𝓞 K))
    {L M : Submodule (𝓞 K) V} (he : Formalism.HermitianLatticesTheory.loc (K := K) p L = Formalism.HermitianLatticesTheory.loc (K := K) p M) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p L ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h p M := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  rw [he]

end Formalism.HermitianLattices.Ext.L3
end
end

