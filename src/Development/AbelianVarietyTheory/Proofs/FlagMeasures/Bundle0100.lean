module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometricEmbeddedDatumPairsEncardIsometrySmul
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.TripInv

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

abbrev lin (s : V ≃ₗ[K] V) : V →ₗ[𝓞 K] V := (s : V →ₗ[K] V).restrictScalars (𝓞 K)

def pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) : Submodule (𝓞 K) (V × V) :=
  Γ.map ((lin s).prodMap (lin s))

theorem gmap_eq (s : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap s M = M.map (lin s) := rfl

theorem mem_gmap (s : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) :
    y ∈ Formalism.HermitianLatticesTheory.gmap s M ↔ s.symm y ∈ M := by
  rw [gmap_eq, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨s.symm y, h, by simp⟩

theorem mem_pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) (p : V × V) :
    p ∈ pmap s Γ ↔ (s.symm p.1, s.symm p.2) ∈ Γ := by
  rw [pmap, Submodule.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro h
    exact ⟨_, h, by ext <;> simp⟩

theorem gmap_injective (s : V ≃ₗ[K] V) : Function.Injective (Formalism.HermitianLatticesTheory.gmap (R := 𝓞 K) s) := by
  intro M M' h
  ext x
  have := congrArg (s x ∈ ·) h
  simpa [mem_gmap] using this

theorem pmap_injective (s : V ≃ₗ[K] V) : Function.Injective (pmap s) := by
  intro Γ Γ' h
  ext p
  have := congrArg ((s p.1, s p.2) ∈ ·) h
  simpa [mem_pmap] using this

theorem smulLat_gmap (s : V ≃ₗ[K] V) (g : 𝓞 K) (M : Submodule (𝓞 K) V) :
    smulLat g (Formalism.HermitianLatticesTheory.gmap s M) = Formalism.HermitianLatticesTheory.gmap s (smulLat g M) := by
  rw [gmap_eq, gmap_eq, smulLat, smulLat, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  rw [← algebraMap_smul K g x, ← algebraMap_smul K g (s x), map_smul]

theorem prod_gmap (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    (Formalism.HermitianLatticesTheory.gmap s A).prod (Formalism.HermitianLatticesTheory.gmap s B) = pmap s (A.prod B) := by
  ext p
  simp [mem_pmap, mem_gmap, Submodule.mem_prod]

theorem fixLat_pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) :
    fixLat (pmap s Γ) = Formalism.HermitianLatticesTheory.gmap s (fixLat Γ) := by
  ext x
  simp [fixLat, mem_pmap, mem_gmap]

theorem toAddSubgroup_gmap (s : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    (Formalism.HermitianLatticesTheory.gmap s M).toAddSubgroup = M.toAddSubgroup.map (lin s).toAddMonoidHom := by
  ext x
  rfl

theorem idx_gmap (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    idx (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) = idx A B := by
  unfold idx
  rw [toAddSubgroup_gmap, toAddSubgroup_gmap]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (by simpa using s.injective)

theorem idxN_gmap (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    GlobalTheory.Mass.idxN (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) = GlobalTheory.Mass.idxN A B :=
  idx_gmap s A B

variable {H : HermSpace K V}

theorem isom_symm {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (x y : V) :
    H.B (s.symm x) (s.symm y) = H.B x y := by
  rw [← hs]
  simp

theorem dual_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.dual H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) = Formalism.HermitianLatticesTheory.gmap s (Formalism.HermitianLatticesTheory.dual H.B.flip M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, mem_gmap,
    LinearMap.restrictScalars_apply, LinearMap.flip_apply]
  constructor
  · intro h z hz
    have := h (s z) (by simpa using hz)
    rwa [← isom_symm hs, LinearEquiv.symm_apply_apply] at this
  · intro h y hy
    have := h _ hy
    rwa [isom_symm hs] at this

theorem isIntLat_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {M : Submodule (𝓞 K) V}
    (hM : GlobalTheory.Mass.IsIntLat H.B.flip M) : GlobalTheory.Mass.IsIntLat H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) := by
  obtain ⟨hL, hI⟩ := hM
  have hfull : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap s M) := by
    rw [gmap_eq]
    haveI : Submodule.IsLattice K (M.map (lin s)) :=
      Submodule.IsLattice.of_fg K (hL.fg.map _)
    refine ⟨?_⟩
    change Submodule.span K ((s : V →ₗ[K] V) '' (M : Set V)) = ⊤
    rw [← Submodule.map_span, hL.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.2 s.surjective]
  refine ⟨hfull, ?_⟩
  · intro x hx y hy
    rw [mem_gmap] at hx hy
    have := hI _ hx _ hy
    simp only [LinearMap.flip_apply] at this ⊢
    rwa [isom_symm hs] at this

theorem discN_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (M : Submodule (𝓞 K) V) :
    GlobalTheory.Mass.discN H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) = GlobalTheory.Mass.discN H.B.flip M := by
  unfold GlobalTheory.Mass.discN
  rw [dual_gmap hs, idxN_gmap]

theorem genBy_gmap (s : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} {j : ℕ} (h : GenBy A B j) :
    GenBy (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) j := by
  classical
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨t.image s, (Finset.card_image_le).trans ht, ?_⟩
  rw [gmap_eq, gmap_eq, Submodule.map_sup, Submodule.map_span, Finset.coe_image]
  rfl

theorem isModIso_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {g : 𝓞 K}
    {M L : Submodule (𝓞 K) V} {Γ : Submodule (𝓞 K) (V × V)} (h : IsModIso H g M L Γ) :
    IsModIso H g (Formalism.HermitianLatticesTheory.gmap s M) (Formalism.HermitianLatticesTheory.gmap s L) (pmap s Γ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prod_gmap]
    exact Submodule.map_mono h1
  · rw [smulLat_gmap, smulLat_gmap, prod_gmap]
    exact Submodule.map_mono h2
  · intro y' hy'
    rw [mem_gmap] at hy'
    obtain ⟨y, hy⟩ := h3 _ hy'
    exact ⟨s y, by simpa [mem_pmap] using hy⟩
  · intro y hy
    rw [mem_gmap] at hy
    obtain ⟨y', hy'⟩ := h4 _ hy
    exact ⟨s y', by simpa [mem_pmap] using hy'⟩
  · intro y hy
    rw [mem_pmap] at hy
    rw [smulLat_gmap, mem_gmap]
    exact h5 _ (by simpa using hy)
  · intro y' hy'
    rw [mem_pmap] at hy'
    rw [smulLat_gmap, mem_gmap]
    exact h6 _ (by simpa using hy')
  · intro p hp q hq
    rw [mem_pmap] at hp hq
    obtain ⟨t, ht⟩ := h7 _ hp _ hq
    exact ⟨t, by simpa only [isom_symm hs] using ht⟩

theorem isDat_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {g : ℕ} {L : Submodule (𝓞 K) V}
    {j x : ℕ} {d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)} (h : IsDat H g L j x d) :
    IsDat H g (Formalism.HermitianLatticesTheory.gmap s L) j x (Formalism.HermitianLatticesTheory.gmap s d.1, pmap s d.2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨isIntLat_gmap hs h1, ?_, isModIso_gmap hs h3, ?_, ?_⟩
  · rw [discN_gmap hs, discN_gmap hs, h2]
  · rw [fixLat_pmap, idx_gmap, h4]
  · rw [fixLat_pmap]
    exact genBy_gmap s h5

def tr (s : V ≃ₗ[K] V)
    (p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V)) :
    (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) :=
  ((Formalism.HermitianLatticesTheory.gmap s p.1.1, pmap s p.1.2), (Formalism.HermitianLatticesTheory.gmap s p.2.1.1, pmap s p.2.1.2), s * p.2.2 * s⁻¹)

theorem tr_injective (s : V ≃ₗ[K] V) : Function.Injective (tr (K := K) s) := by
  rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, η⟩ ⟨⟨a1', a2'⟩, ⟨b1', b2'⟩, η'⟩ h
  simp only [tr, Prod.mk.injEq] at h
  obtain ⟨⟨e1, e2⟩, ⟨e3, e4⟩, e5⟩ := h
  simp only [gmap_injective s e1, pmap_injective s e2, gmap_injective s e3, pmap_injective s e4,
    mul_left_cancel (mul_right_cancel e5)]

theorem tr_mapsTo {s : V ≃ₗ[K] V} (hs : s ∈ isomGrp H) (g : ℕ) (L : Submodule (𝓞 K) V) (j x x' : ℕ) :
    Set.MapsTo (tr s) (Trip H g L j x x') (Trip H g (Formalism.HermitianLatticesTheory.gmap s L) j x x') := by
  have hs' := (mem_isomGrp H s).1 hs
  rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, η⟩ ⟨hA, hB, hη, him, hgr⟩
  refine ⟨isDat_gmap hs' hA, isDat_gmap hs' hB, ?_, ?_, ?_⟩
  · exact (isomGrp H).mul_mem ((isomGrp H).mul_mem hs hη) ((isomGrp H).inv_mem hs)
  · change Formalism.HermitianLatticesTheory.gmap (s * η * s⁻¹) (Formalism.HermitianLatticesTheory.gmap s b1) = Formalism.HermitianLatticesTheory.gmap s a1
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv, Formalism.HermitianLatticesTheory.genusBasic_gmap_mul]
    exact congrArg _ him
  · intro y y'
    change (y, y') ∈ pmap s b2 ↔ (s (η (s.symm y)), y') ∈ pmap s a2
    rw [mem_pmap, mem_pmap]
    simpa using hgr (s.symm y) (s.symm y')

theorem encard_le (HW : HermSpace K V) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (L : Submodule (𝓞 K) V) :
    (Trip HW g L j x x').encard ≤ (Trip HW g (s • L) j x x').encard :=
  Set.encard_le_encard_of_injOn (tr_mapsTo s.2 g L j x x') (tr_injective _).injOn

theorem trip_encard_smul : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : HermSpace K W) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip)
    (L : Submodule (𝓞 K) W), (Trip HW g (s • L) j x x').encard = (Trip HW g L j x x').encard := by
  intro K W _ _ _ _ _ _ _ HW g j x x' s L
  refine le_antisymm ?_ (encard_le HW g j x x' s L)
  have := encard_le HW g j x x' s⁻¹ (s • L)
  exact this.trans_eq (congrArg (fun M => (Trip HW g M j x x').encard)
    (Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (s : W ≃ₗ[K] W) L))

end GlobalTheory.TripInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfForall
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open scoped nonZeroDivisors

namespace GlobalTheory.DegCnt.IdealPow

variable {K : Type} [Field K] [NumberField K] {𝔡 : Ideal (𝓞 K)}

theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  simp [ipow]

theorem ipow_mul (h : 𝔡 ≠ ⊥) (m n : ℤ) : ipow 𝔡 m * ipow 𝔡 n = ipow 𝔡 (m + n) := by
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  unfold ipow
  rw [zpow_add₀ h0, FractionalIdeal.coe_mul]

theorem mul_mem (h : 𝔡 ≠ ⊥) {m n k : ℤ} (hk : m + n = k) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ ipow 𝔡 k := by
  rw [← hk, ← ipow_mul h]
  exact Submodule.mul_mem_mul hx hy

theorem mul_mem_one (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← ipow_zero 𝔡]
  exact mul_mem h hk hx hy

theorem pow_mem (h : 𝔡 ≠ ⊥) {m : ℤ} {x : K} (hx : x ∈ ipow 𝔡 m) (s : ℕ) : x ^ s ∈ ipow 𝔡 (s * m) := by
  induction s with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  | succ s ih => rw [pow_succ]; exact mul_mem h (by push_cast; ring) ih hx

theorem mem_of_forall (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x : K}
    (hx : ∀ y ∈ ipow 𝔡 n, x * y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ ipow 𝔡 m := by
  have h1 : (1 : K) ∈ ipow 𝔡 n * ipow 𝔡 m := by
    rw [ipow_mul h, add_comm, hk, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have h2 : ∀ z ∈ ipow 𝔡 n * ipow 𝔡 m, x * z ∈ ipow 𝔡 m := by
    intro z hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx a ha)
      rw [← mul_assoc, ← hc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ c hb
    · rw [mul_add]; exact add_mem ha hb
  simpa using h2 1 h1

theorem prod_ipow (h : 𝔡 ≠ ⊥) {ι : Type} (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, ipow 𝔡 (n i) = ipow 𝔡 (∑ i ∈ s, n i) := by
  induction s using Finset.induction_on with
  | empty => simp [ipow_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ipow_mul h]

theorem ipow_sum_le (h : 𝔡 ≠ ⊥) {ι : Type} [Fintype ι] (n : ι → ℤ) (J : Submodule (𝓞 K) K)
    (hJ : ∀ α : ι → K, (∀ i, α i ∈ ipow 𝔡 (n i)) → ∏ i, α i ∈ J) : ipow 𝔡 (∑ i, n i) ≤ J := by
  rw [← prod_ipow h]
  have : ∏ i, ipow 𝔡 (n i) = ∏ i, Submodule.span (𝓞 K) (ipow 𝔡 (n i) : Set K) := by simp
  rw [this, Submodule.prod_span, Submodule.span_le]
  intro x hx
  obtain ⟨α, hα, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
  exact hJ α hα

variable [StarRing K]

theorem star_mem_nat (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  induction n generalizing x with
  | zero =>
    rw [Nat.cast_zero, ipow_zero] at hx ⊢
    exact GlobalTheory.UnimodQuot.star_mem_one hx
  | succ n ih =>
    rw [Nat.cast_succ, ← ipow_mul h] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [star_mul']
      refine Submodule.mul_mem_mul (ih ha) ?_
      simp only [ipow, zpow_one, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hb ⊢
      obtain ⟨y, hy, rfl⟩ := hb
      exact hs y hy
    · rw [star_add]; exact add_mem ha hb

theorem star_mem (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) {n : ℤ} {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact star_mem_nat h hs m hx
  · refine mem_of_forall h (neg_add_cancel _) fun y hy => ?_
    have := GlobalTheory.UnimodQuot.star_mem_one (mul_mem_one h (neg_add_cancel _) hx (star_mem_nat h hs m hy))
    rwa [star_mul', star_star] at this

end GlobalTheory.DegCnt.IdealPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReferenceLatticeMemOfMemInnerSpan
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open Formalism.HermitianLatticeCounting.P

noncomputable section

namespace GlobalTheory.DegCnt.ReflectionLatticeMembership

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)

def Sg : Submodule K V := N.F.X ⊔ N.F'.X ⊔ N.Ist

theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (hv : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨a, -, rfl⟩
  simpa using S.smul_mem a hv

theorem normalForm_baseLattice_le_dualSpan_sup_line : N.P0 ≤ rs (𝓞 K) (Sg N) ⊔ line 1 N.F.z := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le ?_ ?_) le_sup_right) ?_
  · refine iSup_le fun a => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
  · refine iSup_le fun a => iSup_le fun _ => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
  · refine iSup_le fun a => iSup_le fun h => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, h, rfl⟩)

theorem Sg_le_Pi [FiniteDimensional K V] : Sg N ≤ N.Pi := by
  rw [NFGeom.Pi_eq]
  exact sup_le (sup_le (le_sup_of_le_left (le_sup_left.trans le_sup_left))
    (le_sup_of_le_left (le_sup_right.trans le_sup_left))) le_sup_right

theorem z_mem_Pi [FiniteDimensional K V] : N.F.z ∈ N.Pi := by
  rw [NFGeom.Pi_eq]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))

theorem eq_zero [FiniteDimensional K V] {q : V} (hS : q ∈ Sg N) (hW : q ∈ N.Wn) : q = 0 := by
  rw [NFGeom.Wn_eq N] at hW
  obtain ⟨w, hw, m, hm, rfl⟩ := Submodule.mem_sup.1 hW
  obtain ⟨κ, rfl⟩ := Submodule.mem_span_singleton.1 hm
  have hwP : w ∈ N.Pi := by
    have e : w = (w + κ • N.F.z) - κ • N.F.z := by abel
    rw [e]
    exact Submodule.sub_mem _ (Sg_le_Pi N hS) (Submodule.smul_mem _ _ (z_mem_Pi N))
  have hw0 : w = 0 := NFGeom.Wt_inf_Pi N hw hwP
  subst hw0
  rw [zero_add] at hS ⊢
  have h1 : H.B N.F.z (κ • N.F.z) = 0 := (mem_perp_iff H (Sg N) _).1 (NFGeom.z_mem_Wn N) _ hS
  have h2 : H.B (κ • N.F.z) N.F.z = 0 := B_swap0 H h1
  have h3 : H.B N.F.z N.F.z = -N.F.T := N.F.zz
  rw [map_smul, LinearMap.smul_apply, h3, smul_eq_mul, mul_neg, neg_eq_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · simp [h]
  · exact absurd h N.F.hT

end GlobalTheory.DegCnt.ReflectionLatticeMembership

namespace GlobalTheory.DegCnt

theorem NF.ref_mem_of_mem_Wn : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : GlobalTheory.DegCnt.NF H r) (L : Submodule (𝓞 K) V), N.F.z ∈ L → ∀ v ∈ N.Ref L, v ∈ N.Wn → v ∈ L := by
  intro K V _ _ _ _ _ _ _ _ H _ r N L hz v hv hvW
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨q, hq, m, hm, rfl⟩ := Submodule.mem_sup.1 (ReflectionLatticeMembership.normalForm_baseLattice_le_dualSpan_sup_line N hp)
  obtain ⟨γ, hγ, rfl⟩ := hm
  obtain ⟨x, rfl⟩ := Submodule.mem_one.1 hγ
  have hm' : ((LinearMap.toSpanSingleton K V N.F.z).restrictScalars (𝓞 K)) (algebraMap (𝓞 K) K x) = x • N.F.z := by
    simp [algebraMap_smul]
  rw [hm'] at hvW ⊢
  have hmW : x • N.F.z ∈ N.Wn := by
    rw [← algebraMap_smul K x N.F.z]
    exact N.Wn.smul_mem _ (NFGeom.z_mem_Wn N)
  have hlW : l ∈ N.Wn := hl.2
  have hq0 : q = 0 := ReflectionLatticeMembership.eq_zero N hq (by
    have h := N.Wn.sub_mem (N.Wn.sub_mem hvW hlW) hmW
    convert h using 1
    abel)
  subst hq0
  rw [zero_add]
  exact L.add_mem (L.smul_mem x hz) hl.1

end GlobalTheory.DegCnt
end
end

