module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0028
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0026
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0023
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0027
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VolumeNormSqLeOne
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0002
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaLEqOfBridge
section
open NumberField Module Matrix Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem alphaL_eq_of_bridge [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin (finrank K V) → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤)
    (hbr : ∀ k, akCount h L 𝔭 k = isoCount 𝔭 k (diagonal u)) :
    alphaL h L 𝔭 = alphaStd K 𝔭 (finrank K V) := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
      (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
        (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast this
  unfold alphaL
  apply Filter.Tendsto.limUnder_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [hbr, isoCount_diag hK h𝔭 u hu hunit j, eq_div_iff (pow_ne_zero _ hN)]
  ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def fibSet (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (T : Submodule (𝓞 K) V') : Set (Submodule (𝓞 K) V) :=
  {Λ | locF 𝔭 Λ = Λ ∧ (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Λ) ∧ S.x₀ ∈ Λ ∧
    S.cut Λ = locF 𝔭 T}

theorem fibLoc_eq_card (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (T : Submodule (𝓞 K) V') : fibLoc S L 𝔭 T = Nat.card (fibSet S L 𝔭 T) := rfl

theorem le_locF (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) : L ≤ locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_le_locS _ L

theorem locF_idem (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) : locF 𝔭 (locF 𝔭 L) = locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_locS_idem _ L

theorem gmap_locF (g : V ≃ₗ[K] V) (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g L) :=
  Formalism.HermitianLatticesTheory.gmap_locS_comm g _ L

theorem cut_locF (S : VecSplit h h') (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) :
    S.cut (locF 𝔭 Λ) = locF 𝔭 (S.cut Λ) := by
  ext a
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [VecSplit.mem_cut_iff, LinearMap.map_smul_of_tower]
    exact hx
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [VecSplit.mem_cut_iff, LinearMap.map_smul_of_tower] at hx
    exact hx

theorem isLattice_gmap (g : V ≃ₗ[K] V) {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) :
    Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : ((Formalism.HermitianLatticesTheory.gmap g L : Submodule (𝓞 K) V) : Set V) = (g : V →ₗ[K] V) '' (L : Set V) := rfl
  exact fun _ _ hli => (LinearIndependent.iff_fractionRing _ _).mp hli

theorem form_smul_smul (s t : 𝓞 K) (x y : V) :
    h (s • x) (t • y) = (conjO K s * t) • h x y := by
  have e : algebraMap (𝓞 K) K (conjO K s) = starRingEnd K (algebraMap (𝓞 K) K s) := rfl
  rw [← algebraMap_smul K s x, ← algebraMap_smul K t y, map_smul, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, Algebra.smul_def, map_mul, e]
  ring

theorem form_mem_locR {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (P : Ideal (𝓞 K))
    {x y : V} (hx : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) P L) (hy : y ∈ Formalism.HermitianLatticesTheory.loc (K := K) P L) :
    h x y ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  refine ⟨conjO K s * t, Submonoid.mul_mem _ (conjO_mem_hcompl P hs) ht, ?_⟩
  rw [← form_smul_smul]
  exact hLi _ hx _ hy

theorem form_mem_locR_gmap {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (P : Ideal (𝓞 K)) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {x y : V}
    (hx : x ∈ Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) P L))
    (hy : y ∈ Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) P L)) :
    h x y ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
  rw [SplitBAux.mem_gmap_iff] at hx hy
  have := form_mem_locR hLi P hx hy
  rwa [SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg)] at this

theorem smul_mem_of_loc_eq {P : Ideal (𝓞 K)} {Λ : Submodule (𝓞 K) V}
    (hΛ : Formalism.HermitianLatticesTheory.loc (K := K) P Λ = Λ) {c : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) P) {x : V}
    (hx : x ∈ Λ) : c • x ∈ Λ := by
  obtain ⟨s, hs, hc⟩ := hc
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
  rw [← hΛ]
  refine ⟨s, hs, ?_⟩
  rw [← smul_assoc, ← hr, algebraMap_smul]
  exact Λ.smul_mem r hx

theorem comb_mem_dualAt_iff (hs : h.IsSymm) (S : VecSplit h h') (p : Ideal (𝓞 K))
    (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L')) ↔
      c * h S.x₀ S.x₀ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ∧
        a ∈ Formalism.HermitianLatticesTheory.dualAt h' p (Formalism.HermitianLatticesTheory.loc (K := K) p L') := by
  rw [mem_dualAt_iff', mem_dualAt_iff']
  constructor
  · intro H
    refine ⟨?_, fun b hb => ?_⟩
    · have := H ((1 : K) • S.x₀ + S.ι 0)
        ((S.comb_mem_loc_adjoin_iff p L' 1 0).mpr ⟨one_mem_locR p, Submodule.zero_mem _⟩)
      rwa [SplitBAux.h_decomp hs S, star_one, one_mul, map_zero, LinearMap.zero_apply, add_zero] at this
    · have := H ((0 : K) • S.x₀ + S.ι b)
        ((S.comb_mem_loc_adjoin_iff p L' 0 b).mpr ⟨Submodule.zero_mem _, hb⟩)
      rwa [SplitBAux.h_decomp hs S, star_zero, zero_mul, zero_mul, zero_add] at this
  · rintro ⟨hc, ha⟩ y hy
    obtain ⟨d, b, rfl⟩ := S.cover y
    obtain ⟨hd, hb⟩ := (S.comb_mem_loc_adjoin_iff p L' d b).mp hy
    rw [SplitBAux.h_decomp hs S, mul_assoc]
    exact Submodule.add_mem _ (mul_mem_locR p (star_mem_locR p hd) hc) (ha b hb)

theorem inv_mem_locR_of_unimod (hs : h.IsSymm) (S : VecSplit h h') {p : Ideal (𝓞 K)}
    {L' : Submodule (𝓞 K) V'} (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L')) :
    (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  have h1 : (h S.x₀ S.x₀)⁻¹ • S.x₀ + S.ι 0 ∈
      Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L')) := by
    rw [comb_mem_dualAt_iff hs, inv_mul_cancel₀ S.hx₀]
    exact ⟨one_mem_locR p, Submodule.zero_mem _⟩
  rw [hU] at h1
  exact ((S.comb_mem_loc_adjoin_iff p L' _ 0).mp h1).1

theorem unimod_adjoin (hs : h.IsSymm) (S : VecSplit h h') {p : Ideal (𝓞 K)}
    {L' : Submodule (𝓞 K) V'} (hn : h S.x₀ S.x₀ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hn' : (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L') : Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L') := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hU ⊢
  ext v
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [comb_mem_dualAt_iff hs, S.comb_mem_loc_adjoin_iff, hU]
  refine and_congr_left fun _ => ⟨fun hc => ?_, fun hc => mul_mem_locR p hc hn⟩
  have := mul_mem_locR p hc hn'
  rwa [mul_assoc, mul_inv_cancel₀ S.hx₀, mul_one] at this

theorem isIntegralLat_adjoin (hs : h.IsSymm) (S : VecSplit h h')
    (hn : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K)) {L' : Submodule (𝓞 K) V'}
    (hL' : Formalism.HermitianLatticesTheory.IsIntegralLat h' L') : Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') := by
  intro x hx y hy
  obtain ⟨r, a, ha, rfl⟩ := (S.mem_adjoin_iff L' x).mp hx
  obtain ⟨t, b, hb, rfl⟩ := (S.mem_adjoin_iff L' y).mp hy
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp hn
  obtain ⟨w, hw⟩ := Submodule.mem_one.mp (hL' a ha b hb)
  rw [SplitBAux.h_decomp hs S, ← hn, ← hw]
  refine Submodule.mem_one.mpr ⟨conjO K r * t * n + w, ?_⟩
  rw [map_add (f := _), map_mul, map_mul]
  rfl

theorem exists_max_over {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  have := h𝔭
  refine Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) 𝔭 ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
  exact bot_le

theorem fibSet_eq_singleton (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {Λ' : Submodule (𝓞 K) V'}
    (hN : Submodule.IsFullLattice K (S.adjoin Λ')) (hNi : Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin Λ'))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hvL : vd h L 𝔭 = 0) (hvN : vd h (S.adjoin Λ') 𝔭 = 0) :
    fibSet S L 𝔭 Λ' = {locF 𝔭 (S.adjoin Λ')} := by
  obtain ⟨P, hP, rfl⟩ := exists_max_over (K := K) h𝔭
  have hUN := (isUnimodularAt_iff_vd hK hF hs hd hN hNi hP).2 hvN
  have hinv := inv_mem_locR_of_unimod hs S hUN
  ext Λ
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, ⟨g, hg, h2⟩, h3, h4⟩
    rw [locF_eq_loc hK hF hP] at h1 h2 h4 ⊢
    ext v
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [S.comb_mem_loc_adjoin_iff, ← h4, VecSplit.mem_cut_iff]
    constructor
    · intro hv
      have hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
        have h5 : h S.x₀ (c • S.x₀ + S.ι a) ∈ Formalism.HermitianLatticesTheory.locR (K := K) P :=
          form_mem_locR_gmap hLi P hg (h2 ▸ h3) (h2 ▸ hv)
        rw [S.h_x₀_comb] at h5
        have := mul_mem_locR P h5 hinv
        rwa [mul_assoc, mul_inv_cancel₀ S.hx₀, mul_one] at this
      refine ⟨hc, ?_⟩
      have := Λ.sub_mem hv (smul_mem_of_loc_eq h1 hc h3)
      rwa [add_sub_cancel_left] at this
    · rintro ⟨hc, ha⟩
      exact Λ.add_mem (smul_mem_of_loc_eq h1 hc h3) ha
  · rintro rfl
    let _ := hL
    let _ := hN
    refine ⟨locF_idem _ _, exists_isom_locF_of_vd_zero (A := L) (B := S.adjoin Λ')
      hK hF hs hd inferInstance inferInstance hLi hNi h𝔭 hvL hvN,
      le_locF _ _ (S.x₀_mem_adjoin Λ'), ?_⟩
    rw [cut_locF, S.cut_adjoin]

theorem notMem_of_vF_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn0 : n ≠ 0)
    (hv : vF 𝔭 n = 0) : n ∉ 𝔭 := by
  intro hn
  have hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := by
    by_contra hb
    apply hn0
    have h1 : n ∈ (⨅ i : ℕ, 𝔭 ^ i) := by
      rw [Submodule.mem_iInf]
      intro i
      rw [not_bddAbove_iff] at hb
      obtain ⟨e, he, hie⟩ := hb i
      exact Ideal.pow_le_pow_right hie.le he
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top, Ideal.mem_bot] at h1
  have h1 : 1 ≤ vF 𝔭 n := le_csSup hb (by simpa using hn)
  omega

end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MeasurableSetBallSet
section
open NumberField NumberField.mixedEmbedding MeasureTheory Module Pointwise

open scoped Classical

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallD

open BallB BallC

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def emb (b : Basis (Fin (finrank K V)) K V) : V →+ (Fin (finrank K V) → mixedSpace K) where
  toFun x := fun i => mixedEmbedding K (b.repr x i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem emb_apply (b : Basis (Fin (finrank K V)) K V) (x : V) (i : Fin (finrank K V)) :
    emb b x i = mixedEmbedding K (b.repr x i) := rfl

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem emb_injective (b : Basis (Fin (finrank K V)) K V) : Function.Injective (emb b) := by
  intro x y hxy
  apply b.repr.injective
  ext i
  exact mixedEmbedding_injective K (congrFun hxy i)

omit [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem psi_emb [IsEmpty {w : InfinitePlace K // w.IsReal}] (b : Basis (Fin (finrank K V)) K V)
    (x : V) (w : {w : InfinitePlace K // w.IsComplex}) (i : Fin (finrank K V)) :
    psi K (Fin (finrank K V)) (emb b x) w i = w.1.embedding (b.repr x i) := by
  rw [psi_apply, emb_apply, mixedEmbedding_apply_isComplex]

def lat (b : Basis (Fin (finrank K V)) K V) (L : Submodule (𝓞 K) V) :
    Submodule ℤ (Fin (finrank K V) → mixedSpace K) :=
  AddSubgroup.toIntSubmodule (L.toAddSubgroup.map (emb b))

omit [StarRing K] [IsScalarTower (𝓞 K) K V] in
theorem mem_lat {b : Basis (Fin (finrank K V)) K V} {L : Submodule (𝓞 K) V}
    {y : Fin (finrank K V) → mixedSpace K} : y ∈ lat b L ↔ ∃ x ∈ L, emb b x = y := Iff.rfl

omit [StarRing K] in
theorem lat_span (b : Basis (Fin (finrank K V)) K V) :
    lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (piBasis K (Fin (finrank K V)))) := by
  ext y
  rw [mem_span_piBasis, mem_lat]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨a, ha⟩ := (b.mem_span_iff_repr_mem (𝓞 K) x).1 hx i
    exact ⟨a, by rw [ha]; rfl⟩
  · intro hy
    choose a ha using hy
    have hr : ∀ i, b.repr (b.equivFun.symm fun i => algebraMap (𝓞 K) K (a i)) i =
        algebraMap (𝓞 K) K (a i) := by
      intro i
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    refine ⟨b.equivFun.symm fun i => algebraMap (𝓞 K) K (a i),
      (b.mem_span_iff_repr_mem (𝓞 K) _).2 fun i => ⟨a i, (hr i).symm⟩, funext fun i => ?_⟩
    rw [emb_apply, hr, ha]

def ballSet [IsEmpty {w : InfinitePlace K // w.IsReal}] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (b : Basis (Fin (finrank K V)) K V) : Set (Fin (finrank K V) → mixedSpace K) :=
  (psi K (Fin (finrank K V))) ⁻¹' Set.pi Set.univ fun w =>
    ell fun i => (w.1.embedding (h (b i) (b i))).re

variable [IsEmpty {w : InfinitePlace K // w.IsReal}] {h : V →ₗ⋆[K] V →ₗ[K] K}
  {b : Basis (Fin (finrank K V)) K V}

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem measurableSet_ballSet : MeasurableSet (ballSet h b) :=
  ((isClosed_set_pi fun _ _ => isClosed_ell _).preimage
    (psi K (Fin (finrank K V))).toContinuousLinearEquiv.continuous).measurableSet

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem convex_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    Convex ℝ (ballSet h b) :=
  (convex_pi fun w _ => convex_ell (hA w)).linear_preimage (psi K (Fin (finrank K V))).toLinearMap

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isBounded_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    Bornology.IsBounded (ballSet h b) := by
  have h1 : ballSet h b = (psi K (Fin (finrank K V))).toContinuousLinearEquiv.symm ''
      Set.pi Set.univ fun w => ell fun i => (w.1.embedding (h (b i) (b i))).re :=
    ((psi K (Fin (finrank K V))).toContinuousLinearEquiv.image_symm_eq_preimage _).symm
  rw [h1]
  exact (psi K (Fin (finrank K V))).toContinuousLinearEquiv.symm.lipschitzWith.isBounded_image
    (Bornology.IsBounded.pi fun w => isBounded_ell (hA w))

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem volume_ballSet
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    volume.real (ballSet h b) =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ InfinitePlace.nrComplexPlaces K /
        ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re := by
  have hm : MeasurableSet (Set.pi Set.univ fun w : {w : InfinitePlace K // w.IsComplex} =>
      ell fun i => (w.1.embedding (h (b i) (b i))).re) :=
    (isClosed_set_pi fun _ _ => isClosed_ell _).measurableSet
  rw [measureReal_def, ballSet,
    (measurePreserving_psi K (Fin (finrank K V))).measure_preimage hm.nullMeasurableSet,
    volume_pi_pi, ENNReal.toReal_prod]
  have h1 : ∀ w : {w : InfinitePlace K // w.IsComplex},
      (volume (ell fun i => (w.1.embedding (h (b i) (b i))).re)).toReal =
        Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ) /
          ∏ i, (w.1.embedding (h (b i) (b i))).re := by
    intro w
    rw [volume_ell (hA w), ENNReal.toReal_ofReal]
    exact div_nonneg (by positivity) (Finset.prod_nonneg fun i _ => (hA w i).le)
  simp only [h1]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

theorem card_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (L : Submodule (𝓞 K) V) {j : ℕ} (hj : 0 < j) :
    ballCount h L ((j : ℝ) ^ 2) =
      Nat.card ↑(ballSet h b ∩ (j : ℝ)⁻¹ • (lat b L : Set (Fin (finrank K V) → mixedSpace K))) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have key : ∀ x : V, (j : ℝ)⁻¹ • emb b x ∈ ballSet h b ↔
      ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ (j : ℝ) ^ 2 := by
    intro x
    rw [forall_embedding_iff hK b ho x]
    simp only [ballSet, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, mem_ell,
      map_smul]
    refine forall_congr' fun w => ?_
    have h1 : ∀ i, Complex.normSq (((j : ℝ)⁻¹ • psi K (Fin (finrank K V)) (emb b x)) w i) =
        ((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i)) := by
      intro i
      rw [Pi.smul_apply, Pi.smul_apply, psi_emb, Complex.real_smul, map_mul, Complex.normSq_ofReal]
      field_simp
    simp only [h1]
    have h2 : ∑ i, (w.1.embedding (h (b i) (b i))).re *
        (((j : ℝ) ^ 2)⁻¹ * Complex.normSq (w.1.embedding (b.repr x i))) =
        (∑ i, (w.1.embedding (h (b i) (b i))).re *
          Complex.normSq (w.1.embedding (b.repr x i))) / (j : ℝ) ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, div_le_one (by positivity)]
  unfold ballCount
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨(j : ℝ)⁻¹ • emb b x.1, (key x.1).2 x.2.2,
      Set.smul_mem_smul_set ⟨x.1, x.2.1, rfl⟩⟩) ⟨?_, ?_⟩)
  · intro x y hxy
    have h1 : (j : ℝ)⁻¹ • emb b x.1 = (j : ℝ)⁻¹ • emb b y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (emb_injective b (smul_right_injective _ (inv_ne_zero hj'.ne') h1))
  · rintro ⟨y, hy1, hy2⟩
    obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hy2
    exact ⟨⟨x, hx, (key x).1 hy1⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.BallD
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NeBotOfIsMaximal
section
open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem vF_lt_of_notMem {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {e : ℕ} (h : n ∉ 𝔭 ^ e) : vF 𝔭 n < e := by
  unfold vF
  have hne : ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ).Nonempty := ⟨0, by simp⟩
  have hlt : ∀ k ∈ ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ), k < e := by
    intro k hk
    by_contra hke
    push Not at hke
    exact h (Ideal.pow_le_pow_right hke hk)
  have hbdd : BddAbove ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ) := ⟨e, fun k hk => (hlt k hk).le⟩
  exact hlt _ (Nat.sSup_mem hne hbdd)

theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ := by
  haveI := h𝔭
  exact Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭

theorem one_lt_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact h𝔭.ne_top
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact ne_bot_of_isMaximal h𝔭
  have h2 : 1 < Ideal.absNorm 𝔭 := by omega
  exact_mod_cast h2

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

