module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefinitePartLatticeDiscriminantEqQuotien
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PrimPerp

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [StarRing K] [FiniteDimensional K V] in
theorem equiv_of_gen {D M : Submodule (𝓞 K) V} {w : V} (hw : w ∈ D) (J : Ideal (𝓞 K))
    (h1 : ∀ a : 𝓞 K, a • w ∈ M ↔ a ∈ J) (h2 : ∀ y ∈ D, ∃ a : 𝓞 K, y - a • w ∈ M) :
    Nonempty ((↥D ⧸ M.comap D.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ J)) := by
  let φ : 𝓞 K →ₗ[𝓞 K] (↥D ⧸ M.comap D.subtype) :=
    (M.comap D.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) D ⟨w, hw⟩
  have hs : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := (M.comap D.subtype).mkQ_surjective q
    obtain ⟨a, ha⟩ := h2 y y.2
    exact ⟨a, ((Submodule.Quotient.eq (M.comap D.subtype)).2 (show y - a • (⟨w, hw⟩ : D) ∈ M.comap D.subtype from ha)).symm⟩
  have hk : LinearMap.ker φ = J := by
    ext a
    rw [LinearMap.mem_ker, ← h1]
    exact Submodule.Quotient.mk_eq_zero _
  exact ⟨(φ.quotKerEquivOfSurjective hs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

theorem perp_prim (H : HermSpace K V) [_root_.NumberField.IsTotallyComplex K] {M : Submodule (𝓞 K) V} {S I W : Submodule K V}
    (hIS : I ≤ S) (hrad : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) (hM : IsUnimodMod H M S I)
    {z : V} {T : ℕ} (hT : 1 ≤ T) (hz : H.B z z = -(T : K))
    (hp : ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K))
    (hW : ∀ y, y ∈ W ↔ y ∈ S ∧ H.B y z = 0) :
    del H (M ⊓ rs (𝓞 K) W) = (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K ∧
      GenBy (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) 1 ∧ IsLatMod (M ⊓ rs (𝓞 K) W) W I ∧
      Nonempty ((↥(dual H (M ⊓ rs (𝓞 K) W)) ⧸ (M ⊓ rs (𝓞 K) W).comap (dual H (M ⊓ rs (𝓞 K) W)).subtype) ≃ₗ[𝓞 K]
        (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) := by
  obtain ⟨a, b⟩ := DelScale.le_of_latMod hM.1
  have hT0 : (T : K) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  have hzM : z ∈ M := by simpa using (hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
  have hzS : z ∈ S := b hzM
  have o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0 := fun i hi => (hrad i (hIS hi)).2 hi
  have o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0 := fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]
  have hint : ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx =>
    ((mem_dual_iff H M x).1 (hM.2.symm ▸ hx)).2
  set U : Submodule K V := Submodule.span K {z} ⊔ I with hU
  have hmU : ∀ u, u ∈ U ↔ ∃ t : K, ∃ i ∈ I, u = t • z + i := fun u => by
    rw [hU, Submodule.mem_sup]
    constructor
    · rintro ⟨x, hx, i, hi, rfl⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact ⟨t, i, hi, rfl⟩
    · rintro ⟨t, i, hi, rfl⟩
      exact ⟨_, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, i, hi, rfl⟩
  have hUS : U ≤ S := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hzS) hIS
  have hWU : S ⊓ perp H U = W := by
    ext y
    rw [hW, Submodule.mem_inf, mem_perp_iff]
    refine and_congr_right fun hy => ⟨fun h => h z ((hmU z).2 ⟨1, 0, I.zero_mem, by simp⟩), fun h x hx => ?_⟩
    obtain ⟨t, i, hi, rfl⟩ := (hmU x).1 hx
    simp [h, o2 i hi y hy]
  have hWS : W ≤ S := fun y hy => ((hW y).1 hy).1
  have hIW : I ≤ W := fun i hi => (hW i).2 ⟨hIS hi, o1 i hi z hzS⟩
  obtain ⟨k1, k2⟩ := Compl.key H hIS hrad hM (le_sup_right : I ≤ U) hUS
  obtain ⟨k3, -⟩ := Compl.key H hIS hrad hM hIW hWS
  rw [hWU] at k1 k2
  rw [k2] at k3
  rw [← hU] at k1 k3
  have hzU : (T : K)⁻¹ • z ∈ U := (hmU _).2 ⟨_, 0, I.zero_mem, (add_zero _).symm⟩
  have hd : (T : K)⁻¹ • z ∈ dual H (M ⊓ rs (𝓞 K) U) := by
    rw [mem_dual_iff, Compl.span_inf (hM.1.2 ▸ hUS)]
    refine ⟨hzU, fun x hx => ?_⟩
    obtain ⟨t, i, hi, rfl⟩ := (hmU x).1 hx.2
    have ht : t • z ∈ M := by simpa using M.sub_mem hx.1 (a hi)
    have e : H.B ((T : K)⁻¹ • z) (t • z + i) = - star t := by
      simp [hz, o2 i hi z hzS]
      field_simp
      try rfl
    rw [e]
    exact Submodule.neg_mem _ (UnimodQuot.star_mem_one ((hp t).1 ht))
  rw [k1] at hd
  obtain ⟨m, hm, w, hw, e⟩ := Submodule.mem_sup.1 hd.2
  have hw' : w ∈ W := hw
  have hwD : w ∈ dual H (M ⊓ rs (𝓞 K) W) := by
    rw [k3]
    exact ⟨hw, Submodule.mem_sup.2 ⟨-m, M.neg_mem hm, _, hzU, by rw [← e]; abel⟩⟩
  have h1 : ∀ c : 𝓞 K, c • w ∈ M ⊓ rs (𝓞 K) W ↔ c ∈ Ideal.span {(T : 𝓞 K)} := by
    intro c
    have e1 : c • w = (algebraMap (𝓞 K) K c * (T : K)⁻¹) • z - c • m := by
      rw [mul_smul, algebraMap_smul, ← e, smul_add]; abel
    rw [Submodule.mem_inf, and_iff_left (Submodule.smul_mem _ c hw), e1,
      M.sub_mem_iff_left (M.smul_mem c hm), hp, Submodule.mem_one, Ideal.mem_span_singleton']
    refine exists_congr fun d => ?_
    rw [eq_mul_inv_iff_mul_eq₀ hT0, ← map_natCast (algebraMap (𝓞 K) K), ← map_mul]
    exact (IsFractionRing.injective (𝓞 K) K).eq_iff
  have h2 : ∀ y ∈ dual H (M ⊓ rs (𝓞 K) W), ∃ c : 𝓞 K, y - c • w ∈ M ⊓ rs (𝓞 K) W := by
    intro y hy
    rw [k3] at hy
    obtain ⟨m', hm', u, hu, e'⟩ := Submodule.mem_sup.1 hy.2
    obtain ⟨t, i, hi, rfl⟩ := (hmU u).1 hu
    have h0 := ((hW y).1 hy.1).2
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hint m' hm' z hzM)
    rw [← e'] at h0
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, hz, o1 i hi z hzS, smul_eq_mul, ← hc] at h0
    have ht : t = algebraMap (𝓞 K) K c * (T : K)⁻¹ := by
      field_simp
      linear_combination -h0
    refine ⟨c, ?_, Submodule.sub_mem _ hy.1 (Submodule.smul_mem _ c hw)⟩
    have : y - c • w = m' + c • m + i := by
      rw [← e', ht, mul_smul, algebraMap_smul, ← e, smul_add]; abel
    rw [this]
    exact M.add_mem (M.add_mem hm' (M.smul_mem c hm)) (a hi)
  have hle : M ⊓ rs (𝓞 K) W ≤ dual H (M ⊓ rs (𝓞 K) W) := by
    rw [k3]
    exact le_inf inf_le_right (inf_le_left.trans le_sup_left)
  obtain ⟨E⟩ := equiv_of_gen hwD _ h1 h2
  refine ⟨?_, ⟨{w}, by simp, ?_⟩, ⟨?_, Compl.span_inf (hM.1.2 ▸ hWS)⟩, ⟨E⟩⟩
  · have i1 : idx (M ⊓ rs (𝓞 K) W) (dual H (M ⊓ rs (𝓞 K) W)) = 1 := AddSubgroup.relIndex_eq_one.2 hle
    have i2 : idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
      have : idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) :=
        Nat.card_congr E.toEquiv
      rw [this, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank,
        IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    rw [del, gidx, i1, i2, mul_comm, pow_mul]
    simp
  · apply le_antisymm
    · intro y hy
      obtain ⟨c, hc⟩ := h2 y hy
      exact Submodule.mem_sup.2 ⟨_, hc, c • w, Submodule.smul_mem _ c (Submodule.subset_span (by simp)), by abel⟩
    · exact sup_le hle (Submodule.span_le.2 (by simpa using hwD))
  · obtain ⟨N, hN, rfl⟩ := hM.1.1
    refine ⟨N ⊓ rs (𝓞 K) W, hN.of_le inf_le_left, ?_⟩
    rw [sup_comm N, sup_inf_assoc_of_le N (show rs (𝓞 K) I ≤ rs (𝓞 K) W from hIW), sup_comm]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → del H (flagPairDefinitePartLattice N.F N.F' Λ) = N.NT ∧ del H (flagPairDefinitePartLattice N.F' N.F Λ) = N.NT ∧ GenBy (dual H (flagPairDefinitePartLattice N.F N.F' Λ)) (flagPairDefinitePartLattice N.F N.F' Λ) 1 ∧ IsLatMod (flagPairDefinitePartLattice N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') ∧ IsLatMod (flagPairDefinitePartLattice N.F' N.F Λ) (wSp N.F N.F') (II N.F N.F') ∧ Nonempty ((↥(dual H (flagPairDefinitePartLattice N.F N.F' Λ)) ⧸ (flagPairDefinitePartLattice N.F N.F' Λ).comap (dual H (flagPairDefinitePartLattice N.F N.F' Λ)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(N.T : 𝓞 K)})) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  haveI := hK.1
  obtain ⟨hNF, -, -, -, -, -, -, hww, -, hT, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hL, hL', hp, hp', -⟩ := _root_.GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hΛ
  have hV := hNF.2.2.2.1
  have hc : N.c ≠ 0 := hNF.1.1
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hzS : N.F.z ∈ uPerp N.F N.F' := by
    have := (hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rw [one_smul] at this
    exact this.1
  have hXV : N.F.X ⊔ N.F'.X ≤ V0 N.F N.F' := le_sup_left
  have hW : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F.z = 0 := by
    intro y
    rw [wSp, uPerp, mem_perp_iff, mem_perp_iff]
    refine ⟨fun h => ⟨fun x hx => h x (hXV hx), h _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))⟩,
      fun h x hx => ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hv
    simp [hzz, h.1 u hu, h.2]
  have hW' : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F'.z = 0 := by
    intro y
    rw [hW, hzz]
    simp [hc]
  have hIX : II N.F N.F' ≤ N.F.X ⊔ N.F'.X := inf_le_left.trans le_sup_left
  have hIS : II N.F N.F' ≤ uPerp N.F N.F' := fun i hi =>
    (mem_perp_iff H _ i).2 fun x hx => (hV i (hXV (hIX hi))).2 hi x (hXV hx)
  have hrad : ∀ x ∈ uPerp N.F N.F', (∀ y ∈ uPerp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
    intro x hx
    constructor
    · intro h
      have h1 : x ∈ N.F.X ⊔ N.F'.X := UnimodQuot.mem_of_perp_perp H _ fun y hy => by
        rw [← H.herm, h y hy, star_zero]
      exact (hV x (hXV h1)).1 ((mem_perp_iff H _ x).1 ((hW x).2 ⟨hx, h _ hzS⟩))
    · intro h y hy
      rw [← H.herm, (mem_perp_iff H _ y).1 hy x (hIX h), star_zero]
  obtain ⟨a1, a2, a3, a4⟩ := perp_prim H hIS hrad hL hT (N.hT ▸ N.F.zz) hp hW
  obtain ⟨b1, -, b3, -⟩ := perp_prim H hIS hrad hL' hT (N.hT' ▸ N.F'.zz) hp' hW'
  have e : flagPairDefinitePartLattice N.F' N.F Λ = latL N.F' N.F Λ ⊓ rs (𝓞 K) (wSp N.F N.F') := by rw [flagPairDefinitePartLattice, hww]
  rw [e]
  exact ⟨a1, b1, a2, a3, b3, a4⟩

end GlobalTheory.DegCnt.PrimPerp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameComplementChangeOfBasis
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem frameForm_symm_zero {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : Hᴴ = H)
    (x y : Fin N → ℂ) : star x ⬝ᵥ (H *ᵥ y) = star (star y ⬝ᵥ (H *ᵥ x)) := by
  rw [star_dotProduct, star_mulVec, hH, ← dotProduct_mulVec]

private theorem dotProduct_mulVec_sum_smul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} {ι : Type}
    [Fintype ι] (x : Fin N → ℂ) (g : ι → ℂ) (v : ι → Fin N → ℂ) :
    star x ⬝ᵥ (H *ᵥ ∑ i, g i • v i) = ∑ i, g i * (star x ⬝ᵥ (H *ᵥ v i)) := by
  simp [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul]

theorem frame_orthogonal_eq_zero {N r k : ℕ} {H : Matrix (Fin N) (Fin N) ℂ}
    {e f : Fin r → Fin N → ℂ} {z : Fin N → ℂ} {w : Fin k → Fin N → ℂ}
    (hN : N = 2 * r + k + 1) (hH : Hᴴ = H)
    (hee : ∀ a b, star (e a) ⬝ᵥ (H *ᵥ e b) = 0) (hff : ∀ a b, star (f a) ⬝ᵥ (H *ᵥ f b) = 0)
    (hef : ∀ a b, star (e a) ⬝ᵥ (H *ᵥ f b) = if a = b then 1 else 0)
    (hz : ∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 ∧ star (f a) ⬝ᵥ (H *ᵥ z) = 0)
    (hzz : star z ⬝ᵥ (H *ᵥ z) ≠ 0)
    (hww : ∀ a b, star (w a) ⬝ᵥ (H *ᵥ w b) = if a = b then 1 else 0)
    (hw : ∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ w a) = 0) ∧
      star z ⬝ᵥ (H *ᵥ w a) = 0)
    (u : Fin N → ℂ) (hu : (∀ c, star (e c) ⬝ᵥ (H *ᵥ u) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ u) = 0) ∧
      star z ⬝ᵥ (H *ᵥ u) = 0) (huw : ∀ a, star (w a) ⬝ᵥ (H *ᵥ u) = 0) : u = 0 := by
  have sym := fun x y => frameForm_symm_zero hH x y
  have hfe : ∀ a b, star (f a) ⬝ᵥ (H *ᵥ e b) = if a = b then 1 else 0 := by
    intro a b
    rw [sym, hef b a]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab, hab.symm]
  have hze : ∀ a, star z ⬝ᵥ (H *ᵥ e a) = 0 := fun a => by rw [sym, (hz a).1, star_zero]
  have hzf : ∀ a, star z ⬝ᵥ (H *ᵥ f a) = 0 := fun a => by rw [sym, (hz a).2, star_zero]
  have hwe : ∀ a c, star (w a) ⬝ᵥ (H *ᵥ e c) = 0 := fun a c => by rw [sym, ((hw a).1 c).1, star_zero]
  have hwf : ∀ a c, star (w a) ⬝ᵥ (H *ᵥ f c) = 0 := fun a c => by rw [sym, ((hw a).1 c).2, star_zero]
  have hwz : ∀ a, star (w a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => by rw [sym, (hw a).2, star_zero]
  have hew : ∀ c a, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 := fun c a => ((hw a).1 c).1
  have hfw : ∀ c a, star (f c) ⬝ᵥ (H *ᵥ w a) = 0 := fun c a => ((hw a).1 c).2
  have hzw : ∀ a, star z ⬝ᵥ (H *ᵥ w a) = 0 := fun a => (hw a).2
  have hez : ∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => (hz a).1
  have hfz : ∀ a, star (f a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => (hz a).2
  set v : (Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit) → Fin N → ℂ :=
    Sum.elim (Sum.elim e f) (Sum.elim w fun _ => z) with hv
  have key : ∀ g : (Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit) → ℂ,
      (∀ j, star (v j) ⬝ᵥ (H *ᵥ ∑ i, g i • v i) = 0) → g = 0 := by
    intro g hg
    simp only [dotProduct_mulVec_sum_smul] at hg
    simp only [Fintype.sum_sum_type] at hg
    funext i
    rcases i with ((a | a) | (a | u))
    · have := hg (.inl (.inr a))
      simpa [hv, hfe, hff, hwe, hfw, hfz, mul_ite] using this
    · have := hg (.inl (.inl a))
      simpa [hv, hee, hef, hew, hez, mul_ite] using this
    · have := hg (.inr (.inl a))
      simpa [hv, hwe, hwf, hww, hwz, mul_ite] using this
    · have := hg (.inr (.inr u))
      simpa [hv, hze, hzf, hzw, hzz] using this
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := key g (fun j => by rw [hg, mulVec_zero, dotProduct_zero])
    exact congrFun this i
  have hcard : Fintype.card ((Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit)) = Module.finrank ℂ (Fin N → ℂ) := by
    simp [hN]
    ring
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hu' : u ∈ Submodule.span ℂ (Set.range v) := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu'
  have hg0 := key g (fun j => by
    rw [hg]
    rcases j with ((a | a) | (a | _))
    · simpa [hv] using (hu.1 a).1
    · simpa [hv] using (hu.1 a).2
    · simpa [hv] using huw a
    · simpa [hv] using hu.2)
  rw [← hg, hg0]
  simp

theorem frame_complement_change_of_basis : ∀ (N r k n : ℕ) (h : k = n) (H : Matrix (Fin N) (Fin N) ℂ) (e f : Fin r → Fin N → ℂ) (z : Fin N → ℂ) (w : Fin k → Fin N → ℂ) (q : Fin n → Fin N → ℂ), N = 2 * r + k + 1 → Hᴴ = H → IsUnit H.det → (∀ a b, star (e a) ⬝ᵥ (H *ᵥ e b) = 0) → (∀ a b, star (f a) ⬝ᵥ (H *ᵥ f b) = 0) → (∀ a b, star (e a) ⬝ᵥ (H *ᵥ f b) = if a = b then 1 else 0) → (∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 ∧ star (f a) ⬝ᵥ (H *ᵥ z) = 0) → star z ⬝ᵥ (H *ᵥ z) ≠ 0 → (∀ a b, star (w a) ⬝ᵥ (H *ᵥ w b) = if a = b then 1 else 0) → (∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ w a) = 0) ∧ star z ⬝ᵥ (H *ᵥ w a) = 0) → (∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ q a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ q a) = 0) ∧ star z ⬝ᵥ (H *ᵥ q a) = 0) → ∀ G : Matrix (Fin n) (Fin n) ℂ, (∀ a b, G a b = star (q a) ⬝ᵥ (H *ᵥ q b)) → IsUnit G.det → ∃ o : Matrix (Fin n) (Fin n) ℂ, IsUnit o.det ∧ oᴴ * G * o = 1 ∧ ∀ s : Matrix (Fin N) (Fin N) ℂ, sᴴ * H * s = H → (∀ a, s *ᵥ e a = e a ∧ s *ᵥ f a = f a) → s *ᵥ z = z → ∃ m ∈ Matrix.unitaryGroup (Fin n) ℂ, m.submatrix (Fin.cast h) (Fin.cast h) = (Matrix.of fun a b => star (w a) ⬝ᵥ (H *ᵥ (s *ᵥ w b))) ∧ G⁻¹ * (Matrix.of fun a b => star (q a) ⬝ᵥ (H *ᵥ (s *ᵥ q b))) = o * m * o⁻¹ := by
  intro N r k n h H e f z w q hN hH _hdet hee hff hef hz hzz hww hw hq G hG hGdet
  subst h
  have sym := fun x y => frameForm_symm_zero hH x y
  have expand : ∀ x : Fin N → ℂ, ((∀ c, star (e c) ⬝ᵥ (H *ᵥ x) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ x) = 0) ∧
      star z ⬝ᵥ (H *ᵥ x) = 0) → x = ∑ a, (star (w a) ⬝ᵥ (H *ᵥ x)) • w a := by
    intro x hx
    have h0 := frame_orthogonal_eq_zero hN hH hee hff hef hz hzz hww hw
      (x - ∑ a, (star (w a) ⬝ᵥ (H *ᵥ x)) • w a) ?_ ?_
    · exact sub_eq_zero.mp h0
    · refine ⟨fun c => ⟨?_, ?_⟩, ?_⟩
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, (hx.1 c).1, fun a => ((hw a).1 c).1]
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, (hx.1 c).2, fun a => ((hw a).1 c).2]
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, hx.2, fun a => (hw a).2]
    · intro a
      simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, hww, mul_ite]
  have parseval : ∀ x y : Fin N → ℂ,
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ y) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ y) = 0) ∧ star z ⬝ᵥ (H *ᵥ y) = 0) →
      star x ⬝ᵥ (H *ᵥ y) = ∑ c, star (star (w c) ⬝ᵥ (H *ᵥ x)) * (star (w c) ⬝ᵥ (H *ᵥ y)) := by
    intro x y hy
    conv_lhs => rw [expand y hy]
    rw [dotProduct_mulVec_sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sym x (w c), mul_comm]
  set P := Matrix.of fun c b => star (w c) ⬝ᵥ (H *ᵥ q b) with hPdef
  have hGP : G = Pᴴ * P := by
    ext a b
    rw [hG, parseval (q a) (q b) (hq b), Matrix.mul_apply]
    simp [hPdef, Matrix.conjTranspose_apply]
  have hP : IsUnit P.det := by
    rw [hGP, Matrix.det_mul, Matrix.det_conjTranspose] at hGdet
    exact isUnit_of_mul_isUnit_right hGdet
  have hPh : IsUnit Pᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hP.star
  refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_det _ hP, ?_, ?_⟩
  · rw [hGP, Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_assoc (Pᴴ)⁻¹,
      Matrix.nonsing_inv_mul _ hPh, Matrix.one_mul, Matrix.mul_nonsing_inv _ hP]
  intro s hs hfix hzfix
  have pres : ∀ x y : Fin N → ℂ, star (s *ᵥ x) ⬝ᵥ (H *ᵥ (s *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
    intro x y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hs]
  have sperp : ∀ x : Fin N → ℂ,
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ x) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ x) = 0) ∧ star z ⬝ᵥ (H *ᵥ x) = 0) →
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0) ∧
        star z ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0) := by
    intro x hx
    refine ⟨fun c => ⟨?_, ?_⟩, ?_⟩
    · rw [← (hfix c).1, pres]; exact (hx.1 c).1
    · rw [← (hfix c).2, pres]; exact (hx.1 c).2
    · rw [← hzfix, pres]; exact hx.2
  set M := Matrix.of fun a b => star (w a) ⬝ᵥ (H *ᵥ (s *ᵥ w b)) with hMdef
  refine ⟨M, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply, ← hww a b, ← pres (w a) (w b),
      parseval _ _ (sperp _ (hw b))]
    simp [hMdef, Matrix.conjTranspose_apply]
  · ext a b
    simp [hMdef]
  · have hQ : (Matrix.of fun a b => star (q a) ⬝ᵥ (H *ᵥ (s *ᵥ q b))) = Pᴴ * (M * P) := by
      ext a b
      have hsq : s *ᵥ q b = ∑ d, P d b • (s *ᵥ w d) := by
        conv_lhs => rw [expand (q b) (hq b)]
        rw [mulVec_sum]
        simp [mulVec_smul, hPdef]
      rw [Matrix.of_apply, parseval _ _ (sperp _ (hq b)), Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hsq, dotProduct_mulVec_sum_smul, Matrix.mul_apply]
      simp [hPdef, hMdef, Matrix.conjTranspose_apply, mul_comm]
    rw [hQ, hGP, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Pᴴ)⁻¹, Matrix.nonsing_inv_mul _ hPh, Matrix.one_mul, Matrix.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRankClausesFirstHalf
section
namespace GlobalTheory.Diag.PG

theorem rankNums_first_half : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x →
    ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * m ^ 5 * f * x ^ eps ≤ k ∧
      Real.log f ≤ Real.sqrt (m / 2 - 1) ∧ C * x ^ eps ≤ f * Real.log k ∧ C * (m ^ 2 * x ^ eps) ≤ k ∧ C ≤ m ∧
      C * x ^ eps ≤ m - 1 ∧ C ≤ k ∧ 1 < x ^ eps := by
  intro eps CD heps heps' _ C
  set C1 : ℝ := max C 2 with hC1
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hC12 : 2 ≤ C1 := le_max_right _ _
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, C1 ≤ x ^ (eps / 2) :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop C1
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, C1 + 1 ≤ x ^ ((1 : ℝ) / 52) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop (C1 + 1)
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, (200 : ℝ) ≤ x ^ ((1 : ℝ) / 16) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 200
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x := Filter.eventually_ge_atTop 2
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and e4)))
  refine ⟨x0, fun x hx m f k lrd Del h => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hx0 x hx
  have hx0' : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  set A := x ^ eps with hA
  have hA1 : 1 < A := Real.one_lt_rpow hx1 heps
  set y := x ^ ((1 : ℝ) / 52) with hy
  have hAy : A ≤ y := Real.rpow_le_rpow_of_exponent_le hx1.le heps'.le
  set q := x ^ ((1 : ℝ) / 4) with hq
  have hqy : q = y ^ (13 : ℕ) := by
    rw [hq, hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
  have hy1 : 1 ≤ y := by linarith
  have hy13 : y ^ 2 ≤ y ^ (13 : ℕ) := pow_le_pow_right₀ hy1 (by norm_num)
  have hq_big : C1 * A + 1 ≤ q := by
    rw [hqy]; nlinarith
  have hm : C1 * A + 1 ≤ m := le_trans hq_big h.m_lo
  have hm1 : 1 ≤ m := by nlinarith
  have hm3 : 3 ≤ m := by nlinarith
  have hm4 : m ≤ m ^ 4 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hf : m ≤ f := le_trans hm4 h.mf
  have hf1 : 1 ≤ f := by linarith
  have hk : m ≤ k := le_trans hf h.fk
  have hCA : C * A ≤ C1 * A := mul_le_mul_of_nonneg_right hCC1 (by linarith)
  have hB0 : 0 ≤ m ^ 5 * f * A := by positivity
  have hk1 : C1 * (m ^ 5 * f * A) ≤ k :=
    le_trans (mul_le_mul_of_nonneg_right h1 hB0) h.k_lo
  have hm25 : m ^ 2 ≤ m ^ 5 * f := by
    have : m ^ 2 ≤ m ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
    nlinarith
  have hlogk : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hC1A : C1 ≤ C1 * A := by
    have := mul_le_mul_of_nonneg_left hA1.le (by linarith : (0:ℝ) ≤ C1)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hA1⟩
  · have : C * (m ^ 5 * f * A) ≤ C1 * (m ^ 5 * f * A) := mul_le_mul_of_nonneg_right hCC1 hB0
    calc C * m ^ 5 * f * A = C * (m ^ 5 * f * A) := by ring
      _ ≤ k := le_trans this hk1
  ·
    set t := x ^ ((1 : ℝ) / 16) with ht
    have hqt : q = t ^ (4 : ℕ) := by
      rw [hq, ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
    have hf0 : 0 < f := by linarith
    have hlf : Real.log f ≤ 5 * Real.log x := by
      have : Real.log f ≤ Real.log (x ^ (5 : ℝ)) :=
        Real.log_le_log hf0 (le_trans h.fk h.k_hi)
      rw [Real.log_rpow (by linarith)] at this
      exact this
    have hlx : Real.log x ≤ t / (1 / 16) := Real.log_le_rpow_div hx0' (by norm_num)
    have h80 : 80 * t ≤ Real.sqrt (m / 2 - 1) := by
      rw [Real.le_sqrt (by linarith)]
      have hmq : t ^ (4 : ℕ) ≤ m := hqt ▸ h.m_lo
      have ht2 : 40000 ≤ t ^ 2 := by nlinarith
      have ht4 : t ^ (4 : ℕ) = t ^ 2 * t ^ 2 := by ring
      have : (80 * t) ^ 2 = 6400 * t ^ 2 := by ring
      nlinarith
      all_goals linarith
    have : 5 * Real.log x ≤ 80 * t := by
      have : t / (1 / 16) = 16 * t := by ring
      linarith
    linarith
  · calc C * A ≤ C1 * A := hCA
      _ ≤ m := by linarith
      _ ≤ f := hf
      _ = f * 1 := (mul_one f).symm
      _ ≤ f * Real.log k := mul_le_mul_of_nonneg_left hlogk (by linarith)
  · have hB2 : 0 ≤ m ^ 2 * A := by positivity
    calc C * (m ^ 2 * A) ≤ C1 * (m ^ 2 * A) := mul_le_mul_of_nonneg_right hCC1 hB2
      _ ≤ C1 * (m ^ 5 * f * A) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_right hm25 (by linarith)
      _ ≤ k := hk1
  · linarith
  · linarith
  · linarith

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassSubspaceCyclicDiscriminantLeStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitStabilizerMass_subspace_cyclicDiscriminant_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (n N₀ : ℕ), orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ discN (hRes h U) (latIn U L) = n} ≤ orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) * (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) * (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞) := by
  first | exact @GlobalTheory.Mass.FixedSub.orbMass_stabilizer_le | exact GlobalTheory.Mass.FixedSub.orbMass_stabilizer_le | (intros; apply GlobalTheory.Mass.FixedSub.orbMass_stabilizer_le <;> assumption)
end

