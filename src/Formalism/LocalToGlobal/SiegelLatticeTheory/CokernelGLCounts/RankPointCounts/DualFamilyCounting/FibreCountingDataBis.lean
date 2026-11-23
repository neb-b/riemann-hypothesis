module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CondZIff

@[expose] public section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def crd (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F) (x : V) (j : Fin m) : K :=
  h (b j) x / jK (ι (a j))

def gmap (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) : V →ₗ[𝓞 K] V where
  toFun x := ∑ i, (∑ j, jK (Y i j) * crd h b a x j) • b i
  map_add' x y := by
    simp only [crd, map_add (f := _), add_div, mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' c x := by
    simp only [crd, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algebra_compatible_smul K c x, algebra_compatible_smul K c, smul_smul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul]; ring

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

theorem crd_sub (x y : V) (j : Fin m) : crd h b a (x - y) j = crd h b a x j - crd h b a y j := by
  simp only [crd, map_sub, sub_div]

theorem crd_smul (c : 𝓞 K) (x : V) (j : Fin m) : crd h b a (c • x) j = jK c * crd h b a x j := by
  unfold crd
  rw [algebra_compatible_smul K c x, LinearMap.map_smul, smul_eq_mul, mul_div_assoc]

variable (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include horth hdiag ha

theorem crd_sum (c : Fin m → K) (k : Fin m) : crd h b a (∑ i, c i • b i) k = c k := by
  have e : ∀ j, jK (ι (a j)) = algebraMap F K ((a j : 𝓞 F) : F) := fun j =>
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K (a j)).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K (a j))
  unfold crd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single k]
  · have hne : jK (ι (a k)) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr
      ((map_ne_zero_iff ι (RingOfIntegers.algebraMap.injective F K)).mpr (ha k))
    rw [LinearMap.map_smul, hdiag k, smul_eq_mul, ← e k, mul_div_assoc, div_self hne, mul_one]
  · intro i _ hik
    rw [LinearMap.map_smul, horth k i (Ne.symm hik), smul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem crd_gmap (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (k : Fin m) :
    crd h b a (gmap h b a Y x) k = ∑ j, jK (Y k j) * crd h b a x j := by
  rw [show gmap h b a Y x = ∑ i, (∑ j, jK (Y i j) * crd h b a x j) • b i from rfl]
  exact crd_sum horth hdiag ha _ k

theorem h_b (x : V) (k : Fin m) : h (b k) x = jK (ι (a k)) * crd h b a x k := by
  have hne : jK (ι (a k)) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr
    ((map_ne_zero_iff ι (RingOfIntegers.algebraMap.injective F K)).mpr (ha k))
  unfold crd
  rw [mul_div_assoc', eq_div_iff hne, mul_comm]

variable (hbX : ∀ i, b i ∈ (⊤ : Submodule K V))
  (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
include hbX hloc

theorem coordsT (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x : V) : x = ∑ i, crd h b a x i • b i := by
  have hxs : x ∈ Submodule.span K (Set.range b) := by
    have hx : x ∈ (⊤ : Submodule K V) := Submodule.mem_top
    rw [← hL.2] at hx
    refine Submodule.span_le.mpr ?_ hx
    intro y hy
    have hyLoc := localizedQuotients.le_locF 𝔭 L hy
    rw [← hloc] at hyLoc
    exact G2.locF_le_spanK h𝔭 hyLoc
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxs
  simp only [crd_sum horth hdiag ha]

theorem h_expand (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x y : V) :
    h x y = ∑ i, star (crd h b a x i) * jK (ι (a i)) * crd h b a y i := by
  have e : ∀ j, jK (ι (a j)) = algebraMap F K ((a j : 𝓞 F) : F) := fun j =>
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K (a j)).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K (a j))
  have e1 : ∀ j, h x (b j) = star (crd h b a x j) * jK (ι (a j)) := by
    intro j
    have hx := coordsT horth hdiag ha hbX hloc h𝔭 hL x
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
    · rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hdiag j, smul_eq_mul, starRingEnd_apply, ← e j]
    · intro i _ hij
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, horth i j hij, smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hy := coordsT horth hdiag ha hbX hloc h𝔭 hL y
  conv_lhs => rw [hy]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul, e1 j, smul_eq_mul]
  ring

theorem mem_B (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x : V) :
    x ∈ locF 𝔭 L ↔ ∀ i, crd h b a x i ∈ HU.SP K 𝔭 := by
  have := h𝔭
  rw [← hloc]
  constructor
  · rintro ⟨s, hs, hsx⟩ i
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsx
    have hz' : s • x = ∑ j, jK (z j) • b j := by
      exact hz.symm.trans (Finset.sum_congr rfl fun j _ => algebra_compatible_smul K (z j) (b j))
    rw [HU.mem_SP_iff_locF]
    refine ⟨s, hs, ?_⟩
    rw [Algebra.smul_def, ← crd_smul, hz', crd_sum horth hdiag ha]
    exact Submodule.mem_one.mpr ⟨z i, rfl⟩
  · intro hx
    rw [coordsT horth hdiag ha hbX hloc h𝔭 hL x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨s, hs, hsc⟩ := HU.mem_SP_iff_locF.mp (hx i)
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp hsc
    refine ⟨s, hs, ?_⟩
    rw [← smul_assoc, ← hz, algebraMap_smul K]
    exact Submodule.smul_mem _ z (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_A (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn ⊤ L) (x : V) :
    x ∈ locF 𝔭 (dualIn h ⊤ L) ↔ ∀ i, jK (ι (a i)) * crd h b a x i ∈ HU.SP K 𝔭 := by
  rw [G2.mem_locF_dualIn_iff (hbX := hbX) (hloc := hloc) (horth := horth) (hdiag := hdiag) (ha := ha)
    hF h𝔭 hL x]
  refine ⟨fun hx i => ?_, fun hx => ⟨Submodule.mem_top, fun i => ?_⟩⟩
  · rw [← h_b horth hdiag ha x i]
    exact hx.2 i
  · rw [h_b horth hdiag ha x i]
    exact hx i

end

end Formalism.L2.SG.Pf.fibreCountingData
