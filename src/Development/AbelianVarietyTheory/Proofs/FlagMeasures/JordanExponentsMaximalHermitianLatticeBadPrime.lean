module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFLeSpanK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsSubDivMemSP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0032
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0023
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF

@[expose] public section

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

noncomputable section
namespace GlobalTheory.MaxLatExpo.LocalProofs

open Module Formalism.L2.SG.Pf.G2

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "jK" => algebraMap (𝓞 K) K
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

private theorem coe_iota_eq_algebraMap_coe (a : 𝓞 F) : jK (ι a) = algebraMap F K (a : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

private theorem jK_iota_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : jK (ι a) ≠ 0 := by
  rw [coe_iota_eq_algebraMap_coe]
  refine (map_ne_zero (algebraMap F K)).mpr ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha

private theorem jK_ne_zero_of_mem_closure_prime_compl {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    jK s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨t, ht, rfl⟩ := hy
    refine jK_iota_ne_zero ?_
    rintro rfl
    exact ht 𝔭.zero_mem
  | one => simp
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_ne_zero hy hz

theorem smul_eq_jK (c : 𝓞 K) (v : V) : c • v = jK c • v := (algebraMap_smul K c v).symm

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {n : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F}

theorem h_sum (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0) (hdiag : ∀ i, h (b i) (b i) = jK (ι (a i)))
    (c : Fin n → K) (k : Fin n) : h (b k) (∑ i, c i • b i) = c k * jK (ι (a k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · rw [hdiag]
  · intro i _ hik
    rw [horth k i (Ne.symm hik), mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem locF_le_spanK (h𝔭 : 𝔭.IsPrime) :
    locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) ≤
      (Submodule.span K (Set.range b)).restrictScalars (𝓞 K) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 : jK s ≠ 0 := jK_ne_zero_of_mem_closure_prime_compl hs
  have h1 : s • x ∈ Submodule.span K (Set.range b) :=
    Submodule.span_le_restrictScalars (𝓞 K) K _ hsx
  have h2 : (jK s)⁻¹ • (s • x) ∈ Submodule.span K (Set.range b) := Submodule.smul_mem _ _ h1
  rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul] at h2
  exact h2

variable (hbX : ∀ i, b i ∈ X) (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
  (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include hbX hloc horth hdiag ha

theorem coords (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn X L) {x : V} (hx : x ∈ X) :
    x = ∑ i, (h (b i) x / jK (ι (a i))) • b i := by
  have hxs : x ∈ Submodule.span K (Set.range b) := by
    rw [← hL.2] at hx
    refine (Submodule.span_le.mpr ?_) hx
    intro y hy
    haveI := h𝔭
    have h1 : y ∈ locF 𝔭 L := Formalism.HermitianLattices.Ext.L3.localizedQuotients.le_locF 𝔭 L hy
    rw [← hloc] at h1
    exact locF_le_spanK h𝔭 h1
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxs
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h_sum horth (fun j => by rw [hdiag j]; exact (coe_iota_eq_algebraMap_coe (a j)).symm) c i,
    mul_div_cancel_right₀ _ (jK_iota_ne_zero (ha i))]

theorem mem_B_iff (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn X L) (x : V) :
    x ∈ locF 𝔭 L ↔ x ∈ X ∧ ∀ i, h (b i) x / jK (ι (a i)) ∈ HU.SP K 𝔭 := by
  haveI := h𝔭
  have hdiag' : ∀ i, h (b i) (b i) = jK (ι (a i)) := fun i => by
    rw [hdiag i]; exact (coe_iota_eq_algebraMap_coe (a i)).symm
  have key : ∀ w ∈ Submodule.span (𝓞 K) (Set.range b), ∀ i,
      h (b i) w / jK (ι (a i)) ∈ (1 : Submodule (𝓞 K) K) := by
    intro w hw i
    obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hw
    have e : (∑ j, z j • b j) = ∑ j, jK (z j) • b j :=
      Finset.sum_congr rfl fun j _ => smul_eq_jK _ _
    rw [e, h_sum horth hdiag' _ i, mul_div_cancel_right₀ _ (jK_iota_ne_zero (ha i))]
    exact Submodule.mem_one.mpr ⟨z i, rfl⟩
  rw [← hloc]
  constructor
  · intro hx
    have hxs := locF_le_spanK h𝔭 hx
    obtain ⟨s, hs, hsx⟩ := hx
    refine ⟨Submodule.span_le.mpr ?_ hxs, fun i => ?_⟩
    · rintro _ ⟨j, rfl⟩
      exact hbX j
    · rw [HU.mem_SP_iff_locF]
      refine Exists.intro s ⟨hs, ?_⟩
      have e : s • (h (b i) x / jK (ι (a i))) = h (b i) (s • x) / jK (ι (a i)) := by
        rw [smul_eq_jK s x, map_smul, smul_eq_mul, Algebra.smul_def, mul_div_assoc]
      rw [e]
      exact key _ hsx i
  · rintro ⟨hxX, hc⟩
    rw [coords hbX hloc horth hdiag ha h𝔭 hL hxX]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨s, hs, hsc⟩ := (HU.mem_SP_iff_locF).mp (hc i)
    obtain ⟨y, hy⟩ := Submodule.mem_one.mp hsc
    refine Exists.intro s ⟨hs, ?_⟩
    rw [← smul_assoc, ← hy, ← smul_eq_jK]
    exact Submodule.smul_mem _ y (Submodule.subset_span ⟨i, rfl⟩)

end

theorem jK_ι (t : 𝓞 F) : jK (ι t) = algebraMap F K (t : F) := rfl

theorem jK_ι_ne_zero {t : 𝓞 F} (ht : t ≠ 0) : jK (ι t) ≠ 0 := by
  rw [jK_ι]
  intro h
  apply ht
  have h1 : ((t : F)) = 0 := (map_eq_zero_iff _ (algebraMap F K).injective).1 h
  exact_mod_cast h1

theorem jordan_ne_zero_of_notMem {𝔭 : Ideal (𝓞 F)} {t : 𝓞 F} (ht : t ∉ 𝔭) : t ≠ 0 := by
  rintro rfl
  exact ht 𝔭.zero_mem

theorem exists_inv_mod {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) (e : ℕ) :
    ∃ u : 𝓞 F, 1 - t * u ∈ 𝔭 ^ e := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨y * ∑ k ∈ Finset.range e, i ^ k, ?_⟩
  have h1 : t * (y * ∑ k ∈ Finset.range e, i ^ k) = 1 - i ^ e := by
    rw [← mul_neg_geom_sum, ← hyi]
    ring
  rw [h1, sub_sub_cancel]
  exact Ideal.pow_mem_pow hi e

theorem exists_mul_mem_span {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ x ∈ 𝔭 ^ vF 𝔭 a, t * x ∈ Ideal.span {a} := by
  have hle : Ideal.span {a} ≤ 𝔭 ^ vF 𝔭 a :=
    (Ideal.span_singleton_le_iff_mem _).2 (localValuationFiltration.mem_pow_vF h𝔭 ha)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJp : ¬ J ≤ 𝔭 := by
    intro hJ𝔭
    apply localValuationFiltration.notMem_pow_vF h𝔭 ha
    have : Ideal.span {a} ≤ 𝔭 ^ (vF 𝔭 a + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hJ𝔭
    exact this (Ideal.mem_span_singleton_self a)
  obtain ⟨t, htJ, ht𝔭⟩ := SetLike.not_le_iff_exists.1 hJp
  refine ⟨t, ht𝔭, fun x hx => ?_⟩
  rw [hJ, mul_comm t x]
  exact Ideal.mul_mem_mul hx htJ

theorem div_mem_SP_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) (z : 𝓞 K) :
    haveI := h𝔭.isPrime
    jK z / jK (ι a) ∈ HU.SP K 𝔭 ↔ z ∈ extP K 𝔭 ^ vF 𝔭 a := by
  have := h𝔭.isPrime
  have ha' := jK_ι_ne_zero (K := K) ha
  rw [HU.mem_SP]
  constructor
  · rintro ⟨t, ht, w, hw⟩
    have e1 : ι t * z = w * ι a := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_mul, map_mul, hw]
      field_simp
    obtain ⟨u, hu⟩ := exists_inv_mod h𝔭 ht (vF 𝔭 a)
    have hA : ι a ∈ extP K 𝔭 ^ vF 𝔭 a := localizedQuotients.ι_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 ha)
    have e2 : z = ι u * (ι t * z) + ι (1 - t * u) * z := by
      rw [map_sub, map_mul, map_one]
      ring
    rw [e2, e1]
    exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hA))
      (Ideal.mul_mem_right _ _ (localizedQuotients.ι_mem_pow hu))
  · intro hz
    obtain ⟨t, ht, htx⟩ := exists_mul_mem_span h𝔭 ha
    refine ⟨t, ht, ?_⟩
    have hle : Ideal.span {ι t} * extP K 𝔭 ^ vF 𝔭 a ≤ Ideal.span {ι a} := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro y hy
      unfold extP at hy
      rw [← Ideal.map_pow] at hy
      refine Submodule.span_induction (p := fun y _ => ι t * y ∈ Ideal.span {ι a}) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (htx x hx)
        rw [← map_mul, ← hc, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · simp
      · intro x y _ _ hx hy
        rw [mul_add]
        exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hx
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1
      (hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz))
    refine ⟨w, ?_⟩
    have := congrArg jK hw
    rw [map_mul, map_mul] at this
    field_simp
    rw [this]

end GlobalTheory.MaxLatExpo.LocalProofs

namespace GlobalTheory.MaxLatExpo

theorem main : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ P ∈ badP h M, ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ M (P.comap (algebraMap (𝓞 F) (𝓞 K))) b a → ∃ i, vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a i) = 1 ∧ ∀ j, j ≠ i → vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a j) = 0 := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd M hM P hPb b a hJ
  have hP : P.IsMaximal := hPb.1
  have hp : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  have hpp := hp.isPrime
  have hl : ∀ L : Submodule (𝓞 K) V, locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = loc (K := K) P L :=
    fun L => locF_eq_loc hK hF hP L
  obtain ⟨-, -, -, hloc⟩ := GlobalTheory.MaxLatStruct.main K V h hK hs (UnimodularLocalization.nondegenerate hd) M hM
  obtain ⟨hconj, -, -, x, hxM, ⟨a0, ha0x, ha0P, ha0P2⟩, hstr⟩ := hloc P hPb
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hconj
  obtain ⟨hbX, hspan, horth, hdiag, ha⟩ := hJ
  have hli : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h1 := congrArg (h (b k)) hg
    rw [map_sum, map_zero] at h1
    simp only [map_smul, smul_eq_mul] at h1
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [horth k j (Ne.symm hj), mul_zero])
      (by simp)] at h1
    have hn : h (b k) (b k) ≠ 0 := by
      rw [hdiag]
      exact (map_ne_zero (algebraMap F K)).2 (by exact_mod_cast ha k)
    exact (mul_eq_zero.mp h1).resolve_right hn
  have hbtop : Submodule.span K (Set.range b) = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hL : IsLatIn (⊤ : Submodule K V) M := by
    refine ⟨hM.1.1.fg, ?_⟩
    apply eq_top_iff.mpr
    rw [← hbtop, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hm : b i ∈ locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) M := by
      rw [← hspan]
      exact LocF.le_locF _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hpp M (b i)).1 hm
    have ht0 : algebraMap F K (t : F) ≠ 0 :=
      (map_ne_zero (algebraMap F K)).2 (by exact_mod_cast Formalism.L2.SG.Pf.G2.ne_zero_of_notMem ht)
    apply (Submodule.smul_mem_iff _ ht0).1
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) F K, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, algebraMap_smul]
    exact Submodule.subset_span htx
  have hdI : dualIn h ⊤ M = dual h M := by
    ext z; simp [dualIn]
  set p := P.comap (algebraMap (𝓞 F) (𝓞 K)) with hpdef
  set S := HU.SP K p with hSdef
  have hB : ∀ z, z ∈ locF p M ↔ ∀ i, h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun z => by
    exact (LocalProofs.mem_B_iff hbX hspan horth hdiag ha hpp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hA : ∀ z, z ∈ locF p (dual h M) ↔ ∀ i, h (b i) z ∈ S := fun z => by
    rw [← hdI]; exact (Formalism.L2.SG.Pf.G2.mem_locF_dualIn_iff hbX hspan horth hdiag ha hF hp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hR : ∀ c, c ∈ locR (K := K) P → c ∈ S := fun c hc => HU.mem_SP_iff_locF.2 (by rw [locF_eq_loc hK hF hP (1 : Submodule (𝓞 K) K)]; exact hc)

  obtain ⟨a0', ha0'⟩ : a0 ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
    refine (conjO_eq_iff_mem_range hF a0).1 (RingOfIntegers.ext ?_)
    rw [conjO_coe]
    change star ((a0 : K)) = (a0 : K)
    rw [ha0x]; exact hs.eq x x
  have ha0ne : a0' ≠ 0 := by
    rintro rfl
    apply ha0P2
    rw [← ha0', map_zero]; exact Submodule.zero_mem _
  have hv0 : vF p a0' = 1 := by
    have h1 := localValuationFiltration.mem_pow_vF hp ha0ne
    have h2 := localValuationFiltration.notMem_pow_vF hp ha0ne
    have hin : a0' ∈ p := by rw [hpdef, Ideal.mem_comap, ha0']; exact ha0P
    rcases Nat.lt_or_ge (vF p a0') 2 with hlt | hge
    · interval_cases hv : vF p a0'
      · rw [zero_add, pow_one] at h2; exact absurd hin h2
      · rfl
    · exfalso
      apply ha0P2
      have := localizedQuotients.ι_mem_pow (K := K) (Ideal.pow_le_pow_right hge h1)
      rwa [hext, ha0'] at this
  have hd0 : h x x = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') := by rw [ha0', ← ha0x]
  have hdne : h x x ≠ 0 := by rw [hd0]; exact LocalProofs.jK_ι_ne_zero ha0ne
  have hα : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ≠ 0 := fun i => LocalProofs.jK_ι_ne_zero (ha i)
  have hy : ∀ k i, h (b k) ((algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i) = if k = i then 1 else 0 := by
    intro k i
    rw [LinearMap.map_smul, smul_eq_mul]
    split_ifs with hki
    · subst hki; rw [hdiag]; exact inv_mul_cancel₀ (hα k)
    · rw [horth k i hki, mul_zero]
  have hyA : ∀ i, (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i ∈ loc (K := K) P (dual h M) := by
    intro i
    rw [← hl, hA]
    intro k
    rw [hy]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  choose c hc hcM using fun i => hstr _ (hyA i)
  have hcS : ∀ i, c i ∈ S := fun i => hR _ (hc i)
  have hE : ∀ i k, ((if k = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b k) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S := by
    intro i k
    have h1 := hcM i
    rw [← hl] at h1
    have := (hB _).1 h1 k
    rwa [map_sub, hy, LinearMap.map_smul, smul_eq_mul] at this
  have hξ : ∀ k, h (b k) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S :=
    (hB x).1 (LocF.le_locF p M hxM)
  have hdS : h x x ∈ S := by rw [hd0]; exact HU.jK_mem_SP _

  have hle1 : ∀ i, vF p (a i) ≤ 1 := by
    intro i
    by_contra hgt
    push_neg at hgt
    have h1 : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) =
          h x x * (((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) + c i * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl]; field_simp; ring
      rw [e]
      exact S.add_mem (S.mul_mem hdS (hE i i)) (S.mul_mem (hcS i) (hξ i))
    have h1' : algebraMap (𝓞 K) K a0 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      rw [show algebraMap (𝓞 K) K a0 = h x x from ha0x]; exact h1
    have h2 := (LocalProofs.div_mem_SP_iff hp (ha i) a0).1 h1'
    rw [hext] at h2
    exact ha0P2 (Ideal.pow_le_pow_right hgt h2)
  have huniq : ∀ i j, i ≠ j → vF p (a j) = 1 → 1 ≤ vF p (a i) → False := by
    intro i j hij hj hi
    have hci : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      have e : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) = c i * (((if j = j then (1 : K) else 0) - c j * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)))
          - c j * (((if j = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) := by
        rw [if_pos rfl, if_neg (fun e => hij e.symm)]; ring
      rw [e]
      exact S.sub_mem (S.mul_mem (hcS i) (hE j j)) (S.mul_mem (hcS j) (hE i j))
    obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 (hcS i)
    have hw1 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      rw [hw, mul_div_assoc]; exact S.mul_mem (HU.jK_mem_SP _) hci
    have hwP : w ∈ P := by
      have := (LocalProofs.div_mem_SP_iff hp (ha j) w).1 hw1
      rwa [hj, pow_one, hext] at this
    have hw2 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') ∈ S :=
      (LocalProofs.div_mem_SP_iff hp ha0ne w).2 (by rw [hv0, pow_one, hext]; exact hwP)
    have htne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := LocalProofs.jK_ι_ne_zero (Formalism.L2.SG.Pf.G2.ne_zero_of_notMem ht)
    have htinv : (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ ∈ S := HU.mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ htne]⟩
    have hcd : c i * (h x x)⁻¹ ∈ S := by
      have e : c i * (h x x)⁻¹ = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ * (algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0')) := by
        rw [hw, ← hd0]; field_simp
      rw [e]; exact S.mul_mem htinv hw2
    have h1 : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = ((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))
          + (c i * (h x x)⁻¹) * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl, map_one]; ring
      rw [e]; exact S.add_mem (hE i i) (S.mul_mem hcd (hξ i))
    have h2 := (LocalProofs.div_mem_SP_iff hp (ha i) 1).1 h1
    rw [hext] at h2
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (Ideal.pow_le_self (by omega) h2))
  have hex : ∃ i, vF p (a i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hPb.2
    have hinv : ∀ i, algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun i =>
      (LocalProofs.div_mem_SP_iff hp (ha i) 1).2 (by rw [hcon i, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
    have heq : loc (K := K) P (dual h M) = loc (K := K) P M := by
      rw [← hl, ← hl]
      ext z
      rw [hA, hB]
      constructor
      · intro hz i
        have e : h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = h (b i) z * (algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          rw [map_one]; ring
        rw [e]; exact S.mul_mem (hz i) (hinv i)
      · intro hz i
        have e : h (b i) z = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * (h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          field_simp [hα i]
        rw [e]; exact S.mul_mem (HU.jK_mem_SP _) (hz i)
    obtain ⟨σ, hσ⟩ := GlobalTheory.MaxLatStruct.star_int (K := K)
    have hinj := IsFractionRing.injective (𝓞 K) K
    have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
      fun r => ⟨σ r, hσ r⟩
    unfold IsUnimodularAt
    rw [locDual_dualAt_loc h hinj hstar, ← le_antisymm (locDual_loc_dual_le h P M)
      (locDual_dualAt_le h hstar P M hM.1.1.fg)]
    exact heq
  obtain ⟨i, hi⟩ := hex
  have hi1 : vF p (a i) = 1 := le_antisymm (hle1 i) (Nat.one_le_iff_ne_zero.2 hi)
  refine ⟨i, hi1, fun j hji => ?_⟩
  by_contra hj
  exact huniq j i hji hi1 (Nat.one_le_iff_ne_zero.2 hj)

end GlobalTheory.MaxLatExpo
