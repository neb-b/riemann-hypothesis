module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLeMaximalIdealPowSmulOfDirected
section
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Chevalley

end GlobalTheory.Chevalley

namespace GlobalTheory.Chevalley

end GlobalTheory.Chevalley

namespace GlobalTheory.Chevalley

open TensorProduct Polynomial IsLocalRing in
private theorem isArtinian_quotient_maximalIdeal_pow_succ_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (n : ℕ) : IsArtinian B (M ⧸ (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M))) := by
  have hmin : maximalIdeal B ∈ (maximalIdeal B ^ (n + 1)).minimalPrimes := by
    refine ⟨⟨(maximalIdeal.isMaximal B).isPrime, Ideal.pow_le_self (Nat.succ_ne_zero n)⟩, ?_⟩
    rintro q ⟨hq, hle⟩ -
    exact hq.le_of_pow_le hle
  have : IsArtinianRing (B ⧸ maximalIdeal B ^ (n + 1)) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  exact isArtinian_of_surjective_algebraMap
    (Ideal.Quotient.mk_surjective (I := maximalIdeal B ^ (n + 1)))

open TensorProduct Polynomial IsLocalRing in
private theorem mem_of_forall_mem_sup_maximalIdeal_pow_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (K : Submodule B M) (x : M)
    (h : ∀ n, x ∈ K ⊔ maximalIdeal B ^ n • (⊤ : Submodule B M)) : x ∈ K := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M ⧸ K) (maximalIdeal B)
    (maximalIdeal.isMaximal B).ne_top
  have hx : K.mkQ x ∈ ⨅ n, maximalIdeal B ^ n • (⊤ : Submodule B (M ⧸ K)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (h n)
    have hmap : (maximalIdeal B ^ n • (⊤ : Submodule B M)).map K.mkQ ≤
        maximalIdeal B ^ n • (⊤ : Submodule B (M ⧸ K)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    have hzq := hmap (Submodule.mem_map_of_mem hz)
    have hy0 : K.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hy
    rw [map_add (f := _), hy0, zero_add]
    exact hzq
  rw [hbot, Submodule.mem_bot] at hx
  exact (Submodule.Quotient.mk_eq_zero K).mp hx

open TensorProduct Polynomial IsLocalRing in
private theorem exists_limit_of_sub_mem_maximalIdeal_pow_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [AddCommGroup M]
    [Module B M] [Module.Finite B M] (s : ℕ) (y : ℕ → M)
    (hy : ∀ k, y (k + 1) - y k ∈ maximalIdeal B ^ (s + k) • (⊤ : Submodule B M)) :
    ∃ x, ∀ k, x - y k ∈ maximalIdeal B ^ (s + k) • (⊤ : Submodule B M) := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := B) (M := M)
  have hlift : ∀ (J : Ideal B) (z : M), z ∈ J • (⊤ : Submodule B M) →
      ∃ c : Fin m → B, (∀ l, c l ∈ J) ∧ ∑ l, c l • g l = z := by
    intro J z hz
    rw [← hg, Submodule.mem_ideal_smul_span_iff_exists_sum] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, ha, (Finsupp.sum_fintype a (fun i c => c • g i) fun i => zero_smul B (g i)).symm⟩
  choose c hcI hcsum using fun k => hlift _ _ (hy k)
  obtain ⟨S, hS⟩ : ∃ S : Fin m → ℕ → B, ∀ l n, S l n = ∑ k ∈ Finset.range n, c k l :=
    ⟨_, fun _ _ => rfl⟩
  have hSdiff : ∀ l n p, n ≤ p → S l p - S l n ∈ maximalIdeal B ^ (s + n) := by
    intro l n p hnp
    rw [hS, hS, ← Finset.sum_range_add_sum_Ico _ hnp, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk' := (Finset.mem_Ico.mp hk).1
    exact Ideal.pow_le_pow_right (by omega) (hcI k l)
  have hprec : IsPrecomplete (maximalIdeal B) B := inferInstance
  have hlim : ∀ l, ∃ L, ∀ n, S l n - L ∈ maximalIdeal B ^ (s + n) := by
    intro l
    obtain ⟨L, hL⟩ := hprec.prec (f := S l) (fun {a b} hab => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, Submodule.neg_mem_iff]
      exact Ideal.pow_le_pow_right (by omega) (hSdiff l a b hab))
    refine ⟨L, fun n => ?_⟩
    have h1 := hL (s + n)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    have h2 := hSdiff l n (s + n) (by omega)
    have e : S l n - L = (S l (s + n) - L) - (S l (s + n) - S l n) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (by omega) h1) h2
  choose L hL using hlim
  refine ⟨y 0 + ∑ l, L l • g l, fun k => ?_⟩
  have htel : ∑ l, S l k • g l = y k - y 0 := by
    simp only [hS, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp_rw [hcsum]
    exact Finset.sum_range_sub y k
  have e : y 0 + ∑ l, L l • g l - y k = -∑ l, (S l k - L l) • g l := by
    simp only [sub_smul, Finset.sum_sub_distrib, htel]
    abel
  rw [e, Submodule.neg_mem_iff]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem_smul (hL l k) Submodule.mem_top


open TensorProduct Polynomial IsLocalRing in
theorem _root_.GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed :
    ∀ (B M ι : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [IsAdicComplete (maximalIdeal B) B] [AddCommGroup M] [Module B M] [Module.Finite B M]
      (K : ι → Submodule B M), Nonempty ι → Directed (· ≥ ·) K → (⨅ i, K i) = ⊥ →
      ∀ N : ℕ, ∃ i, K i ≤ maximalIdeal B ^ N • (⊤ : Submodule B M) := by
  intro B M ι _ _ _ _ _ _ _ K hne hdir hbot N
  haveI := hne
  have hmin : ∀ n, ∃ j, ∀ i, K j ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) ≤
      K i ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n
    haveI := isArtinian_quotient_maximalIdeal_pow_succ_smul B M n
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ :=
      (wellFounded_lt (α := Submodule B (M ⧸ (maximalIdeal B ^ (n + 1) •
        (⊤ : Submodule B M))))).has_min
        (Set.range fun i => (K i).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ)
        (Set.range_nonempty _)
    refine ⟨j, fun i => ?_⟩
    obtain ⟨k, hki, hkj⟩ := hdir i j
    have hle := Submodule.map_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hkj
    have heq : (K k).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ =
        (K j).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ := by
      by_contra hne'
      exact hj _ ⟨k, rfl⟩ (lt_of_le_of_ne hle hne')
    have hji := Submodule.map_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hki
    rw [heq] at hji
    have hc := Submodule.comap_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hji
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ] at hc
    rwa [sup_comm (K j), sup_comm (K i)]
  choose j hj using hmin
  by_contra hcon
  push_neg at hcon
  have hE_step : ∀ n, ∀ x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M),
      ∃ x' ∈ K (j (n + 1)) ⊔ maximalIdeal B ^ (n + 1 + 1) • (⊤ : Submodule B M),
        x - x' ∈ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hj n (j (n + 1)) hx)
    exact ⟨a, Submodule.mem_sup_left ha, by simpa using hb⟩
  have hE_anti : ∀ n, K (j (n + 1)) ⊔ maximalIdeal B ^ (n + 1 + 1) • (⊤ : Submodule B M) ≤
      K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := fun n =>
    (hj (n + 1) (j n)).trans
      (sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) _)
  have hE_mono : ∀ n p, n ≤ p → K (j p) ⊔ maximalIdeal B ^ (p + 1) • (⊤ : Submodule B M) ≤
      K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n p hnp
    induction hnp with
    | refl => exact le_rfl
    | step _ ih => exact (hE_anti _).trans ih
  have hE_zero : ∀ x, (∀ n, x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)) →
      x = 0 := by
    intro x hx
    have hmem : x ∈ ⨅ i, K i := Submodule.mem_iInf _ |>.mpr fun i =>
      mem_of_forall_mem_sup_maximalIdeal_pow_smul B M (K i) x fun n => by
        have hle : K i ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) ≤
            K i ⊔ maximalIdeal B ^ n • (⊤ : Submodule B M) :=
          sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))) _
        exact hle (hj n i (hx n))
    rwa [hbot, Submodule.mem_bot] at hmem
  have hnot : ¬ K (j N) ⊔ maximalIdeal B ^ (N + 1) • (⊤ : Submodule B M) ≤
      maximalIdeal B ^ (N + 1) • (⊤ : Submodule B M) := fun h =>
    hcon (j N) ((le_sup_left.trans h).trans
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))))
  obtain ⟨x0, hx0, hx0P⟩ := SetLike.not_le_iff_exists.mp hnot
  choose f hf1 hf2 using hE_step
  let y : (k : ℕ) → {x // x ∈ K (j (N + k)) ⊔ maximalIdeal B ^ (N + k + 1) • (⊤ : Submodule B M)} :=
    fun k => Nat.rec (motive := fun k =>
        {x // x ∈ K (j (N + k)) ⊔ maximalIdeal B ^ (N + k + 1) • (⊤ : Submodule B M)})
      ⟨x0, hx0⟩ (fun k z => ⟨f (N + k) z.1 z.2, hf1 _ _ _⟩) k
  have hy_succ : ∀ k, (y (k + 1)).1 = f (N + k) (y k).1 (y k).2 := fun k => rfl
  obtain ⟨x, hx⟩ := exists_limit_of_sub_mem_maximalIdeal_pow_smul B M (N + 1)
    (fun k => (y k).1) (fun k => by
      have e : N + 1 + k = N + k + 1 := by omega
      rw [hy_succ, e, ← neg_sub, Submodule.neg_mem_iff]
      exact hf2 (N + k) (y k).1 (y k).2)
  have hxE : ∀ n, x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n
    have e : N + 1 + n = N + n + 1 := by omega
    have hd := hx n
    rw [e] at hd
    have hk := Submodule.add_mem _ (y n).2 (Submodule.mem_sup_right hd)
    rw [add_sub_cancel] at hk
    exact hE_mono n (N + n) (by omega) hk
  have hx0' := hE_zero x hxE
  apply hx0P
  have h0 := hx 0
  rw [hx0', zero_sub, Submodule.neg_mem_iff] at h0
  exact h0

end GlobalTheory.Chevalley
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocallyConstantCutoffClosedEmbedding
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.CutOff

theorem exists_isClopen_isCompact_superset {R : Type} [TopologicalSpace R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] {Z : Set R} (hZ : IsCompact Z) :
    ∃ U : Set R, IsClopen U ∧ IsCompact U ∧ Z ⊆ U := by
  classical
  have h : ∀ z : R, ∃ V : Set R, IsClopen V ∧ IsCompact V ∧ z ∈ V := by
    intro z
    obtain ⟨K, hK, hKz⟩ := exists_compact_mem_nhds z
    obtain ⟨V, hV, hzV, hVK⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1 hKz
    exact ⟨V, hV, hK.of_isClosed_subset hV.isClosed hVK, hzV⟩
  choose V hVc hVk hzV using h
  obtain ⟨t, -, ht⟩ := hZ.elim_nhds_subcover V (fun z _ => (hVc z).isOpen.mem_nhds (hzV z))
  exact ⟨⋃ z ∈ t, V z, isClopen_biUnion_finset fun z _ => hVc z,
    t.isCompact_biUnion fun z _ => hVk z, ht⟩

theorem exists_nhds_one_mul_mem_iff {R : Type} [Group R] [TopologicalSpace R]
    [IsTopologicalGroup R] {U : Set R} (hUo : IsOpen U) (hUk : IsCompact U) :
    ∃ W ∈ 𝓝 (1 : R), ∀ w ∈ W, ∀ x, w * x ∈ U ↔ x ∈ U := by
  open scoped Pointwise in
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_mul_left hUk hUo subset_rfl
  refine ⟨V ∩ V⁻¹, inter_mem hV (inv_mem_nhds_one R hV), ?_⟩
  rintro w ⟨hw, hw'⟩ x
  constructor
  · intro h
    have : w⁻¹ * (w * x) ∈ U := hVU (Set.mul_mem_mul (Set.mem_inv.1 hw') h)
    simpa using this
  · intro h
    exact hVU (Set.mul_mem_mul hw h)

theorem isLocallyConstant_indicator_one {R : Type} [TopologicalSpace R] {U : Set R}
    (hU : IsClopen U) : IsLocallyConstant (U.indicator (fun _ => (1 : ℝ))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx] with y hy
    simp [hx, hy]
  · filter_upwards [hU.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [hx, Set.notMem_compl_iff.not.1 (by simpa using hy)]

theorem exists_cutoff : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by
  intro R S _ _ _ _ _ _ _ _ _ _ _ i hi ν _ Z hZ
  classical
  obtain ⟨U, hUc, hUk, hZU⟩ := exists_isClopen_isCompact_superset hZ
  obtain ⟨W, hW, hWU⟩ := exists_nhds_one_mul_mem_iff hUc.isOpen hUk
  set β : R → ℝ := U.indicator (fun _ => (1 : ℝ)) with hβ
  have hβlc : IsLocallyConstant β := isLocallyConstant_indicator_one hUc
  have hβc : Continuous β := hβlc.continuous
  have hβ0 : ∀ x, 0 ≤ β x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  set F : R → ℝ := fun g => ∫ s, β (g * i s) ∂ν with hF
  have hFinv : ∀ g t, F (g * i t) = F g := by
    intro g t
    have := integral_mul_left_eq_self (μ := ν) (fun s => β (g * i s)) t
    simpa [hF, mul_assoc, map_mul] using this
  have hβmul : ∀ w ∈ W, ∀ x, β (w * x) = β x := by
    intro w hw x
    simp [hβ, Set.indicator, hWU w hw x]
  have hFW : ∀ w ∈ W, ∀ g, F (w * g) = F g := by
    intro w hw g
    simp only [hF, mul_assoc, hβmul w hw]
  have hFlc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hc : Tendsto (fun y => y * g⁻¹) (𝓝 g) (𝓝 1) := by
      simpa using (continuous_mul_const g⁻¹).tendsto g
    filter_upwards [hc hW] with y hy
    have := hFW _ hy g
    rwa [inv_mul_cancel_right] at this
  have hFpos : ∀ g ∈ U, 0 < F g := by
    intro g hg
    have hcont : Continuous (fun s => β (g * i s)) :=
      hβc.comp (continuous_const.mul hi.continuous)
    have hKc : IsCompact (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      hi.isCompact_preimage ((Homeomorph.mulLeft g).isCompact_preimage.2 hUk)
    have hKcl : IsClosed (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      (hUc.isClosed.preimage (Homeomorph.mulLeft g).continuous).preimage hi.continuous
    have hsupp : HasCompactSupport (fun s => β (g * i s)) := by
      refine HasCompactSupport.intro' hKc hKcl fun x hx => ?_
      have hx' : g * i x ∉ U := hx
      simp [hβ, hx']
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hsupp
      (fun s => hβ0 _) (by simp [hβ, hg])
  refine ⟨fun g => β g / F g, ?_, ?_, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hβlc hFlc (· / ·)
  · refine HasCompactSupport.intro hUk fun x hx => ?_
    simp [hβ, hx]
  · intro g
    exact div_nonneg (hβ0 g) (integral_nonneg fun s => hβ0 _)
  · intro z hz s₀
    have h1 : ∫ s, β (z * i s₀ * i s) / F (z * i s₀ * i s) ∂ν
        = ∫ s, β (z * i s) / F (z * i s) ∂ν := by
      have := integral_mul_left_eq_self (μ := ν) (fun s => β (z * i s) / F (z * i s)) s₀
      simpa [mul_assoc, map_mul] using this
    rw [h1]
    have h2 : ∀ s, β (z * i s) / F (z * i s) = β (z * i s) / F z := fun s => by rw [hFinv]
    simp_rw [h2]
    rw [integral_div]
    exact div_self (hFpos z (hZU hz)).ne'

end GlobalTheory.CutOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma

open Polynomial


open Matrix MeasureTheory in
open Polynomial in
theorem _root_.GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    [Module.Finite E V] (f : Module.End E V) (h : (LinearMap.charpoly f).Separable) :
    LinearMap.charpoly f ∣ minpoly E f := by
  set L := AlgebraicClosure E
  have hinj : Function.Injective (algebraMap E L) := (algebraMap E L).injective
  rw [← map_dvd_map (algebraMap E L) hinj (LinearMap.charpoly_monic f)]
  have hm0 : (minpoly E f).map (algebraMap E L) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral f))
  have hroot : ∀ r ∈ ((LinearMap.charpoly f).map (algebraMap E L)).roots,
      r ∈ ((minpoly E f).map (algebraMap E L)).roots := by
    intro r hr
    rw [mem_roots hm0]
    rw [mem_roots (Polynomial.map_ne_zero (LinearMap.charpoly_monic f).ne_zero),
      ← LinearMap.charpoly_baseChange, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hr
    obtain ⟨v, hv⟩ := hr.exists_hasEigenvector
    have hzero : aeval (f.baseChange L) ((minpoly E f).map (algebraMap E L)) = 0 := by
      rw [aeval_map_algebraMap]
      have hφ := Polynomial.aeval_algHom_apply (Module.End.baseChangeHom E L V) f (minpoly E f)
      rw [minpoly.aeval, map_zero] at hφ
      exact hφ
    have hv' :=
      Module.End.aeval_apply_of_hasEigenvector (p := (minpoly E f).map (algebraMap E L)) hv
    rw [hzero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at hv'
    exact hv'.resolve_right hv.2
  have hsplit := IsAlgClosed.splits ((LinearMap.charpoly f).map (algebraMap E L))
  rw [hsplit.eq_prod_roots_of_monic ((LinearMap.charpoly_monic f).map _),
    Multiset.prod_X_sub_C_dvd_iff_le_roots hm0, Multiset.le_iff_subset (nodup_roots h.map)]
  exact hroot


open Matrix MeasureTheory in
open Polynomial in
theorem _root_.GlobalTheory.UnitLemma.exists_basis_pow_of_separable : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K), B.P.Separable →
    ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E
      B.A, ∀ i, e i = B.g ^ (i : ℕ) := by
  intro K B hsep
  set g := B.g
  have hmin : minpoly K.E (LinearMap.mulLeft K.E g) = minpoly K.E g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A)
      (fun x y hxy => by simpa using congrArg (fun φ => φ 1) hxy) g
  have hdvd := _root_.GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable _ hsep
  rw [hmin] at hdvd
  have hdeg : (minpoly K.E g).natDegree =
      Module.finrank K.E B.A := by
    apply le_antisymm (minpoly.natDegree_le g)
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E g)]
    exact natDegree_le_of_dvd hdvd (minpoly.ne_zero (Algebra.IsIntegral.isIntegral g))
  have hli : LinearIndependent K.E
      (fun i : Fin (Module.finrank K.E B.A) => g ^ (i : ℕ)) :=
    (linearIndependent_pow g).comp (Fin.cast hdeg.symm) (Fin.cast_injective _)
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (Fintype.card_fin _),
    fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemOfSpanEqTop
section
namespace GlobalTheory.DenominatorOfSpan

open GlobalTheory.UnitLemma

theorem exists_smul_mem_of_span_eq_top {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (L : Submodule O A) (hL : Submodule.span E (L : Set A) = ⊤) (x : A) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set A) := by rw [hL]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hay
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul e y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have hs' : e * algebraMap O E (s : O) = algebraMap O E n := hs
    refine ⟨a * (s : O), mul_ne_zero ha (nonZeroDivisors.ne_zero s.2), ?_⟩
    have h1 : (s : O) • e • y = n • y := by
      rw [← algebraMap_smul E (s : O), ← mul_smul, mul_comm, hs', algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.smul_mem n hay

theorem exists_denominator {K : UQ} (B : InvAlg K) (L : Submodule K.O B.A)
    (hL : Submodule.span K.E (L : Set B.A) = ⊤) (x : B.A) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ L :=
  exists_smul_mem_of_span_eq_top L hL x

end GlobalTheory.DenominatorOfSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAlgebraInvolutionRhoPowEqCardBox
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  intro K B a r φ c hφ hker hint k
  have hK : (intUnits K.O B.A).subgroupOf B.T = φ.ker := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  unfold InvAlg.rho
  rw [hK]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have he : ∀ q : B.T ⧸ φ.ker, e q = φ (Quotient.out q) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h1 : Nat.card {q : B.T ⧸ φ.ker //
      IsIntegral K.O ((((Quotient.out q : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} =
      Nat.card {v : Fin r → ℤ // ∀ i, v i ∈ Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)} := by
    apply Nat.card_congr
    refine (e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv ?_
    intro q
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.trans_apply, MulEquiv.coe_toEquiv, he, Set.mem_Icc, ← abs_le]
    exact hint _ k
  rw [h1, Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : Nat.card (Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)) = 2 * k * c i + 1 := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_Icc, Int.card_Icc, show 2 * k * c i = 2 * (k * c i) by ring]
    omega
  exact h2

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianLinearEquivContinuous
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem et_equiv_continuous (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous j ∧ Continuous j.symm := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : CompleteSpace F := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace F
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : FiniteDimensional F (Fin r → E) := inferInstance
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  refine ⟨?_, ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap (R := F) (j.toLinearMap.restrictScalars F)
  · exact LinearMap.continuous_of_finiteDimensional (j.symm.toLinearMap.restrictScalars F)

end GlobalTheory.JR
end

