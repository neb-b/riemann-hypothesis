module

public import Mathlib
public import GroundTheory.LocalFields.PrincipalUnitsModule
public import GroundTheory.LocalFields.MaximalUnramified

@[expose] public section

-- bundled from GroundTheory.LocalFields.PadicLogLinear
section
namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem eq_zero_of_forall_mem_valBall {y : K} (h : ∀ N : ℤ, y ∈ valBall (K := K) N) : y = 0 := by
  by_contra hy
  have := h (ord y + 1)
  rw [mem_valBall, normalizedValuation_eq_exp_ord hy, WithZero.exp_le_exp] at this
  omega

theorem exists_mem_valBall (y : K) : ∃ M : ℤ, y ∈ valBall (K := K) M := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  · exact ⟨ord y, by rw [mem_valBall, normalizedValuation_eq_exp_ord hy]⟩

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem padicHom_padicInt_mem_valBall_zero (t : ℤ_[p]) :
    CharZero.padicHom K p (t : ℚ_[p]) ∈ valBall (K := K) 0 := by
  rw [mem_valBall, neg_zero, WithZero.exp_zero, ← map_one (normalizedValuation K),
    normalizedValuation_le_iff, map_one]
  exact CharZero.valuation_padicHom_padicInt_le_one K p t


include p in
include p in
theorem padicLog_mem_valBall_of_mem {k : ℕ} (hk : absRamificationIndex (K := K) ≤ k)
    {w : Additive (unitFiltrationUnits K 1)} (hw : w ∈ principalFiltration (K := K) k) :
    padicLog K w ∈ valBall (K := K) (k + 1) := by
  rw [mem_principalFiltration] at hw
  rw [padicLog_apply]
  refine logSeries_mem_valBall p hw ?_
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have : (absRamificationIndex (K := K) : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem padicLog_smul (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K (a • u) = CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_valBall fun N ↦ ?_
  set e := absRamificationIndex (K := K)
  have he := one_le_absRamificationIndex (K := K) p
  obtain ⟨M, hM⟩ := exists_mem_valBall (padicLog K u)
  set k : ℕ := N.toNat + M.natAbs + e + 1 with hk_def
  set c : ℤ := ((a.appr k : ℕ) : ℤ)
  have hac := dvd_sub_appr p k a
  obtain ⟨t, ht⟩ := hac
  have hw := smul_sub_intCast_smul_mem p (dvd_sub_appr p k a) u
  have h1 := padicLog_mem_valBall_of_mem p (by omega : e ≤ k) hw
  rw [map_sub, map_zsmul, zsmul_eq_mul] at h1
  have h2 : CharZero.padicHom K p (a : ℚ_[p]) - (c : K) =
      ((p ^ k : ℕ) : K) * CharZero.padicHom K p (t : ℚ_[p]) := by
    have := congrArg (fun z : ℤ_[p] ↦ CharZero.padicHom K p (z : ℚ_[p])) ht
    simp only [PadicInt.coe_sub, PadicInt.coe_intCast, map_sub, map_intCast, PadicInt.coe_mul,
      PadicInt.coe_pow, PadicInt.coe_natCast, map_mul, map_pow, map_natCast] at this
    rw [this]; push_cast; ring
  have h3 : (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u ∈
      valBall (K := K) (e * k + 0 + M) := by
    rw [h2]
    exact mul_mem_valBall (mul_mem_valBall (natCast_prime_pow_mem_valBall p k)
      (padicHom_padicInt_mem_valBall_zero p t)) hM
  have heq : padicLog K (a • u) - CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u =
      (padicLog K (a • u) - (c : K) * padicLog K u) -
        (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u := by ring
  rw [heq]
  have hNt := Int.self_le_toNat N
  have hMa := neg_abs_le M
  have hMa' := abs_nonneg M
  have hN1 : N ≤ (k : ℤ) + 1 := by rw [hk_def]; push_cast; omega
  have hN2 : N ≤ (e : ℤ) * k + 0 + M := by
    have : (k : ℤ) ≤ e * k := by
      have : (1 : ℤ) ≤ e := by exact_mod_cast he
      nlinarith [(by positivity : (0 : ℤ) ≤ k)]
    rw [hk_def] at this ⊢; push_cast at this ⊢; omega
  exact sub_mem (valBall_antitone hN1 h1) (valBall_antitone hN2 h3)

end GroundTheory.LocalField
end

-- bundled from GroundTheory.LocalFields.WeilGroupDefs
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract Topology

section Frobenius

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow (n : ℤ) :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (maximalUnramifiedExtensionFrobenius K Ω ^ n) =
      Multiplicative.ofAdd (n : ℤ̂) := by
  rw [map_zpow, unramifiedDegree_maximalUnramifiedExtensionFrobenius, ← ofAdd_zsmul, zsmul_one]

theorem injective_zpow_maximalUnramifiedExtensionFrobenius :
    Function.Injective fun n : ℤ ↦ maximalUnramifiedExtensionFrobenius K Ω ^ n := by
  intro m n h
  have h' := congrArg (unramifiedDegree K (maximalUnramifiedExtension K Ω)) h
  simp only [unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow] at h'
  exact Int.cast_injective (Multiplicative.ofAdd.injective h')

def frobeniusZPowersEquiv :
    Multiplicative ℤ ≃* Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :=
  MonoidHom.ofInjective (f := zpowersHom _ (maximalUnramifiedExtensionFrobenius K Ω))
    (fun _ _ h ↦ Multiplicative.toAdd.injective
      (injective_zpow_maximalUnramifiedExtensionFrobenius K Ω h))

end Frobenius

section Weil

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

def weilSubgroup : Subgroup (Ω ≃ₐ[K] Ω) :=
  (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω)).comap
    (AlgEquiv.restrictNormalHom (maximalUnramifiedExtension K Ω))


variable {K Ω} in
theorem mem_weilSubgroup_iff {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ weilSubgroup K Ω ↔ ∃ n : ℤ,
      σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ^ n := by
  simp only [weilSubgroup, Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
  exact exists_congr fun n ↦ eq_comm


variable {K Ω} in
theorem restrictNormal_eq_frobenius_zpow_iff (σ : Ω ≃ₐ[K] Ω) (n : ℤ) :
    σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ^ n ↔
      unramifiedDegree K Ω σ = Multiplicative.ofAdd (n : ℤ̂) := by
  rw [← unramifiedDegree_restrictNormal, ← unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow K Ω n]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm


variable {K Ω} in
theorem mem_weilSubgroup_iff_unramifiedDegree {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ weilSubgroup K Ω ↔ ∃ n : ℤ, unramifiedDegree K Ω σ = Multiplicative.ofAdd (n : ℤ̂) := by
  rw [mem_weilSubgroup_iff]
  exact exists_congr fun n ↦ restrictNormal_eq_frobenius_zpow_iff σ n

theorem fixingSubgroup_le_weilSubgroup :
    (maximalUnramifiedExtension K Ω).fixingSubgroup ≤ weilSubgroup K Ω := by
  intro σ hσ
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker] at hσ
  exact mem_weilSubgroup_iff.2 ⟨0, by rw [zpow_zero]; exact hσ⟩

theorem exists_restrictNormal_eq_frobenius_zpow (n : ℤ) :
    ∃ σ : Ω ≃ₐ[K] Ω,
      σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ^ n :=
  AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := maximalUnramifiedExtension K Ω) (E := Ω) _

theorem dense_weilSubgroup : Dense (weilSubgroup K Ω : Set (Ω ≃ₐ[K] Ω)) := by
  have : T2Space (Ω ≃ₐ[K] Ω) := krullTopology_t2
  set C := (weilSubgroup K Ω).topologicalClosure with hC
  have hCc : IsCompact (C : Set (Ω ≃ₐ[K] Ω)) := (Subgroup.isClosed_topologicalClosure _).isCompact
  have himc : IsClosed (unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω))) :=
    (hCc.image continuous_unramifiedDegree).isClosed
  have hsub : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) ⊆
      unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_restrictNormal_eq_frobenius_zpow K Ω n
    refine ⟨σ, (weilSubgroup K Ω).le_topologicalClosure (mem_weilSubgroup_iff.2 ⟨n, hσ⟩), ?_⟩
    show _ = Multiplicative.ofAdd 1 ^ n
    rw [(restrictNormal_eq_frobenius_zpow_iff σ n).1 hσ, ← ofAdd_zsmul, zsmul_one]
  have huniv : unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← dense_zpowers_ofAdd_one.closure_eq]
    exact himc.closure_subset_iff.2 hsub
  rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, ← hC]
  refine Set.eq_univ_of_forall fun τ ↦ ?_
  obtain ⟨c, hc, hcτ⟩ : unramifiedDegree K Ω τ ∈ unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) := by
    rw [huniv]; trivial
  have hk : c⁻¹ * τ ∈ (unramifiedDegree K Ω).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcτ, inv_mul_cancel]
  rw [ker_unramifiedDegree] at hk
  have hk' : c⁻¹ * τ ∈ C :=
    (weilSubgroup K Ω).le_topologicalClosure (fixingSubgroup_le_weilSubgroup K Ω hk)
  have := C.mul_mem hc hk'
  rwa [mul_inv_cancel_left] at this

def WeilGroup : Type _ := weilSubgroup K Ω

namespace WeilGroup





variable {K Ω}







end WeilGroup

end Weil

end GroundTheory.LocalField
end
end

