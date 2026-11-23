module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformBoundOnClosedCone
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt

theorem bound_of_local_bounds_of_blockScale :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (T : Set ((Σ k, J k) → ℂ))
    (Bd : ((Σ k, J k) → ℂ) → ℝ → Prop),
    (∀ w ∈ T, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ w ∈ closure T, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → w ∈ T) →
    (∀ w x, Bd w x → w ∈ T) →
    (∀ w x (c : K → ℂ), (∀ k, c k ≠ 0) → Bd w x → Bd (fun p => c p.1 * w p) x) →
    (∀ w₀ ∈ T, ∃ N ∈ 𝓝 w₀, ∃ C : ℝ, ∀ w ∈ N, ∀ x, Bd w x → |x| ≤ C) →
    ∃ C : ℝ, ∀ w x, Bd w x → |x| ≤ C := by
  intro K _ J _ T Bd hT hcl hBdT hscale hloc
  classical
  obtain ⟨A, hA⟩ : ∃ A : Set ((Σ k, J k) → ℂ),
      A = (⋂ p, {w | ‖w p‖ ≤ 1}) ∩ ⋂ k, ⋃ i, {w | ‖w ⟨k, i⟩‖ = 1} := ⟨_, rfl⟩
  have hAcl : IsClosed A := by
    rw [hA]
    exact (isClosed_iInter fun p => isClosed_le (continuous_norm.comp (continuous_apply p))
      continuous_const).inter (isClosed_iInter fun k => isClosed_iUnion_of_finite fun i =>
        isClosed_eq (continuous_norm.comp (continuous_apply _)) continuous_const)
  have hA_le : ∀ w ∈ A, ∀ p, ‖w p‖ ≤ 1 := by
    intro w hw p
    rw [hA] at hw
    exact Set.mem_iInter.mp hw.1 p
  have hA_ne : ∀ w ∈ A, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
    intro w hw k
    rw [hA] at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hw.2 k)
    refine ⟨i, fun h0 => ?_⟩
    have hi' : ‖w ⟨k, i⟩‖ = 1 := hi
    rw [h0, norm_zero] at hi'
    exact zero_ne_one hi'
  have hScl : IsClosed (T ∩ A) := by
    apply isClosed_of_closure_subset
    intro w hw
    have hwT : w ∈ closure T := closure_mono Set.inter_subset_left hw
    have hwA : w ∈ A := hAcl.closure_subset (closure_mono Set.inter_subset_right hw)
    exact ⟨hcl w hwT (hA_ne w hwA), hwA⟩
  have hSsub : T ∩ A ⊆ Metric.closedBall 0 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact hA_le w hw.2
  have hScpt : IsCompact (T ∩ A) := (isCompact_closedBall 0 1).of_isClosed_subset hScl hSsub
  choose N hN C hC using fun w (hw : w ∈ T ∩ A) => hloc w hw.1
  obtain ⟨t, ht⟩ := hScpt.elim_nhds_subcover' N hN
  refine ⟨∑ s ∈ t, |C s.1 s.2|, ?_⟩
  intro w x hBd
  have hwT := hBdT w x hBd
  have hmax : ∀ k, ∃ i, ∀ j, ‖w ⟨k, j⟩‖ ≤ ‖w ⟨k, i⟩‖ := by
    intro k
    obtain ⟨i₀, -⟩ := hT w hwT k
    haveI : Nonempty (J k) := ⟨i₀⟩
    exact Finite.exists_max fun j => ‖w ⟨k, j⟩‖
  choose m hm using hmax
  have hmpos : ∀ k, 0 < ‖w ⟨k, m k⟩‖ := by
    intro k
    obtain ⟨i₀, hi₀⟩ := hT w hwT k
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi₀) (hm k i₀)
  obtain ⟨c, hc⟩ : ∃ c : K → ℂ, c = fun k => ((‖w ⟨k, m k⟩‖⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hc0 : ∀ k, c k ≠ 0 := by
    intro k
    rw [hc]
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (hmpos k).ne')
  have hBd' := hscale w x c hc0 hBd
  have hnorm : ∀ (k : K) (j : J k), ‖c k * w ⟨k, j⟩‖ = ‖w ⟨k, j⟩‖ / ‖w ⟨k, m k⟩‖ := by
    intro k j
    rw [hc, norm_mul, Complex.norm_real, norm_inv, norm_norm, div_eq_inv_mul]
  have hw'S : (fun p => c p.1 * w p) ∈ T ∩ A := by
    refine ⟨hBdT _ _ hBd', ?_⟩
    rw [hA]
    refine ⟨Set.mem_iInter.mpr fun p => ?_, Set.mem_iInter.mpr fun k => Set.mem_iUnion.mpr ⟨m k, ?_⟩⟩
    · obtain ⟨k, j⟩ := p
      show ‖c k * w ⟨k, j⟩‖ ≤ 1
      rw [hnorm]
      exact (div_le_one (hmpos k)).mpr (hm k j)
    · show ‖c k * w ⟨k, m k⟩‖ = 1
      rw [hnorm]
      exact div_self (hmpos k).ne'
  obtain ⟨s, hs, hsN⟩ := Set.mem_iUnion₂.mp (ht hw'S)
  calc |x| ≤ C s.1 s.2 := hC s.1 s.2 _ hsN x hBd'
    _ ≤ |C s.1 s.2| := le_abs_self _
    _ ≤ ∑ s ∈ t, |C s.1 s.2| :=
      Finset.single_le_sum (f := fun s : ↥(T ∩ A) => |C s.1 s.2|) (fun _ _ => abs_nonneg _) hs

end GlobalTheory.CompanionTheory.Ar.RootHt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtGenIndependentChoice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

theorem gen_chart_change (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (a : K → ℤ) (e₀ τ : Ω) (c₀ c₁ : (k : K) → J k) (u u' : ℂ)
    (hξ : IsCptGen ξ) (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (h₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0)
    (h₁ : ∀ k, w ⟨k, c₁ k⟩ ≠ 0) (hu : ValAt ξ z (τ / gen y a e₀ c₀) u)
    (hu' : ValAt ξ z (τ / gen y a e₀ c₁) u') :
    u * ∏ k, w ⟨k, c₀ k⟩ ^ a k = u' * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
  classical
  obtain ⟨hz, -⟩ := val_spec hu
  have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (isUnit_iff_ne_zero.2 (h₀ k))).1
  have hy₁ : ∀ k, y ⟨k, c₁ k⟩ ≠ 0 := fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).1
  have hr : ∀ k, ∃ r : ℂ, ValAt ξ z (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) r ∧ w ⟨k, c₀ k⟩ = r * w ⟨k, c₁ k⟩ :=
    fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).2 (c₀ k)
  choose r hrv hrw using hr
  have hr0 : ∀ k, r k ≠ 0 := fun k hk => h₀ k (by rw [hrw k, hk, zero_mul])
  have hprod : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k) (∏ k ∈ s, r k ^ a k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using val_one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact val_mul (val_zpow (hr0 k) (hrv k) (a k)) ih
  have hg₀ : (∏ k, y ⟨k, c₀ k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₀ k)
  have hg₁ : (∏ k, y ⟨k, c₁ k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₁ k)
  have hΩ : τ / gen y a e₀ c₁ = (τ / gen y a e₀ c₀) * ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k := by
    have : ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k = (∏ k, y ⟨k, c₀ k⟩ ^ a k) / ∏ k, y ⟨k, c₁ k⟩ ^ a k := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k _ => div_zpow _ _ _
    rw [this]
    unfold gen
    field_simp
  have hval : u' = u * ∏ k, r k ^ a k := by
    have h := val_mul hu (hprod Finset.univ)
    rw [← hΩ] at h
    exact val_unique hξ hu' h
  have hw₀ : ∏ k, w ⟨k, c₀ k⟩ ^ a k = (∏ k, r k ^ a k) * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [hrw k, mul_zpow]
  rw [hw₀, hval, _root_.mul_assoc]

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

