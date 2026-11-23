module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvIrrComm
public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0004
public import GroundTheory.GlobalFields.TateThesis.Bundle0002

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvIrrAvg
section
noncomputable section

open scoped InnerProductSpace
open UniformSpace GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)
variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

def fixSub (K : Subgroup G) : Submodule ℂ M where
  carrier := {a | ∀ κ ∈ K, ρ κ a = a}
  add_mem' {a b} ha hb κ hκ := by rw [map_add (f := _), ha κ hκ, hb κ hκ]
  zero_mem' κ _ := map_zero _
  smul_mem' c a ha κ hκ := by rw [map_smul, ha κ hκ]

include hinv in
theorem avg_exists [TopologicalSpace G] [IsTopologicalGroup G] (hsm : IsSmooth ρ) (Z : Submodule ℂ M)
    (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z) (K : Subgroup G) (hKc : IsCompact (K : Set G)) (x : M)
    (hx : ∀ κ ∈ K, ρ κ x = x) (z : M) (hz : z ∈ Z) :
    ∃ a ∈ Z, (∀ κ ∈ K, ρ κ a = a) ∧
      dist (iota B hB x) (iota B hB a) ≤ dist (iota B hB x) (iota B hB z) := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hf : Continuous fun g : G => ρ g z := by
    refine continuous_discrete_rng.2 fun b => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨(fun h => g⁻¹ * h) ⁻¹' {h | ρ h z = z}, fun h hh => ?_,
      (continuous_const_mul g⁻¹).isOpen_preimage _ (hsm z), ?_⟩
    · simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] at hh hg ⊢
      rw [← hg, show h = g * (g⁻¹ * h) by group, rho_mul, hh]
    · simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel, rho_one]
  have hfin : ((fun g : G => ρ g z) '' (K : Set G)).Finite := (hKc.image hf).finite_of_discrete
  set O := hfin.toFinset with hO
  have hmem : ∀ m, m ∈ O ↔ ∃ k ∈ K, ρ k z = m := fun m => by
    rw [hO, Set.Finite.mem_toFinset]; rfl
  have hzO : z ∈ O := (hmem z).2 ⟨1, K.one_mem, rho_one ρ z⟩
  have hcard : (O.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨z, hzO⟩)
  have hcardC : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨z, hzO⟩)
  refine ⟨(O.card : ℂ)⁻¹ • ∑ m ∈ O, m, Z.smul_mem _ (Z.sum_mem fun m hm => ?_), fun κ hκ => ?_, ?_⟩
  · obtain ⟨k, _, rfl⟩ := (hmem m).1 hm
    exact hZ k z hz
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
      apply congrArg (fun v : M => (O.card : ℂ)⁻¹ • v)
      refine Finset.sum_nbij' (fun m => ρ κ m) (fun m => ρ κ⁻¹ m) (fun m hm => ?_) (fun m hm => ?_)
        (fun m _ => rho_inv ρ κ m) (fun m _ => ?_) (fun _ _ => rfl)
      · obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
        exact (hmem _).2 ⟨κ * k, K.mul_mem hκ hk, rho_mul ρ κ k z⟩
      · obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
        exact (hmem _).2 ⟨κ⁻¹ * k, K.mul_mem (K.inv_mem hκ) hk, rho_mul ρ κ⁻¹ k z⟩
      · simp
  · have hdist : ∀ m ∈ O, ‖iota B hB x - iota B hB m‖ = ‖iota B hB x - iota B hB z‖ := by
      intro m hm
      obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
      have e : iota B hB x - iota B hB (ρ k z) = pi B hB ρ hinv k (iota B hB x - iota B hB z) := by
        rw [map_sub, pi_iota, pi_iota, hx k hk]
      rw [e, norm_pi]
    have hsum : iota B hB x - iota B hB ((O.card : ℂ)⁻¹ • ∑ m ∈ O, m) =
        (O.card : ℂ)⁻¹ • ∑ m ∈ O, (iota B hB x - iota B hB m) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, map_smul, map_sum,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcardC, one_smul]
    rw [dist_eq_norm, dist_eq_norm, hsum, norm_smul]
    calc ‖((O.card : ℂ))⁻¹‖ * ‖∑ m ∈ O, (iota B hB x - iota B hB m)‖
        ≤ ‖((O.card : ℂ))⁻¹‖ * ∑ m ∈ O, ‖iota B hB x - iota B hB m‖ := by gcongr; exact norm_sum_le _ _
      _ = ‖((O.card : ℂ))⁻¹‖ * (O.card * ‖iota B hB x - iota B hB z‖) := by
          rw [Finset.sum_congr rfl hdist, Finset.sum_const, nsmul_eq_mul]
      _ = ‖iota B hB x - iota B hB z‖ := by
          rw [norm_inv, Complex.norm_natCast, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvKirB
section
noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

def ballLe (r : ValueGroupWithZero k) : AddSubgroup k where
  carrier := {x | valuation k x ≤ r}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact ((valuation k).map_add a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa [Valuation.map_neg] using ha

def ballLt (γ : (ValueGroupWithZero k)ˣ) : AddSubgroup k where
  carrier := {x | valuation k x < γ}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (valuation k).map_add_lt ha hb
  zero_mem' := by simp [Units.zero_lt]
  neg_mem' {a} ha := by simpa [Valuation.map_neg] using ha

theorem isOpen_ballLt (γ : (ValueGroupWithZero k)ˣ) : IsOpen ((ballLt γ : AddSubgroup k) : Set k) :=
  (ballLt γ).isOpen_of_mem_nhds (g := 0) ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ hx => hx⟩)

theorem psi_ball (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ γ : (ValueGroupWithZero k)ˣ, ∀ x : k, valuation k x < γ → ψ x = 1 := by
  have hU : {t : k | ‖((ψ t : Circle) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : k) := by
    have hc : Continuous fun t : k => ‖((ψ t : Circle) : ℂ) - 1‖ :=
      ((continuous_subtype_val.comp hψ).sub continuous_const).norm
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hU
  let H : Subgroup Circle :=
    { carrier := ψ '' {x | valuation k x < γ}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, (valuation k).map_add_lt ha hb, AddChar.map_add_eq_mul ψ a b⟩
      one_mem' := ⟨0, by simp [Units.zero_lt], AddChar.map_zero_eq_one ψ⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, by simpa [Valuation.map_neg] using ha, AddChar.map_neg_eq_inv ψ a⟩ }
  have hH := GroundTheory.Global.Circle.subgroup_eq_bot_of_norm_sub_one_lt H (by
    rintro _ ⟨a, ha, rfl⟩; exact hγ ha)
  refine ⟨γ, fun x hx => ?_⟩
  have : ψ x ∈ H := ⟨x, hx, rfl⟩
  rw [hH] at this
  exact Subgroup.mem_bot.1 this

theorem small_of_triv (ψ : AddChar k Circle) (y : k) (hy : ψ y ≠ 1) (γ : (ValueGroupWithZero k)ˣ) (b : k)
    (h : ∀ t : k, valuation k t ≤ valuation k y * ↑γ⁻¹ → ψ (b * t) = 1) : valuation k b < γ := by
  by_contra hb'
  have hb := not_lt.1 hb'
  have hb0 : (0 : ValueGroupWithZero k) < valuation k b := lt_of_lt_of_le (Units.zero_lt γ) hb
  have hb0' : b ≠ 0 := fun h0 => by simp [h0] at hb0
  apply hy
  have e : b * (y / b) = y := by field_simp
  rw [← e]
  refine h _ ?_
  rw [map_div₀, div_eq_mul_inv, Units.val_inv_eq_inv_val]
  gcongr (valuation k y) * ?_
  exact (inv_le_inv₀ hb0 (Units.zero_lt γ)).2 hb

theorem continuous_U (c : Fin (m + 1)) : Continuous (fun x : Fin (m + 1) → k => U c x) := by
  have hc : ∀ x' : (Fin (m + 1) → k) → (Fin (m + 1) → k), Continuous x' →
      Continuous fun x => colM c (x' x) := by
    intro x' hx'
    refine continuous_const.add (continuous_matrix fun p q => ?_)
    by_cases h : q = c ∧ p < c
    · simp only [Matrix.of_apply, if_pos h]; exact (continuous_apply p).comp hx'
    · simp only [Matrix.of_apply, if_neg h]; exact continuous_const
  exact Units.continuous_iff.2 ⟨hc id continuous_id, hc (fun x => -x) continuous_neg⟩

end DiscreteGroups.sglob.LConvKir
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvSepA
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem delta_avg {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K)
    (L₁ L₂ : WT (m := m) ψ →ₗ[ℂ] ℂ) (h₁ : ∀ κ ∈ K, ∀ x, L₁ (rhoW ψ κ x) = L₁ x)
    (h₂ : ∀ κ ∈ K, ∀ x, L₂ (rhoW ψ κ x) = L₂ x) :
    L₁ (delta ψ K') * L₂ (delta ψ K) = L₁ (delta ψ K) * L₂ (delta ψ K') := by
  have hKc : CompactSpace K := isCompact_iff_compactSpace.1 hK.2.1
  have hopen : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.1.preimage continuous_subtype_val
  have : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (K ⧸ K'.subgroupOf K) := Fintype.ofFinite _
  set P : WT (m := m) ψ := ∑ q : K ⧸ K'.subgroupOf K,
    rhoW ψ ((Quotient.out q : K) : GL (Fin m) k) (delta ψ K') with hP
  have hrep : ∀ a b : K, b⁻¹ * a ∈ K'.subgroupOf K →
      rhoW ψ (a : GL (Fin m) k) (delta ψ K') = rhoW ψ (b : GL (Fin m) k) (delta ψ K') := by
    intro a b hab
    have e : (a : GL (Fin m) k) = b * ((b⁻¹ * a : K) : GL (Fin m) k) := by simp
    rw [e, map_mul, Module.End.mul_apply, rhoW_delta (Subgroup.mem_subgroupOf.1 hab)]
  have hfix : ∀ κ ∈ K, rhoW ψ κ P = P := by
    intro κ hκ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨κ, hκ⟩ : K)) _ _ fun q => ?_
    rw [MulAction.toPerm_apply, ← Module.End.mul_apply, ← map_mul]
    have e : (QuotientGroup.mk (Quotient.out ((⟨κ, hκ⟩ : K) • q)) : K ⧸ K'.subgroupOf K) =
        QuotientGroup.mk ((⟨κ, hκ⟩ : K) * Quotient.out q) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    have := hrep ((⟨κ, hκ⟩ : K) * Quotient.out q) (Quotient.out ((⟨κ, hκ⟩ : K) • q)) (QuotientGroup.eq.1 e)
    simpa using this
  have hL : ∀ L : WT (m := m) ψ →ₗ[ℂ] ℂ, (∀ κ ∈ K, ∀ x, L (rhoW ψ κ x) = L x) →
      L P = (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) * L (delta ψ K') := by
    intro L hL
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum, Finset.sum_congr rfl fun q _ => hL _ (Quotient.out q).2 _, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hs : ∀ g, (P : GL (Fin m) k → ℂ) g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K, g = u * κ := by
    intro g hg
    rw [hP, Submodule.coe_sum, Finset.sum_apply] at hg
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
    rw [rhoW_apply] at hq
    by_contra hno
    refine hq (delta_eq_zero ?_)
    rintro ⟨u, hu, κ', hκ', he⟩
    exact hno ⟨u, hu, κ' * ((Quotient.out q : K) : GL (Fin m) k)⁻¹,
      K.mul_mem (hle hκ') (K.inv_mem (Quotient.out q).2), by rw [← mul_assoc, ← he, mul_inv_cancel_right]⟩
  obtain ⟨s, hPs⟩ : ∃ s : ℂ, P = s • delta ψ K := ⟨_, eq_smul_delta hK P hfix hs⟩
  have a1 := hL L₁ h₁
  have a2 := hL L₂ h₂
  rw [hPs, map_smul, smul_eq_mul] at a1 a2
  have c0 : (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply mul_left_cancel₀ c0
  linear_combination (-L₂ (delta ψ K)) * a1 + L₁ (delta ψ K) * a2

def pairI (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (x y : WT (m := m) ψ) : ℂ :=
  I fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g


variable (ψ) in
def formI (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (pairI I)
    (fun x x' y => by
      simp only [pairI]
      rw [← map_add (f := _)]; congr 1; funext g
      simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]; ring)
    (fun c x y => by
      simp only [pairI]
      rw [← map_smul]; congr 1; funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]; ring)
    (fun x y y' => by
      simp only [pairI]
      rw [← map_add (f := _)]; congr 1; funext g
      simp only [Submodule.coe_add, Pi.add_apply]; ring)
    (fun c x y => by
      simp only [pairI]
      rw [← map_smul]; congr 1; funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

theorem formI_apply (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (x y : WT (m := m) ψ) :
    formI ψ I x y = I fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g := rfl

end DiscreteGroups.sglob.LConv

end
end

