module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumDeltaDecomposition
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

def lieRank {Ψ : Type} (N j : ℕ) (s : Ψ ⊕ Ψ) : ℝ := if s.isLeft then (j : ℝ) else ((N - j : ℕ) : ℝ)

theorem delta_card_filter_lt {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).card = j := by
  have h : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).map Fin.valEmbedding = Finset.range j := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro ha
      exact ⟨⟨a, lt_of_lt_of_le ha hj⟩, ha, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Finset.card_range]

theorem delta_card_filter_ge {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  rw [delta_card_filter_lt hj] at h
  omega

theorem pLie_zero {Ψ : Type} {N j : ℕ} (hj : j ≤ N) (s : Ψ ⊕ Ψ) :
    (pLie j 0 s : RP Ψ N) = C (lieRank N j s) := by
  cases s with
  | inl τ =>
    simp only [pLie, pkLow, pow_zero, Finset.sum_const, delta_card_filter_lt hj, lieRank, Sum.isLeft_inl, if_true,
      nsmul_eq_mul, mul_one, map_natCast]
  | inr τ =>
    simp only [pLie, pow_zero, Finset.sum_const, delta_card_filter_ge hj, lieRank, Sum.isLeft_inr,
      Bool.false_eq_true, if_false, nsmul_eq_mul, mul_one, map_natCast]

theorem degFl_C_mul {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (c : ℝ) (Q : RP Ψ N) :
    degFl (C c * Q) = c * degFl Q := by
  simp only [degFl, coeff_C_mul]
  have h : ∀ f g : (Ψ → Equiv.Perm (Fin N)) → ℝ, ∑ σ, f σ * (c * g σ) = c * ∑ σ, f σ * g σ := by
    intro f g
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h]
  ring

theorem deltaTerm_eq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), j ≤ N → 0 < N → FrobShape frob → ∃ κ : ℕ → ℝ, ∀ (p : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), 2 ≤ p → 1 ≤ k → deltaTerm j p τ (frob p τ) k Q = -(Real.log p / ((p : ℝ) - 1)) * ∑ σ, Sh j σ (pk τ k * Q) + κ p * ∑ σ, Tot σ (pk τ k * Q) + restTerm j p (frob p τ) k Q := by
  intro Ψ _ _ N j frob hj hN hF
  rcases isEmpty_or_nonempty Ψ with hE | ⟨⟨τ₀⟩⟩
  · exact ⟨0, fun _ τ => isEmptyElim τ⟩
  refine ⟨fun p => Real.log p / N * ∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n), ?_⟩
  intro p τ k Q hp hk
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hSh : ∑ σ, Sh j σ (pk τ k * Q) = k * degFl (pkLow j τ (k - 1) * Q) := by
    rw [Finset.sum_congr rfl (fun σ _ => (_root_.GlobalTheory.CompanionTheory.Ar.Top.sh_tot_pk_mul Ψ N j τ σ k Q hk).1)]
    simp
  have hTot : ∑ σ, Tot σ (pk τ k * Q) = if k = 1 then N * degFl Q else 0 := by
    rw [Finset.sum_congr rfl (fun σ _ => (_root_.GlobalTheory.CompanionTheory.Ar.Top.sh_tot_pk_mul Ψ N j τ σ k Q hk).2)]
    by_cases h1 : k = 1 <;> simp [h1]
  rw [hSh, hTot]
  by_cases h1 : k = 1
  · subst h1
    have hrank : ∀ n, degFl (pLie j (1 - 1) (frob p τ n) * Q) =
        lieRank N j (frob p τ₀ n) * degFl Q := by
      intro n
      have : lieRank N j (frob p τ n) = lieRank N j (frob p τ₀ n) := by
        simp only [lieRank, hF p n τ τ₀]
      rw [Nat.sub_self, pLie_zero hj, degFl_C_mul, this]
    have hsum : (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * degFl (pLie j (1 - 1) (frob p τ n) * Q)) =
        (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * lieRank N j (frob p τ₀ n)) * degFl Q := by
      rw [← tsum_mul_right]
      exact tsum_congr (fun n => by rw [hrank]; ring)
    simp only [deltaTerm, restTerm, hsum]
    simp only [if_true, Nat.one_lt_ofNat, Nat.not_ofNat_le_one, if_false]
    field_simp
    ring
  · have h2 : 2 ≤ k := by omega
    simp only [deltaTerm, restTerm, h1, if_false, h2, if_true]
    ring

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBAveraged
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem sum_group_apply_eq {Ψ : Type} (Γ : Subgroup (Equiv.Perm Ψ)) [Fintype Γ]
    (htr : ∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') (f : Ψ → ℝ) (τ τ' : Ψ) :
    ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ) = ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ') := by
  obtain ⟨ρ, hρ, rfl⟩ := htr τ' τ
  exact Fintype.sum_equiv (Equiv.mulRight (⟨ρ, hρ⟩ : Γ)) _ _ (fun g => by simp [Equiv.Perm.mul_apply])

theorem exists_group_mean {Ψ : Type} (Γ : Subgroup (Equiv.Perm Ψ)) [Fintype Γ]
    (htr : ∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') (f : Ψ → ℝ) :
    ∃ A : ℝ, ∀ τ, ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ) = (Fintype.card Γ : ℝ) * A := by
  rcases isEmpty_or_nonempty Ψ with h | ⟨⟨τ₀⟩⟩
  · exact ⟨0, fun τ => (h.false τ).elim⟩
  · have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    refine ⟨(∑ g : Γ, f ((g : Equiv.Perm Ψ) τ₀)) / (Fintype.card Γ : ℝ), fun τ => ?_⟩
    rw [mul_div_cancel₀ _ hc]
    exact sum_group_apply_eq Γ htr f τ τ₀

theorem mean_estimate {G Ψ : Type} [Fintype G] [Nonempty G] [Fintype Ψ] (P V H bd A Bs : ℝ) (S U : Ψ → ℝ)
    (a b : G → Ψ → ℝ) (hA : ∀ τ, ∑ g, a g τ = (Fintype.card G : ℝ) * A)
    (hB : ∀ τ, ∑ g, b g τ = (Fintype.card G : ℝ) * Bs)
    (h : ∀ g, |P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)| ≤ bd) :
    |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)| ≤ bd := by
  have hn : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card G : ℝ) with hndef
  have h1 : ∑ g, ∑ τ, (a g τ - b g τ) * S τ = n * ((A - Bs) * ∑ τ, S τ) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hA, hB]
    ring
  have h2 : ∑ g, ∑ τ, b g τ * U τ = n * (Bs * ∑ τ, U τ) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_mul, hB]
    ring
  have key : ∑ g : G, (P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)) =
      n * (P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)) := by
    have : ∀ g : G, P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ) =
        (P - V * H) + V * ∑ τ, (a g τ - b g τ) * S τ + V * ∑ τ, b g τ * U τ := fun g => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [← hndef]
    ring
  have hle : n * |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)| ≤ n * bd := by
    calc n * |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)|
        = |n * (P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ))| := by
          rw [abs_mul, abs_of_pos hn]
      _ = |∑ g : G, (P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ))| := by rw [key]
      _ ≤ ∑ g : G, |P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g : G, bd := Finset.sum_le_sum fun g _ => h g
      _ = n * bd := by simp [hndef]
  exact le_of_mul_le_mul_left hle hn

theorem thmBA_of_thmB_propA : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.ThmB II hh → T.PropA II →
    LabelInv (Ψ := Ψ) (N := N) hh → T.ThmBA II hh := by
  intro II Ψ _ _ N T hh hB hA hL
  obtain ⟨C, B₁, hC⟩ := hB
  obtain ⟨Γ, htr, hinv⟩ := hA
  have : Fintype Γ := Fintype.ofFinite _
  refine ⟨C, max B₁ 2, fun B hBge => ?_⟩
  obtain ⟨α, β, hm⟩ := hC B (le_trans (le_max_left _ _) hBge)
  obtain ⟨A, hAm⟩ := exists_group_mean Γ htr α
  obtain ⟨Bs, hBm⟩ := exists_group_mean Γ htr β
  refine ⟨A, Bs, fun m hdeg => ?_⟩
  refine mean_estimate (G := Γ) _ _ _ _ A Bs _ _ (fun g τ => α ((g : Equiv.Perm Ψ) τ))
    (fun g τ => β ((g : Equiv.Perm Ψ) τ)) hAm hBm fun g => ?_
  set F : RP Ψ N := monomial m 1 with hF
  set φ : Ψ × Fin N → Ψ × Fin N := fun x => ((g : Equiv.Perm Ψ) x.1, x.2) with hφ
  have hR : (monomial (m.mapDomain φ) 1 : RP Ψ N) = rename φ F := (rename_monomial φ m 1).symm
  have hest := hm (m.mapDomain φ) (by rw [Finsupp.degree_mapDomain]; exact hdeg)
  have anti := fun τ j => ((_root_.GlobalTheory.CompanionTheory.Ar.Top.flag_integral_permutations Ψ N).2 (g : Equiv.Perm Ψ) F).2 j τ
  have hS : ∑ τ, (α τ - β τ) * Sh T.j τ (rename φ F) =
      ∑ τ, (α ((g : Equiv.Perm Ψ) τ) - β ((g : Equiv.Perm Ψ) τ)) * Sh T.j τ F := by
    rw [← Equiv.sum_comp (g : Equiv.Perm Ψ)]
    exact Finset.sum_congr rfl fun τ _ => by rw [(anti τ T.j).1]
  have hU : ∑ τ, β τ * Tot τ (rename φ F) = ∑ τ, β ((g : Equiv.Perm Ψ) τ) * Tot τ F := by
    rw [← Equiv.sum_comp (g : Equiv.Perm Ψ)]
    exact Finset.sum_congr rfl fun τ _ => by rw [(anti τ T.j).2]
  rw [hR, hS, hU, hinv g g.2 B (le_trans (le_max_right _ _) hBge) F, hL g F] at hest
  exact hest

end GlobalTheory.CompanionTheory.Ar.Top
end

