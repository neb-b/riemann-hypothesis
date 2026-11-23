module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem exists_uniformiser_max (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ ϖ : k, ϖ ≠ 0 ∧ valuation k ϖ < 1 ∧ ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  obtain ⟨x, hx⟩ := valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hx' : e (valuation k x) = WithZero.exp (-1 : ℤ) := by rw [hx]; simp
  refine ⟨x, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero, map_zero] at hx'
    exact WithZero.zero_ne_coe hx'
  · rw [← e.strictMono.lt_iff_lt, hx', map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro y hy
    rw [← e.strictMono.le_iff_le, hx']
    have hlt : e (valuation k y) < 1 := by rw [← map_one e]; exact e.strictMono hy
    rcases eq_or_ne (e (valuation k y)) 0 with h | h
    · rw [h]; exact zero_le'
    · rw [← WithZero.exp_log h] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]; omega

theorem eig_jacquet_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Cut ψ r → ∀ v ∈ twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  intro k _ _ _ _ r t ψ V _ _ π hπ hψ hord hcut v hv heig
  obtain ⟨ϖ, hϖ0, hϖ1, hϖmax⟩ := exists_uniformiser_max k
  let z : GL (Fin (r + t)) k := diagT k (Fin (r + t)) (fun i => if (i : ℕ) < r then Units.mk0 ϖ hϖ0 else 1)
  have hz : z.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then ϖ else 1) := by
    simp only [z]; rw [val_diagT]; congr 1; funext i; split_ifs <;> simp
  obtain ⟨hD, -⟩ := _root_.GlobalTheory.PsType.grp_theta_datum k (r + t) ψ hψ hord
  obtain ⟨hSD, hSmono⟩ := _root_.GlobalTheory.StripGrp.strip_datum_monotone k (r + t) ψ r ϖ hψ hϖ0 hϖ1 hϖmax
  obtain ⟨h0J, hθ1, h1KO, hconj⟩ := _root_.GlobalTheory.PsType.strip_props k (r + t) ψ r ϖ hϖ0 hϖ1 hϖmax hcut
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.PsType.twKer_one_mem_aug_stage _ V π _ (strip ψ r ϖ) hSmono (_root_.GlobalTheory.PsType.strip_exhaust k r t ψ ϖ hψ hϖ0 hϖ1 hϖmax) v hv
  refine _root_.GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain (GL (Fin (r + t)) k) V π hπ (grp ψ) (strip ψ r ϖ) (theta ψ) z hD hSD hSmono
    (fun y hy => ⟨h0J y hy, hθ1 0 y hy⟩) (hconj z hz) ?_ ?_ m v hm heig
  · intro y hy
    by_cases hyJ : y ∈ grp ψ
    · exact Or.inl ⟨hyJ, hθ1 1 y hy⟩
    · exact Or.inr (_root_.GlobalTheory.PsType.not_intertwine k (r + t) ψ hord y (h1KO y hy) hyJ)
  · intro j hj
    obtain ⟨y, hy, hblk⟩ := _root_.GlobalTheory.PsType.clear_upper_right k (r + t) ψ r ϖ hord hcut j hj
    have hyJ : y ∈ grp ψ := h0J y hy
    have hyinv : y⁻¹ ∈ grp ψ := hD.inv y hyJ
    have hg : y⁻¹ * j ∈ grp ψ := hD.mul _ hyinv _ hj
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.PsType.conj_blockLower_mem_theta k (r + t) ψ r ϖ hϖ0 hϖ1 z hz (y⁻¹ * j) hg hblk
    refine ⟨y, hy, h1, ?_⟩
    rw [h2, _root_.GlobalTheory.PsType.theta_mul k (r + t) ψ hord _ hyinv _ hj, hθ1 0 _ ((hSD 0).inv y hy), one_mul]

end GlobalTheory.PsType
