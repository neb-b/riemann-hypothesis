module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0005
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FamilyLogGammaSmallHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.DivisionRationalLattice
section
namespace Formalism.MainNotions.Ext

theorem finOrdG_holds : FinOrdG := finite_order_adelic

end Formalism.MainNotions.Ext

namespace Formalism.MainNotions.UnusedSlot33

theorem division_rational_lattice (D : Formalism.BasicNotions.D7) : division_rows_rational_lattice D :=
  finiteModel_of_heckeEstimate D (finite_order_of_totally_real Formalism.MainNotions.Ext.finOrdG_holds D)

end Formalism.MainNotions.UnusedSlot33
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.InducedCmType
section
namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem induced_cm_type (D : D7) : InducedCMType D := by
  intro τ a

  have hmem : embT D τ ∈ Formalism.MainNotions.GlobalTheoryTheory.PhiEmb D := ⟨((D.eTau τ : D.R.Psi) : D.R.GG), (D.eTau τ).2, rfl⟩
  exact (Formalism.MainNotions.UnusedSlot33.second_proposition_every_localisation D).2.1 _ hmem _ a.2

theorem cm_field_facts_hold (D : D7) : HostFieldConditions D :=
  Formalism.MainNotions.TaylorLogMetric.first_hypothesis_of_lifting D (Formalism.MainNotions.UnusedSlot33.ramification_two_and_conjugation_at_q_and_d D)

end Formalism.MainNotions.GL3Theta
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem exists_conj_OK (a : 𝓞 D.host.K) : ∃ a' : 𝓞 D.host.K, (((a' : D.host.K)) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
  have hsq : D.host.conj D.host.sqd ∈ IntermediateField.adjoin ℚ {D.host.sqd} := by
    rw [D.host.gal_sqd]
    exact mul_mem (intCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hmap : IntermediateField.map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E)
      (IntermediateField.adjoin ℚ {D.host.sqd}) ≤ IntermediateField.adjoin ℚ {D.host.sqd} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    exact IntermediateField.adjoin_simple_le_iff.2 hsq
  have hx : ((a : D.host.K) : D.host.E) ∈ IntermediateField.adjoin ℚ {D.host.sqd} := (a : D.host.K).2
  have hK : D.host.conj ((a : D.host.K) : D.host.E) ∈ D.host.K :=
    hmap ((IntermediateField.mem_map _).2 ⟨_, hx, rfl⟩)
  have hint : IsIntegral ℤ (⟨_, hK⟩ : D.host.K) := by
    rw [← isIntegral_algebraMap_iff (B := D.host.E)]
    have ha : IsIntegral ℤ ((a : D.host.K) : D.host.E) :=
      a.isIntegral_coe.algebraMap
    exact ha.map D.host.conj.toAlgHom.toRingHom.toIntAlgHom
  let b : integralClosure ℤ D.host.K := ⟨⟨_, hK⟩, hint⟩
  exact ⟨b, rfl⟩

theorem okp_swap (α : ℂ_[p] × ℂ_[p]) (hα : α ∈ OKp D lam) : α.swap ∈ OKp D lam := by
  have hc : ∀ x : D.host.E, D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := by
    intro x
    simp only [← D.embE_φ₀, RingHom.comp_apply, D.embE_conj, D.starLL_cx]
  unfold OKp at hα ⊢
  refine map_mem_closure continuous_swap hα ?_
  rintro _ ⟨a, rfl⟩
  obtain ⟨a', ha'⟩ := exists_conj_OK D a
  refine ⟨a', ?_⟩
  simp only [tauK, tauKc, ha', Prod.swap_prod_mk, hc, Complex.conj_conj]

omit [Fact p.Prime] in
theorem test_vector_mem_schwartz_bruhat (z : D.host.E) : D.host.φ₀ z ∈ Qbar := by
  have h : IsIntegral ℚ z := Algebra.IsIntegral.isIntegral z
  exact mem_algebraicClosure_iff.2 (h.map D.host.φ₀.toRatAlgHom).isAlgebraic

theorem lamPhi_add (x y : D.host.E) : lamC lam (D.host.φ₀ (x + y)) = lamC lam (D.host.φ₀ x) + lamC lam (D.host.φ₀ y) := by
  unfold lamC
  rw [dite_eq_left (test_vector_mem_schwartz_bruhat D (x + y)), dite_eq_left (test_vector_mem_schwartz_bruhat D x), dite_eq_left (test_vector_mem_schwartz_bruhat D y), ← map_add lam]
  exact congrArg lam (Subtype.ext (by simp))

theorem lamPhi_mul (x y : D.host.E) : lamC lam (D.host.φ₀ (x * y)) = lamC lam (D.host.φ₀ x) * lamC lam (D.host.φ₀ y) := by
  unfold lamC
  rw [dite_eq_left (test_vector_mem_schwartz_bruhat D (x * y)), dite_eq_left (test_vector_mem_schwartz_bruhat D x), dite_eq_left (test_vector_mem_schwartz_bruhat D y), ← map_mul lam]
  exact congrArg lam (Subtype.ext (by simp))

theorem okp_add (α β : ℂ_[p] × ℂ_[p]) (hα : α ∈ OKp D lam) (hβ : β ∈ OKp D lam) : α + β ∈ OKp D lam := by
  unfold OKp at hα hβ ⊢
  refine map_mem_closure₂ (f := fun u v : ℂ_[p] × ℂ_[p] => u + v) continuous_add hα hβ ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨a + b, ?_⟩
  have hab : (((a + b : 𝓞 D.host.K) : D.host.K) : D.host.E)
      = ((a : D.host.K) : D.host.E) + ((b : D.host.K) : D.host.E) := by simp
  simp only [tauK, tauKc, hab, map_add D.host.conj, lamPhi_add, Prod.mk_add_mk]

theorem okp_mul (α β : ℂ_[p] × ℂ_[p]) (hα : α ∈ OKp D lam) (hβ : β ∈ OKp D lam) : α * β ∈ OKp D lam := by
  unfold OKp at hα hβ ⊢
  refine map_mem_closure₂ (f := fun u v : ℂ_[p] × ℂ_[p] => u * v) continuous_mul hα hβ ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨a * b, ?_⟩
  have hab : (((a * b : 𝓞 D.host.K) : D.host.K) : D.host.E)
      = ((a : D.host.K) : D.host.E) * ((b : D.host.K) : D.host.E) := by simp
  simp only [tauK, tauKc, hab, map_mul D.host.conj, lamPhi_mul, Prod.mk_mul_mk]

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TransInvOf
section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem lamOf_lat (HI : IdealLattice) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ := by
  have hd : D.host.d ≠ 0 := by
    intro h0
    have hs : D.host.sqd = 0 := by
      have h := D.host.sqd_sq
      rw [h0] at h
      simp at h
      exact h
    have hK : D.host.K = ⊥ := by
      show IntermediateField.adjoin ℚ {D.host.sqd} = ⊥
      rw [hs]
      exact IntermediateField.adjoin_simple_eq_bot_iff.mpr (zero_mem _)
    have h1 := (IntermediateField.finrank_eq_one_iff).mpr hK
    have h2 := Formalism.HC.HostRaw.finrank_K (H := D.host.toHostRaw)
    omega
  have hreal : IsEmpty (D.host.K →+* ℝ) := by
    refine ⟨fun f => ?_⟩
    have hs : (⟨D.host.sqd, Formalism.HC.HostRaw.sqd_mem_K (H := D.host.toHostRaw)⟩ : D.host.K) ^ 2 =
        -((D.host.d : ℕ) : D.host.K) := by
      apply Subtype.ext
      simpa using D.host.sqd_sq
    have h2 := congrArg f hs
    rw [map_pow, map_neg, map_natCast] at h2
    have h3 := sq_nonneg (f ⟨D.host.sqd, Formalism.HC.HostRaw.sqd_mem_K (H := D.host.toHostRaw)⟩)
    have h4 : (0 : ℝ) < (D.host.d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    linarith
  obtain ⟨⟨w₁, w₂, hw, heq⟩, -⟩ :=
    HI D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) (Formalism.HC.HostRaw.finrank_K (H := D.host.toHostRaw))
      hreal cc δ hc hδ
  exact ⟨w₁, w₂, hw, heq⟩

theorem delta_ne (HI : IdealLattice) (HD : DiscrNe) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat HI D cc hc 1 one_ne_zero
  intro h0
  have h12 : δ ^ 12 = discr (lamOf D cc 1) := hδ
  rw [h0, hL] at h12
  exact HD w₁ w₂ hw (by simpa using h12.symm)

end Formalism.MainNotions.Ext
end

