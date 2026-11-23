module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0004
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0002
public import Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLetters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext

theorem embT_injective (D : D7) : Function.Injective (embT D) := by
  intro τ τ' h
  have h1 := (factEmb D.R D.host).1.1 h
  exact D.eTau.injective (Subtype.ext h1)

theorem card_Tau_eq (D : D7) : Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E := by
  have h1 := Module.finrank_mul_finrank ℚ D.host.K D.host.E
  rw [Formalism.MainNotions.Ext.finrank_K D.host, Formalism.MainNotions.StandardLattice.finrank_host D] at h1
  rw [D.what₂.card_Tau]
  omega

theorem trace_sum_over_letters (H : TraceSum) (D : D7) : StandardLatticesGL3.TraceMapNormalisation D :=
  H D.host.E D.host.K D.host.φ₀ D.what₂.Tau (embT D) (embT_injective D) (GL3Theta.induced_cm_type D) (card_Tau_eq D)

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpDict
section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

noncomputable def conjK : D.host.K →+* D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  (AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K →+* D.host.K)

theorem conjK_coe (x : D.host.K) : ((conjK D x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K x

noncomputable def tauKp : D.host.K →+* ℂ_[p] :=
  lam.comp ((D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring (fun _ => test_vector_mem_schwartz_bruhat D _))

theorem tauKp_apply (x : D.host.K) : tauKp D lam x = lamC lam (D.host.φ₀ (x : D.host.E)) := by
  unfold tauKp lamC
  first
  | rfl
  | (simp [test_vector_mem_schwartz_bruhat]; done)
  | (rw [dif_pos (test_vector_mem_schwartz_bruhat D _)]; rfl)

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpInertOf
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

def InertPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (b : K) (d p : ℕ), b ^ 2 = -(d : K) → p.Prime →
    jacobiSym (-(d : ℤ)) p = -1 → (Ideal.span {(p : 𝓞 K)}).IsPrime

theorem okpInert_of (HO : OkpInertG) (HI : InertPrime) (D : D7) : okpInert D := by
  intro p _ lam h2 hin
  have := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  obtain ⟨b, hb, -⟩ := exists_gen_K D.host
  have hb' : b ^ 2 = -(D.host.d : D.host.K) := by rw [hb]; push_cast; rfl
  have hpr := HI D.host.K (finrank_K D.host) b D.host.d p hb' (Fact.out) hin

  let φK : D.host.K →+* Qbar :=
    (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring (fun x => test_vector_mem_schwartz_bruhat D _)
  let c : D.host.K →+* D.host.K := (AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K →+* D.host.K)
  have hc : ∀ x : D.host.K, ((c x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := fun x =>
    AlgEquiv.restrictNormal_commutes D.host.conj D.host.K x
  have hne : ∃ x, c x ≠ x := by
    refine ⟨b, fun h => ?_⟩
    have hbE : ((b : D.host.K) : D.host.E) ^ 2 = -(D.host.d : D.host.E) := by
      have := congrArg (fun z : D.host.K => (z : D.host.E)) hb'
      simpa using this
    have h1 := hc b
    rw [h] at h1

    have h3 := Formalism.BasicNotions.Examples₂.emb_conj D.host D.host.φ₀ (b : D.host.E)
    rw [← h1] at h3
    have h4 : (D.host.φ₀ (b : D.host.E)) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, hbE]; simp
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h3.symm
    rw [hr] at h4
    have h5 : ((r ^ 2 : ℝ) : ℂ) = ((-(D.host.d : ℝ) : ℝ) : ℂ) := by push_cast; exact h4
    have h6 : r ^ 2 = -(D.host.d : ℝ) := by exact_mod_cast h5
    have h7 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
    nlinarith [sq_nonneg r]
  have key := HO D.host.K c p (lam.comp φK) (finrank_K D.host) hne h2 hpr
  rw [← key]
  unfold OKp
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp only [tauK, tauKc, RingHom.comp_apply]
    rw [lamC_mem' lam (test_vector_mem_schwartz_bruhat D _), lamC_mem' lam (test_vector_mem_schwartz_bruhat D _)]
    congr 2
    exact Subtype.ext (congrArg D.host.φ₀ (hc _))
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp only [tauK, tauKc, RingHom.comp_apply]
    rw [lamC_mem' lam (test_vector_mem_schwartz_bruhat D _), lamC_mem' lam (test_vector_mem_schwartz_bruhat D _)]
    congr 2
    exact Subtype.ext (congrArg D.host.φ₀ (hc _)).symm

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhEvenOf
section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem delta_ne' (HI : IdealLattice) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  delta_ne HI discrNe_holds D cc hc δ hδ

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhIsotropicOf
section
namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext

def OkpSwap (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ∀ α ∈ OKp D lam, α.swap ∈ OKp D lam

def OkpTrace (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ∀ α ∈ OKp D lam, ∃ n : ℤ_[p], α.1 + α.2 = zc n

def OkpNeg (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((-1 : ℂ_[p]), (-1 : ℂ_[p])) ∈ OKp D lam

def OkpTwo (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ OKp D lam

def OkpDiff (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 →
    ∃ α ∈ OKp D lam, ‖α.1 - α.2‖ = if p = D.host.d then ((p : ℝ) ^ ((1 : ℝ) / 2))⁻¹ else 1

theorem okpSwap_holds (D : D7) : OkpSwap D := by
  intro p _ lam α hα
  have hsq : D.host.conj D.host.sqd ∈ D.host.K := by
    rw [Formalism.HC.HostRaw.conj_sqd]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hK : ∀ x ∈ D.host.K, D.host.conj x ∈ D.host.K := by
    intro x hx
    have hle : (D.host.K).map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) ≤ D.host.K := by
      show (IntermediateField.adjoin ℚ {D.host.sqd}).map
        (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) ≤ D.host.K
      rw [IntermediateField.adjoin_map, Set.image_singleton,
        IntermediateField.adjoin_simple_le_iff]
      exact hsq
    exact hle ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)
  have hint : ∀ a : NumberField.RingOfIntegers D.host.K, IsIntegral ℤ (D.host.conj ((a : D.host.K) : D.host.E)) := by
    intro a
    have h0 : IsIntegral ℤ ((a : D.host.K) : D.host.E) :=
      (NumberField.RingOfIntegers.isIntegral_coe a).map ((D.host.K).val.restrictScalars ℤ)
    exact h0.map ((D.host.conj : D.host.E →ₐ[ℚ] D.host.E).restrictScalars ℤ)
  have key : ∀ a : NumberField.RingOfIntegers D.host.K, ∃ b : NumberField.RingOfIntegers D.host.K,
      ((b : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
    intro a
    have hy : IsIntegral ℤ
        (⟨D.host.conj ((a : D.host.K) : D.host.E), hK _ (a : D.host.K).2⟩ : D.host.K) :=
      (isIntegral_algHom_iff ((D.host.K).val.restrictScalars ℤ)
        (fun x y h => Subtype.ext h)).1 (hint a)
    exact ⟨⟨⟨D.host.conj ((a : D.host.K) : D.host.E), hK _ (a : D.host.K).2⟩, hy⟩, rfl⟩
  have hmaps : Set.MapsTo Prod.swap
      (Set.range fun a : NumberField.RingOfIntegers D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K)))
      (Set.range fun a : NumberField.RingOfIntegers D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K))) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := key a
    refine ⟨b, ?_⟩
    simp only [Prod.swap_prod_mk, tauK, tauKc, hb, Formalism.HC.HostRaw.conj_conj]
  unfold OKp at hα ⊢
  exact map_mem_closure continuous_swap hα hmaps

theorem okpNeg_holds (D : D7) : OkpNeg D := by
  intro p _ lam
  have hQ : (-1 : ℂ) ∈ Qbar := neg_mem (one_mem _)
  have hl : lamC lam (-1 : ℂ) = -1 := by
    unfold lamC
    rw [dite_eq_left hQ]
    have e : (⟨-1, hQ⟩ : Qbar) = -1 := Subtype.ext (by first | rfl | simp | norm_num)
    rw [e, map_neg, map_one]
  have hc : D.host.conj (-1 : D.host.E) = -1 := by simp
  unfold OKp
  refine subset_closure ⟨-1, ?_⟩
  simp [tauK, tauKc, hc, hl]

theorem okpTwo_holds (D : D7) : OkpTwo D := by
  intro p _ lam
  have hQ : (2 : ℂ) ∈ Qbar := by
    first
      | norm_num
      | simp
      | (have h := add_mem (one_mem Qbar) (one_mem Qbar); rwa [one_add_one_eq_two] at h)
  have hl : lamC lam (2 : ℂ) = 2 := by
    unfold lamC
    rw [dite_eq_left hQ]
    have e : (⟨2, hQ⟩ : Qbar) = 1 + 1 := Subtype.ext (by
      first
        | (show (2 : ℂ) = ((1 : Qbar) : ℂ) + ((1 : Qbar) : ℂ); norm_num)
        | (push_cast; norm_num)
        | rfl)
    rw [e, map_add (f := _), map_one] <;> norm_num
  have hc : D.host.conj (2 : D.host.E) = 2 := by
    first
      | (rw [show (2 : D.host.E) = 1 + 1 by norm_num, map_add (f := _), map_one])
      | exact map_ofNat _ 2
  have hz : (((2 : NumberField.RingOfIntegers D.host.K) : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : NumberField.RingOfIntegers D.host.K) = 1 + 1 by norm_num]
    first
      | (push_cast; norm_num)
      | simp
      | norm_num
  have hφ : D.host.φ₀ (2 : D.host.E) = 2 := by
    first
      | (rw [show (2 : D.host.E) = 1 + 1 by norm_num, map_add (f := _), map_one]; norm_num)
      | simp
  unfold OKp
  refine subset_closure ⟨2, ?_⟩
  simp only [tauK, tauKc, hz, hc, hφ, hl, Prod.mk.injEq, and_self]

theorem cube_of (H : CubeOfTwoIdentities) (D : D7) (h2 : cube2 D) (h3 : cube3 D) : cube D := by
  intro p _ cc δ g hA
  exact H p g hA.2.2.2.2 (h2 p cc δ g hA) (h3 p cc δ g hA)

theorem jetsPh_of (HH : JetsHigh) (H1 : JetsOne) (H2 : JetsTwo) (D : D7) (hc : cube D) (hn : phNorm D)
    (hb : beConj D) (hdf : OkpDiff D) : jetsPh D := by
  intro p _ cc δ g hA hp
  have hok := hA.2.2.2.2
  obtain ⟨α₀, hα₀, hnorm⟩ := hdf p g.lam hp
  have hprod : ‖(α₀.1 - α₀.2) * g.jetPh 2‖ ≤ 1 :=
    H2 p g α₀.1 α₀.2 hok (hb p cc δ g hA hp α₀ hα₀)
  rw [norm_mul] at hprod
  refine ⟨fun i hi2 => ?_, fun α hα => H2 p g α.1 α.2 hok (hb p cc δ g hA hp α hα),
    fun hpd => ?_, fun hpd => ?_⟩
  · by_cases hi1 : i = 1
    · subst hi1
      have hn1 := hn p cc δ g hA hp ((-1 : ℂ_[p]), (-1 : ℂ_[p])) (okpNeg_holds D p g.lam)
      have hm : ((-1 : ℂ_[p]), (-1 : ℂ_[p])).1 * ((-1 : ℂ_[p]), (-1 : ℂ_[p])).2 = 1 := by
        norm_num
      rw [hm, map_one, one_mul] at hn1
      exact H1 p g hok hp hn1
    · exact HH p g hok (hc p cc δ g hA) i hi1 hi2
  · rw [if_neg hpd] at hnorm
    rw [hnorm, one_mul] at hprod
    exact hprod
  · rw [if_pos hpd] at hnorm
    rw [hnorm] at hprod
    have hpos : (0 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
    have h3 := mul_le_mul_of_nonneg_left hprod hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_one] at h3
    exact h3


end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtPhDualWHolds
section
namespace Formalism.MainNotions.Ext

theorem addPtW_holds : AddPtW :=
  fun p _ g hOk hF σ a b ha hb =>
    formal_group_add_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 hF σ a b ha hb

theorem mulPtW_holds : MulPtW :=
  fun p _ g hOk c hc σ a ha =>
    formal_group_mul_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 c hc σ a ha

end Formalism.MainNotions.Ext
end

