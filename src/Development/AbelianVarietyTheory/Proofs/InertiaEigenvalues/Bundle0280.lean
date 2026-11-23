module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpPositionConditionsAtLetter
section
noncomputable section

open Classical

namespace GlobalTheory.PositionData

theorem mnLo_le_zero' (Fl : Finset ℤ) : mnLo Fl ≤ 0 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem mnLo_le' (Fl : Finset ℤ) {z : ℤ} (hz : z ∈ Fl) : mnLo Fl ≤ z :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem hz)

theorem le_mxLo' (t : ℕ) (Fl : Finset ℤ) : (t : ℤ) - 1 ≤ mxLo t Fl :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem le_mxLo_of_mem (t : ℕ) (Fl : Finset ℤ) {z : ℤ} (hz : z ∈ Fl) : z ≤ mxLo t Fl :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem hz)

theorem mxLo_cases (t : ℕ) (Fl : Finset ℤ) : mxLo t Fl = (t : ℤ) - 1 ∨ mxLo t Fl ∈ Fl :=
  Finset.mem_insert.mp (Finset.max'_mem _ _)

theorem mnLo_cases (Fl : Finset ℤ) : mnLo Fl = 0 ∨ mnLo Fl ∈ Fl :=
  Finset.mem_insert.mp (Finset.min'_mem _ _)

theorem mnAll_le_zero' (Fl Fc : Finset ℤ) : mnAll Fl Fc ≤ 0 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem mnAll_le' (Fl Fc : Finset ℤ) {z : ℤ} (hz : z ∈ Fl ∪ Fc) : mnAll Fl Fc ≤ z :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem hz)

theorem le_mxAll' (t : ℕ) (Fl Fc : Finset ℤ) : (t : ℤ) - 1 ≤ mxAll t Fl Fc :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem le_mxAll_of_mem (t : ℕ) (Fl Fc : Finset ℤ) {z : ℤ} (hz : z ∈ Fl ∪ Fc) :
    z ≤ mxAll t Fl Fc :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem hz)

theorem far_from_block (z c σ : ℤ) (t : ℕ) (B : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ (t : ℤ) - 1)
    (hσ : (σ : ℝ) ≤ 2 * B) (hz : 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) :
    σ + 2 < |z - c| := by
  have hc0' : (0 : ℝ) ≤ c := by exact_mod_cast hc0
  have hc1' : (c : ℝ) ≤ (t : ℝ) - 1 := by exact_mod_cast hc1
  have key : (σ : ℝ) + 2 < |(z : ℝ) - c| := by
    rcases le_abs'.mp hz with h | h
    · rw [lt_abs]; right; linarith
    · rw [lt_abs]; left; linarith
  exact_mod_cast key

end GlobalTheory.PositionData

namespace GlobalTheory.PositionData

theorem position_conditions : ∀ (l t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ) (sgP σ : ℤ),
    1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    (∀ n : ℤ, W0 + (-η - 2 * (sgP : ℝ) - 3) ≤ (n : ℝ) → (n : ℝ) ≤ W0 + (S + η + η + 2 * (sgP : ℝ) + 4) →
      ¬ (l : ℤ) ∣ n) →
    (σ : ℝ) ≤ 2 * B → σ ≤ sgP → 2 * η + 8 * B + 7 < (l : ℝ) →
    (∀ u ∈ GlobalTheory.PositionData.US up Fl Fc, 1 ≤ u ∧ u ≤ (GlobalTheory.PositionData.hS up t Fl Fc : ℤ) - 1) ∧
    1 ≤ GlobalTheory.PositionData.wS up Fl Fc ∧
    (GlobalTheory.PositionData.wS up Fl Fc : ℤ) + t - 1 ≤ (GlobalTheory.PositionData.hS up t Fl Fc : ℤ) - 1 ∧
    (up = true → (GlobalTheory.PositionData.wS up Fl Fc : ℤ) + t - 1 ≤ GlobalTheory.PositionData.etaS t Fl) ∧
    (up = false → (GlobalTheory.PositionData.hS up t Fl Fc : ℤ) - GlobalTheory.PositionData.etaS t Fl ≤ GlobalTheory.PositionData.wS up Fl Fc) ∧
    (GlobalTheory.PositionData.etaS t Fl : ℤ) + 4 * σ + 6 < l ∧
    (∀ x ∈ Formalism.MainNotions.tableLineDegreeTwo.lows up (GlobalTheory.PositionData.hS up t Fl Fc) (GlobalTheory.PositionData.etaS t Fl) (GlobalTheory.PositionData.US up Fl Fc),
      ∀ y ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (GlobalTheory.PositionData.wS up Fl Fc) t, σ + 2 < |x - y|) ∧
    Formalism.WachCohomologyFacts.V2.ResidueAvoidance l up (GlobalTheory.PositionData.hS up t Fl Fc) (GlobalTheory.PositionData.etaS t Fl) σ (GlobalTheory.PositionData.US up Fl Fc) := by
  intro l t up Fl Fc η S B W0 sgP σ ht htη hB hS0 hFl hFc hW0 hn hσB hσs hl
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hσs' : (σ : ℝ) ≤ sgP := by exact_mod_cast hσs
  have hmx0 := le_mxLo' t Fl
  have hmn0 := mnLo_le_zero' Fl
  have hmx : (mxLo t Fl : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    rcases mxLo_cases t Fl with h | h
    · rw [h]; push_cast; linarith
    · have := (hFl _ h).1; rw [abs_le] at this; linarith
  have hmn : ((t : ℝ) - 1) / 2 - η ≤ (mnLo Fl : ℝ) := by
    rcases mnLo_cases Fl with h | h
    · rw [h]; push_cast; linarith
    · have := (hFl _ h).1; rw [abs_le] at this; linarith
  have hηS : (etaS t Fl : ℤ) = mxLo t Fl - mnLo Fl + 1 := by
    unfold etaS; rw [Int.toNat_of_nonneg]; omega

  have hfar : ∀ z ∈ Fl ∪ Fc, 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2| := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact (hFl z h).2
    · have := (hFc z h).1
      cases up
      · simp only [Bool.false_eq_true, if_false] at this
        rw [abs_sub_comm]; exact le_trans hW0 (le_trans this (le_abs_self _))
      · simp only [if_true] at this
        exact le_trans hW0 (le_trans this (le_abs_self _))
  have hT1 : (etaS t Fl : ℤ) + 4 * σ + 6 < l := by
    have : ((etaS t Fl : ℤ) : ℝ) + 4 * σ + 6 < l := by
      rw [hηS]; push_cast; linarith
    exact_mod_cast this
  have hT2 : ∀ x ∈ US up Fl Fc, ∀ y ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (wS up Fl Fc) t, σ + 2 < |x - y| := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    rw [Formalism.WachCohomologyFacts.Top.GlobalTheory, Finset.mem_Icc] at hy
    have := far_from_block z (y - wS up Fl Fc) σ t B (by omega) (by omega) hσB
      (hfar z (Finset.mem_val.mp hz))
    have e : z + (wS up Fl Fc : ℤ) - y = z - (y - wS up Fl Fc) := by ring
    rw [e]; exact this
  have hT2' : ∀ x ∈ Formalism.MainNotions.tableLineDegreeTwo.lows up (hS up t Fl Fc) (etaS t Fl) (US up Fl Fc),
      ∀ y ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (wS up Fl Fc) t, σ + 2 < |x - y| := by
    intro x hx
    exact hT2 x (Multiset.mem_filter.mp hx).1
  cases up
  ·
    have hmA0 := mnAll_le_zero' Fl Fc
    have hw : (wS false Fl Fc : ℤ) = 1 - mnAll Fl Fc := by
      simp only [wS, Bool.false_eq_true, if_false]; rw [Int.toNat_of_nonneg]; omega
    have hh : (hS false t Fl Fc : ℤ) = mxLo t Fl + (1 - mnAll Fl Fc) + 1 := by
      simp only [hS, Bool.false_eq_true, if_false]; rw [Int.toNat_of_nonneg] <;> omega
    have hcl : ∀ z ∈ Fc, ((z : ℝ)) ≤ ((t : ℝ) - 1) / 2 - W0 ∧
        ((t : ℝ) - 1) / 2 - (W0 + S + η + 1) ≤ z := by
      intro z hz
      have := hFc z hz
      simp only [Bool.false_eq_true, if_false] at this
      constructor <;> linarith [this.1, this.2]
    refine ⟨?_, by omega, by omega, by simp, fun _ => by omega, hT1, hT2', ?_⟩
    · intro u hu
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hu
      have hz' := Finset.mem_val.mp hz
      have h1 := mnAll_le' Fl Fc hz'
      have h2 : z ≤ mxLo t Fl := by
        rcases Finset.mem_union.mp hz' with h | h
        · exact le_mxLo_of_mem t Fl h
        · have := (hcl z h).1
          have : (z : ℝ) < ((t : ℤ) - 1 : ℤ) := by push_cast; linarith
          have : z < (t : ℤ) - 1 := by exact_mod_cast this
          omega
      omega
    · intro x hx m hm1 hm2
      rcases Multiset.mem_filter.mp hx with ⟨hxU, hxW⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hxU
      have hz' := Finset.mem_val.mp hz
      simp only [Formalism.WachCohomologyFacts.V2.InWinN, Bool.false_eq_true, if_false] at hxW
      have hzc : z ∈ Fc := by
        rcases Finset.mem_union.mp hz' with h | h
        · exfalso; apply hxW
          have := mnLo_le' Fl h; have := le_mxLo_of_mem t Fl h
          constructor <;> omega
        · exact h
      simp only [Bool.false_eq_true, if_false]
      intro heq
      have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub m _ l).mp heq.symm
      rw [hηS] at hm2
      have e : (hS false t Fl Fc : ℤ) - (z + (wS false Fl Fc : ℤ)) = mxLo t Fl + 1 - z := by
        rw [hh, hw]; ring
      rw [e] at hd
      have hm1r : (-2 * σ - 2 : ℝ) ≤ m := by exact_mod_cast hm1
      have hm2r : (m : ℝ) ≤ (mxLo t Fl : ℝ) - mnLo Fl + 1 + 2 * σ + 3 := by exact_mod_cast hm2
      have hzc' := hcl z hzc
      apply hn (mxLo t Fl + 1 - z - m)
      · push_cast; linarith
      · push_cast; linarith
      · exact hd
  ·
    have hw : (wS true Fl Fc : ℤ) = 1 - mnLo Fl := by
      simp only [wS, if_true]; rw [Int.toNat_of_nonneg]; omega
    have hmA := le_mxAll' t Fl Fc
    have hh : (hS true t Fl Fc : ℤ) = mxAll t Fl Fc + (1 - mnLo Fl) + 1 := by
      simp only [hS, if_true]; rw [hw, Int.toNat_of_nonneg]; omega
    have hcl : ∀ z ∈ Fc, ((t : ℝ) - 1) / 2 + W0 ≤ z ∧
        (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + (W0 + S + η + 1) := by
      intro z hz
      have := hFc z hz
      simp only [if_true] at this
      constructor <;> linarith [this.1, this.2]
    refine ⟨?_, by omega, by omega, fun _ => by omega, by simp, hT1, hT2', ?_⟩
    · intro u hu
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hu
      have hz' := Finset.mem_val.mp hz
      have h2 := le_mxAll_of_mem t Fl Fc hz'
      have h1 : mnLo Fl ≤ z := by
        rcases Finset.mem_union.mp hz' with h | h
        · exact mnLo_le' Fl h
        · have := (hcl z h).1
          have : (0 : ℝ) < z := by linarith
          have : 0 < z := by exact_mod_cast this
          omega
      omega
    · intro x hx m hm1 hm2
      rcases Multiset.mem_filter.mp hx with ⟨hxU, hxW⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hxU
      have hz' := Finset.mem_val.mp hz
      simp only [Formalism.WachCohomologyFacts.V2.InWinN, if_true] at hxW
      have hzc : z ∈ Fc := by
        rcases Finset.mem_union.mp hz' with h | h
        · exfalso; apply hxW
          have := mnLo_le' Fl h; have := le_mxLo_of_mem t Fl h
          constructor <;> omega
        · exact h
      simp only [if_true]
      intro heq
      have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub m _ l).mp heq.symm
      rw [hηS] at hm2
      rw [hw] at hd
      have hm1r : (-2 * σ - 2 : ℝ) ≤ m := by exact_mod_cast hm1
      have hm2r : (m : ℝ) ≤ (mxLo t Fl : ℝ) - mnLo Fl + 1 + 2 * σ + 3 := by exact_mod_cast hm2
      have hzc' := hcl z hzc
      apply hn (z + (1 - mnLo Fl) - m)
      · push_cast; linarith
      · push_cast; linarith
      · exact hd

end GlobalTheory.PositionData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthGlobalCocyclesLeSumPlacesOver
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.CountL

theorem length_le_of_semilinear {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (hf : Function.Injective f) : Module.length R M ≤ Module.length S N := by
  have : RingHomSurjective σ := ⟨hσ⟩
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_strictMono (Submodule.map f) (Submodule.map_strictMono_of_injective hf)

theorem length_le_inf_comap_add {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (C : Submodule R M) (A H : Submodule S N) (hC : ∀ x ∈ C, f x ∈ A) :
    Module.length R ↥C ≤
      Module.length R ↥(C ⊓ H.comap f) + Module.length S (↥A ⧸ H.comap A.subtype) := by
  let g : ↥C →ₛₗ[σ] (↥A ⧸ H.comap A.subtype) :=
    (H.comap A.subtype).mkQ.comp ((f.domRestrict C).codRestrict A fun x => hC x x.2)
  have hg : ∀ x : ↥C, x ∈ LinearMap.ker g → f x ∈ H := fun x hx =>
    (Submodule.Quotient.mk_eq_zero (H.comap A.subtype)).1 hx
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype (LinearMap.ker g).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)]
  refine add_le_add ?_ ?_
  · refine Module.length_le_of_injective
      ((C.subtype.comp (LinearMap.ker g).subtype).codRestrict (C ⊓ H.comap f)
        fun x => ⟨x.1.2, hg x.1 x.2⟩) ?_
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  · refine length_le_of_semilinear hσ ((LinearMap.ker g).liftQ g le_rfl) ?_
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem exists_le_forall_le {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (K : ι → Submodule R M) (C : Submodule R M) (b : ℕ∞)
    (h : ∀ q, ∀ C₀ ≤ C, Module.length R ↥C₀ ≤ Module.length R ↥(C₀ ⊓ K q) + b) (Q : Finset ι) :
    ∃ C' : Submodule R M, C' ≤ C ∧ (∀ q ∈ Q, C' ≤ K q) ∧
      Module.length R ↥C ≤ (Q.card : ℕ∞) * b + Module.length R ↥C' := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨C₀, h₁, h₂, h₃⟩ := ih
    refine ⟨C₀ ⊓ K a, inf_le_left.trans h₁, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact inf_le_right
      · exact inf_le_left.trans (h₂ q hq)
    · rw [Finset.card_insert_of_notMem ha]
      refine h₃.trans ((add_le_add le_rfl (h a C₀ h₁)).trans (le_of_eq ?_))
      push_cast
      ring

theorem length_quot_natCast_le {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (p : ℕ) :
    Module.length S (S ⧸ Ideal.span {(p : S)}) ≤ Module.length R (R ⧸ Ideal.span {(p : R)}) := by
  refine length_le_of_semilinear (σ := e.symm.toRingHom) e.symm.surjective
    (Submodule.mapQ (Ideal.span {(p : S)}) (Ideal.span {(p : R)}) e.symm.toRingHom.toSemilinearMap ?_) ?_
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨e.symm y, by
      show _ = e.symm (y * p)
      simp⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : e.symm x ∈ Ideal.span {(p : R)} := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx'
    refine (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton'.2 ⟨e y, ?_⟩)
    simpa using congrArg e hy

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
noncomputable def locFunS {D : D7} (i : D.nd.Loc) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    (GE D.nd → KOG (D.nd.O i) k) →ₛₗ[(D.nbr i w hw).eO.toRingHom]
      (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) where
  toFun := locFun i M w hw
  map_add' a b := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_add _ _
  map_smul' c a := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_smulₛₗ c _


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (e : ℕ), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs M e ∧ ∀ f ∈ C, InCut i r Xs M w hw f) → ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ f ∈ C', IsFinL i M f) ∧ Module.length (D.nd.O i) ↥C ≤ (((placesOver D.host.E (D.nd.l i)).ncard * e : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) + Module.length (D.nd.O i) ↥C' := by
  intro D i r Xs k M C e h
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin := finite_placesOver D.host.E (D.nd.l i) hl.ne_zero
  letI : Fintype ↥(placesOver D.host.E (D.nd.l i)) := hfin.fintype
  obtain ⟨C', h₁, h₂, h₃⟩ := exists_le_forall_le
    (fun q : ↥(placesOver D.host.E (D.nd.l i)) =>
      (HfD (Br.PD D.loc D.nbr i q.1 q.2) (Br.locLat D.nbr i q.1 q.2 M)).comap (locFunS i M q.1 q.2))
    C ((e : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i)) (by
      rintro ⟨w, hw⟩ C₀ hC₀
      refine (length_le_inf_comap_add (D.nbr i w hw).eO.surjective (locFunS i M w hw) C₀
        (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M)) _
        (fun f hf => (h w hw).2 f (hC₀ hf))).trans (add_le_add le_rfl ?_)
      refine le_trans (h w hw).1 (mul_le_mul' le_rfl ?_)
      unfold lenOl lenQ
      rw [Br.PD_p]
      exact length_quot_natCast_le (D.nbr i w hw).eO _) Finset.univ
  refine ⟨C', h₁, fun f hf w hw => h₂ ⟨w, hw⟩ (Finset.mem_univ _) hf, ?_⟩
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← mul_assoc] at h₃
  rw [Nat.cast_mul]
  exact h₃

end GlobalTheory.Cut.CountL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentCyclotomicEigenvectorsWeights
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem actC_apply_eq_σC {l : ℕ} [Fact l.Prime] (g : GQ l) (y : ℂ_[l]) :
    GlobalTheory.Cyc.Model.actC g y = Formalism.Per.σC g y := by
  change GlobalTheory.Cyc.Model.extHom g y = Formalism.Per.σC g y
  have hc : Continuous (Formalism.Per.σC g) :=
    (AddMonoidHomClass.isometry_of_norm (Formalism.Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (GlobalTheory.Cyc.Model.extHom_cont g) hc
  | ih x => exact (GlobalTheory.Cyc.Model.extHom_coe g x).trans (GlobalTheory.RingBasics.σC_coe g x).symm

theorem linIndep_of_eigen_weights : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n ℂ_[l]) (ι : Type) [Fintype ι] (v : ι → n → ℂ_[l]) (w : ι → ℤ), (∀ (g : ↥(GK K)) j, (A g).mulVec (fun i => Formalism.Per.σC (g : GQ l) (v j i)) = algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) • v j) → (∀ (a : ℤ) (c : ι → Om l), (∀ j, c j ∈ K.1) → (∀ j, w j ≠ a → c j = 0) → ∑ j, (c j : ℂ_[l]) • v j = 0 → c = 0) → LinearIndependent ℂ_[l] v := by
  intro l _ P n _ _ K A ι _ v w hA hK
  classical

  set e : GQ l → ℤ → ℂ_[l] := fun g k => algebraMap ℚ_[l] ℂ_[l] ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) with he
  have e_ne : ∀ g k, e g k ≠ 0 := fun g k => by
    simp only [he, ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[l] ℂ_[l]).injective, Units.ne_zero,
      not_false_eq_true]
  have e_sub : ∀ g (a b : ℤ), e g (a - b) * e g b = e g a := fun g a b => by
    simp only [he, ← map_mul, ← Units.val_mul, ← zpow_add, sub_add_cancel]
  have hcyc : GlobalTheory.Cyc.IsCyc P.χQ := P.χQ_cyc
  rw [Fintype.linearIndependent_iff]
  suffices key : ∀ m : ℕ, ∀ a : ι → ℂ_[l], (Finset.univ.filter (fun j => a j ≠ 0)).card = m →
      ∑ j, a j • v j = 0 → a = 0 by
    intro a ha j
    exact congrFun (key _ a rfl ha) j
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a hcard hrel
  by_contra hne
  obtain ⟨j0, hj0⟩ : ∃ j0, a j0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  set b : ι → ℂ_[l] := fun j => (a j0)⁻¹ * a j with hb
  have hbrel : ∑ j, b j • v j = 0 := by
    simp only [hb, mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  have hb0 : b j0 = 1 := by simp only [hb, inv_mul_cancel₀ hj0]
  have hsupp : ∀ j, b j ≠ 0 ↔ a j ≠ 0 := fun j => by
    simp only [hb, ne_eq, mul_eq_zero, inv_eq_zero, hj0, false_or]

  have htw : ∀ g : ↥(GK K), ∀ j, Formalism.Per.σC (g : GQ l) (b j) * e g (w j) = e g (w j0) * b j := by
    intro g
    have h1 : (∑ j, Formalism.Per.σC (g : GQ l) (b j) • (fun i => Formalism.Per.σC (g : GQ l) (v j i))) = 0 := by
      funext i
      have hi := congrFun hbrel i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_zero (Formalism.Per.σC (g : GQ l)), ← hi, map_sum]
      simp only [map_mul]
    have h2 : ∑ j, (Formalism.Per.σC (g : GQ l) (b j) * e g (w j)) • v j = 0 := by
      have := congrArg (fun u => (A g).mulVec u) h1
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hA, Matrix.mulVec_zero, smul_smul] at this
      exact this
    set d : ι → ℂ_[l] := fun j => Formalism.Per.σC (g : GQ l) (b j) * e g (w j) - e g (w j0) * b j with hd
    have hdrel : ∑ j, d j • v j = 0 := by
      simp only [hd, sub_smul, Finset.sum_sub_distrib]
      rw [h2]
      simp only [mul_smul, ← Finset.smul_sum, hbrel, smul_zero, sub_zero]
    have hdsub : Finset.univ.filter (fun j => d j ≠ 0) ⊆ (Finset.univ.filter (fun j => a j ≠ 0)).erase j0 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
      refine ⟨?_, ?_⟩
      · rintro rfl
        apply hj
        simp only [hd, hb0, map_one, one_mul, mul_one, sub_self]
      · rw [← hsupp]
        intro hbj
        apply hj
        simp only [hd, hbj, map_zero, zero_mul, mul_zero, sub_self]
    have hlt : (Finset.univ.filter (fun j => d j ≠ 0)).card < m := by
      rw [← hcard]
      refine lt_of_le_of_lt (Finset.card_le_card hdsub) (Finset.card_erase_lt_of_mem ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj0
    have hd0 := ih _ hlt d rfl hdrel
    intro j
    exact sub_eq_zero.1 (congrFun hd0 j)

  have hin : ∀ j, ∃ x : Om l, x ∈ K.1 ∧ (x : ℂ_[l]) = b j ∧ (w j ≠ w j0 → x = 0) := by
    intro j
    have hfix : ∀ g ∈ GK K, GlobalTheory.Cyc.chiC P.χQ (w j - w j0) g * GlobalTheory.Cyc.Model.actC g (b j) = b j := by
      intro g hg
      rw [actC_apply_eq_σC]
      have h := htw ⟨g, hg⟩ j
      change Formalism.Per.σC g (b j) * e g (w j) = e g (w j0) * b j at h
      change e g (w j - w j0) * Formalism.Per.σC g (b j) = b j
      apply mul_left_cancel₀ (e_ne g (w j0))
      rw [← h, ← e_sub g (w j) (w j0)]
      ring
    have hT := GlobalTheory.Cyc.tate_invariants_twist l GlobalTheory.Cyc.Model.actC P.χQ GlobalTheory.Cyc.Model.isActC_actC hcyc K
      (w j - w j0) (b j) hfix
    by_cases hw : w j = w j0
    · obtain ⟨x, hxK, hx⟩ := hT.2 (sub_eq_zero.2 hw)
      exact ⟨x, hxK, hx, fun h => absurd hw h⟩
    · have hbj : b j = 0 := hT.1 (sub_ne_zero.2 hw)
      exact ⟨0, K.1.zero_mem, by rw [hbj]; exact UniformSpace.Completion.coe_zero, fun _ => rfl⟩
  choose c hcK hcb hc0 using hin
  have hc : c = 0 := hK (w j0) c hcK hc0 (by simp only [hcb]; exact hbrel)
  have : b j0 = 0 := by rw [← hcb j0, hc, Pi.zero_apply]; exact UniformSpace.Completion.coe_zero
  rw [hb0] at this
  exact one_ne_zero this

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLatStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_of_qB_mem_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M n : ℕ), 1 ≤ M → ∀ z : ℚ_[l], qB P z ∈ Lat AI M n → ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  first | exact @GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat | exact GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat | (intros; apply GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat <;> assumption)
end

