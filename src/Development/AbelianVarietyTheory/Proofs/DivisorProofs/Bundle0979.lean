module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormDegreeLeFieldDegreeAlgebraicPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEigenvalueDropsOffBlock
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR
variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

theorem casDrop_term (F : ι → ι → Module.End ℂ M) (hF : IsGl F) (a b j k : ι) :
    F a b * F b a * F j k = F j k * (F a b * F b a) + (F a b * (if a = j then F b k else 0) - F a b * (if k = b then F j a else 0))
      + ((if b = j then F a k else 0) * F b a - (if k = a then F j b else 0) * F b a) := by
  have h1 := hF b a j k
  have h2 := hF a b j k
  have e1 : F b a * F j k = F j k * F b a + ((if a = j then F b k else 0) - (if k = b then F j a else 0)) := by
    rw [← h1]; abel
  have e2 : F a b * F j k = F j k * F a b + ((if b = j then F a k else 0) - (if k = a then F j b else 0)) := by
    rw [← h2]; abel
  calc F a b * F b a * F j k = F a b * (F b a * F j k) := mul_assoc _ _ _
    _ = F a b * F j k * F b a + F a b * ((if a = j then F b k else 0) - (if k = b then F j a else 0)) := by
        rw [e1, mul_add, mul_assoc]
    _ = _ := by rw [e2]; simp only [add_mul, sub_mul, mul_sub, mul_assoc]; abel

theorem cas_mul_off (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (hF : IsGl F) (j k : ι) (hj : s j = false)
    (hk : s k = true) :
    cas s F * F j k = F j k * cas s F + (2 : ℂ) • (∑ b, if s b = false then F j b * F b k else 0)
      - (2 : ℂ) • (∑ b, if s b = true then F j b * F b k else 0)
      + (((Finset.univ.filter fun a => s a = true).card : ℂ) - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • F j k := by
  have hjk : j ≠ k := by intro h; rw [h, hk] at hj; exact Bool.noConfusion hj
  have sw : ∀ a, F a k * F j a = F j a * F a k - F j k := by
    intro a
    have h := hF a k j a
    rw [if_neg (Ne.symm hjk), if_pos rfl] at h
    calc F a k * F j a = (F a k * F j a - F j a * F a k) + F j a * F a k := by abel
      _ = _ := by rw [h]; abel
  have cnt : ∀ c : Bool, (∑ a, if s a = c then F a k * F j a else 0)
      = (∑ a, if s a = c then F j a * F a k else 0) - ((Finset.univ.filter fun a => s a = c).card : ℂ) • F j k := by
    intro c
    have : (∑ a, if s a = c then F a k * F j a else 0)
        = ∑ a, ((if s a = c then F j a * F a k else 0) - (if s a = c then F j k else 0)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : s a = c
      · simp only [if_pos h, sw]
      · simp [h]
    rw [this, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have S1 : ∑ a, ∑ b, (if s a = s b then F a b * (if a = j then F b k else 0) else 0)
      = ∑ b, if s b = false then F j b * F b k else 0 := by
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hj]; by_cases h : s b <;> simp [h]
    · intro a _ ha; simp [ha]
    · simp
  have S2 : ∑ a, ∑ b, (if s a = s b then F a b * (if k = b then F j a else 0) else 0)
      = ∑ a, if s a = true then F a k * F j a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single k]
    · rw [hk]; simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have S3 : ∑ a, ∑ b, (if s a = s b then (if b = j then F a k else 0) * F b a else 0)
      = ∑ a, if s a = false then F a k * F j a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single j]
    · rw [hj]; simp
    · intro b _ hb; simp [hb]
    · simp
  have S4 : ∑ a, ∑ b, (if s a = s b then (if k = a then F j b else 0) * F b a else 0)
      = ∑ b, if s b = true then F j b * F b k else 0 := by
    rw [Finset.sum_eq_single k]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hk]; by_cases h : s b <;> simp [h]
    · intro a _ ha; simp [Ne.symm ha]
    · simp
  have expand : ∀ a b, (if s a = s b then F a b * F b a else 0) * F j k
      = (if s a = s b then F j k * (F a b * F b a) else 0)
        + ((if s a = s b then F a b * (if a = j then F b k else 0) else 0)
          - (if s a = s b then F a b * (if k = b then F j a else 0) else 0))
        + ((if s a = s b then (if b = j then F a k else 0) * F b a else 0)
          - (if s a = s b then (if k = a then F j b else 0) * F b a else 0)) := by
    intro a b
    by_cases h : s a = s b
    · simp only [if_pos h]; exact casDrop_term F hF a b j k
    · simp [h]
  unfold cas
  simp only [Finset.sum_mul, expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4, cnt, cnt]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  simp only [two_smul, sub_smul]
  abel

end GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_drop : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ (α β x ω : ℂ) (y : ι → M), IsGl F → (∀ a b, qop F α β a b = 0) →
    (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ a, cas s F (y a) = ω • y a) →
    ∀ j, s j = false → cas s F (∑ b, F j b (y b)) = (ω - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ)
      - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • ∑ b, F j b (y b) := by
  intro ι M _ _ _ _ s F α β x ω y hF hq hy0 hyA hω j hj
  set r : ℂ := ((Finset.univ.filter fun a => s a = true).card : ℂ)
  set r' : ℂ := ((Finset.univ.filter fun a => s a = false).card : ℂ)
  set T : ι → Module.End ℂ M := fun b => ∑ c, if s c = true then F j c * F c b else 0 with hT

  have quad : ∀ b, s b = true → (∑ c, if s c = false then F j c * F c b else 0) = α • F j b - T b := by
    intro b hb
    have hjb : j ≠ b := by intro h; rw [h, hb] at hj; exact Bool.noConfusion hj
    have h := hq j b
    simp only [qop, if_neg hjb, sub_zero] at h
    have split : (∑ c, F j c * F c b) = (∑ c, if s c = false then F j c * F c b else 0) + T b := by
      rw [hT, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      cases s c <;> simp
    rw [split] at h
    calc (∑ c, if s c = false then F j c * F c b else 0) = ((∑ c, if s c = false then F j c * F c b else 0) + T b - α • F j b)
          + α • F j b - T b := by abel
      _ = α • F j b - T b := by rw [h]; abel

  have term : ∀ b, cas s F (F j b (y b)) = (ω + 2 * α + r - r') • F j b (y b) - (4 : ℂ) • T b (y b) := by
    intro b
    cases hb : s b
    · simp [hT, hy0 b hb]
    · have h := cas_mul_off s F hF j b hj hb
      rw [quad b hb] at h
      have h' := congrArg (fun L : Module.End ℂ M => L (y b)) h
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h'
      rw [h', hω b, map_smul]
      module
  have sumT : (∑ b, T b (y b)) = x • ∑ b, F j b (y b) := by
    have : ∀ b, T b (y b) = ∑ c, if s c = true then F j c (F c b (y b)) else 0 := by
      intro b
      simp only [hT, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> rfl
    simp only [this]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    cases hc : s c
    · simp [hy0 c hc]
    · simp only [if_true]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hyA c hc, map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [term]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum, sumT, smul_smul, ← sub_smul]
  congr 1
  ring

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirCommuteSameBlockUnit
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_mul_comm_of_block : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), IsGl F → ∀ a b, s a = s b → cas s F * F a b = F a b * cas s F := by
  intro ι M _ _ _ _ s F hF a b hab
  rw [← sub_eq_zero]
  have key : ∀ c d, F c d * F d c * F a b - F a b * (F c d * F d c) =
      ((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0)) := by
    intro c d
    have e : F c d * F d c * F a b - F a b * (F c d * F d c) =
        F c d * (F d c * F a b - F a b * F d c) + (F c d * F a b - F a b * F c d) * F d c := by noncomm_ring
    rw [e, hF d c a b, hF c d a b]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  have h0 : cas s F * F a b - F a b * cas s F = ∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0 := by
    simp only [cas, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : s c = s d
    · simp only [h, if_true]; exact key c d
    · simp only [h, if_false, zero_mul, mul_zero, sub_self]
  have h1 : (∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp
  have h4 : (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  have h2 : (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro d _ hd; simp [Ne.symm hd]
    · simp
  have h3 : (∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro d _ hd; simp [hd]
    · simp
  rw [h0]
  have split : (∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0) =
      ((∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0)) +
      ((∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [split, h1, h2, h3, h4]
  abel

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirEigenNonnegRealUnitary
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_diag_unitOn (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (hU : UnitOn s F U) :
    (∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re) ∧
      (U ≠ ⊥ → ∃ (ω : ℝ) (v : M), v ∈ U ∧ v ≠ 0 ∧ cas s F v = (ω : ℂ) • v) := by
  obtain ⟨hfin, hst, ip, hherm, hpos, hadj⟩ := hU
  have hw : ∀ w ∈ U, (ip w w).im = 0 ∧ 0 ≤ (ip w w).re := by
    intro w hw
    constructor
    · have h := congrArg Complex.im (hherm w hw w hw)
      simp at h
      linarith
    · by_cases h0 : w = 0
      · simp [h0]
      · exact le_of_lt (hpos w hw h0)
  have key : ∀ v ∈ U, ip v (cas s F v) = ∑ a, ∑ b, if s a = s b then ip (F b a v) (F b a v) else 0 := by
    intro v hv
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cas, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [Module.End.mul_apply]
      exact (hadj b a h.symm v hv (F b a v) (hst b a h.symm v hv)).symm
    · simp
  have hS : ∀ v ∈ U, (ip v (cas s F v)).im = 0 ∧ 0 ≤ (ip v (cas s F v)).re := by
    intro v hv
    rw [key v hv, Complex.im_sum, Complex.re_sum]
    constructor
    · refine Finset.sum_eq_zero fun a _ => ?_
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h
      · exact (hw _ (hst b a h.symm v hv)).1
      · simp
    · refine Finset.sum_nonneg fun a _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_nonneg fun b _ => ?_
      split_ifs with h
      · exact (hw _ (hst b a h.symm v hv)).2
      · simp
  have first : ∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re := by
    intro c v hv h0 hc
    have e := hS v hv
    rw [hc, map_smul, smul_eq_mul, Complex.mul_im, Complex.mul_re] at e
    have r0 := (hw v hv).1
    have rp := hpos v hv h0
    rw [r0] at e
    simp only [mul_zero, zero_add, sub_zero] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp e1 with h | h
      · exact h
      · exact absurd h (ne_of_gt rp)
    · by_contra hneg
      push_neg at hneg
      nlinarith
  refine ⟨first, fun hne => ?_⟩
  have hcU : ∀ x ∈ U, cas s F x ∈ U := by
    intro x hx
    simp only [cas, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    split_ifs with h
    · rw [Module.End.mul_apply]
      exact hst a b h _ (hst b a h.symm x hx)
    · simp
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
  haveI : FiniteDimensional ℂ U := hfin
  let g : Module.End ℂ U := (cas s F).restrict hcU
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue g
  obtain ⟨w, hw'⟩ := hc.exists_hasEigenvector
  have hgw : g w = c • w := Module.End.mem_eigenspace_iff.mp hw'.1
  have hw0 : (w : M) ≠ 0 := fun h => hw'.2 (Subtype.ext h)
  have hcw : cas s F (w : M) = c • (w : M) := by
    have := congrArg Subtype.val hgw
    simpa [g] using this
  have hc' := first c w w.2 hw0 hcw
  refine ⟨c.re, w, w.2, hw0, ?_⟩
  rw [hcw]
  congr 1
  apply Complex.ext <;> simp [hc'.1]

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderEmbeddingOpenImmersion
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PadicPolys

theorem minpoly_coeff_bdd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1),
      f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ),
        ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  intro p _ G K' f' hf β
  obtain ⟨k0, hk0⟩ := GlobalTheory.AtPBd.main p G 1 K' f' one_pos hf
  set R : ℝ := (p : ℝ) ^ k0 with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  refine ⟨max (R * R) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y h hy φ k
  have hnrm : IsNrm G 1 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h := by
    show nrmG (sigG G 1) 1 _ = _
    simp [nrmG]
    rfl
  obtain ⟨hs, -, hrt, hrti⟩ := hk0 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h 1 hnrm (by simpa using hy)
  set yC : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyC
  have hint : IsIntegral G.F yC := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly G.F yC).Monic := minpoly.monic hint
  have hsn : ‖(((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)‖ ≤ R := by
    rw [← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
    exact hs
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hroot : ∀ μ ∈ ((minpoly G.F yC).map φ).roots, ‖μ‖ ≤ R * R := by
    intro μ hμ
    have hμ' : ((minpoly G.F yC).map φ).IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
    rcases GlobalTheory.GlobEig.liesOver_or_conj G φ with hφ | hφ
    · obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G φ hφ yC μ hμ'
      rw [← hν]
      exact (hrt i ν hνr).trans (le_mul_of_one_le_left (by linarith) hR1)
    · have h2 := GlobalTheory.GlobEig.isRoot_minpoly_sh G yC φ μ hμ'
      obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G _ hφ (sh G yC) μ h2
      have h3 := GlobalTheory.GlobEig.isRoot_inv G i β (y : G.Cˣ × ℚˣ).1 (y : G.Cˣ × ℚˣ).2 y.2.1 ν hνr
      have h4 := hrti i _ h3
      rw [← hν]
      have e : ν = ν * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)⁻¹ * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) := by
        field_simp
      rw [e, norm_mul]
      exact mul_le_mul h4 hsn (norm_nonneg _) (by linarith)
  have hdeg : (minpoly G.F yC).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le yC
  rw [← Polynomial.coeff_map]
  exact Polynomial.coeff_bdd_of_roots_le φ hmon (IsAlgClosed.splits _) hdeg hroot k

end GlobalTheory.LKCx.PadicPolys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainLengthLeFinrankAddOne
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem chain_length_le_finrank_add_one : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (G U C : Submodule ℂ V), FiniteDimensional ℂ U → G ≤ U ⊔ C → ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ k, C ≤ N k) → (∀ k l, k < l → ∃ v ∈ N l, v ∈ G ∧ v ∉ N k) → m ≤ Module.finrank ℂ U + 1 := by
  intro V _ _ G U C hU hGUC m N hN hC hsep
  let g : Fin m → Submodule ℂ U := fun k => (N k).comap U.subtype
  have hg : StrictMono g := by
    intro k l hkl
    refine lt_of_le_of_ne (fun x hx => hN.monotone hkl.le hx) ?_
    intro heq
    obtain ⟨v, hvl, hvG, hvk⟩ := hsep k l hkl
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp (hGUC hvG)
    have hcl : c ∈ N l := hC l hc
    have hul : u ∈ N l := by simpa using (N l).sub_mem hvl hcl
    have hmem : (⟨u, hu⟩ : U) ∈ g l := hul
    rw [← heq] at hmem
    exact hvk ((N k).add_mem hmem (hC k hc))
  let f : Fin m → Fin (Module.finrank ℂ U + 1) := fun k =>
    ⟨Module.finrank ℂ (g k), Nat.lt_succ_of_le (Submodule.finrank_le _)⟩
  have hf : Function.Injective f := by
    intro k l h
    have h' : Module.finrank ℂ (g k) = Module.finrank ℂ (g l) := congrArg Fin.val h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (hg hlt))) h'
    · exact (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (hg hlt))) h'.symm
  simpa using Fintype.card_le_of_injective f hf

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfMonicAevalPowersLinearIndependentStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_monic_aeval_powers_linearIndependent : ∀ (K : Type) [CommRing K] (n : ℕ) (X : Matrix (Fin n) (Fin n) K) (P : Polynomial K), P.Monic → P.natDegree = n → Polynomial.aeval X P = 0 → LinearIndependent K (fun i : Fin n => X ^ (i : ℕ)) → X.charpoly = P := by
  first | (exact @GlobalTheory.charpoly_eq_of_monic_aeval_linearIndependent) | (exact GlobalTheory.charpoly_eq_of_monic_aeval_linearIndependent) | (intros; apply GlobalTheory.charpoly_eq_of_monic_aeval_linearIndependent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormDegreeLeFieldDegreeAlgebraicPointStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chowForm_degree_le_field_degree_algebraic_point : ∀ (K : Type) [Field K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → IsChowFormInt (coneIdeal K y) 0 δ f → δ ≤ Module.finrank K (IntermediateField.adjoin K (Set.range y)) := by
  first | exact @GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt | exact GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt | (intros; apply GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CircleEqOneIffOfConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem circle_eq_one_iff_of_conj {K L : Type} [Field K] [Field L] [Algebra K L] (s t : L →+* ℂ) (a b : Circle) (y : K)
    (ha : (a : ℂ) = s (algebraMap K L y)) (hb : (b : ℂ) = t (algebraMap K L y)) : b = 1 ↔ a = 1 := by
  rw [← Circle.coe_eq_one, ← Circle.coe_eq_one, ha, hb, map_eq_one_iff t t.injective, map_eq_one_iff s s.injective]

theorem logHookSum_of_bijective {D : D7} (i : Fin D.R.m) (l : D.what₂.Tau → D.what₂.Tau) (hl : Function.Bijective l) :
    logHookSum i l = logHookSum i id := by
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) :=
    fun ρ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  unfold logHookSum
  simp only [pW, qW, hs, id]
  exact hl.sum_comp (fun ρ => Real.log ((hookRows (D.R.sigW ((i : ℕ) + 1)).1 (aPl D i (D.R.sigW ((i : ℕ) + 1)).1 ρ) *
    hookRows (D.R.sigW ((i : ℕ) + 1)).2 (aMi D i (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 ρ) : ℕ) : ℝ))

end GlobalTheory.GalLift
end

