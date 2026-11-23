module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OfDualFamilies
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0259
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHermSesqOf
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ConjNorm.Inter

open GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

def sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (by intro a b c; simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum, mul_div_assoc])
    (by intro a b c; simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c), ← Finset.mul_sum,
        mul_div_assoc])

theorem isHerm_sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : IsHerm (GlobalTheory.ConjNorm.Inter.sesqOf D T N N') := by
  intro x y
  change Hf D T y x = starRingEnd ℂ (Hf D T x y)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem lam_mul_mem (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem klat_gen {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    ∃ S : Set (Matrix (Fin N') (Fin N) D.host.E), Submodule.span D.host.K S = ⊤ ∧
      A = AddSubgroup.closure {z | ∃ w ∈ lamOf D cc δ, ∃ B ∈ S, z = w • embV D (tor0 D cc δ) B} := by
  rcases hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩
  · refine ⟨Set.range b, hb.2, ?_⟩
    unfold LaB
    congr 1
    ext z
    simp [tor0]
  · refine ⟨YYl D L L', ?_, rfl⟩
    obtain ⟨r, y, y', hy, -, h⟩ := GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
    rw [eq_top_iff]
    intro x _
    rw [h x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hy i))

theorem klat_smul_mem {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) (a : 𝓞 D.host.K)
    {x : VC D N N'} (hx : x ∈ A) : D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ A := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, lam_mul_mem a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem embV_smul (h : GL3Theta.InducedCMType D) (k : D.host.K) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (k • B) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) B := by
  funext τ i j
  change embT D τ ((k : D.host.E) * B i j) = D.host.φ₀ (k : D.host.E) * embT D τ (B i j)
  rw [map_mul, h τ k]

theorem embV_add (B B' : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (B + B') = embV D (tor0 D cc δ) B + embV D (tor0 D cc δ) B' := by
  funext τ i j
  exact map_add (embT D τ) _ _

theorem embV_zero : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  exact map_zero (embT D τ)

theorem klat_rat (h : GL3Theta.InducedCMType D) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A)
    {x : VC D N N'} (hx : x ∈ A) : ∃ B, x = δ • embV D (tor0 D cc δ) B := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  have hl : ∀ w ∈ lamOf D cc δ, ∃ k : D.host.K, w = δ * D.host.φ₀ (k : D.host.E) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw => obtain ⟨c, -, rfl⟩ := hw; exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨k, rfl⟩ := ha
      obtain ⟨k', rfl⟩ := hb
      exact ⟨k + k', by simp [mul_add]⟩
    | neg a _ ha =>
      obtain ⟨k, rfl⟩ := ha
      exact ⟨-k, by simp⟩
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, -, rfl⟩ := hw
    obtain ⟨k, rfl⟩ := hl w hw
    exact ⟨k • B, by rw [embV_smul h, smul_smul]⟩
  | zero => exact ⟨0, by rw [embV_zero, smul_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨B', rfl⟩ := hb
    exact ⟨B + B', by rw [embV_add, smul_add]⟩
  | neg a _ ha =>
    obtain ⟨B, rfl⟩ := ha
    exact ⟨(-1 : D.host.K) • B, by rw [embV_smul h]; simp⟩

theorem klat_mul_mem (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A : AddSubgroup (VC D N N')}
    (hA : KLat D (tor0 D cc δ) A) (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ m • (δ • embV D (tor0 D cc δ) B) ∈ A := by
  have hA' := hA
  obtain ⟨S, hS, hAS⟩ := klat_gen hA'
  have hB : B ∈ Submodule.span D.host.K S := hS ▸ Submodule.mem_top
  induction hB using Submodule.span_induction with
  | mem B hB =>
    refine ⟨Ideal.absNorm cc, Nat.pos_of_ne_zero (fun e => hcc (Ideal.absNorm_eq_zero_iff.1 e)), ?_⟩
    rw [hAS]
    refine AddSubgroup.subset_closure ⟨(Ideal.absNorm cc : ℂ) * δ,
      AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp [mul_comm]⟩, B, hB, ?_⟩
    rw [← smul_smul, Nat.cast_smul_eq_nsmul]
  | zero => exact ⟨1, one_pos, by simp [embV_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, ha⟩ := ha
    obtain ⟨n, hn, hb⟩ := hb
    refine ⟨m * n, by positivity, ?_⟩
    rw [embV_add, smul_add, smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.nsmul_mem ha _
    · rw [mul_smul]; exact A.nsmul_mem hb _
  | smul k B _ hB =>
    obtain ⟨m, hm, hB⟩ := hB
    obtain ⟨n, hn, hk⟩ := exists_integral_multiples ℤ ℚ ({k} : Finset D.host.K)
    have hk' : IsIntegral ℤ (n.natAbs • k) := by
      have := hk k (Finset.mem_singleton_self k)
      rcases Int.natAbs_eq n with e | e
      · rw [e] at this; simpa using this
      · rw [e] at this; simpa using this.neg
    refine ⟨m * n.natAbs, Nat.mul_pos hm (Int.natAbs_pos.2 hn), ?_⟩
    convert klat_smul_mem hA ⟨_, hk'⟩ hB using 1
    rw [embV_smul h]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    change _ = D.host.φ₀ ((n.natAbs • k : D.host.K) : D.host.E) * _
    simp
    ring

theorem klat_finite (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A₁ A₂ : AddSubgroup (VC D N N')}
    (h₁ : KLat D (tor0 D cc δ) A₁) (h₂ : KLat D (tor0 D cc δ) A₂) (hfg : A₂.FG) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) :=
  finite_quot hfg fun x hx => by
    obtain ⟨B, rfl⟩ := klat_rat h h₂ hx
    exact klat_mul_mem h hcc h₁ B

theorem klat_facts (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ IsSelfDual (GlobalTheory.ConjNorm.Inter.sesqOf D (tor0 D cc δ) N N') A ∧
      IsSemiChar (GlobalTheory.ConjNorm.Inter.sesqOf D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := GlobalTheory.ConjNorm.Line.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h3, h4, le_antisymm h2 h1, ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine isSemiChar_round (GlobalTheory.ConjNorm.Inter.isHerm_sesqOf D _ N N') (Real.sqrt D.host.d) h1 (fun x hx => ?_) h5
  have := klat_smul_mem hA a hx
  rwa [ha] at this

end GlobalTheory.ConjNorm.Inter


open GlobalTheory.ThetaInter GlobalTheory.ConjNorm.Inter in
theorem GlobalTheory.ConjNorm.unitary_all : ∀ D : D7, IntertwinerUnitary D := by
  intro D cc δ hc N N' A₁ A₂ h₁ h₂ th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := GlobalTheory.ConjNorm.Inter.klat_facts hc h₁
  obtain ⟨f₂, s₂, d₂, c₂⟩ := GlobalTheory.ConjNorm.Inter.klat_facts hc h₂
  have hH := GlobalTheory.ConjNorm.Inter.isHerm_sesqOf D (tor0 D cc δ) N N'
  have hψ := (GlobalTheory.InducedType.induced_type D).1.1
  have := _root_.GlobalTheory.ConjNorm.Inter.klat_finite hψ hc.1.1 h₁ h₂ f₂
  have := _root_.GlobalTheory.ConjNorm.Inter.klat_finite hψ hc.1.1 h₂ h₁ f₁
  have : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have t₂ := discrete_of_selfDual hH d₂ f₂
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (GlobalTheory.ConjNorm.Inter.sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A₁ := hth.2
  exact ⟨fun x => mean_opU MeasureTheory.volume hH t₁ s₁ c₁ hth.1.continuous hF x,
    ⟨differentiable_inter (H := GlobalTheory.ConjNorm.Inter.sesqOf D (tor0 D cc δ) N N') (α := al D (tor0 D cc δ)) A₁ A₂ hth.1,
      inter_mem_fixedBy hH c₁ d₂ c₂ hF⟩,
    mean_inter MeasureTheory.volume hH t₁ s₁ t₂ s₂ d₁ c₁ d₂ c₂ hth.1 hF,
    inter_inter hH d₁ d₂ c₁ hF⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotient
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.Fibres

def trFac (Λ : AddSubgroup ℂ) (z ω : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
    (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)))

variable {Λ : AddSubgroup ℂ}

theorem thetaTranslationOperator_apply (ω : ℂ) (G : ℂ → ℂ) (z : ℂ) : U1 Λ ω G z = G (z + ω) * trFac Λ z ω := rfl

theorem trFac_mul {β : ℂ} {n : ℕ} (hb : β * starRingEnd ℂ β = (n : ℂ)) (z ω : ℂ) :
    trFac Λ (β * z) (β * ω) = trFac Λ z ω ^ n := by
  simp only [trFac]
  rw [← Complex.exp_nat_mul, ← hb, map_mul]
  congr 1
  ring

theorem trFac_add_sub (v z ω : ℂ) :
    trFac Λ (v + z) ω * trFac Λ (z - v) ω = trFac Λ z ω ^ 2 := by
  simp only [trFac]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sg_sq (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    sgStar Λ (z + ω) ^ 2 * trFac Λ z ω ^ 2 = sgStar Λ z ^ 2 := by
  rw [← mul_pow, ← thetaTranslationOperator_apply, h.sg_law hω]
  split_ifs <;> ring

theorem sqTh_law (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (v z : ℂ) :
    sqTh Λ v (z + ω) * trFac Λ z ω ^ 2 = sqTh Λ v z := by
  have h1 := h.sg_law hω (v + z)
  have h2 := h.sg_law hω (z - v)
  rw [thetaTranslationOperator_apply] at h1 h2
  have e1 : sgStar Λ (v - (z + ω)) = -sgStar Λ (z - v + ω) := by
    rw [← h.sg_neg]; congr 1; ring
  have e2 : sgStar Λ (v - z) = -sgStar Λ (z - v) := by
    rw [← h.sg_neg]; congr 1; ring
  have e3 : sgStar Λ (v + z + ω) * sgStar Λ (z - v + ω) * trFac Λ z ω ^ 2 =
      sgStar Λ (v + z) * sgStar Λ (z - v) := by
    rw [← trFac_add_sub v, mul_mul_mul_comm, h1, h2]
    split_ifs <;> ring
  simp only [sqTh]
  rw [e1, e2, ← add_assoc]
  linear_combination (-1 / sgStar Λ v ^ 2) * e3

theorem law_of_fac (h : IsLat Λ) {F : ℂ → ℂ} {k : ℕ} {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ)
    (hF : F (z + ω) * trFac Λ z ω ^ (2 * k) = F z) :
    F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k) := by
  rw [← hF, pow_mul (sgStar Λ z), ← sg_sq h hω z]
  ring

theorem isogeny_fibres : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  intro Λ h β t₀ k hβ htr hN h2 h1 h1'
  have hβ' : ∀ ω ∈ Λ, (1 - β) * ω ∈ Λ := fun ω hω => by
    rw [sub_mul, one_mul]; exact Λ.sub_mem hω (hβ ω hω)
  have hN' : β * (1 - β) = 2 * (k : ℂ) := by
    rw [← htr, add_sub_cancel_left, hN]; push_cast; ring
  have ht₀ : t₀ ∉ Λ := fun hh => h1 (hβ _ hh)
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exfalso
      simp only [Nat.cast_zero, mul_zero, mul_eq_zero] at hN'
      rcases hN' with h0 | h0
      · exact h1 (by rw [h0, zero_mul]; exact Λ.zero_mem)
      · exact h1' (by rw [h0, zero_mul]; exact Λ.zero_mem)
    · exact hk
  have hnat : ∀ (n : ℕ) (x : ℂ), x ∈ Λ → (n : ℂ) * x ∈ Λ := fun n x hx => by
    rw [← nsmul_eq_mul]; exact Λ.nsmul_mem hx n
  have h2t₁ : 2 * (β * t₀) ∈ Λ := by
    convert hβ _ h2 using 1; ring
  have hplus : t₀ + β * t₀ ∉ Λ := fun hh => h1' (by
    convert Λ.sub_mem hh h2t₁ using 1; ring)
  have hminus : t₀ - β * t₀ ∉ Λ := fun hh => h1' (by
    convert hh using 1; ring)
  have hla : ∀ x : ℂ, 2 * (β * x) ∈ Λ → InRationalLattice Λ x := fun x hx =>
    ⟨4 * k, by omega, by
      convert hβ' _ hx using 1
      push_cast
      linear_combination (-2 * x) * hN'⟩
  obtain ⟨hd, h0, hev, -, hz, hU⟩ := GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity Λ h t₀ ht₀ h2
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.evenTheta_eq_prod_sigmaStarSquareQuotient Λ h k (fun z => GL3Theta.th0 Λ t₀ (β * z))
    (hd.comp (by fun_prop)) (fun z => by rw [mul_neg, hev]) (by rw [mul_zero, h0])
    (fun ω hω z => law_of_fac h (F := fun z => GL3Theta.th0 Λ t₀ (β * z)) hω z (by
      have hn : β * ω / 2 + t₀ ∉ Λ := fun hh => h1' (by
        convert Λ.sub_mem (hβ' _ hh) (hnat k ω hω) using 1
        linear_combination (-ω / 2) * hN')
      have := hU _ (hβ ω hω) hn (β * z)
      rw [thetaTranslationOperator_apply, trFac_mul hN] at this
      simpa only [mul_add] using this))
  obtain ⟨Q', hQ', hQe'⟩ := GlobalTheory.T.evenTheta_eq_prod_sigmaStarSquareQuotient Λ h (2 * k) (fun z => sqTh Λ (β * t₀) (β * z))
    ((h.differentiable_sqTh _).comp (by fun_prop)) (fun z => by rw [mul_neg, sqTh_neg])
    (by rw [mul_zero, h.sqTh_zero h1])
    (fun ω hω z => law_of_fac h (F := fun z => sqTh Λ (β * t₀) (β * z)) hω z (by
      have := sqTh_law h (hβ ω hω) (β * t₀) (β * z)
      rw [trFac_mul hN, ← pow_mul, mul_comm (2 * k) 2] at this
      simpa only [mul_add] using this))
  have hA : ∀ i, β * Q i + t₀ ∈ Λ := fun i => by
    rw [← hz, hQe]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      ((h.sqTh_eq_zero (hQ i) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem)))
  have hB : ∀ j, β * t₀ + β * Q' j ∈ Λ ∨ β * t₀ - β * Q' j ∈ Λ := fun j => by
    rw [← h.sqTh_eq_zero h1, hQe']
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      ((h.sqTh_eq_zero (hQ' j) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem)))
  have hC : ∀ x : ℂ, x ∉ Λ → β * t₀ - β * x ∈ Λ → ∃ j, wpF Λ (Q' j) = wpF Λ x := fun x hx hx' => by
    have h3 := (h.sqTh_eq_zero h1 (β * x)).2 (Or.inr hx')
    rw [hQe', Finset.prod_eq_zero_iff] at h3
    obtain ⟨j, -, hj⟩ := h3
    exact ⟨j, ((h.wp_eq_iff (hQ' j) hx).2 ((h.sqTh_eq_zero (hQ' j) x).1 hj)).symm⟩
  refine ⟨Q, Q', fun i => ⟨hQ i, hla _ ?_⟩, fun j => ⟨hQ' j, hla _ ?_⟩, hQe, hQe', ?_,
    hC _ ht₀ (by rw [sub_self]; exact Λ.zero_mem), hC _ h1 ?_, ?_⟩
  · convert Λ.sub_mem (hnat 2 _ (hA i)) h2 using 1
    push_cast; ring
  · rcases hB j with hj | hj
    · convert Λ.sub_mem (hnat 2 _ hj) h2t₁ using 1
      push_cast; ring
    · convert Λ.sub_mem h2t₁ (hnat 2 _ hj) using 1
      push_cast; ring
  · intro i j hij
    have ha := hA i
    rcases (h.wp_eq_iff (hQ i) (hQ' j)).1 hij.symm with hc | hc <;> rcases hB j with hj | hj
    · exact hplus (by convert Λ.sub_mem (Λ.add_mem ha hj) (hβ _ hc) using 1; ring)
    · exact hminus (by convert Λ.sub_mem (Λ.sub_mem ha hj) (hβ _ hc) using 1; ring)
    · exact hminus (by convert Λ.sub_mem (Λ.sub_mem ha hj) (hβ _ hc) using 1; ring)
    · exact hplus (by convert Λ.sub_mem (Λ.add_mem ha hj) (hβ _ hc) using 1; ring)
  · convert hnat k _ h2 using 1
    linear_combination t₀ * hN'
  · intro he
    rcases (h.wp_eq_iff ht₀ h1).1 he.symm with hc | hc
    · exact hplus hc
    · exact hminus hc

end GlobalTheory.EvenTheta.Fibres
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalisedThetaPullbackMemTorsionTranslatesSpanA
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem U_pullB_eq_prod (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (g : ℂ → ℂ) (t z : VC D N N') :
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b g) z =
      ∏ j, U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) g (coordB D (tor0 D cc δ) b j z) := by
  obtain ⟨-, -, hP, -, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by rw [coordB_add]
  · congr 1
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [tor0]
    ring

theorem normalisedThetaPullback_mem_torsionTranslatesSpan (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (N N' r : ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) :
    pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ Tr D (tor0 D cc δ) b := by
  have hG : admG1 D := (GlobalTheory.InducedType.induced_type D).1
  have hgood := isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ
  obtain ⟨-, -, -, hL, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  set t : VC D N N' := ∑ j, (fun _ : Fin r => t0) j • embV D (tor0 D cc δ) (b j) with htdef
  have hco : ∀ j, coordB D (tor0 D cc δ) b j t = t0 := fun j => hgood.coordB_sum hb.1 _ j
  have h2 : (2 : ℕ) • t ∈ LaB D (tor0 D cc δ) b := by
    rw [hL]
    intro k
    rw [two_nsmul, coordB_add, hco, ← two_mul]
    exact ht.1
  have hq : U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0 ∈ Qbar := by
    have := (_root_.GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hc).1 t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ 0
    simpa [coef1] using this
  have hmem : U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∈
      Tr D (tor0 D cc δ) b := Submodule.subset_span ⟨t, ⟨2, two_pos, h2⟩, rfl⟩
  have := Submodule.smul_mem _
    (⟨(U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0)⁻¹ ^ r, pow_mem (inv_mem hq) r⟩ : Qbar) hmem
  convert this using 1
  funext z
  change _ = (U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0)⁻¹ ^ r *
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z
  rw [U_pullB_eq_prod D hG cc δ b hb]
  simp only [hco, pullB, GL3Theta.th0, div_eq_inv_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end GlobalTheory.ThetaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PosDefOneSubOfSumSqLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.HolDS

theorem exists_congr_one_of_posDef {n : Type} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ} (h : S.PosDef) :
    ∃ d : Matrix n n ℂ, IsUnit d.det ∧ dᴴ * S * d = 1 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 h.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  have hd : B.det ≠ 0 := by
    have h2 := h.det_pos.ne'
    rw [hB, Matrix.det_mul] at h2
    exact right_ne_zero_of_mul h2
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det _ hd.isUnit, ?_⟩
  rw [hB, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd.isUnit]
  simp

end GlobalTheory.HolDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlopeEHolds
section
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem slopeK_holds : SlopeK := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hs G hG C _ M hM N e X
  exact ⟨_root_.GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK K v₀ hv ι n lam R hR hs G hG C M hM N e X,
    _root_.GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK K v₀ hv ι n lam R hR hs G hG C M hM N e X⟩

theorem slopeE_holds : SlopeE := by
  intro E K _ _ _ _ _ _ v₀ hv cE hcE ι _ emb hemb n lam R hR hs J hJ C _ L hL N e X
  have h := _root_.GlobalTheory.TestLat.defGram_selfDual_of_embedding E K cE hcE ι emb hemb n J hJ
  have h1 := slopeK_holds K v₀ hv ι n lam R hR hs (gramK emb J) (fun τ => (h τ).1) C
    (fun c τ => tauLat emb τ (L c)) (fun c τ => ((h τ).2.2 (L c) (hL c)).1) N e X
  have h2 := slopeK_holds K v₀ hv ι n lam R hR hs (gramKd emb J) (fun τ => (h τ).2.1) C
    (fun c τ => dualFr (tauLat emb τ (L c))) (fun c τ => ((h τ).2.2 (L c) (hL c)).2) N e X
  exact ⟨h1.2, fun hm => (h1.1 hm).1, h2.2, fun hm => (h2.1 hm).1⟩

theorem slope_holds : GlobalTheory.TestLat.SlopeK ∧ GlobalTheory.TestLat.SlopeE := ⟨slopeK_holds, slopeE_holds⟩

end GlobalTheory.TestLat
end

