module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelDyWeights
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy

section Steps

variable {Ψ : Type} {p q : ℕ}

theorem blkF_ne_inl (K₀ : Type) (r : Ψ × Fin (p + q)) (k : K₀) : blkF Ψ p q K₀ r ≠ some (.inl k) := by
  delta blkF
  split_ifs <;> simp

theorem blkF_eq_inr (K₀ : Type) (r : Ψ × Fin (p + q)) (t : StepIx Ψ p q) :
    blkF Ψ p q K₀ r = some (.inr t) ↔ IsProperStep (p + q) p r.2 ∧ stepOf Ψ p q r = t := by
  delta blkF
  split_ifs with hp <;> simp [hp]

theorem stepOf_eq_left (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inl τ'))) :
    stepOf Ψ p q (τ, i) = ⟨.inl τ', a⟩ ↔ τ = τ' ∧ (i : ℕ) = a := by
  delta stepOf
  dsimp only
  split_ifs with hi
  · constructor
    · intro e
      rcases Sigma.mk.inj_iff.mp e with ⟨h1, h2⟩
      cases h1
      exact ⟨rfl, congrArg Fin.val (eq_of_heq h2)⟩
    · rintro ⟨rfl, h2⟩
      exact Sigma.ext rfl (heq_of_eq (Fin.ext h2))
  · constructor
    · intro e
      exact absurd (Sigma.mk.inj_iff.mp e).1 Sum.inr_ne_inl
    · rintro ⟨-, h2⟩
      have ha : (a : ℕ) < p := a.2
      exfalso
      omega

theorem stepOf_eq_right (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inr τ'))) :
    stepOf Ψ p q (τ, i) = ⟨.inr τ', a⟩ ↔ τ = τ' ∧ (i : ℕ) = p + a := by
  delta stepOf
  dsimp only
  split_ifs with hi
  · constructor
    · intro e
      exact absurd (Sigma.mk.inj_iff.mp e).1 Sum.inl_ne_inr
    · rintro ⟨-, h2⟩
      exfalso
      omega
  · constructor
    · intro e
      rcases Sigma.mk.inj_iff.mp e with ⟨h1, h2⟩
      cases h1
      have h3 : (i : ℕ) - p = a := congrArg Fin.val (eq_of_heq h2)
      exact ⟨rfl, by omega⟩
    · rintro ⟨rfl, h2⟩
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (show (i : ℕ) - p = a by omega)))

end Steps

section Main

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {n : Ψ ⊕ Ψ → ℕ}
  {A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {x₀ : (Σ k, J₀ k) → Ω} {m : Ψ ⊕ Ψ → ℕ}


open Classical in
theorem dy_apply (h : ModelOK A x₀ m) (r : Ψ × Fin (p + q)) (k : K₀ ⊕ StepIx Ψ p q) :
    (model A x₀ m h).dy r k =
      if ∀ r', blkF Ψ p q K₀ r' ≠ some k then -twist m r k else if blkF Ψ p q K₀ r = some k then 1 else 0 := by
  delta FlagModel.dy
  by_cases hc : ∀ p', (model A x₀ m h).blk p' ≠ some k
  · rw [dite_eq_left hc, if_pos (show ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' ≠ some k from hc)]
    rfl
  · rw [dite_eq_right hc, if_neg (show ¬ ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' ≠ some k from hc)]
    by_cases hb : (model A x₀ m h).blk r = some k
    · rw [if_pos hb, if_pos (show blkF Ψ p q K₀ r = some k from hb)]
    · rw [if_neg hb, if_neg (show ¬ blkF Ψ p q K₀ r = some k from hb)]


open Classical in
theorem twist_left (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inl τ'))) (ha : (a : ℕ) + 1 = p) :
    twist (K₀ := K₀) m (τ, i) (.inr ⟨.inl τ', a⟩) = -(if τ' = τ ∧ p ≤ (i : ℕ) + 1 then 1 else 0) := by
  delta twist
  dsimp only
  rw [if_neg (show ¬ ((Sum.inl τ' : Ψ ⊕ Ψ) = Sum.inr τ ∧ (a : ℕ) + 1 = q ∧ (i : ℕ) + 1 = p + q) from fun hh => Sum.inl_ne_inr hh.1), add_zero]
  by_cases hc : τ' = τ ∧ p ≤ (i : ℕ) + 1
  · rw [if_pos (show (Sum.inl τ' : Ψ ⊕ Ψ) = Sum.inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ) + 1 from ⟨congrArg Sum.inl hc.1, ha, hc.2⟩), if_pos hc]
  · rw [if_neg (show ¬ ((Sum.inl τ' : Ψ ⊕ Ψ) = Sum.inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ) + 1) from fun hh => hc ⟨Sum.inl_injective hh.1, hh.2.2⟩), if_neg hc]


open Classical in
theorem twist_right (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inr τ'))) (ha : (a : ℕ) + 1 = q) :
    twist (K₀ := K₀) m (τ, i) (.inr ⟨.inr τ', a⟩) = -(if τ' = τ ∧ (i : ℕ) + 1 = p + q then 1 else 0) := by
  delta twist
  dsimp only
  rw [if_neg (show ¬ ((Sum.inr τ' : Ψ ⊕ Ψ) = Sum.inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ) + 1) from fun hh => Sum.inr_ne_inl hh.1), zero_add]
  by_cases hc : τ' = τ ∧ (i : ℕ) + 1 = p + q
  · rw [if_pos (show (Sum.inr τ' : Ψ ⊕ Ψ) = Sum.inr τ ∧ (a : ℕ) + 1 = q ∧ (i : ℕ) + 1 = p + q from ⟨congrArg Sum.inr hc.1, ha, hc.2⟩), if_pos hc]
  · rw [if_neg (show ¬ ((Sum.inr τ' : Ψ ⊕ Ψ) = Sum.inr τ ∧ (a : ℕ) + 1 = q ∧ (i : ℕ) + 1 = p + q) from fun hh => hc ⟨Sum.inr_injective hh.1, hh.2.2⟩), if_neg hc]


open Classical in
theorem dy_left (h : ModelOK A x₀ m) (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inl τ'))) :
    (model A x₀ m h).dy (τ, i) (.inr ⟨.inl τ', a⟩) =
      if τ = τ' ∧ ((i : ℕ) = a ∨ ((a : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) then 1 else 0 := by
  have ha : (a : ℕ) < p := a.2
  have key : ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' = some (.inr ⟨.inl τ', a⟩) ↔
      r'.1 = τ' ∧ (r'.2 : ℕ) = a ∧ (a : ℕ) + 1 ≠ p := by
    rintro ⟨σ', j⟩
    rw [blkF_eq_inr, stepOf_eq_left]
    dsimp only
    delta IsProperStep
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, h4, by omega⟩
    · rintro ⟨h3, h4, h5⟩
      exact ⟨⟨by omega, by omega⟩, h3, h4⟩
  by_cases hp : (a : ℕ) + 1 = p
  · rw [dy_apply h, if_pos (fun r' e => ((key r').1 e).2.2 hp), twist_left τ τ' i a hp, neg_neg]
    rcases eq_or_ne τ' τ with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne, hne.symm]
  · rw [dy_apply h, if_neg (fun H => H (τ', ⟨(a : ℕ), by omega⟩) ((key _).2 ⟨rfl, rfl, hp⟩))]
    simp only [key]
    rcases eq_or_ne τ τ' with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne]


open Classical in
theorem dy_right (h : ModelOK A x₀ m) (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inr τ'))) :
    (model A x₀ m h).dy (τ, i) (.inr ⟨.inr τ', a⟩) = if τ = τ' ∧ (i : ℕ) = p + a then 1 else 0 := by
  have ha : (a : ℕ) < q := a.2
  have key : ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' = some (.inr ⟨.inr τ', a⟩) ↔
      r'.1 = τ' ∧ (r'.2 : ℕ) = p + a ∧ (a : ℕ) + 1 ≠ q := by
    rintro ⟨σ', j⟩
    rw [blkF_eq_inr, stepOf_eq_right]
    dsimp only
    delta IsProperStep
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, h4, by omega⟩
    · rintro ⟨h3, h4, h5⟩
      exact ⟨⟨by omega, by omega⟩, h3, h4⟩
  by_cases hq : (a : ℕ) + 1 = q
  · rw [dy_apply h, if_pos (fun r' e => ((key r').1 e).2.2 hq), twist_right τ τ' i a hq, neg_neg]
    rcases eq_or_ne τ' τ with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne, hne.symm]
  · rw [dy_apply h, if_neg (fun H => H (τ', ⟨p + (a : ℕ), by omega⟩) ((key _).2 ⟨rfl, rfl, hq⟩))]
    simp only [key]
    rcases eq_or_ne τ τ' with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne]

end Main


open Classical in
theorem dy_flag : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (τ : Ψ) (i : Fin (p + q)), (∀ k, (model A x₀ m h).dy (τ, i) (.inl k) = -((rkW i * m (.inl τ) + rkO i * m (.inr τ) : ℕ) : ℤ)) ∧ ∀ t : StepIx Ψ p q, ((t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 1) ∧ (¬ (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 0) := by
  intro Ψ _ p q Ω _ _ n A K₀ _ J₀ _ x₀ m h τ i
  refine ⟨fun k => ?_, fun t => ?_⟩
  · rw [dy_apply h, if_pos (fun r' => blkF_ne_inl K₀ r' k)]
    rfl
  · obtain ⟨s, a⟩ := t
    cases s with
    | inl τ' =>
      have e := (eq_comm.trans (stepOf_eq_left τ τ' i a) :
        (⟨.inl τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ↔ _)
      have hc : ((⟨.inl τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ∨
          ((Sum.inl τ' : Ψ ⊕ Ψ) = .inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) ↔
          (τ = τ' ∧ ((i : ℕ) = a ∨ ((a : ℕ) + 1 = p ∧ p ≤ (i : ℕ)))) := by
        rw [e, Sum.inl.injEq]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
          · exact ⟨h1, Or.inl h2⟩
          · exact ⟨h1.symm, Or.inr ⟨h2, h3⟩⟩
        · rintro ⟨h1, h2 | ⟨h2, h3⟩⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1.symm, h2, h3⟩
      refine ⟨fun hc' => ?_, fun hn => ?_⟩
      · rw [dy_left h, if_pos (hc.1 hc')]
      · rw [dy_left h, if_neg (fun h' => hn (hc.2 h'))]
    | inr τ' =>
      have e := (eq_comm.trans (stepOf_eq_right τ τ' i a) :
        (⟨.inr τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ↔ _)
      have hc : ((⟨.inr τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ∨
          ((Sum.inr τ' : Ψ ⊕ Ψ) = .inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) ↔
          (τ = τ' ∧ (i : ℕ) = p + a) := by
        rw [e]
        constructor
        · rintro (h1 | ⟨h1, -⟩)
          · exact h1
          · exact absurd h1 Sum.inr_ne_inl
        · intro h1
          exact Or.inl h1
      refine ⟨fun hc' => ?_, fun hn => ?_⟩
      · rw [dy_right h, if_pos (hc.1 hc')]
      · rw [dy_right h, if_neg (fun h' => hn (hc.2 h'))]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionInBlockField
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField

private theorem aeval_mul_scale_of_homog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {S : Type} [CommRing S] [Algebra ℤ S] (f : MvPolynomial (Σ k, ι k) ℤ) (d : K → ℕ)
    (hf : ∀ m ∈ f.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) (t : K → S) (w : (Σ k, ι k) → S) :
    MvPolynomial.aeval (fun q : Σ k, ι k => t q.1 * w q) f = (∏ k, t k ^ d k) * MvPolynomial.aeval w f := by
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  have key : (m.prod fun q e => (t q.1 * w q) ^ e) = (∏ k, t k ^ d k) * m.prod fun q e => w q ^ e := by
    simp_rw [mul_pow]
    rw [Finsupp.prod_mul]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [key]
  ring

private theorem mConeMap_eq_prod_X_pow_mul_C {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : MvPolynomial (Σ k, ι k) ℤ) (d : K → ℕ)
    (hh : ∀ m ∈ h.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) :
    mConeMap y h = (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) * MvPolynomial.C (MvPolynomial.aeval y h) := by
  have e : (fun p : Σ k, ι k => MvPolynomial.C (y p) * (MvPolynomial.X p.1 : MvPolynomial K Ω)) =
      fun p => (MvPolynomial.X p.1 : MvPolynomial K Ω) * MvPolynomial.C (y p) := by
    funext p
    ring
  show MvPolynomial.aeval _ h = _
  rw [e, aeval_mul_scale_of_homog h d hh (fun k => (MvPolynomial.X k : MvPolynomial K Ω))
    (fun p => MvPolynomial.C (y p))]
  congr 1
  exact MvPolynomial.aeval_algebraMap_apply (MvPolynomial K Ω) y h

theorem algebraMap_mem_blockFnField :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] [CharZero Φ]
      (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (s : M.Ω),
      zb ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal zb) s → algebraMap M.Ω Φ s ∈ blockFnField y := by
  intro K _ ι _ Φ _ _ y Ψ N j M zb s hzb hreg
  obtain ⟨d, g, h, hg, hh, hQ, hgs⟩ := hreg
  obtain ⟨-, hzv⟩ := hzb
  have hxh : MvPolynomial.aeval M.x h ≠ 0 := by
    intro h0
    apply hQ
    have hker : h ∈ mCoordIdeal M.x := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C M.x h d hh, h0, map_zero, mul_zero]
    have hz := hzv h hker
    have hz' : MvPolynomial.aeval zb h = 0 := by
      rw [MvPolynomial.aeval_def, algebraMap_int_eq, ← MvPolynomial.eval_map]
      exact hz
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C zb h d hh, hz', map_zero, mul_zero]
  have hs : s = MvPolynomial.aeval M.x g / MvPolynomial.aeval M.x h := eq_div_of_mul_eq hxh hgs.symm
  rw [hs, map_div₀, ← MvPolynomial.aeval_algebraMap_apply, ← MvPolynomial.aeval_algebraMap_apply]
  have hne : ∀ k, ∃ i, (⇑(algebraMap M.Ω Φ) ∘ M.x) ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := M.x_ne k
    exact ⟨i, (map_ne_zero _).mpr hi⟩
  choose c hc using hne
  have hYy : ∀ q, (⇑(algebraMap M.Ω Φ) ∘ M.x) q = y ⟨q.1.val, q.2⟩ := fun q => (M.y_base q).symm
  generalize (⇑(algebraMap M.Ω Φ) ∘ M.x) = Y at hYy hc ⊢
  have hsc : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ, (∀ m ∈ p.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) →
      MvPolynomial.aeval Y p =
        (∏ k, Y ⟨k, c k⟩ ^ d k) * MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p := by
    intro p hp
    have eY : Y = fun q : Σ k, baseIdx ι M.blk k => Y ⟨q.1, c q.1⟩ * (Y q / Y ⟨q.1, c q.1⟩) := by
      funext q
      rw [mul_comm, div_mul_cancel₀ _ (hc q.1)]
    conv_lhs => rw [eY]
    exact aeval_mul_scale_of_homog p d hp (fun k => Y ⟨k, c k⟩) (fun q => Y q / Y ⟨q.1, c q.1⟩)
  have hP : (∏ k, Y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  rw [hsc g hg, hsc h hh, mul_div_mul_left _ _ hP]
  have hw : ∀ q, Y q / Y ⟨q.1, c q.1⟩ ∈ blockFnField y := by
    intro q
    rw [hYy, hYy]
    apply IntermediateField.subset_adjoin
    exact ⟨⟨q.1.val, q.2⟩, ⟨q.1.val, c q.1⟩, rfl, rfl⟩
  have hmem : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ,
      MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p ∈ blockFnField y := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast]
      exact intCast_mem _ a
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (hw n)
  exact div_mem (hmem g) (hmem h)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricFormula
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

private theorem hermOfFun_h_eq_of_homogeneous_of_pos {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hF : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hpos : 0 < F z) : (hermOfFun ι a F).h z = F z := by
  have h0 : (torusSetoid (ι := ι)).r (orbitRep z) z := Quotient.mk_out (s := torusSetoid) z
  obtain ⟨c, hc, hcz⟩ := h0
  have ho : orbitRep z = torusSmul (fun k => (c k)⁻¹) z := by
    funext p
    conv_rhs => rw [hcz]
    simp only [torusSmul]
    rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]
  have hc' : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have hpc : 0 < ∏ k, ‖(c k)⁻¹‖ ^ a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc' k)) _
  have hr := refNorm_pos a hz
  show refNorm a z * Real.exp (Real.log (F (orbitRep z) / refNorm a (orbitRep z))) = F z
  rw [ho, hF _ hc', refNorm_smul, mul_div_mul_left _ _ hpc.ne', Real.exp_log (div_pos hpos hr)]
  field_simp

private theorem smoothRep_h_eq_of_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (A : HermLine ι) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) :
    (smoothRep P A).h z = A.h z := by
  unfold smoothRep
  split_ifs with h
  · exact h.choose_spec.2.2 z hz
  · rfl

private theorem eval_torusSmul_map_eq_eval_mConeMap {K : Type} {ι : K → Type} (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (f : MRing ι) :
    eval (torusSmul c z) (map (Int.castRingHom ℂ) f) = MvPolynomial.eval c (mConeMap z f) := by
  have h : (eval (torusSmul c z)).comp (map (Int.castRingHom ℂ)) =
      (MvPolynomial.eval c).comp (mConeMap z).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · intro q
      simp [mConeMap, torusSmul, mul_comm]
  exact RingHom.congr_fun h f

private theorem torusSmul_mem_mcPts_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    torusSmul c z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hf' : f ∈ mCoordIdeal z := VertFactorPos.mCoordIdeal_le hz hf
    rw [eval_torusSmul_map_eq_eval_mConeMap, RingHom.mem_ker.1 hf', map_zero]

theorem muReg_h_eq_of_mem_mcPts : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ), ∀ z ∈ mcPts (mCoordIdeal D.y), (muReg X.H X.S B t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B t z hz
  have hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz.1
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D
  have hsm := VertFactorSmooth.proof VertFactorPos.proof II Ψ K ι Ω E D
  have hproj : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → X.M.proj (torusSmul c z) = X.M.proj z := fun c hc =>
    ((X.M.fibre z hz (torusSmul c z) (torusSmul_mem_mcPts_mCoordIdeal D.y hz hc)).2 ⟨c, hc, rfl⟩).symm
  have hreg : (X.S.regLine t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) := by
    refine hermOfFun_h_eq_of_homogeneous_of_pos (muLine X.H).a
      (fun w => X.S.ref.h w * Real.exp (X.S.regWeight t (X.M.proj w))) z hz' ?_
      (mul_pos (X.S.ref.pos z hz') (Real.exp_pos _))
    intro c hc
    show X.S.ref.h (torusSmul c z) * Real.exp (X.S.regWeight t (X.M.proj (torusSmul c z))) =
      (∏ k, ‖c k‖ ^ (muLine X.H).a k) * (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)))
    have hs : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ (muLine X.H).a k) * X.S.ref.h z := by
      rw [← X.S.ref_deg]
      exact X.S.ref.smul c z hc
    rw [hproj c hc, hs, mul_assoc]
  rw [muReg, smoothRep_h_eq_of_mem_mcPts _ _ z hz]
  refine (hermOfFun_h_eq_of_homogeneous_of_pos (muTwDeg X.H B)
    (fun w => (X.S.regLine t).h w * ∏ p ∈ D.SB B, D.vertFactor p w) z hz' ?_ ?_).trans ?_
  · intro c hc
    show (X.S.regLine t).h (torusSmul c z) * ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
      (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * ((X.S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z)
    have h1 : (X.S.regLine t).h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * (X.S.regLine t).h z :=
      (X.S.regLine t).smul c z hc
    have h2 : ∀ p ∈ D.SB B,
        D.vertFactor p (torusSmul c z) = (∏ k, ‖c k‖ ^ D.vdeg p k) * D.vertFactor p z :=
      fun p hp => (hsm p (Finset.mem_filter.1 hp).1).1 z hz c hc
    rw [h1, Finset.prod_congr rfl h2, Finset.prod_mul_distrib, muTwDeg,
      MuRegSmooth.prod_norm_zpow_add_sum hc]
    ring
  · exact mul_pos ((X.S.regLine t).pos z hz')
      (Finset.prod_pos fun p hp => hpos p (Finset.mem_filter.1 hp).1 z hz)
  · show (X.S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z = _
    rw [hreg]

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ScaledCoordinatesValueAtPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec

theorem isValueAt_aeval {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
    {y' : (Σ k, ι' k) → Ω} {z : (Σ k, ι' k) → ℂ} {σ : Type} {s : σ → Ω} {w : σ → ℂ}
    (hv : ∀ q, IsValueAt y' (s q) z (w q)) (f : MvPolynomial σ ℤ) :
    IsValueAt y' (aeval s f) z (eval w (map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C n => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_intCast y' z n
  | add p q hp hq => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_add hp hq
  | mul_X p i hp => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_mul hp (hv i)

theorem mem_mcPts_of_specialise : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (a : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (zt : (Σ k, ι k) → ℂ) (e : K → Ω) (s : (Σ k, ι k) → Ω) (t : K → ℂ), z ∈ mcPts (mCoordIdeal y') → (∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) → (∀ k, e k ≠ 0) → (∀ k, t k ≠ 0) → (∀ q, a q = e q.1 * s q) → (∀ q, IsValueAt y' (s q) z (t q.1 * zt q)) → zt ∈ mcPts (mCoordIdeal a) := by
  intro K _ ι _ K' _ ι' _ Ω _ a y' z zt e s t hz hzt he ht has hv
  refine ⟨hzt, fun f hf => ?_⟩
  obtain ⟨T, hT, hE⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal a
  rw [hE] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨d, hd⟩ := hT g hg
    have h0 : aeval a g = 0 :=
      (GlobalTheory.CompanionTheory.Ar.PB.form_mem_mCoordIdeal_iff a hd).1 (by rw [hE]; exact Ideal.subset_span hg)
    have ha : a = fun p => e p.1 * s p := funext has
    have h1 : aeval s g = 0 := by
      have h := GroundTheory.Heights₂.Heights.Inter.ChartNormPts.aeval_smul_homog g d hd e s
      rw [← ha, h0] at h
      have hne : (∏ k, e k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (he k)
      exact (mul_eq_zero.1 h.symm).resolve_left hne
    have hval := isValueAt_aeval (w := fun q => t q.1 * zt q) hv g
    rw [h1] at hval
    have h2 := GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_zero hz hval
    rw [ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog g d hd t zt] at h2
    have hne : (∏ k, t k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)
    exact (mul_eq_zero.1 h2).resolve_left hne
  | zero => simp
  | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
  | smul r x _ hx => simp [smul_eq_mul, map_mul, hx]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec
end
end

