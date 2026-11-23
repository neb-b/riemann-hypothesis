module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0152
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0145
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0153
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFacts
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.LSeq

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem lpow_nzd (n : ℕ) : (l : A.Acr0) ^ n ∈ nonZeroDivisors A.Acr0 :=
  pow_mem (A.acris_torsion_free l (Fact.out : l.Prime).ne_zero) n


set_option synthInstance.maxHeartbeats 400000 in
def alphaL (n : ℕ) : A.Acr0 →ₗ[A.Acr0] (A.Acr0 ⧸ Ideal.span {(l : A.Acr0) ^ (n + 1)}) :=
  (Submodule.mkQ _).comp (LinearMap.mulLeft A.Acr0 ((l : A.Acr0) ^ n))


set_option synthInstance.maxHeartbeats 400000 in
def alpha (n : ℕ) : A.Acr 1 →+ A.Acr (n + 1) :=
  ((Ideal.span {(l : A.Acr0) ^ 1}).liftQ (alphaL A n) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker]
    simp only [alphaL, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩)).toAddMonoidHom

theorem alpha_mk (n : ℕ) (y : A.Acr0) :
    alpha A n (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y) := rfl

theorem alpha_injective (n : ℕ) : Function.Injective (alpha A n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr 1 y = x := Ideal.Quotient.mk_surjective x
  rw [alpha_mk] at hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  have h0 : (l : A.Acr0) ^ n * (y - c * (l : A.Acr0) ^ 1) = 0 := by
    rw [mul_sub, ← hc]; ring
  have h1 := mem_nonZeroDivisors_iff_left.1 (lpow_nzd A n) _ h0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨c, (sub_eq_zero.1 h1).symm⟩)

theorem alpha_exact (n : ℕ) : Function.Exact (alpha A n) (A.red n.le_succ) := by
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr (n + 1) y = x := Ideal.Quotient.mk_surjective x
  rw [red_mk]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    exact ⟨A.mkAcr 1 c, by rw [alpha_mk, ← hc, mul_comm]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ : ∃ w, A.mkAcr 1 w = z := Ideal.Quotient.mk_surjective z
    rw [← red_mk A n.le_succ y, ← hz, alpha_mk, red_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨w, mul_comm _ _⟩)

theorem racrSeq (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RAcrSeq l :=
  fun n => ⟨fun A => alpha A n, fun A y => alpha_mk A n y, fun A => ⟨alpha_injective A n, alpha_exact A n⟩⟩

end GlobalTheory.CompanionTheory.LSeq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNorm
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.ChartDenom

theorem exists_nat_mul_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω} (hx : x ∈ chartRingQ y c) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Ω) * x ∈ chartRingZ y c := by
  unfold chartRingQ at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Nat.cast_one, one_mul]
    exact Algebra.subset_adjoin hx
  | algebraMap r =>
    refine ⟨r.den, r.den_ne_zero, ?_⟩
    have h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : ((r.den : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_ne_zero
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [h]
    exact intCast_mem _ _
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u + v) = (n : Ω) * ((m : Ω) * u) + (m : Ω) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hmu) (mul_mem (natCast_mem _ _) hnv)
  | mul u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u * v) = ((m : Ω) * u) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact mul_mem hmu hnv

theorem chartLatQ_le_span_chartLatNm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ),
      chartLatQ y a τ ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
  intro K _ ι _ Ω _ _ y a τ s hs
  classical
  have hex : ∀ c : ∀ k, ι k, ∃ n : ℕ, n ≠ 0 ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_chartRingZ y c (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hc⟩
  choose n hn0 hn using hex
  have hN : (∏ c, n c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hn0 c
  have hNΩ : (((∏ c, n c : ℕ)) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hmem : (((∏ c, n c : ℕ)) : Ω) * s ∈ chartLatNm y a τ := by
    intro c hc
    have e : ((((∏ c, n c : ℕ)) : Ω) * s) * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
          ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
      push_cast; ring
    rw [e]
    have h : (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
        ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) ∈ chartRingZ y c :=
      mul_mem (natCast_mem _ _) (hn c hc)
    exact Subalgebra.algebraMap_mem (integralClosure (chartRingZ y c) Ω) (⟨_, h⟩ : chartRingZ y c)
  have h1 : (((∏ c, n c : ℕ)) : Ω) * s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω) :=
    Submodule.subset_span hmem
  have h2 := Submodule.smul_mem _ (((∏ c, n c : ℕ) : ℚ)⁻¹) h1
  have e : (((∏ c, n c : ℕ) : ℚ)⁻¹) • ((((∏ c, n c : ℕ)) : Ω) * s) = s := by
    rw [Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hNΩ, one_mul]
  rwa [e] at h2

end GlobalTheory.CompanionTheory.Ar.ChartDenom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShift
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Conductor

theorem mem_chartRingQ_of_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω}
    (hx : x ∈ chartRingZ y c) : x ∈ chartRingQ y c := by
  unfold chartRingZ at hx
  unfold chartRingQ
  induction hx using Algebra.adjoin_induction with
  | mem z hz => exact Algebra.subset_adjoin hz
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add u v _ _ hu hv => exact add_mem hu hv
  | mul u v _ _ hu hv => exact mul_mem hu hv

theorem exists_conductor_section :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
      ∃ (e : K → ℕ) (c : Ω), c ≠ 0 ∧ ∀ (a : K → ℤ) (τ : ℕ),
        ∀ s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω),
          c * s ∈ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
  classical
  intro K _ ι _ Ω _ _ y D _ hbir
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  refine ⟨∑ c : C, δ c, ∏ c : C, aeval y (F c), Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c,
    fun a τ s hs => ?_⟩
  have key : ∀ s ∈ chartLatNm y a τ, (∏ c : C, aeval y (F c)) * s ∈
      chartLatQ y ((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) 1 := by
    intro s hs c' hc'
    let c : C := ⟨c', hc'⟩
    have hx := hs c' hc'
    have hm : ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) *
          (((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) k))) =
        (∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) * Conductor.invMon y c' (∑ c : C, δ c) := by
      rw [← Conductor.prod_zpow_eq_invMon, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc' k)]
      congr 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
      ring
    apply mem_chartRingQ_of_mem_chartRingZ
    rw [hm, ← Conductor.invMon_sum y c' Finset.univ δ]
    have hsplit : (∏ b : C, aeval y (F b)) * s * ((∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) *
          ∏ b : C, Conductor.invMon y c' (δ b)) =
        (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
          (aeval y (F c) * Conductor.invMon y c' (δ c) *
            (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
        ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
        Finset.prod_mul_distrib]
      ring
    rw [hsplit]
    exact mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b)) (hcond c _ hx)
  induction hs using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero => simpa using Submodule.zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
  | smul r u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hu

end GlobalTheory.CompanionTheory.Conductor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingOfTrivialFrameStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishing_of_trivial_frame : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (E : Frame (Φ := Φ) 0) (F : C ⥤ ModuleCat.{0} R),
    Subsingleton (F.obj E.D) → ∀ n, Subsingleton (CH.H F n) := by
  intro R _ C _ Φ E F hD n
  have hInitial : Limits.IsInitial E.D := by
    refine Limits.IsInitial.ofUniqueHom (fun T => Classical.choice (E.ne T)) ?_
    intro T f
    obtain ⟨g, -, hg⟩ := E.bij f (fun _ => 0) (fun i => i.elim0)
    exact (hg _ (fun i => i.elim0)).trans (hg _ (fun i => i.elim0)).symm
  obtain ⟨-, -, hex0, hex⟩ := CrystallineSemistableComparison.P.initial F E.D hInitial
  have key : ∀ x : CH.H F n, x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).2.1 a ha).2 ?_
    cases n with
    | zero =>
      obtain ⟨m, hm⟩ := hex0 a ha
      rw [one_smul] at hm
      have hm0 : m = 0 := Subsingleton.elim _ _
      rw [hm0, map_zero] at hm
      exact hm.symm
    | succ n =>
      obtain ⟨y, hy⟩ := hex n a ha
      rw [one_smul] at hy
      exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingShortExactStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishing_short_exact : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂)
    (β : F₂ ⟶ F₃), (∀ T, Function.Injective (α.app T).hom) → (∀ T, Function.Exact (α.app T).hom (β.app T).hom) →
    (∀ T, Function.Surjective (β.app T).hom) → (∀ n, Subsingleton (CH.H F₂ n)) → (∀ n, Subsingleton (CH.H F₃ n)) →
    ∀ n, Subsingleton (CH.H F₁ n) := by
  first | exact @GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | exact GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | (intros; apply GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosed
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeZcoc

theorem plogK_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f) (s : ℕ)
    {x : B} (hx : x ∈ J) : f (plogK δ s x) = plogK δ' s (f x) := by
  unfold plogK
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, ← hf.2 x hx]

theorem units_cancel {G : Type} [CommGroup G] (a b c d e f : G) :
    (a * b * c⁻¹) * (c * d * e⁻¹) = (b * d * f⁻¹) * (a * f * e⁻¹) := by
  have h1 : (a * b * c⁻¹) * (c * d * e⁻¹) = a * b * d * e⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  have h2 : (b * d * f⁻¹) * (a * f * e⁻¹) = (a * b * d) * e⁻¹ * (f⁻¹ * f) := by
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [h1, h2, inv_mul_cancel, mul_one]

theorem plogK_four {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (hs : pdP δ s = ⊥)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) {a b c d : B} (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) (hc : c - 1 ∈ J)
    (hd : d - 1 ∈ J) (h : a * b = c * d) :
    plogK δ s (a - 1) + plogK δ s (b - 1) = plogK δ s (c - 1) + plogK δ s (d - 1) := by
  rw [← GlobalTheory.T.truncated_log_multiplicative δ s hs hu ha hb, ← GlobalTheory.T.truncated_log_multiplicative δ s hs hu hc hd]
  simp only [add_sub_cancel]
  rw [h]

theorem add_eq {B : Type} [CommRing B] {a c d b a' c' d' b' : B} (h₁ : a = a') (h₂ : c = c') (h₃ : d = d')
    (h₄ : b = b') (h : a' + c' = d' + b') : a + c = d + b := by
  rw [h₁, h₂, h₃, h₄, h]

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def rr (Λ : CLiftK g D) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c) (χ : a ⟶ c) : (g.obj c).Bˣ :=
  Units.map (g.map ψ).φ.toMonoidHom (Λ.w φ) * Λ.w ψ * (Λ.w χ)⁻¹

theorem r_eq (Λ : CLiftK g D) (σ : ComposableArrows C 2) :
    Λ.r σ = rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) := rfl

theorem rr_coboundary (Λ : CLiftK g D) {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁) (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃)
    (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f₀₃ : c₀ ⟶ c₃) (h₀₂ : f₀₂ = f₀₁ ≫ f₁₂) (h₁₃ : f₁₃ = f₁₂ ≫ f₂₃) :
    Units.map (g.map f₂₃).φ.toMonoidHom (rr Λ f₀₁ f₁₂ f₀₂) * rr Λ f₀₂ f₂₃ f₀₃ =
      rr Λ f₁₂ f₂₃ f₁₃ * rr Λ f₀₁ f₁₃ f₀₃ := by
  subst h₀₂ h₁₃
  have e : Units.map (g.map (f₁₂ ≫ f₂₃)).φ.toMonoidHom (Λ.w f₀₁) =
      Units.map (g.map f₂₃).φ.toMonoidHom (Units.map (g.map f₁₂).φ.toMonoidHom (Λ.w f₀₁)) := by
    rw [g.map_comp]; rfl
  unfold rr
  rw [e, map_mul, map_mul, map_inv]
  exact units_cancel _ _ _ _ _ _

theorem map_zK (Λ : CLiftK g D) (s : ℕ) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    (show (g.obj c).B from ((g ⋙ O (smFun X q)).map ρ).hom (zK Λ s σ)) =
      plogK (g.obj c).δ s (((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1) := by
  change (g.map ρ).φ (plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1)) = _
  rw [plogK_map (g.map ρ).dp s (_root_.GlobalTheory.CompanionTheory.ConeUnit.r_sub_one Λ σ), map_sub, map_one]
  rfl

theorem mem_J (Λ : CLiftK g D) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    ((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1 ∈ (g.obj c).J := by
  have := (g.map ρ).hle (_root_.GlobalTheory.CompanionTheory.ConeUnit.r_sub_one Λ σ)
  rw [Ideal.mem_comap, map_sub, map_one] at this
  exact this

theorem map_id_unit {c : C} (ρ : c ⟶ c) (h : ρ = 𝟙 c) (u : (g.obj c).Bˣ) :
    Units.map (g.map ρ).φ.toMonoidHom u = u := by
  subst h
  rw [g.map_id]
  ext; rfl

theorem nat_isUnit (T : Thick (smFun X q)) (n : ℕ) (hn : n ≠ 0) : IsUnit (n : T.B) := by
  have h : IsUnit (n : K) := (Nat.cast_ne_zero.2 hn).isUnit
  have := h.map T.i
  rwa [map_natCast] at this

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → CH.d _ 2 (zK Λ s) = 0 := by
  intro K _ _ X q C _ g D Λ s hs
  funext τ
  change ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (toLast i τ)).hom (zK Λ s (face i τ)) = 0
  rw [Fin.sum_univ_four]
  have h0 := map_zK Λ s (face 0 τ) (toLast 0 τ)
  have h1 := map_zK Λ s (face 1 τ) (toLast 1 τ)
  have h2 := map_zK Λ s (face 2 τ) (toLast 2 τ)
  have h3 := map_zK Λ s (face 3 τ) (toLast 3 τ)
  have m0 := mem_J Λ (face 0 τ) (toLast 0 τ)
  have m1 := mem_J Λ (face 1 τ) (toLast 1 τ)
  have m2 := mem_J Λ (face 2 τ) (toLast 2 τ)
  have m3 := mem_J Λ (face 3 τ) (toLast 3 τ)
  have e0 : Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) = Λ.r (face 0 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 0 τ) (τ.map_id _) _
  have e1 : Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) = Λ.r (face 1 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 1 τ) (τ.map_id _) _
  have e2 : Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) = Λ.r (face 2 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 2 τ) (τ.map_id _) _
  have key : Units.map (g.map (toLast 3 τ)).φ.toMonoidHom (Λ.r (face 3 τ)) *
      Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) =
      Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) *
      Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) := by
    rw [e0, e1, e2]
    exact rr_coboundary Λ (τ.map' 0 1) (τ.map' 1 2) (τ.map' 2 3) (τ.map' 0 2) (τ.map' 1 3) (τ.map' 0 3)
      (τ.map'_comp 0 1 2) (τ.map'_comp 1 2 3)
  have hval := congrArg (Units.val) key
  rw [Units.val_mul, Units.val_mul] at hval
  have p := plogK_four (g.obj (τ.obj (Fin.last 3))).δ s (hs _) (nat_isUnit (g.obj (τ.obj (Fin.last 3)))) m3 m1 m0 m2 hval
  have fin : ∀ a b c d : (g ⋙ O (smFun X q)).obj (τ.obj (Fin.last 3)), a + c = d + b →
      (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 4) : ℕ) • c +
        (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) • d = 0 := by
    intro a b c d h
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
    rw [e0, e1, e2, e3]
    have : (-1 : ℤ) ^ 3 = -1 := by norm_num
    rw [this, pow_zero, pow_one, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_smul, one_smul, neg_one_smul, neg_one_smul]
    calc a + -b + c + -d = (a + c) - (d + b) := by abel
      _ = 0 := by rw [h, sub_self]
  refine fin _ _ _ _ ?_
  exact add_eq (B := (g.obj (τ.obj (Fin.last 3))).B) h0 h2 h3 h1 p.symm

end GlobalTheory.CompanionTheory.ConeZcoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCoordNeZero
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Relevant

theorem exists_coord_ne_zero :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Ω _ _ y D hP k
  obtain ⟨i, hi⟩ := hP.2.1.2.2 k
  exact ⟨i, fun h0 => hi (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.X_mem_of_eq_zero h0)⟩

end GlobalTheory.CompanionTheory.Ar.Relevant
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_critical_comparison_map : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {d : ℕ} (E : Frame Φ (d + 1))
    (a b : ℤ → IdF Φ.A) (r : ℤ), (∀ r' T, (b r').S T ≤ (a r').S T) → Q.Crit a r → Q.Crit a (r - 1) → Q.Crit b r → Q.Crit b (r - 1) →
    ∃ β : Cut.P0 Q ⋙ Cut.U E ⋙ sq (a r) (b r) ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq (a (r - 1)) (b (r - 1)),
      (∀ X, Function.Injective ((Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))).app X).hom) ∧
      (∀ X, Function.Exact ((Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))).app X).hom (β.app X).hom) ∧
      (∀ X, Function.Surjective (β.app X).hom) ∧
      ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (a r) (b r) (Q.P X.T)) (z' : sqM (a (r - 1)) (b (r - 1)) (Q.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        (β.app X).hom z = z' := by
  first | exact @GlobalTheory.CompanionTheory.PolySes.ses | exact GlobalTheory.CompanionTheory.PolySes.ses | (intros; apply GlobalTheory.CompanionTheory.PolySes.ses <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingTensorFiltrationStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_splitting_tensor_filtration : ∀ {O A Γ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing Γ] [Algebra O Γ] [Module.Flat O Γ]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m),
    ∃ g : (∀ i, S.N i ⊗[O] Γ) ≃ₗ[O] A ⊗[O] Γ, (∀ i n x, g (Pi.single i (n ⊗ₜ x)) = S.ν i n ⊗ₜ x) ∧
      ∀ (r : ℕ) (z : ∀ i, S.N i ⊗[O] Γ), g z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ)) ↔
        ∀ i : Fin m, (i : ℕ) < r → z i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.GrTens.main | exact GlobalTheory.CompanionTheory.GrTens.main | (intros; apply GlobalTheory.CompanionTheory.GrTens.main <;> assumption)
end

