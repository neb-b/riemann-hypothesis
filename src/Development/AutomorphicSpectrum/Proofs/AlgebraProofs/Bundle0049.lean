module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0048
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_kernel_derivative_vanishes : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : Germ.FB R d O) (u : Fin d → R) (g : Germ.PS R 2 d), alpha B p u = 0 → pow1 B p = Germ.ev (n := 2) ![ptPow R d p 0, Germ.pt R d 1] g → ∀ j, MvPowerSeries.pderiv (R := R) ((0 : Fin 1), j) (∑ i, MvPowerSeries.C (u i) * Germ.ev (n := 1) ![0, Germ.pt R d 0] (MvPowerSeries.pderiv (R := R) ((0 : Fin 2), i) g)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Kill.germKill | exact GlobalTheory.CompanionTheory.Ar.Kill.germKill | (intros; apply GlobalTheory.CompanionTheory.Ar.Kill.germKill <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneous
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem graph_bihomog : GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.Statement :=
  GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FunctionFieldCurveExists
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.FF

theorem places_form_curve : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K], ∃ C : ACurve K, IsFFCurve k C ∧ Nonempty C.I ∧ ∀ i (x : K), IsAlgebraic k x → C.v i x ≤ 1 :=
  @PositivityTheory.HtPt.Cc.inh_ff

end GlobalTheory.CompanionTheory.Ar.FF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitCharactersUnramifiedStatement
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_characters_unramified : ∀ (E : Type) [Field E] [NumberField E] (R K S : Type) [CommRing R] [IsDomain R] [CharZero R] [Field K] [Fintype S] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (σ : S → (𝓞 E →+* R)) (π : R →+* K), Function.Injective σ → Fintype.card S = Module.finrank ℚ E → ¬ (p : ℤ) ∣ NumberField.discr E → ∃ χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K), IsSplit χ ∧ ∀ s a, ((χ s a : algebraicClosure (ZMod p) K) : K) = π (σ s a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit | exact GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisColengthStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_basis_colength : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisLengthsStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_basis_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1

section Rel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_zero_of_mem_mCoordIdeal (y : (Σ k, ι k) → Ω) {h : MRing ι}
    (hh : h ∈ mCoordIdeal y) : aeval y h = 0 := by
  let φ : MvPolynomial K Ω →ₐ[ℤ] Ω :=
    (aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ
  have e : φ.comp (mConeMap y) = aeval y := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp [φ, mConeMap]
  have h0 : mConeMap y h = 0 := hh
  rw [← e, AlgHom.comp_apply, h0, map_zero]

theorem exists_monic_rel (y : (Σ k, ι k) → Ω) {f g : MRing ι} {d : K → ℕ} {θ : Ω}
    (hf : IsMultiHomog f d) (hg : IsMultiHomog g d) (hθ : IsIntegral ℤ θ)
    (he : aeval y f = θ * aeval y g) :
    ∃ (n : ℕ) (c : ℕ → MRing ι),
      1 * f ^ n + ∑ j ∈ Finset.range n, c j * f ^ j * g ^ (n - j) ∈ mCoordIdeal y := by
  classical
  obtain ⟨p, hpm, hp⟩ := hθ
  set n := p.natDegree
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp
  refine ⟨n, fun j => C (p.coeff j), ?_⟩
  rw [one_mul]
  refine LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := n • d) ?_ ?_
  · refine LocalRep.isMultiHomog_add (SectionOrderAtPoint.isMultiHomog_pow' hf n)
      (SectionOrderAtPoint.isMultiHomog_sum' _ _ fun j hj => ?_)
    have h1 := LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_mul
      (LocalRep.isMultiHomog_C (ι := ι) (p.coeff j)) (SectionOrderAtPoint.isMultiHomog_pow' hf j))
      (SectionOrderAtPoint.isMultiHomog_pow' hg (n - j))
    convert h1 using 1
    have hj' : j ≤ n := (Finset.mem_range.mp hj).le
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add]
    rw [← add_mul, Nat.add_sub_cancel' hj']
  · have hsum : ∀ j ∈ Finset.range n,
        aeval y (C (p.coeff j) * f ^ j * g ^ (n - j)) =
          aeval y g ^ n * (algebraMap ℤ Ω (p.coeff j) * θ ^ j) := by
      intro j hj
      have hj' : j ≤ n := (Finset.mem_range.mp hj).le
      have e3 : aeval y g ^ n = aeval y g ^ j * aeval y g ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hj']
      simp only [map_mul, map_pow, aeval_C, he]
      rw [e3]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, Finset.sum_congr rfl hsum, ← Finset.mul_sum, map_pow, he, mul_pow]
    linear_combination (aeval y g ^ n) * hp

end Rel

theorem mem_minimalPrimes_of_rel {R : Type*} [CommRing R] [IsNoetherianRing R] {P W : Ideal R}
    (hP : P.IsPrime) {a b : R} (ha : a ∉ P) {n : ℕ} (c : ℕ → R)
    (hrel : 1 * a ^ n + ∑ j ∈ Finset.range n, c j * a ^ j * b ^ (n - j) ∈ P)
    (hW : W ∈ (P ⊔ Ideal.span {b}).minimalPrimes) : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hbW : b ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
  have h1 : (1 : R) ∉ W := (Ideal.ne_top_iff_one W).mp hWp.ne_top
  have haW : a ∈ W := SectionOrderAtPoint.mem_of_rel hWp hbW h1 c (hPW hrel)
  refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr haW)⟩, fun Q hQ hQW => ?_⟩
  exact (eq_of_le_of_mem_minimalPrimes hP hW hQ.1 (le_sup_left.trans hQ.2)
    (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))) ha hQW).ge

theorem divCycle_eq_of_unit_ratio : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (d : K → ℕ) (f g : MRing ι) (θ : Ω), IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f d → IsMultiHomog g d → aeval y g ≠ 0 → θ ≠ 0 → IsIntegral ℤ θ → IsIntegral ℤ θ⁻¹ → aeval y f = θ * aeval y g → divSupp (mCoordIdeal y) f = divSupp (mCoordIdeal y) g ∧ ∀ W ∈ divSupp (mCoordIdeal y) g, multAt ((mCoordIdeal y) ⊔ Ideal.span {f}) W = multAt ((mCoordIdeal y) ⊔ Ideal.span {g}) W := by
  intro K _ ι _ Ω _ y D d f g θ hV hf hg hgy hθ0 hθ hθi he
  have hP : (mCoordIdeal y).IsPrime := hV.2.1.1
  have hfy : aeval y f ≠ 0 := by
    rw [he]
    exact mul_ne_zero hθ0 hgy
  have hfP : f ∉ mCoordIdeal y := fun h => hfy (aeval_eq_zero_of_mem_mCoordIdeal y h)
  have hgP : g ∉ mCoordIdeal y := fun h => hgy (aeval_eq_zero_of_mem_mCoordIdeal y h)
  obtain ⟨n, c, hrel⟩ := exists_monic_rel y hf hg hθ he
  obtain ⟨m, c', hrel'⟩ := exists_monic_rel y hg hf hθi
    (by rw [he, ← mul_assoc, inv_mul_cancel₀ hθ0, one_mul])
  refine ⟨?_, ?_⟩
  · ext W
    exact ⟨fun h => ⟨mem_minimalPrimes_of_rel hP hgP c' hrel' h.1, h.2⟩,
      fun h => ⟨mem_minimalPrimes_of_rel hP hfP c hrel h.1, h.2⟩⟩
  · intro W hW
    have hWg := hW.1
    have hWf := mem_minimalPrimes_of_rel hP hfP c hrel hWg
    have hWp : W.IsPrime := hWg.1.1
    have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hWg.1.2
    have h1 : (1 : MRing ι) ∉ W := (Ideal.ne_top_iff_one W).mp hWp.ne_top
    let pW : PrimeSpectrum (MRing ι) := ⟨W, hWp⟩
    have hle1 := SectionOrderAtPoint.locLen_le_of_rel hP hfP hgP pW hPW h1 c hrel (locLen_ne_top hWg)
    have hle2 := SectionOrderAtPoint.locLen_le_of_rel hP hgP hfP pW hPW h1 c' hrel' (locLen_ne_top hWf)
    have := congrArg ENat.toNat (le_antisymm hle2 hle1)
    simpa [multAt, hWp, ReciprocityTheory.ChartRestriction.G.AI.locLen] using this

end GlobalTheory.CompanionTheory.Ar.Giv
end

