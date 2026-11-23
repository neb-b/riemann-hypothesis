module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0104
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivLeadMinorExpHermitianZeroDiag
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.MinorJet

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) s := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y s
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt s h
  simp only [Complex.coe_smul]
  exact h2

end Linfty

theorem hasDerivAt_mul_entry {r : ℕ} (G H : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' H' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s * H s) i j) ((G' * H t + G t * H') i j) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hG i k).fun_mul (hH k j))
  simpa [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using h

theorem hasDerivAt_adjugate_entry {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (h0 : G t = 1)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (A i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s).adjugate i j) ((A.trace • (1 : Matrix (Fin r) (Fin r) ℂ) - A) i j) t := by
  have hP : ∀ a b, HasDerivAt (fun s => (G s).adjugate a b)
      ((((G t).updateRow b (Pi.single a 1)).adjugate * A.updateRow b 0).trace) t := by
    intro a b
    have hrow : ∀ p q, HasDerivAt (fun s => (G s).updateRow b (Pi.single a 1) p q)
        ((A.updateRow b 0) p q) t := by
      intro p q
      by_cases hp : p = b
      · subst hp
        simp only [updateRow_self]
        exact hasDerivAt_const _ _
      · simp only [updateRow_ne hp]
        exact hG p q
    have h := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun s => (G s).updateRow b (Pi.single a 1)) _ t hrow
    simpa only [adjugate_apply] using h
  let D : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b =>
    (((G t).updateRow b (Pi.single a 1)).adjugate * A.updateRow b 0).trace
  have hD : ∀ a b, HasDerivAt (fun s => (G s).adjugate a b) (D a b) t := fun a b => hP a b
  have h1 := hasDerivAt_mul_entry (fun s => (G s).adjugate) G D A t hD hG i j
  have h2 := (ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det G A t hG).mul_const ((1 : Matrix (Fin r) (Fin r) ℂ) i j)
  have h3 : HasDerivAt (fun s => (G s).det * (1 : Matrix (Fin r) (Fin r) ℂ) i j)
      ((D * G t + (G t).adjugate * A) i j) t := by
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [adjugate_mul, Matrix.smul_apply, smul_eq_mul]
  have hu := h3.unique h2
  rw [h0, adjugate_one, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply] at hu
  have hDij : D i j = A.trace * (1 : Matrix (Fin r) (Fin r) ℂ) i j - A i j := by
    linear_combination hu
  convert hD i j using 1
  rw [hDij, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

private theorem sum_castLE_lemma {n l : ℕ} (hl : l ≤ n) (f : Fin n → ℂ) :
    ∑ x : Fin l, f (Fin.castLE hl x) = ∑ a : Fin n, if a.val < l then f a else 0 := by
  have e : (Finset.univ : Finset (Fin l)).map (Fin.castLEEmb hl) =
      Finset.univ.filter (fun a : Fin n => a.val < l) := by
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro h
      exact ⟨⟨a.val, h⟩, Fin.ext rfl⟩
  rw [← Finset.sum_filter, ← e, Finset.sum_map]
  rfl

theorem trace_block {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ) (hl : l ≤ n) :
    ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace -
      (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
    ((∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 : ℝ) : ℂ) := by
  have hH : ∀ a b, Y a b * Y b a = ((‖Y b a‖ ^ 2 : ℝ) : ℂ) := by
    intro a b
    have e : Y a b = star (Y b a) := by
      have := congrFun (congrFun hY a) b
      rw [conjTranspose_apply] at this
      exact this.symm
    rw [e, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e1 : ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
      ∑ a : Fin n, if a.val < l then ∑ b : Fin n, Y a b * Y b a else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Matrix.mul_apply]
    exact sum_castLE_lemma hl (fun a => ∑ b : Fin n, Y a b * Y b a)
  have e2 : (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) *
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
      ∑ a : Fin n, if a.val < l then ∑ b : Fin n, (if b.val < l then Y a b * Y b a else 0) else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.submatrix_apply]
    rw [← sum_castLE_lemma hl (fun a => ∑ b : Fin n, if b.val < l then Y a b * Y b a else 0)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact sum_castLE_lemma hl (fun b => Y (Fin.castLE hl x) b * Y b (Fin.castLE hl x))
  have key : ∀ a : Fin n, ((if a.val < l then ∑ b : Fin n, Y a b * Y b a else 0) -
      (if a.val < l then ∑ b : Fin n, (if b.val < l then Y a b * Y b a else 0) else 0)) =
      ∑ b : Fin n, ((if l ≤ b.val ∧ a.val < l then ‖Y b a‖ ^ 2 else 0 : ℝ) : ℂ) := by
    intro a
    by_cases ha : a.val < l
    · rw [if_pos ha, if_pos ha, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases hb : b.val < l
      · rw [if_pos hb, if_neg (fun h => absurd h.1 (Nat.not_le.mpr hb)), sub_self,
          Complex.ofReal_zero]
      · rw [if_neg hb, sub_zero, if_pos ⟨Nat.le_of_not_lt hb, ha⟩, hH]
    · rw [if_neg ha, if_neg ha, sub_self]
      symm
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [if_neg (fun h => ha h.2), Complex.ofReal_zero]
  rw [e1, e2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun a _ => key a), Finset.sum_comm,
    Complex.ofReal_sum]
  simp only [Complex.ofReal_sum]

theorem deriv_leadMinor_exp : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Y.IsHermitian → (∀ a, Y a a = 0) → ∀ (l : ℕ) (hl : l ≤ n), deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re) 0 = 0 ∧ deriv (deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)) 0 = ∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
  intro n Y hY hdiag l hl
  have hE0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  have hM0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl) = 1 := by
    rw [hE0]
    exact submatrix_one _ (Fin.castLE_injective hl)
  have hM'0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    rw [hE0, Matrix.one_mul]
  have htr : (Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace = 0 := by
    simp [Matrix.trace, hdiag]
  have hM : ∀ (t : ℝ) x y, HasDerivAt
      (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl) x y)
      ((NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y) t :=
    fun t x y => hasDerivAt_exp_entry Y t (Fin.castLE hl x) (Fin.castLE hl y)
  have hf : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (leadMinor (NormedSpace.exp ((s : ℂ) • Y)) l hl).re)
      (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
        (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re t := by
    intro t
    have hg := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det
      (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)) _ t (hM t)
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg
    simpa [leadMinor, Function.comp_def] using h
  have hderiv : deriv (fun s : ℝ => (leadMinor (NormedSpace.exp ((s : ℂ) • Y)) l hl).re) =
      fun t : ℝ => (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
        (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re :=
    funext fun t => (hf t).deriv
  rw [hderiv]
  refine ⟨?_, ?_⟩
  · beta_reduce
    rw [hM0, hM'0, adjugate_one, Matrix.one_mul, htr, Complex.zero_re]
  · have hadj : ∀ x y, HasDerivAt
        (fun s : ℝ => ((NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate x y)
        (((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) -
          Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) x y) 0 := by
      intro x y
      have h := hasDerivAt_adjugate_entry
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)) _ 0 hM0
        (hM 0) x y
      rwa [hM'0] at h
    have hMd : ∀ x y, HasDerivAt
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y)
        ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y) 0 := by
      intro x y
      have h := hasDerivAt_mul_entry (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y)) (fun _ => Y)
        (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y) 0 0 (hasDerivAt_exp_entry Y 0)
        (fun _ _ => hasDerivAt_const _ _) (Fin.castLE hl x) (Fin.castLE hl y)
      rw [hE0, Matrix.one_mul, Matrix.mul_zero, add_zero] at h
      exact h
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
      hasDerivAt_mul_entry
        (fun s : ℝ => ((NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate)
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl))
        _ _ 0 hadj hMd x x)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hsum
    have h3 : HasDerivAt
        (fun t : ℝ => (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re)
        ((((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) - Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) *
          (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) +
          ((NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace).re 0 := h2
    have hv : (((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) - Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) *
          (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) +
          ((NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
        ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace - (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace := by
      rw [hM0, hM'0, adjugate_one, htr, zero_smul, zero_sub, Matrix.neg_mul, Matrix.one_mul,
        Matrix.trace_add, Matrix.trace_neg]
      ring
    rw [h3.deriv, hv, trace_block Y hY l hl, Complex.ofReal_re]

end GlobalTheory.MinorJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearOfGramEq
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

noncomputable def conjLinearCombination {M : Type} [AddCommGroup M] [Module ℂ M] {I : Type}
    (b : I → M) : (I →₀ ℂ) →ₗ⋆[ℂ] M where
  toFun c := c.sum fun i x => star x • b i
  map_add' c d := by
    rw [Finsupp.sum_add_index']
    · intro i; simp
    · intro i x y; rw [star_add, add_smul]
  map_smul' r c := by
    rw [Finsupp.sum_smul_index' (by intro i; simp), Finsupp.smul_sum]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [smul_smul, smul_eq_mul, star_mul', starRingEnd_apply]

theorem conjLinearCombination_single {M : Type} [AddCommGroup M] [Module ℂ M] {I : Type}
    (b : I → M) (i : I) (x : ℂ) :
    conjLinearCombination b (Finsupp.single i x) = star x • b i := by
  change (Finsupp.single i x).sum (fun i x => star x • b i) = _
  rw [Finsupp.sum_single_index]; simp

theorem exists_conjLinear_of_gram_eq :
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Type) [AddCommGroup M] [Module ℂ M] (N : M → M → ℂ) (I : Type) (a : I → W) (b : I → M), (∀ p p' q, N (p + p') q = N p q + N p' q) → (∀ (c : ℂ) p q, N (c • p) q = c * N p q) → (∀ p q, N q p = star (N p q)) → (∀ p, N p p = 0 → p = 0) → Submodule.span ℂ (Set.range a) = ⊤ → (∀ i j, N (b j) (b i) = ⟪a j, a i⟫_ℂ) → ∃ Jm : W →ₗ⋆[ℂ] M, (∀ i, Jm (a i) = b i) ∧ ∀ ξ η, N (Jm η) (Jm ξ) = ⟪η, ξ⟫_ℂ := by
  intro W _ _ M _ _ N I a b hadd hsmul hstar hdef hspan hgram
  have hadd2 : ∀ p q q', N p (q + q') = N p q + N p q' := by
    intro p q q'
    rw [hstar (q + q') p, hadd, star_add, ← hstar, ← hstar]
  have hsmul2 : ∀ (c : ℂ) p q, N p (c • q) = star c * N p q := by
    intro c p q
    rw [hstar (c • q) p, hsmul, star_mul', ← hstar]
  have hz1 : ∀ q, N 0 q = 0 := by
    intro q
    have := hsmul 0 0 q
    simpa using this
  have hz2 : ∀ p, N p 0 = 0 := by
    intro p
    rw [hstar 0 p, hz1, star_zero]
  set A := Finsupp.linearCombination ℂ a with hA
  set B := conjLinearCombination b with hB
  have key : ∀ c d, N (B c) (B d) = ⟪A c, A d⟫_ℂ := by
    intro c d
    induction c using Finsupp.induction_linear with
    | zero => simp [hz1]
    | add c c' h h' => rw [map_add (f := _), map_add (f := _), hadd, inner_add_left, h, h']
    | single i x =>
      induction d using Finsupp.induction_linear with
      | zero => simp [hz2]
      | add d d' h h' => rw [map_add (f := _), map_add (f := _), hadd2, inner_add_right, h, h']
      | single j y =>
        rw [hA, hB, conjLinearCombination_single, conjLinearCombination_single,
          Finsupp.linearCombination_single, Finsupp.linearCombination_single, hsmul, hsmul2,
          inner_smul_left, inner_smul_right, hgram, star_star, starRingEnd_apply]
  have hr : LinearMap.range A = ⊤ := by
    rw [hA, Finsupp.range_linearCombination, hspan]
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective A hr
  have hs' : ∀ w, A (s w) = w := fun w => LinearMap.congr_fun hs w
  refine ⟨B.comp s, fun i => ?_, fun ξ η => ?_⟩
  · have h0 : B (s (a i) - Finsupp.single i 1) = 0 := by
      apply hdef
      have : A (s (a i) - Finsupp.single i 1) = 0 := by
        rw [map_sub, hs', hA, Finsupp.linearCombination_single, one_smul, sub_self]
      rw [key, this, inner_zero_left]
    rw [map_sub, sub_eq_zero, hB, conjLinearCombination_single, star_one, one_smul] at h0
    exact h0
  · change N (B (s η)) (B (s ξ)) = _
    rw [key, hs', hs']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FewOrbitsSubspacesHermitianLatticeDiscriminantStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.few_orbits_subspaces_hermitian_lattice_discriminant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (j n : ℕ), 1 ≤ n → ∃ s : Finset (Submodule K V), (s.card : ℝ) ≤ (n : ℝ) ^ (1 + Real.logb 2 (Module.finrank ℚ K)) ∧ (∀ U ∈ s, Module.finrank K U = j) ∧ ∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) n).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U := by
  first | exact @GlobalTheory.Mass.FewOrbits.main | exact GlobalTheory.Mass.FewOrbits.main | (intros; apply GlobalTheory.Mass.FewOrbits.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinAdeleAlgebraMapInj
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ClassDict

theorem exu_rep {G Γ Gf : Type} [Group G] [Group Γ] [Group Gf] (P R U : Subgroup G) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (Φ : Gf ≃* P) (h0 : P)
    (hK : ∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : P) : G) ∈ U)
    (h1 : ∀ γ : Γ, (Φ (ιf γ)).1 ∈ R) (h2 : ∀ r ∈ R, ∃ γ : Γ, (Φ (ιf γ)).1 = r)
    {C : Type} (yc : C → P)
    (hb : Function.Bijective
      (fun c => (Quotient.mk'' (yc c) : ClassSet (R.subgroupOf P) (U.subgroupOf P)))) (h : Gf) :
    ∃! c : C, ∃ (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf) := by
  have key : ∀ a b : P, (Quotient.mk'' a : ClassSet (R.subgroupOf P) (U.subgroupOf P)) = Quotient.mk'' b ↔
      ∃ x ∈ R.subgroupOf P, ∃ y ∈ U.subgroupOf P, b = x * a * y := fun a b => @DoubleCoset.eq _ _ _ _ a b
  have fwd : ∀ (c : C) (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf) →
      (Quotient.mk'' (yc c) : ClassSet (R.subgroupOf P) (U.subgroupOf P)) = Quotient.mk'' (Φ h * h0) := by
    intro c γ κ hc
    rw [key]
    refine ⟨Φ (ιf γ), ?_, h0⁻¹ * Φ κ * h0, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact h1 γ
    · rw [Subgroup.mem_subgroupOf]
      exact (hK κ).1 κ.2
    · simp only [hc, map_mul, MulEquiv.apply_symm_apply, mul_assoc]
  obtain ⟨c, hc⟩ := hb.2 (Quotient.mk'' (Φ h * h0))
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := (key _ _).1 hc
    rw [Subgroup.mem_subgroupOf] at hx hy
    obtain ⟨γ, hγ⟩ := h2 _ hx
    have hκ : Φ.symm (h0 * y * h0⁻¹) ∈ K := by
      rw [hK, MulEquiv.apply_symm_apply]
      have e : h0⁻¹ * (h0 * y * h0⁻¹) * h0 = y := by group
      rw [e]
      exact hy
    refine ⟨γ, ⟨_, hκ⟩, ?_⟩
    apply Φ.injective
    have hγ' : Φ (ιf γ) = x := Subtype.ext hγ
    have hΦ : Φ h = x * yc c * y * h0⁻¹ := by
      rw [← hxy]
      group
    simp only [map_mul, MulEquiv.apply_symm_apply, hγ', hΦ]
    group
  · rintro c' ⟨γ, κ, hc'⟩
    exact hb.1 ((fwd c' γ κ hc').trans hc.symm)

theorem stab_triv {G Γ Gf : Type} [Group G] [Group Γ] [Group Gf] (P U : Subgroup G) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (Φ : Gf ≃* P) (h0 : P)
    (hK : ∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : P) : G) ∈ U)
    (hn : ∀ (x : Gf) (γ : Γ), x⁻¹ * ιf γ * x ∈ K → γ = 1) (y : P) (γ : Γ)
    (hγ : (Φ (ιf γ)).1 ∈ U.map (MulAut.conj y.1).toMonoidHom) : (Φ (ιf γ)).1 = 1 := by
  obtain ⟨u, hu, hyu⟩ := Subgroup.mem_map.1 hγ
  have e : ((Φ (ιf γ) : P) : G) = (y : G) * u * (y : G)⁻¹ := by
    rw [← hyu]
    simp [MulAut.conj_apply]
  have hmem : (Φ.symm (y * h0⁻¹))⁻¹ * ιf γ * Φ.symm (y * h0⁻¹) ∈ K := by
    rw [hK]
    convert hu using 1
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    push_cast
    rw [e]
    group
  rw [hn _ _ hmem]
  simp

theorem bc_inj_of_inj {A B : Type} [CommRing A] [CommRing B] {k : ℕ} {φ : A →+* B}
    (hφ : Function.Injective φ) : Function.Injective (bc (n := Fin k) φ) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  funext i j
  exact hφ (congrFun (congrFun h' i) j)

theorem finAdele_algebraMap_inj (F : Type) [Field F] [NumberField F] :
    Function.Injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  have : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
    rw [← map_zero (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_one (algebraMap F (FiniteAdeleRing (𝓞 F) F))] at h'
    simp only [FiniteAdeleRing.algebraMap_apply] at h'
    rw [HeightOneSpectrum.adicCompletion.coe_zero, HeightOneSpectrum.adicCompletion.coe_one] at h'
    exact zero_ne_one h'
  exact (algebraMap F _).injective

theorem classReps_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gf : Type) [Group Γ] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)), (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ γ : Γ, ∃ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J ∧ (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J → ∃ γ : Γ, (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → ∀ (C : Type) (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → (∀ h : Gf, ∃! c : C, ∃ (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf)) ∧ ((∀ (x : Gf) (γ : Γ), x⁻¹ * ιf γ * x ∈ K → γ = 1) → ∀ (c : C) (g : GL (Fin n) E), g ∈ UJ (σ : E →+* E) J → bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → g = 1) := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gf _ _ ιf K Φ h0 hK h1 h2 C yc hb
  have hR1 : ∀ γ : Γ, (Φ (ιf γ)).1 ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F) := by
    intro γ
    obtain ⟨g, hg, hgγ⟩ := h1 γ
    rw [hgγ]
    unfold ratPts
    exact Subgroup.mem_map_of_mem _ hg
  have hR2 : ∀ r ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ γ : Γ, (Φ (ιf γ)).1 = r := by
    intro r hr
    unfold ratPts at hr
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hr
    exact h2 g hg
  refine ⟨fun h => exu_rep _ _ S.U ιf K Φ h0 hK hR1 hR2 yc hb h, fun hn c g hg hgU => ?_⟩
  obtain ⟨γ, hγ⟩ := h2 g hg
  have hs := stab_triv _ S.U ιf K Φ h0 hK hn (yc c) γ (by rw [hγ]; exact hgU)
  rw [hγ] at hs
  have hinj : Function.Injective (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) := by
    intro a b hab
    exact Algebra.TensorProduct.includeLeft_injective (S := F) (finAdele_algebraMap_inj F) hab
  exact bc_inj_of_inj hinj (hs.trans (map_one _).symm)

end GlobalTheory.ClassDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.WeightInf

theorem invVol_nn {G : Type} [Group G] (A B : Subgroup G) : 0 ≤ GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  positivity

theorem invVol_pos' {G : Type} [Group G] (A B : Subgroup G) (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0) :
    0 < GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  have h1' := Nat.pos_of_ne_zero h1
  have h2' := Nat.pos_of_ne_zero h2
  positivity

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), (∀ (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → 0 < N.om Λ ∧ ∀ s ∈ N.R, N.om (s • Λ) = N.om Λ) ∧ ∀ (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V), 0 ≤ omI F F' 𝔡 Λ ∧ (∀ N : NF H r, Adapt F F' 𝔡 N → omI F F' 𝔡 Λ ≤ N.om Λ) ∧ ∀ a c : ℝ, 0 ≤ c → (∃ N : NF H r, Adapt F F' 𝔡 N) → (∀ N : NF H r, Adapt F F' 𝔡 N → a ≤ c * N.om Λ) → a ≤ c * omI F F' 𝔡 Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r
  refine ⟨?_, ?_⟩
  · intro N g Λ hg hT
    have hnil := (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).2.2.2.2
    have href := (GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hT).2.2.2.2.1
    have hΛdata := ((isUnimod_iff H Λ).1 hT.1.1).1
    have hΛ : Submodule.IsFullLattice K Λ :=
      { toIsLattice := Submodule.IsLattice.of_fg K hΛdata.1, span_eq_top := hΛdata.2 }
    have hrefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
      refine { toIsLattice := href, span_eq_top := ?_ }
      obtain ⟨-, -, hC, -, hWn, hUp, -, -, -, -, -, hPi⟩ :=
        GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
      have hP : N.Pi ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
        rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
        exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
          fun _ hx => Submodule.mem_sup_left hx)
      have hW : N.Wt ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
        intro x hx
        have hxW : x ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hx
        obtain ⟨c, hc, hcx⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛdata.2 x
        rw [← Submodule.smul_mem_iff _ hc]
        apply Submodule.subset_span
        apply Submodule.mem_sup_right
        refine ⟨⟨?_, Submodule.mem_sup_left hcx⟩, N.Wn.smul_mem c hxW⟩
        rw [hUp]
        exact Submodule.mem_sup_left (N.Wn.smul_mem c hxW)
      apply eq_top_iff.mpr
      rw [← hC.sup_eq_top]
      exact sup_le hW hP
    have h1 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil Λ _ hΛ hrefFull
    have h2 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ Λ hrefFull hΛ
    refine ⟨invVol_pos' _ _ h2.1 h1.1, fun s hs => ?_⟩
    have h3 := (GlobalTheory.DegCnt.StabInv.main K V H hK r N g Λ hg hT s hs).2.1.1
    unfold NF.om
    rw [h3]
    exact h1.2 s hs
  · intro F F' 𝔡 Λ
    have hnn : ∀ x ∈ ((fun N : NF H r => N.om Λ) '' {N | Adapt F F' 𝔡 N}), (0 : ℝ) ≤ x := by
      rintro _ ⟨N, -, rfl⟩
      exact invVol_nn _ _
    refine ⟨Real.sInf_nonneg hnn, fun N hN => csInf_le ⟨0, hnn⟩ ⟨N, hN, rfl⟩, ?_⟩
    rintro a c hc ⟨N₀, hN₀⟩ h
    rcases hc.eq_or_lt with rfl | hc
    · simpa using h N₀ hN₀
    · rw [← div_le_iff₀' hc]
      refine le_csInf ⟨_, N₀, hN₀, rfl⟩ ?_
      rintro _ ⟨N, hN, rfl⟩
      rw [div_le_iff₀' hc]
      exact h N hN

end GlobalTheory.DegAsm.WeightInf
end

