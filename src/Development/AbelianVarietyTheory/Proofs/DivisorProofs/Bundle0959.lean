module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChange
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.HilbBaseChange

open Module TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem homogeneousComponent_map_algebraMap {σ K L : Type} [Field K] [Field L] [Algebra K L] (n : ℕ) (p : MvPolynomial σ K) :
    homogeneousComponent n (MvPolynomial.map (algebraMap K L) p) =
      MvPolynomial.map (algebraMap K L) (homogeneousComponent n p) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem homogeneousComponent_mem_span_map_homogeneous {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (P : Ideal (MvPolynomial σ K)) (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P)
    {g : MvPolynomial σ L}
    (hg : g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))))
    (n : ℕ) :
    homogeneousComponent n g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) ''
      ((P.restrictScalars K ⊓ homogeneousSubmodule σ K n : Submodule K (MvPolynomial σ K)) :
        Set (MvPolynomial σ K))) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, hq, rfl⟩ := hy
    rw [homogeneousComponent_map_algebraMap]
    exact Submodule.subset_span ⟨_, ⟨hP q hq n, homogeneousComponent_mem n q⟩, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem mem_span_image_of_mem_ideal_map {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (P : Ideal (MvPolynomial σ K)) {g : MvPolynomial σ L}
    (hg : g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L)) :
    g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))) := by
  obtain ⟨M, hM⟩ : ∃ M : Submodule L (MvPolynomial σ L),
      M = Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))) :=
    ⟨_, rfl⟩
  rw [← hM]
  have hX : ∀ (i : σ) (x : MvPolynomial σ L), x ∈ M → X i * x ∈ M := by
    intro i x hx
    rw [hM] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, hq, rfl⟩ := hy
      refine Submodule.subset_span ⟨X i * q, P.mul_mem_left _ hq, ?_⟩
      simp
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  have hmul : ∀ (a x : MvPolynomial σ L), x ∈ M → a * x ∈ M := by
    intro a x hx
    induction a using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.C_mul']; exact M.smul_mem c hx
    | add p q hp hq => rw [add_mul]; exact M.add_mem hp hq
    | mul_X p i hp =>
      rw [show p * X i * x = X i * (p * x) by ring]
      exact hX i _ hp
  induction hg using Submodule.span_induction with
  | mem y hy => rw [hM]; exact Submodule.subset_span hy
  | zero => exact M.zero_mem
  | add y z _ _ hy hz => exact M.add_mem hy hz
  | smul a y _ hy => exact hmul a y hy

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem decompose_coe_eq_homogeneousComponent {σ L : Type} [Field L]
    (g : MvPolynomial σ L) (n : ℕ) :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := L)
    (((DirectSum.decompose (homogeneousSubmodule σ L)) g) n : MvPolynomial σ L) =
      homogeneousComponent n g := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := L)
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  by_cases hn : n ∈ Finset.range (g.totalDegree + 1)
  · rw [Finset.sum_eq_single n]
    · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g)
    · intro i _ hi
      exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) hi
    · intro h; exact absurd hn h
  · rw [homogeneousComponent_eq_zero]
    · refine Finset.sum_eq_zero fun i hi => ?_
      exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) (by rintro rfl; exact hn hi)
    · simp at hn; omega

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem linearIndependent_map_algebraMap {σ K L : Type} [Field K] [Field L] [Algebra K L] {ι : Type} {v : ι → MvPolynomial σ K}
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => MvPolynomial.map (algebraMap K L) (v i)) := by
  have h := Module.Flat.linearIndependent_one_tmul (S := L) hv
  have h2 := h.map' (algebraTensorAlgEquiv K L).toLinearEquiv.toLinearMap
    (algebraTensorAlgEquiv K L).toLinearEquiv.ker
  have he : (fun i => MvPolynomial.map (algebraMap K L) (v i)) =
      (algebraTensorAlgEquiv K L).toLinearEquiv.toLinearMap ∘ fun i => (1 : L) ⊗ₜ[K] v i := by
    funext i
    simp [algebraTensorAlgEquiv_tmul]
  rw [he]
  exact h2

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem finrank_span_map_algebraMap_eq {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (W : Submodule K (MvPolynomial σ K)) [FiniteDimensional K W] :
    Module.finrank L (Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (W : Set (MvPolynomial σ K)))) =
      Module.finrank K W := by
  let b := Module.finBasis K W
  let v : Fin (Module.finrank K W) → MvPolynomial σ L :=
    fun i => MvPolynomial.map (algebraMap K L) (b i : MvPolynomial σ K)
  have hli : LinearIndependent L v :=
    linearIndependent_map_algebraMap (b.linearIndependent.map' W.subtype (Submodule.ker_subtype W))
  have hspan : Submodule.span L (Set.range v) =
      Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (W : Set (MvPolynomial σ K))) := by
    apply le_antisymm
    · refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (b i).2, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, hw, rfl⟩
      have hw' : (⟨w, hw⟩ : W) ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
      have key : ∀ x : W, x ∈ Submodule.span K (Set.range b) →
          MvPolynomial.map (algebraMap K L) (x : MvPolynomial σ K) ∈
            (Submodule.span L (Set.range v)).restrictScalars K := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
        | smul c y _ hy =>
          have : MvPolynomial.map (algebraMap K L) ((c • y : W) : MvPolynomial σ K) =
              c • MvPolynomial.map (algebraMap K L) (y : MvPolynomial σ K) := by
            simp [MvPolynomial.smul_eq_C_mul, Algebra.smul_def]
          rw [this]
          exact Submodule.smul_mem _ c hy
      exact key _ hw'
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]


open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem _root_.GlobalTheory.HilbBaseChange.idealHilbertPoly_map : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (N : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L), ∀ n : ℕ, homogeneousComponent n g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) ∧ _root_.GlobalTheory.idealHilbertPoly (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) = _root_.GlobalTheory.idealHilbertPoly P := by
  intro K L _ _ _ N P hP
  have hW : ∀ n : ℕ,
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).restrictScalars L ⊓
          homogeneousSubmodule (Fin N) L n =
        Submodule.span L ((MvPolynomial.map (algebraMap K L)) ''
          ((P.restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K (MvPolynomial (Fin N) K)) :
            Set (MvPolynomial (Fin N) K))) := by
    intro n
    apply le_antisymm
    · rintro g ⟨hg1, hg2⟩
      have := homogeneousComponent_mem_span_map_homogeneous P hP (mem_span_image_of_mem_ideal_map P hg1) n
      rwa [homogeneousComponent_of_mem hg2, if_pos rfl] at this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
      exact ⟨Ideal.mem_map_of_mem _ hw1,
        (mem_homogeneousSubmodule _ _).2 (((mem_homogeneousSubmodule _ _).1 hw2).map _)⟩
  have hA : ∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L),
      ∀ n : ℕ, homogeneousComponent n g ∈
        P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) := by
    intro g hg n
    have h := homogeneousComponent_mem_span_map_homogeneous P hP (mem_span_image_of_mem_ideal_map P hg) n
    rw [← hW n] at h
    exact h.1
  refine ⟨hA, ?_⟩
  have hhomP : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) P := by
    intro i r hr
    rw [decompose_coe_eq_homogeneousComponent]
    exact hP r hr i
  have hhomQ : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) L)
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
    intro i r hr
    rw [decompose_coe_eq_homogeneousComponent]
    exact hA r hr i
  have hdim : ∀ n : ℕ,
      Module.finrank L (_root_.GlobalTheory.quotPiece
        (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) (n : ℤ)) =
      Module.finrank K (_root_.GlobalTheory.quotPiece P (n : ℤ)) := by
    intro n
    have h1 := _root_.GlobalTheory.finrank_quotPiece_add
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) n
    have h2 := _root_.GlobalTheory.finrank_quotPiece_add P n
    rw [hW n, finrank_span_map_algebraMap_eq, _root_.GlobalTheory.ProjCut.finrank_homogeneousSubmodule] at h1
    rw [_root_.GlobalTheory.ProjCut.finrank_homogeneousSubmodule] at h2
    omega
  obtain ⟨n₀, hn₀⟩ := ((_root_.GlobalTheory.eventually_finrank_quotPiece hhomQ).and
    (_root_.GlobalTheory.eventually_finrank_quotPiece hhomP)).exists_forall_of_atTop
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
  · intro a b h
    simpa using h
  · intro m
    obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (by omega)
    simp only [Set.mem_setOf_eq]
    rw [← h1, ← h2, hdim]

end GlobalTheory.HilbBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterEqOneCayleyRotation
section
open scoped Matrix
open Formalism.BasicNotions.TH

noncomputable section

namespace GlobalTheory.UnitaryCharRot

open Complex

def signatureOneOneForm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def boost : Matrix (Fin 2) (Fin 2) ℂ := !![5/4, 3/4; 3/4, 5/4]

def boostInv : Matrix (Fin 2) (Fin 2) ℂ := !![5/4, -3/4; -3/4, 5/4]

def upperUnip (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1 + t * I, -(t * I); t * I, 1 - t * I]

def lowerUnip (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1 + t * I, t * I; -(t * I), 1 - t * I]

theorem upperUnip_mem (t : ℝ) : (upperUnip t)ᴴ * signatureOneOneForm * upperUnip t = signatureOneOneForm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperUnip, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
theorem lowerUnip_mem (t : ℝ) : (lowerUnip t)ᴴ * signatureOneOneForm * lowerUnip t = signatureOneOneForm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerUnip, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
theorem boost_mem : (boost)ᴴ * signatureOneOneForm * boost = signatureOneOneForm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
theorem boostInv_mem : (boostInv)ᴴ * signatureOneOneForm * boostInv = signatureOneOneForm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boostInv, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
theorem boost_boostInv : boost * boostInv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, boostInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
theorem boostInv_boost : boostInv * boost = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, boostInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
theorem upperUnip_neg (u : ℝ) : upperUnip u * upperUnip (-u) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
theorem lowerUnip_neg (u : ℝ) : lowerUnip u * lowerUnip (-u) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
theorem upperUnip_comm (u : ℝ) : boost * upperUnip u * boostInv * upperUnip (-u) = upperUnip (3 * u) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, boostInv, upperUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
theorem lowerUnip_comm (u : ℝ) : boostInv * lowerUnip u * boost * lowerUnip (-u) = lowerUnip (3 * u) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, boostInv, lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))

theorem zeta_eq (x : ℝ) : (1 + 2 * I * x) / (1 - 2 * I * x) =
    (((1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) : ℝ) : ℂ) + (((4 * x) / (1 + 4 * x ^ 2) : ℝ) : ℂ) * I := by
  have h1 : (1 - 2 * I * x) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h3 : (1 + 4 * x ^ 2) ≠ 0 := by positivity
  rw [div_eq_iff h1, Complex.ext_iff]
  generalize hc : (1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) = c
  generalize hs : (4 * x) / (1 + 4 * x ^ 2) = s
  simp
  subst hc hs
  constructor <;> field_simp <;> ring
theorem zeta_eq' (x : ℝ) : (1 - 2 * I * x) / (1 + 2 * I * x) =
    (((1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) : ℝ) : ℂ) - (((4 * x) / (1 + 4 * x ^ 2) : ℝ) : ℂ) * I := by
  have h1 : (1 + 2 * I * x) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h3 : (1 + 4 * x ^ 2) ≠ 0 := by positivity
  rw [div_eq_iff h1, Complex.ext_iff]
  generalize hc : (1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) = c
  generalize hs : (4 * x) / (1 + 4 * x ^ 2) = s
  simp
  subst hc hs
  constructor <;> field_simp <;> ring

theorem rot_eq (x : ℝ) : upperUnip x * lowerUnip (2 * x / (1 + 4 * x ^ 2)) * upperUnip x =
    !![(1 + 2 * I * x) / (1 - 2 * I * x), 0; 0, (1 - 2 * I * x) / (1 + 2 * I * x)] := by
  have h3 : (1 + 4 * x ^ 2) ≠ 0 := by positivity
  rw [zeta_eq, zeta_eq']
  generalize hc : (1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) = c
  generalize hs : (4 * x) / (1 + 4 * x ^ 2) = s
  generalize hy : 2 * x / (1 + 4 * x ^ 2) = y
  ext i j; fin_cases i <;> fin_cases j <;> simp [upperUnip, lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    subst hc hs hy <;> (try constructor) <;> field_simp <;> ring

variable {R S : ℕ}

def pl (i0 : Fin R) (j0 : Fin S) : Fin 2 → Fin R ⊕ Fin S := ![Sum.inl i0, Sum.inr j0]

def emb (i0 : Fin R) (j0 : Fin S) : Matrix (Fin R ⊕ Fin S) (Fin 2) ℂ :=
  Matrix.of fun k p => if k = pl i0 j0 p then 1 else 0

def inPlane (i0 : Fin R) (j0 : Fin S) (M : Matrix (Fin 2) (Fin 2) ℂ) : Mat R S :=
  1 + emb i0 j0 * (M - 1) * (emb i0 j0)ᵀ

variable (i0 : Fin R) (j0 : Fin S)
theorem embT_emb : (emb i0 j0)ᵀ * emb i0 j0 = 1 := by
  ext p q; fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, emb, pl, Fintype.sum_sum_type, Matrix.one_apply, Function.swap]
theorem emb_ct : (emb i0 j0)ᴴ = (emb i0 j0)ᵀ := by
  ext p k; simp only [emb, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]; split_ifs <;> simp
theorem embT_ct : ((emb i0 j0)ᵀ)ᴴ = emb i0 j0 := by
  ext k p; simp only [emb, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]; split_ifs <;> simp
theorem Jm_diag : Jm R S = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
  ext k l; rcases k with k | k <;> rcases l with l | l <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
theorem sig_diag : signatureOneOneForm = Matrix.diagonal ![1, -1] := by
  ext p q; fin_cases p <;> fin_cases q <;> simp [signatureOneOneForm]
theorem Jm_emb : Jm R S * emb i0 j0 = emb i0 j0 * signatureOneOneForm := by
  rw [Jm_diag, sig_diag]
  ext k p; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; rcases k with k | k <;> fin_cases p <;> simp [emb, pl] <;>
    split_ifs <;> simp
theorem embT_Jm : (emb i0 j0)ᵀ * Jm R S = signatureOneOneForm * (emb i0 j0)ᵀ := by
  rw [Jm_diag, sig_diag]
  ext p k; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; rcases k with k | k <;> fin_cases p <;> simp [emb, pl] <;>
    split_ifs <;> simp
theorem inPlane_diag (a b : ℂ) : inPlane i0 j0 !![a, 0; 0, b] = Matrix.fromBlocks (Matrix.diagonal (Function.update 1 i0 a)) 0 0
    (Matrix.diagonal (Function.update 1 j0 b)) := by
  ext k l; rcases k with k | k <;> rcases l with l | l <;>
    simp [inPlane, emb, pl, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.diagonal_apply, Function.update_apply, Function.swap]
  · by_cases h1 : k = i0 <;> by_cases h2 : l = i0 <;> simp [h1, h2]
    subst h1; simp [Ne.symm h2]
  · by_cases h1 : k = j0 <;> by_cases h2 : l = j0 <;> simp [h1, h2]
    subst h1; simp [Ne.symm h2]
theorem inPlane_one : inPlane i0 j0 1 = 1 := by simp [inPlane]
theorem inPlane_mul (M M' : Matrix (Fin 2) (Fin 2) ℂ) : inPlane i0 j0 (M * M') = inPlane i0 j0 M * inPlane i0 j0 M' := by
  have e3 : ∀ Z : Matrix (Fin 2) (Fin R ⊕ Fin S) ℂ, (emb i0 j0)ᵀ * (emb i0 j0 * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, embT_emb, Matrix.one_mul]
  have hM : M * M' - 1 = (M - 1) + (M' - 1) + (M - 1) * (M' - 1) := by noncomm_ring
  simp only [inPlane, hM, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, e3]
  abel
theorem inPlane_ct (M : Matrix (Fin 2) (Fin 2) ℂ) : (inPlane i0 j0 M)ᴴ = inPlane i0 j0 Mᴴ := by
  simp [inPlane, Matrix.conjTranspose_mul, emb_ct, embT_ct, Matrix.mul_assoc]
theorem inPlane_mem (M : Matrix (Fin 2) (Fin 2) ℂ) (h : Mᴴ * signatureOneOneForm * M = signatureOneOneForm) :
    (inPlane i0 j0 M)ᴴ * Jm R S * inPlane i0 j0 M = Jm R S := by
  have e1 : ∀ Z : Matrix (Fin R ⊕ Fin S) (Fin R ⊕ Fin S) ℂ, (emb i0 j0)ᵀ * (Jm R S * Z) = signatureOneOneForm * ((emb i0 j0)ᵀ * Z) :=
    fun Z => by rw [← Matrix.mul_assoc, embT_Jm, Matrix.mul_assoc]
  have e2 : ∀ Z : Matrix (Fin 2) (Fin R ⊕ Fin S) ℂ, Jm R S * (emb i0 j0 * Z) = emb i0 j0 * (signatureOneOneForm * Z) :=
    fun Z => by rw [← Matrix.mul_assoc, Jm_emb, Matrix.mul_assoc]
  have e3 : ∀ Z : Matrix (Fin 2) (Fin R ⊕ Fin S) ℂ, (emb i0 j0)ᵀ * (emb i0 j0 * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, embT_emb, Matrix.one_mul]
  have key : (Mᴴ - 1) * signatureOneOneForm + signatureOneOneForm * (M - 1) + (Mᴴ - 1) * (signatureOneOneForm * (M - 1)) = 0 := by
    have : (Mᴴ - 1) * signatureOneOneForm + signatureOneOneForm * (M - 1) + (Mᴴ - 1) * (signatureOneOneForm * (M - 1)) = Mᴴ * signatureOneOneForm * M - signatureOneOneForm := by noncomm_ring
    rw [this, h, sub_self]
  have key' : emb i0 j0 * ((Mᴴ - 1) * (signatureOneOneForm * (emb i0 j0)ᵀ)) + emb i0 j0 * (signatureOneOneForm * ((M - 1) * (emb i0 j0)ᵀ)) +
      emb i0 j0 * ((Mᴴ - 1) * (signatureOneOneForm * ((M - 1) * (emb i0 j0)ᵀ))) = 0 := by
    have := congrArg (fun X => emb i0 j0 * X * (emb i0 j0)ᵀ) key
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero] at this
    exact this
  rw [inPlane_ct]
  simp only [inPlane, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, e1, e2, e3, embT_Jm]
  rw [← sub_eq_zero]; rw [← sub_eq_zero] at key'; rw [← key']; abel

theorem char_eq_one_rot : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∀ (i0 : Fin R) (j0 : Fin S) (x : ℝ),
      χ (Matrix.fromBlocks (Matrix.diagonal (Function.update 1 i0 ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)))) 0 0
        (Matrix.diagonal (Function.update 1 j0 ((1 - 2 * Complex.I * x) / (1 + 2 * Complex.I * x))))) = 1 := by
  intro R S χ hmul _ hne i0 j0 x
  have hG : ∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S →
      (g * h)ᴴ * Jm R S * (g * h) = Jm R S := by
    intro g h hg hh
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Jm R S * (g * h) = hᴴ * (gᴴ * Jm R S * g) * h := by simp only [Matrix.mul_assoc]
      _ = Jm R S := by rw [hg, hh]
  have h1mem : (1 : Mat R S)ᴴ * Jm R S * 1 = Jm R S := by simp
  have h1 : χ 1 = 1 := by
    have e := hmul 1 1 h1mem h1mem
    rw [Matrix.one_mul] at e
    exact mul_left_cancel₀ (hne 1 h1mem) (e.symm.trans (mul_one _).symm)
  have key : ∀ a b c d : Mat R S, aᴴ * Jm R S * a = Jm R S → bᴴ * Jm R S * b = Jm R S →
      cᴴ * Jm R S * c = Jm R S → dᴴ * Jm R S * d = Jm R S → a * c = 1 → b * d = 1 → χ (a * b * c * d) = 1 := by
    intro a b c d ha hb hc hd hac hbd
    have hab := hG a b ha hb
    have habc := hG _ c hab hc
    rw [hmul _ d habc hd, hmul _ c hab hc, hmul a b ha hb]
    have e1 := hmul a c ha hc
    have e2 := hmul b d hb hd
    rw [hac, h1] at e1
    rw [hbd, h1] at e2
    linear_combination (-(χ b * χ d)) * e1 - e2
  have hn : ∀ t : ℝ, χ (inPlane i0 j0 (upperUnip t)) = 1 := by
    intro t
    have e := key (inPlane i0 j0 boost) (inPlane i0 j0 (upperUnip (t / 3))) (inPlane i0 j0 boostInv) (inPlane i0 j0 (upperUnip (-(t / 3))))
      (inPlane_mem i0 j0 _ boost_mem) (inPlane_mem i0 j0 _ (upperUnip_mem _)) (inPlane_mem i0 j0 _ boostInv_mem) (inPlane_mem i0 j0 _ (upperUnip_mem _))
      (by rw [← inPlane_mul, boost_boostInv, inPlane_one]) (by rw [← inPlane_mul, upperUnip_neg, inPlane_one])
    rwa [← inPlane_mul, ← inPlane_mul, ← inPlane_mul, upperUnip_comm, show 3 * (t / 3) = t by ring] at e
  have hn' : ∀ t : ℝ, χ (inPlane i0 j0 (lowerUnip t)) = 1 := by
    intro t
    have e := key (inPlane i0 j0 boostInv) (inPlane i0 j0 (lowerUnip (t / 3))) (inPlane i0 j0 boost) (inPlane i0 j0 (lowerUnip (-(t / 3))))
      (inPlane_mem i0 j0 _ boostInv_mem) (inPlane_mem i0 j0 _ (lowerUnip_mem _)) (inPlane_mem i0 j0 _ boost_mem) (inPlane_mem i0 j0 _ (lowerUnip_mem _))
      (by rw [← inPlane_mul, boostInv_boost, inPlane_one]) (by rw [← inPlane_mul, lowerUnip_neg, inPlane_one])
    rwa [← inPlane_mul, ← inPlane_mul, ← inPlane_mul, lowerUnip_comm, show 3 * (t / 3) = t by ring] at e
  have m := inPlane_mem i0 j0 _ (upperUnip_mem x)
  have m' := inPlane_mem i0 j0 _ (lowerUnip_mem (2 * x / (1 + 4 * x ^ 2)))
  rw [← inPlane_diag, ← rot_eq, inPlane_mul, inPlane_mul, hmul _ _ (hG _ _ m m') m, hmul _ _ m m']
  simp only [hn, hn', mul_one]

end GlobalTheory.UnitaryCharRot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompactsStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryAdelic_prod_local_compacts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (D : ∀ v : AwayP p, Set (Gv G v)), (∀ v, IsCompact (D v)) → (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D v ⊆ IntV G v) → IsCompact {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_prod_local) | (exact GlobalTheory.OrbFinAf.isCompact_prod_local) | (intros; apply GlobalTheory.OrbFinAf.isCompact_prod_local  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompactStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryPointsAtPlace_fst_mem_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K → IsCompact {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem) | (exact GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem) | (intros; apply GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegralStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEffectivePicClass_add_integral : ∀ {X : Scheme.{0}} [IsIntegral X] (a b : GlobalTheory.CechPic.Pic X), GlobalTheory.EffBound.Eff a → GlobalTheory.EffBound.Eff b → GlobalTheory.EffBound.Eff (a + b) := by
  first | exact @GlobalTheory.EffBound.eff_add | exact GlobalTheory.EffBound.eff_add | (intros; apply GlobalTheory.EffBound.eff_add <;> assumption)
end

