module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ChowHt

section Sizes

variable {F K : Type} [Field F] [Field K] {N n : ℕ}

def finSize (w : Matrix (Fin N) (Fin n) F) (φ : F →+* K) (v : AbsoluteValue K ℝ) (y : Fin N → K) : ℝ :=
  ⨆ k, v (∑ j, φ (w j k) * y j)

def archSize (A : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, ‖∑ j, A j i * y j‖ ^ 2)

theorem pointHeight_eq [NumberField F] [NumberField K] [Algebra F K] (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (y : Fin N → K) :
    pointHeight w A y = ((∑ᶠ v : FinitePlace K, Real.log (finSize w (algebraMap F K) v.1 y)) +
      ∑ τ : K →+* ℂ, Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j))) /
        (Module.finrank ℚ K : ℝ) := rfl

theorem le_finSize (w : Matrix (Fin N) (Fin n) F) (φ : F →+* K) (v : AbsoluteValue K ℝ) (y : Fin N → K) (k : Fin n) :
    v (∑ j, φ (w j k) * y j) ≤ finSize w φ v y :=
  le_ciSup (f := fun k => v (∑ j, φ (w j k) * y j)) (Set.finite_range _).bddAbove k

theorem finSize_nonneg (w : Matrix (Fin N) (Fin n) F) (φ : F →+* K) (v : AbsoluteValue K ℝ) (y : Fin N → K) :
    0 ≤ finSize w φ v y := Real.iSup_nonneg fun _ => v.nonneg _

theorem finSize_smul (w : Matrix (Fin N) (Fin n) F) (φ : F →+* K) (v : AbsoluteValue K ℝ) (c : K) (y : Fin N → K) :
    finSize w φ v (c • y) = v c * finSize w φ v y := by
  rw [finSize, finSize, Real.mul_iSup_of_nonneg (v.nonneg c)]
  refine iSup_congr fun k => ?_
  rw [← map_mul, Finset.mul_sum]
  exact congrArg v (Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _)

theorem archSize_smul (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (y : Fin N → ℂ) :
    archSize A (c • y) = ‖c‖ * archSize A y := by
  rw [archSize, archSize, ← Real.sqrt_sq (norm_nonneg c), ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [← mul_pow, ← norm_mul, Finset.mul_sum]
  exact congrArg (‖·‖ ^ 2) (Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _)

theorem finSize_pos {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤) (φ : F →+* K)
    (v : AbsoluteValue K ℝ) {y : Fin N → K} (hy : y ≠ 0) : 0 < finSize w φ v y := by
  refine (finSize_nonneg w φ v y).lt_of_ne' fun h => hy (funext fun j => ?_)
  have h0 : ∀ k, ∑ j, φ (w j k) * y j = 0 := fun k =>
    v.eq_zero.1 (le_antisymm (h ▸ le_finSize w φ v y k) (v.nonneg _))
  have key : ∀ u ∈ Submodule.span F (Set.range w.col), ∑ j, φ (u j) * y j = 0 := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; exact h0 k
    | zero => simp
    | add a b _ _ ha hb => simp [add_mul, Finset.sum_add_distrib, ha, hb]
    | smul c a _ ha => simp [mul_assoc, ← Finset.mul_sum, ha]
  simpa [Pi.single_apply, apply_ite φ] using key (Pi.single j 1) (hw ▸ trivial)

theorem archSize_pos {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {y : Fin N → ℂ} (hy : y ≠ 0) :
    0 < archSize A y := by
  refine Real.sqrt_pos.2 ((Finset.sum_nonneg fun _ _ => sq_nonneg _).lt_of_ne' fun h => hy ?_)
  refine Matrix.eq_zero_of_vecMul_eq_zero hA (funext fun i => ?_)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h i (Finset.mem_univ i)
  simpa [Matrix.vecMul, dotProduct, mul_comm] using this

theorem norm_pairing_le {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (u y : Fin N → ℂ) :
    ‖∑ j, u j * y j‖ ≤ frameNorm A u * archSize A y := by
  have e : ∑ j, u j * y j = ∑ i, A⁻¹.mulVec u i * ∑ j, A j i * y j := by
    conv_lhs => rw [← Matrix.one_mulVec u, ← A.mul_nonsing_inv hA.isUnit, ← Matrix.mulVec_mulVec]
    generalize A⁻¹.mulVec u = c
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

variable {Ω : Type} [Field Ω] [Algebra F Ω]

abbrev coordField (F : Type) [Field F] [Algebra F Ω] (y : Fin N → Ω) : IntermediateField F Ω :=
  IntermediateField.adjoin F (Set.range y)

instance numberField_coordField [NumberField F] [Algebra.IsAlgebraic F Ω] (y : Fin N → Ω) :
    NumberField (coordField F y) :=
  have : FiniteDimensional F (coordField F y) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  NumberField.of_module_finite F _

def vecHeight [NumberField F] [Algebra.IsAlgebraic F Ω] (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (y : Fin N → Ω) : ℝ :=
  pointHeight w A (K := coordField F y) fun j => ⟨y j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩

end Sizes

structure HermSys (F : Type) [Field F] [NumberField F] extends LinSys F where

  n : ℕ

  w : Matrix (Fin N) (Fin n) F

  A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ

  abelian₂ : ℝ

namespace HermSys

variable {F : Type} [Field F] [NumberField F] (T : HermSys F)

def lattice : Submodule (𝓞 F) (Fin T.N → F) := Submodule.span (𝓞 F) (Set.range T.w.col)

def normAt {E : Type} [Field E] [Algebra F E] (τ : E →+* ℂ) (u : Fin T.N → E) : ℝ :=
  frameNorm (T.A (τ.comp (algebraMap F E))) fun j => τ (u j)

def Spans : Prop := Submodule.span F (Set.range T.w.col) = ⊤

structure IsAlgebraicData : Prop where

  variety : T.IsVariety

  indep : T.Indep

  spans : T.Spans

  bpf : T.BasePointFree

def Hermitian : Prop := ∀ σ, (T.A σ).det ≠ 0

def ConjInvariant : Prop := ConjCompat T.A

def NormsLe : Prop := ∀ (k : Fin T.n) (σ : F →+* ℂ), T.normAt σ (T.w.col k) ≤ T.abelian₂

def IntGenerates : Prop := ∀ u ∈ T.lattice, u ∈ Submodule.span ℤ (Set.range T.w.col)

structure ShortGenerators : Prop where

  int : T.IntGenerates

  le : T.NormsLe

  one_le : 1 ≤ T.abelian₂

def IsHeight (h : ℝ) : Prop :=
  ∃ (d : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), 0 < d ∧ IsChowForm T.imageIdeal T.D d f ∧
    ((T.D : ℝ) + 1) * d * h = formHeight d T.w T.A f

theorem isHeight_iff {h : ℝ} : T.IsHeight h ↔ ∃ (d : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F),
    IsChowForm T.imageIdeal T.D d f ∧ ((T.D : ℝ) + 1) * d * h = formHeight d T.w T.A f :=
  ⟨fun ⟨d, f, _, hf⟩ => ⟨d, f, hf⟩, fun ⟨d, f, hf, e⟩ => ⟨d, f, hf.isChowFormInt.pos, hf, e⟩⟩

theorem isHeight_of_isChowForm {d : ℕ} {f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F}
    (hf : IsChowForm T.imageIdeal T.D d f) : T.IsHeight (formHeight d T.w T.A f / (((T.D : ℝ) + 1) * d)) :=
  T.isHeight_iff.2 ⟨d, f, hf, mul_div_cancel₀ _
    (mul_ne_zero (by positivity) (Nat.cast_ne_zero.2 hf.isChowFormInt.pos.ne'))⟩

def baseChange (E : Type) [Field E] [NumberField E] [Algebra F E] : HermSys E where
  toLinSys := T.toLinSys.baseChange E
  n := T.n
  w := T.w.map (algebraMap F E)
  A τ := T.A (τ.comp (algebraMap F E))
  abelian₂ := T.abelian₂

section Norms

variable {K : Type} [Field K] {φ : F →+* K} {σ : F →+* ℂ}

variable {T}

end Norms

def ptHeight {Ω : Type} [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω] (x : T.Pt Ω) : ℝ :=
  vecHeight T.w T.A (T.coords x.1)

abbrev geomPts (E : Type) [Field E] [Algebra F E] (I : (T.toLinSys.baseChange E).Y.IdealSheafData) :
    Set ((T.toLinSys.baseChange E).Pt (AlgebraicClosure E)) :=
  (T.toLinSys.baseChange E).subPts I (AlgebraicClosure E)

def cycleHeight (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E]
    (I : (T.toLinSys.baseChange E).Y.IdealSheafData) : ℝ :=
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure E) := Algebra.IsAlgebraic.trans F E _
  ∑ᶠ x ∈ T.geomPts E I, T.ptHeight (LinSys.toBase x)

abbrev linSection (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) :
    (T.toLinSys.baseChange E).Y.IdealSheafData :=
  (T.toLinSys.baseChange E).cut s

end HermSys

structure Tuple (F : Type) [Field F] [NumberField F] extends HermSys F where

  bd : Closeds Y

  j₀ : ℕ

  th : (lbPow L j₀).Sec

namespace Tuple

variable {F : Type} [Field F] [NumberField F] (T : Tuple F)

def U : T.Y.Opens := T.bd.compl

structure IsGeometric : Prop where

  alg : T.IsAlgebraicData

  bd_ne : T.bd ≠ ⊤

structure IsBirationalOffBoundary : Prop where

  birational : T.Birational

  noContract : T.NoContract T.bd

  one_le : 1 ≤ T.j₀

  th_ne : T.th ≠ 0

  th_vanish : ∀ y ∈ T.bd, y ∉ nonzeroLocus T.th

def theta (h : ℝ) : ℝ := T.n * T.D * T.j₀ * T.del * (2 + |h| + Real.log T.abelian₂)

def InOpen (E : Type) [Field E] [Algebra F E] (I : (T.toLinSys.baseChange E).Y.IdealSheafData) : Prop :=
  ∀ y ∈ I.support, T.toLinSys.bcFst E y ∈ T.U

structure IsGoodSection (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) : Prop where

  finiteEtale : (T.toLinSys.baseChange E).IsFiniteEtaleSub (T.linSection E s)

  inOpen : T.InOpen E (T.linSection E s)

theorem IsGoodSection.finite_geomPts {T : Tuple F} {E : Type} [Field E] [Algebra F E] {s : Fin T.D → Fin T.N → E}
    (h : T.IsGoodSection E s) : (T.geomPts E (T.linSection E s)).Finite :=
  h.finiteEtale.finite.finite_subPts _

end Tuple

abbrev projTuple (M : ℕ) : Tuple ℚ where
  toLinSys := projSys ℚ M
  n := M + 1
  w := 1
  A _ := 1
  abelian₂ := 1
  bd := (ProjSpace.chart ℚ M (Fin.last M)).compl
  j₀ := 1
  th := secToPow (ProjSpace.coord ℚ M (Fin.last M)) 1

namespace projTuple

variable (M : ℕ)

theorem spans : (projTuple M).Spans := top_le_iff.1 fun u _ => by
  rw [pi_eq_sum_univ' u]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, ?_⟩)
  funext j
  simp [Matrix.one_apply, Pi.single_apply]

theorem shortGenerators : (projTuple M).ShortGenerators := by
  refine ⟨fun u hu => ?_, fun k σ => ?_, le_rfl⟩
  · induction hu using Submodule.span_induction with
    | mem _ h => exact Submodule.subset_span h
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c a _ ha =>
      obtain ⟨z, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective c
      rw [eq_intCast Rat.ringOfIntegersEquiv.symm z, Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ ha
  · simp [HermSys.normAt, frameNorm, Matrix.one_apply, apply_ite]

end projTuple

end GlobalTheory.Adelic
