module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasurablePartitionOfUnityUnitLogTranslate
section
open NumberField MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory
namespace UnitLogPartition

open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

theorem exists_nonneg_hasSum_lattice_translates (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ η : V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ z, 0 ≤ η z) ∧
      ∀ y, HasSum (fun l : L => η (y + l)) 1 := by
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_radius_lattice_translate_norm_le V L
  let b : ContDiffBump (0 : V) := ⟨R, R + 1, hR, by linarith⟩
  have hφc : HasCompactSupport (b : V → ℝ) := b.hasCompactSupport
  have hφs : ContDiff ℝ ∞ (b : V → ℝ) := b.contDiff
  have hlf := GlobalTheory.PeriodicPartition.locallyFinite_support_translate L b hφc
  set S : V → ℝ := fun z => ∑ᶠ l : L, b (z + l) with hS
  have hSs : ContDiff ℝ ∞ S := by
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : L) (z : V) => b (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  have hSp : ∀ (l : L) z, S (z + l) = S z := by
    intro l z
    show ∑ᶠ m : L, b (z + l + m) = ∑ᶠ m : L, b (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : L => b (z + m))]
    simp [add_assoc]
  have hSpos : ∀ z, 0 < S z := by
    intro z
    obtain ⟨l, hl⟩ := hcov z
    have h1 := single_le_finsum (f := fun l : L => b (z + l)) l (hlf.point_finite z)
      (fun l => b.nonneg)
    have h2 : b (z + l) = 1 := b.one_of_mem_closedBall (by simpa using hl)
    simp only [h2] at h1
    exact lt_of_lt_of_le one_pos h1
  refine ⟨fun z => b z / S z, hφs.div hSs fun z => (hSpos z).ne', ?_,
    fun z => div_nonneg b.nonneg (hSpos z).le, fun y => ?_⟩
  · simp only [div_eq_mul_inv]
    exact hφc.mul_right
  · simp only [hSp]
    have hfin : (Function.support fun l : L => b (y + l)).Finite := hlf.point_finite y
    have h1 : HasSum (fun l : L => b (y + l)) (S y) := by
      have hs : Summable (fun l : L => b (y + l)) := summable_of_hasFiniteSupport hfin
      have := hs.hasSum
      rwa [tsum_eq_finsum hfin] at this
    have := h1.div_const (S y)
    rwa [div_self (hSpos y).ne'] at this

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I] {φ : I → K →+* ℂ}

def idx (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) : I := (hφ w.embedding).exists.choose

theorem idx_spec (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) :
    w.embedding = φ (idx hφ w) ∨ w.embedding = ComplexEmbedding.conjugate (φ (idx hφ w)) :=
  (hφ w.embedding).exists.choose_spec

theorem apply_eq_norm (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) (x : K) :
    w x = ‖φ (idx hφ w) x‖ := by
  rcases idx_spec hφ w with h | h
  · rw [← norm_embedding_eq, h]
  · rw [← norm_embedding_eq, h, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

theorem idx_surjective (hφ : GlobalTheory.CMVal.IsCMType φ) (i : I) : ∃ w, idx hφ w = i := by
  refine ⟨InfinitePlace.mk (φ i), ?_⟩
  exact (hφ (InfinitePlace.mk (φ i)).embedding).unique (idx_spec hφ _) (embedding_mk_eq (φ i))

theorem ulog_idx [_root_.NumberField.IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = w.mult * Real.log (w (u : K)) := by
  unfold GlobalTheory.HeckeTheta.ulog
  rw [(IsTotallyComplex.isComplex w).mult_eq_two, ← apply_eq_norm hφ, Real.log_pow]

theorem sum_ulog_idx [_root_.NumberField.IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = 0 := by
  simp only [ulog_idx hφ]
  exact sum_mult_mul_log u

def mean (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : ℝ :=
  (∑ w : InfinitePlace K, y (idx hφ w)) / Fintype.card (InfinitePlace K)

def proj (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : logSpace K :=
  fun w => y (idx hφ w.1) - mean hφ y

theorem proj_add_ulog [_root_.NumberField.IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) (u : (𝓞 K)ˣ) :
    proj hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = proj hφ y + logEmbedding K (Additive.ofMul u) := by
  funext w
  have hm : mean hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = mean hφ y := by
    unfold mean
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_ulog_idx hφ, add_zero]
  simp only [proj, hm, Pi.add_apply, logEmbedding_component, ← ulog_idx hφ]
  ring

theorem continuous_proj (hφ : GlobalTheory.CMVal.IsCMType φ) : Continuous (proj hφ) := by
  unfold proj mean
  fun_prop

end UnitLogPartition


open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace UnitLogPartition in
theorem exists_measurable_nonneg_hasSum_ulog_translates : ∀ (K : Type) [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ →
    ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧
      (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧
      ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  classical
  intro K _ _ _ I _ φ hφ
  obtain ⟨η, hη, hc, h0, hs⟩ := exists_nonneg_hasSum_lattice_translates (logSpace K) (unitLattice K)
  refine ⟨fun y => η (proj hφ y) / Nat.card (torsion K), ?_, ?_, ?_, ?_⟩
  · exact ((hη.continuous.comp (continuous_proj hφ)).div_const _).measurable
  · intro y
    exact div_nonneg (h0 _) (Nat.cast_nonneg _)
  · intro y
    have h1 := ((Additive.ofMul.trans (logEmbeddingEquiv K).toEquiv).hasSum_iff).mpr (hs (proj hφ y))
    have h2 := GlobalTheory.UnitPartition.hasSum_quot (torsion K) _ _ h1
    convert h2 using 2 with u
    beta_reduce
    rw [proj_add_ulog hφ]
    rfl
  · obtain ⟨ρ, hρ⟩ := hc.isCompact.isBounded.exists_norm_le
    set n : ℝ := (Fintype.card (InfinitePlace K) : ℝ) with hn_def
    refine ⟨2 * (n * |ρ|), fun y hy i j => ?_⟩
    have hη0 : η (proj hφ y) ≠ 0 := fun h => hy (by simp [h])
    have hn : ‖proj hφ y‖ ≤ ρ := hρ _ (subset_tsupport _ hη0)
    set d : InfinitePlace K → ℝ := fun w => y (idx hφ w) - mean hφ y with hd
    have hn1 : (1 : ℝ) ≤ n := by
      rw [hn_def]; exact Nat.one_le_cast.mpr (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
    have hsub : ∀ w : {w : InfinitePlace K // w ≠ w₀}, |d w.1| ≤ |ρ| := fun w =>
      ((norm_le_pi_norm (proj hφ y) w).trans hn).trans (le_abs_self ρ)
    have hsum : ∑ w, d w = 0 := by
      have hn0 : n ≠ 0 := by positivity
      simp only [hd, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mean]
      rw [← hn_def, mul_div_cancel₀ _ hn0, sub_self]
    have hall : ∀ w, |d w| ≤ n * |ρ| := by
      intro w
      by_cases hw : w = w₀
      · rw [hw]
        rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
        rw [eq_neg_of_add_eq_zero_left hsum, abs_neg]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ |ρ| fun v _ => hsub v).trans ?_
        rw [nsmul_eq_mul]
        gcongr
        rw [Finset.card_univ, hn_def]
        exact_mod_cast Fintype.card_subtype_le _
      · exact (hsub ⟨w, hw⟩).trans (le_mul_of_one_le_left (abs_nonneg _) hn1)
    obtain ⟨v, rfl⟩ := idx_surjective hφ i
    obtain ⟨v', rfl⟩ := idx_surjective hφ j
    have e : y (idx hφ v) - y (idx hφ v') = d v - d v' := by simp [hd]
    rw [e]
    linarith [le_abs_self (d v), neg_abs_le (d v'), hall v, hall v']

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbedding
section
open Formalism.UG GlobalTheory.SatakeWeyl

open Matrix

namespace GlobalTheory.SatakeWeyl.InclusionMultiplication

variable {L : Type} [Field L] {n r : ℕ}

def incl (L : Type) [Field L] (e : Fin r → Fin n) : Matrix (Fin n) (Fin r) L :=
  Matrix.of fun a i => if a = e i then 1 else 0

theorem incl_mul_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix (Fin r) p L)
    (i : Fin r) (j : p) : (incl L e * M) (e i) j = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem incl_mul_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix (Fin r) p L)
    {a : Fin n} (ha : a ∉ Set.range e) (j : p) : (incl L e * M) a j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : a ≠ e i := fun h => ha ⟨i, h.symm⟩
  simp [incl, this]

theorem mul_inclT_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix p (Fin r) L)
    (i : p) (j : Fin r) : (M * (incl L e)ᵀ) i (e j) = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem mul_inclT_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix p (Fin r) L)
    (i : p) {a : Fin n} (ha : a ∉ Set.range e) : (M * (incl L e)ᵀ) i a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : a ≠ e j := fun h => ha ⟨j, h.symm⟩
  simp [incl, this]

theorem inclT_mul_incl {e : Fin r → Fin n} (he : Function.Injective e) : (incl L e)ᵀ * incl L e = 1 := by
  ext i j
  simp [Matrix.mul_apply, incl, Function.swap, he.eq_iff, Matrix.one_apply, eq_comm]

theorem antiJ_apply (i j : Fin n) : antiJ L n i j = if i.rev = j then 1 else 0 := by
  have : (i.val + j.val + 1 = n) ↔ i.rev = j := by
    have := i.2
    rw [Fin.ext_iff, Fin.val_rev]; omega
  simp only [antiJ, this]

theorem antiJ_transpose : (antiJ L n)ᵀ = antiJ L n := by
  ext i j
  simp only [Matrix.transpose_apply, antiJ, add_comm i.val j.val]

theorem antiJ_mul_incl {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    antiJ L n * incl L e = incl L e * antiJ L r := by
  ext a i
  have h1 : (antiJ L n * incl L e) a i = incl L e a.rev i := by
    simp [Matrix.mul_apply, antiJ_apply]
  have h2 : (incl L e * antiJ L r) a i = incl L e a i.rev := by
    simp [Matrix.mul_apply, antiJ_apply, Fin.rev_eq_iff]
  rw [h1, h2]
  simp [incl, hr, Fin.rev_eq_iff]

theorem inclT_mul_antiJ {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    (incl L e)ᵀ * antiJ L n = antiJ L r * (incl L e)ᵀ := by
  have := congrArg Matrix.transpose (antiJ_mul_incl (L := L) hr)
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, antiJ_transpose, antiJ_transpose] at this

def ext1 (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) : Matrix (Fin n) (Fin n) L :=
  1 + incl L e * (M - 1) * (incl L e)ᵀ

theorem extendMatrixByIdentityAlongIndices_mul {e : Fin r → Fin n} (he : Function.Injective e) (M N : Matrix (Fin r) (Fin r) L) :
    ext1 e (M * N) = ext1 e M * ext1 e N := by
  have h : incl L e * (M - 1) * (incl L e)ᵀ * (incl L e * (N - 1) * (incl L e)ᵀ)
      = incl L e * ((M - 1) * (N - 1)) * (incl L e)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl L e)ᵀ, inclT_mul_incl he, Matrix.one_mul]
  have h2 : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  unfold ext1
  rw [add_mul, mul_add, mul_add, h, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  abel

theorem conjTranspose_extendMatrixByIdentityAlongIndices (σ : L →+* L) (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) :
    cT σ (ext1 e M) = ext1 e (cT σ M) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cT, ext1, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add (f := _),
    map_sum, map_mul, incl, Matrix.of_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite σ, map_one,
    map_zero, Finset.sum_mul]
  congr 1
  · simp only [eq_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [eq_comm (a := i) (b := j)]
    ring

theorem extendMatrixByIdentityAlongIndices_unitary [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {e : Fin r → Fin n} (he : Function.Injective e)
    (hr : ∀ i, e i.rev = (e i).rev) (M : Matrix (Fin r) (Fin r) L)
    (hM : cT σ M * antiJ L r * M = antiJ L r) :
    cT σ (ext1 e M) * antiJ L n * ext1 e M = antiJ L n := by
  have hJ : ∀ N : Matrix (Fin r) (Fin r) L, antiJ L n * ext1 e N
      = ext1 e (antiJ L r * N * antiJ L r) * antiJ L n := by
    intro N
    have h2 : antiJ L r * N * antiJ L r - 1 = antiJ L r * (N - 1) * antiJ L r := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.UnitarySwap.antiJ_mul_self]
    unfold ext1
    rw [h2, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, antiJ_mul_incl hr]
    simp only [Matrix.mul_assoc]
    rw [inclT_mul_antiJ hr, ← Matrix.mul_assoc (antiJ L r) (antiJ L r), GlobalTheory.UnitarySwap.antiJ_mul_self,
      Matrix.one_mul]
  rw [conjTranspose_extendMatrixByIdentityAlongIndices, Matrix.mul_assoc, hJ, ← Matrix.mul_assoc, ← extendMatrixByIdentityAlongIndices_mul he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM,
    GlobalTheory.UnitarySwap.antiJ_mul_self]
  simp [ext1]

end GlobalTheory.SatakeWeyl.InclusionMultiplication


open GlobalTheory.SatakeWeyl.InclusionMultiplication in
theorem GlobalTheory.SatakeWeyl.embExists : GlobalTheory.SatakeWeyl.EmbExists := by
  intro L _ _ σ n r e he hr
  choose f hf using fun g : GU σ r => exists_mat (σ := σ) (ext1 e (mat g)) (extendMatrixByIdentityAlongIndices_unitary σ he hr _ g.2)
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, fun g => ⟨fun i j => ?_, fun a b hab => ?_⟩⟩
  · rw [mat_mul, hf, hf, hf, mat_mul, extendMatrixByIdentityAlongIndices_mul he]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply, mul_inclT_apply he, incl_mul_apply he]
    simp [Matrix.one_apply, he.eq_iff]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply]
    rcases hab with h | h
    · rw [Matrix.mul_assoc, incl_mul_apply_of_not _ h, add_zero]
    · rw [mul_inclT_apply_of_not _ _ h, add_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecVectorFieldOfDualNumberSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spec_vectorField_of_dualNumber_section : ∀ (A : Type) [CommRing A] (σ : A →+* DualNumber A), (∀ a, (σ a).fst = a) → ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧ ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd := by
  first | exact @GlobalTheory.SpecField.exists_isField | exact GlobalTheory.SpecField.exists_isField | (intros; apply GlobalTheory.SpecField.exists_isField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevelStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F), 0 < N → HasLevel N L → ∃ (𝔞 𝔟 : Frac F) (x : F), L = split 𝔞 𝔟 x := by
  first | exact @GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | exact GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | (intros; apply GlobalTheory.HilbFam.exists_eq_split_of_hasLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceUniformiserIdele
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem exists_split_unif_idele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)) (x : OF E),
    Splits v → (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) →
    ∃ π : (Af E)ˣ, (∀ P, Over P v → (π : Af E) P = iota x P) ∧ (∀ P, ¬ Over P v → (π : Af E) P = 1) ∧
      modF π = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ 2 ∧ ∀ χ : HChar E, TrivOnF χ → finPart χ π = 1 := by
  classical
  intro E _ _ _ v x hv hx
  obtain ⟨h2, hN⟩ := _root_.GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hv
  obtain ⟨P₁, P₂, hne, hP₁, hP₂⟩ := hv
  have hx0 : (x : maximalRealSubfield E) ≠ 0 := fun h => by
    have h0 : x = 0 := Subtype.ext h
    have h1 := hx P₁ hP₁
    rw [h0, iota_zero, zero_coord, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  let k : (maximalRealSubfield E)ˣ := Units.mk0 (x : maximalRealSubfield E) hx0
  let y : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom (Formalism.L2.Host.upF (maximalRealSubfield E) k)
  have hy : (y : Af E) = iota x := rfl
  set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS
  have hmem : ∀ P, P ∈ S ↔ Over P v := fun P => mem_aboveF P v
  have hin : ∀ P, Over P v → ((∏ P ∈ S, single P (coord P y) : (Af E)ˣ) : Af E) P = iota x P := fun P hP => by
    rw [Fibre.prod_single_apply, if_pos ((hmem P).2 hP), hy]
  have hout : ∀ P, ¬ Over P v → ((∏ P ∈ S, single P (coord P y) : (Af E)ˣ) : Af E) P = 1 := fun P hP => by
    rw [Fibre.prod_single_apply, if_neg (fun h => hP ((hmem P).1 h))]
  refine ⟨∏ P ∈ S, single P (coord P y), hin, hout, ?_, fun χ hχ => ?_⟩
  · have hS2 : S = {P₁, P₂} := by
      ext R
      rw [hmem, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨h2 P₁ P₂ hP₁ hP₂ hne R, fun h => by rcases h with rfl | rfl <;> assumption⟩
    unfold modF
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun P hP => by
      by_contra h
      refine hP ?_
      beta_reduce
      rw [hout P (fun h' => h ((hmem P).2 h'))]
      simp)]
    rw [Finset.prod_congr rfl (g := fun _ => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) (fun P hP => by
      rw [hin P ((hmem P).1 hP), hx P ((hmem P).1 hP), WithZero.log_exp, (hN P ((hmem P).1 hP)).1, zpow_neg_one])]
    rw [Finset.prod_const, hS2, Finset.card_pair hne]
  · have h1 := hχ.1 v k
    unfold Formalism.L2.Host.HChar.resFin at h1
    rw [MonoidHom.finsetProd_apply] at h1
    rw [map_prod, ← h1]
    exact Finset.prod_congr rfl fun P _ => rfl

end GlobalTheory.CMVal.Euler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableBoundHilbertEisensteinTerms
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem norm_qPow_eq_exp {F : Type} [Field F] [NumberField F] (ξ : F) (w : Emb F → ℂ) :
    ‖qPow ξ w‖ = Real.exp (-(2 * Real.pi * ∑ i : Emb F, i ξ * (w i).im)) := by
  unfold qPow
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.im_sum]

theorem norm_eTr_eq_one {F : Type} [Field F] [NumberField F] (y : F) : ‖eTr y‖ = 1 := by
  unfold eTr
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem exists_summable_bound_terms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ), IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → ∃ M : F → ℝ, Summable M ∧ ∀ (ξ : F) (z : Emb F → ℂ), (∀ i, 1 / 2 ≤ ‖1 + z i * c‖ ∧ τ.im / 2 ≤ (τ + t * z i / (1 + z i * c)).im) → ‖a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))‖ ≤ M ξ := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t hc hτ
  obtain ⟨-, -, hpos, hsum⟩ := hc
  set w₀ : Emb F → ℂ := fun _ ↦ ((τ.im / 2 : ℝ) : ℂ) * Complex.I with hw₀
  have him : ∀ i, (w₀ i).im = τ.im / 2 := fun i ↦ by simp [hw₀]
  have hw : w₀ ∈ upperHalf F := fun i ↦ by rw [him i]; positivity
  have hs : Summable fun ξ : F ↦ ‖a ξ * qPow ξ w₀‖ := summable_norm_iff.mpr (hsum w₀ hw).summable
  refine ⟨fun ξ ↦ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) * ‖a ξ * qPow ξ w₀‖, hs.mul_left _, ?_⟩
  intro ξ z hz
  by_cases ha : a ξ = 0
  · simp [ha]
  have hnn : ∀ i : Emb F, 0 ≤ i ξ := fun i ↦ by
    by_cases h0 : ξ = 0
    · simp [h0]
    · exact ((hpos ξ h0 ha).2 i).le
  set w : Emb F → ℂ := fun i ↦ τ + t * z i / (1 + z i * c) with hwdef
  have key : Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) *
      ∏ i : Emb F, Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)) = qPow ξ w := by
    rw [← Complex.exp_sum, ← Complex.exp_add, ← GlobalTheory.HilbFam.sum_realEmb_eq_trace F ξ]
    unfold qPow
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hwdef]
    ring
  have hq : ‖qPow ξ w‖ ≤ ‖qPow ξ w₀‖ := by
    rw [norm_qPow_eq_exp, norm_qPow_eq_exp]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [him i]
    exact mul_le_mul_of_nonneg_left (hz i).2 (hnn i)
  have hp : ‖∏ i : Emb F, (1 + z i * c)⁻¹ ^ k‖ ≤ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) := by
    rw [norm_prod, ← Finset.card_univ]
    have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun i : Emb F ↦ ‖(1 + z i * c)⁻¹ ^ k‖)
      (g := fun _ ↦ (2 : ℝ) ^ k) (fun i _ ↦ norm_nonneg _) (fun i _ ↦ by
        rw [norm_pow, norm_inv]
        apply pow_le_pow_left₀ (by positivity)
        have := (hz i).1
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith)
    rwa [Finset.prod_const] at h
  have e : a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c))) =
      (∏ i : Emb F, (1 + z i * c)⁻¹ ^ k) * (eTr (ξ * x) * (a ξ * qPow ξ w)) := by
    rw [← key, Finset.prod_mul_distrib]
    ring
  rw [e, norm_mul, norm_mul, norm_eTr_eq_one, one_mul, norm_mul]
  show _ ≤ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) * ‖a ξ * qPow ξ w₀‖
  rw [norm_mul (a ξ)]
  gcongr

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleSheaf_excision_shortExact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ (w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0), (ShortComplex.mk _ _ w).ShortExact := by
  first | (exact @GlobalTheory.EtC.MVFree.shortExact) | (exact GlobalTheory.EtC.MVFree.shortExact) | (intros; apply GlobalTheory.EtC.MVFree.shortExact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosedStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ c : CommRing.Pic B, ∃ d, d ^ q = c := by
  first | (exact @GlobalTheory.PicDiv.pic_divisible) | (exact GlobalTheory.PicDiv.pic_divisible) | (intros; apply GlobalTheory.PicDiv.pic_divisible  <;> assumption)
end

