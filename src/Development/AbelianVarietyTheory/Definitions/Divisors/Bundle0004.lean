module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
section
open MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.LGrp

section Rational
open Polynomial

def IsLaurentPoly (R : RatFunc ℂ) : Prop :=
  ∃ (m : ℕ) (p : ℂ[X]), R * RatFunc.X ^ m = algebraMap _ _ p

def lFactor (S : Multiset ℂˣ) : RatFunc ℂ := (S.map fun a : ℂˣ => (1 - RatFunc.C (a : ℂ) * RatFunc.X)⁻¹).prod

end Rational

section ZetaNonvanishing₂
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

variable [MeasurableSpace (GL n k)]

variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
private theorem valuation_det_le_one_of_entries_integer {y : GL n k}
    (h : ∀ i j, (y : Matrix n n k) i j ∈ (valuation k).integer) :
    valuation k (GeneralLinearGroup.det y : k) ≤ 1 := by
  set A : Matrix n n (valuation k).integer := Matrix.of fun i j => ⟨(y : Matrix n n k) i j, h i j⟩
  have e : (y : Matrix n n k) = ((valuation k).integer.subtype).mapMatrix A := by
    ext i j
    rfl
  have hd : (GeneralLinearGroup.det y : k) = (valuation k).integer.subtype A.det := by
    rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, ← e]
  rw [hd]
  exact (Valuation.mem_integer_iff _ _).mp (SetLike.coe_mem _)


open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
theorem _root_.GlobalTheory.LGrp.nabs_det_of_mem_KO {x : GL n k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det x) = 1 := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have h1 := valuation_det_le_one_of_entries_integer hx.1
  have h2 := valuation_det_le_one_of_entries_integer hx.2
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at h2
  have hpos : 0 < valuation k (GeneralLinearGroup.det x : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
private theorem smGL_ord_pow_eq_mul (x : kˣ) (m : ℕ) :
    _root_.GlobalTheory.SmGL.ord k (x ^ m) = m * _root_.GlobalTheory.SmGL.ord k x := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
  | succ m ih =>
    rw [pow_succ, _root_.GlobalTheory.SmGL.ord_mul, ih]
    push_cast
    ring

open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
private theorem exists_unit_ord_eq_one_and_nabs_eq_inv_resCard :
    ∃ ϖ : kˣ, _root_.GlobalTheory.SmGL.ord k ϖ = 1 ∧
      _root_.GlobalTheory.SplitWeil.nabs k ϖ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
  have hp0 : (p : k) ≠ 0 := by
    intro h
    exact hp.ne_zero (Subtype.ext h)
  obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact (uniformizer_pos (R := k)).ne hy
  have hyint : y ∈ (valuation k).integer := by
    rw [Valuation.mem_integer_iff, hy]
    exact uniformizer_lt_one.le
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
  have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
  have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
    _root_.GlobalTheory.SmGL.ord_eq_one hy
  have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
    apply _root_.GlobalTheory.SmGL.ord_eq_zero
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
  have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
    ext
    have := congrArg Subtype.val hu
    simpa using this
  rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, smGL_ord_pow_eq_mul,
    zero_add] at hyo
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · omega


open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
theorem _root_.GlobalTheory.LGrp.nabs_eq_zpow (x : kˣ) :
    _root_.GlobalTheory.SplitWeil.nabs k x =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-_root_.GlobalTheory.SmGL.ord k x) := by
  obtain ⟨ϖ, hord, habs⟩ := exists_unit_ord_eq_one_and_nabs_eq_inv_resCard (k := k)
  have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
    have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
    positivity
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
    have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
    exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
  have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
    have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, hord,
      _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp only [Units.val_one, map_one])] at h
    omega
  have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
    intro m
    refine Int.induction_on m ?_ ?_ ?_
    · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
      rw [zpow_zero]
      exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
    · intro i ih
      rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, habs, hord]
      refine ⟨?_, rfl⟩
      rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
    · intro i ih
      rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, hinv, oinv]
      refine ⟨?_, by ring⟩
      rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
  set o := _root_.GlobalTheory.SmGL.ord k x
  have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
    rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
    ring
  have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
    _root_.GlobalTheory.SmGL.nabs_eq_one k
      (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
  have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
    rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc _root_.GlobalTheory.SplitWeil.nabs k x
      = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
    _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
      rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]


end ZetaNonvanishing₂

end GlobalTheory.LGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FibreRankCompOfSurjective
section
noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module

namespace GlobalTheory.PDiv

theorem finrank_eq_ker_mul_range (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    finrank k A = finrank k (A ⧸ kerIdeal f) *
      finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap) := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  exact GlobalTheory.finrank_eq_mul_of_basis_tensor_self k (AlgHom.range (f : B →ₐ[k] A)) A _ Subtype.val_injective
    ⟨((Module.finBasis k _).baseChange A).map e.symm⟩

variable {O : Type} [CommRing O]

abbrev fibreDim (M : Type) [AddCommGroup M] [Module O M] (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[O] M)

abbrev fibreRank {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : M →ₗ[O] N) (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField))

section Linear

variable {M N P : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup P] [Module O P]

theorem fibreDim_congr (e : M ≃ₗ[O] N) (q : PrimeSpectrum O) : fibreDim M q = fibreDim N q :=
  (e.baseChange O _ M N).finrank_eq

theorem fibreRank_comp_of_surjective (g : N →ₗ[O] P) {f : M →ₗ[O] N}
    (hf : Function.Surjective f) (q : PrimeSpectrum O) :
    fibreRank (g ∘ₗ f) q = fibreRank g q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (LinearMap.lTensor_surjective _ hf)

theorem fibreRank_equiv_comp (e : N ≃ₗ[O] P) (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (e.toLinearMap ∘ₗ f) q = fibreRank f q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq (e.baseChange O _ N P) _

variable [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]

theorem fibreDim_dual (q : PrimeSpectrum O) : fibreDim (CartierDual O M) q = fibreDim M q :=
  (fibreDim_congr (CartierDual.toDual O M) q).trans (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M M _ LinearMap.id).1

theorem rankAtStalk_dual (q : PrimeSpectrum O) :
    rankAtStalk (CartierDual O M) q = rankAtStalk M q := by
  rw [rankAtStalk_eq, rankAtStalk_eq]
  exact fibreDim_dual q

theorem fibreRank_transpose (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (CartierDual.transpose f) q = fibreRank f q := by
  have h : CartierDual.transpose f = (CartierDual.toDual O M).symm.toLinearMap ∘ₗ
      (f.dualMap ∘ₗ (CartierDual.toDual O N).toLinearMap) := rfl
  rw [h, fibreRank_equiv_comp, fibreRank_comp_of_surjective _ (CartierDual.toDual O N).surjective]
  exact (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M N _ f).2

end Linear

variable {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B]
  [Module.Finite O A]

theorem fibreDim_eq_ker_mul_range (f : B →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreRank (f : B →ₐ[O] A).toLinearMap q :=
  GlobalTheory.hopf_order_formula_fibre finrank_eq_ker_mul_range O A B _ f

theorem fibreDim_ne_zero (q : PrimeSpectrum O) : fibreDim A q ≠ 0 := by
  have : Nontrivial (q.asIdeal.ResidueField ⊗[O] A) :=
    (counitAlgHom q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[O] A)).domain_nontrivial
  exact finrank_pos.ne'

variable [Module.Projective O A] [Module.Finite O B] [Module.Projective O B]

theorem dual_map_surjective (f : B →ₐc[O] A)
    (h : ∀ q : PrimeSpectrum O, fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreDim B q) :
    Function.Surjective (CartierDual.map f) := by
  refine (GlobalTheory.surjective_injective_of_fibre_rank O _ _ (CartierDual.transpose (f : B →ₐ[O] A).toLinearMap)).1 fun q => ?_
  refine (fibreRank_transpose _ q).trans (Eq.trans ?_ (fibreDim_dual q).symm)
  have h1 := fibreDim_eq_ker_mul_range f q
  have h2 : fibreDim (A ⧸ kerIdeal f) q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, zero_mul])
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h2) (h1.symm.trans (h q))

theorem fibreDim_ker_dual [IsCocomm O A] (g : A →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim (CartierDual O A ⧸ kerIdeal (CartierDual.map g)) q =
      fibreDim (A ⧸ kerIdeal g) q := by
  have h1 := fibreDim_eq_ker_mul_range g q
  have h2 := fibreDim_eq_ker_mul_range (CartierDual.map g) q
  have h3 : fibreRank (CartierDual.map g : CartierDual O A →ₐ[O] CartierDual O A).toLinearMap q =
    fibreRank (g : A →ₐ[O] A).toLinearMap q := fibreRank_transpose (g : A →ₐ[O] A).toLinearMap q
  rw [h3, fibreDim_dual, h1] at h2
  have h4 : fibreRank (g : A →ₐ[O] A).toLinearMap q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, mul_zero])
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4) h2).symm

theorem ker_eq_of_fibreDim_eq {D E : Type} [CommRing D] [CommRing E] [Algebra O D] [Algebra O E]
    [Module.Finite O D] [Module.Finite O E] [Module.Projective O E] (π : D →ₐ[O] E)
    (hπ : Function.Surjective π) (I : Ideal D) (hI : I ≤ RingHom.ker π)
    (h : ∀ q : PrimeSpectrum O, fibreDim (D ⧸ I) q = fibreDim E q) : RingHom.ker π = I := by
  refine le_antisymm (fun d hd => ?_) hI
  let π' : (D ⧸ I) →ₐ[O] E := Ideal.Quotient.liftₐ I π hI
  have hs : Function.Surjective π' := fun e => by
    obtain ⟨d, rfl⟩ := hπ e
    exact ⟨Ideal.Quotient.mk I d, rfl⟩
  have hi := (GlobalTheory.surjective_injective_of_fibre_rank O _ _ π'.toLinearMap).2 inferInstance inferInstance hs h
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hi (a₁ := Ideal.Quotient.mk I d) (a₂ := 0)
    (by rw [map_zero]; exact hd))

end GlobalTheory.PDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def cstOn (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom

def IsEtCoord (p : X ⟶ Sp R) (U : X.Opens) {d : ℕ} (t : Fin d → Γ(X, U)) : Prop :=
  (MvPolynomial.eval₂Hom (cstOn p U) t).Etale

structure SncChart (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) where

  U : X.Opens
  affine : IsAffineOpen U

  t : Fin d → Γ(X, U)
  etale : IsEtCoord p U t

  c : ∀ i, (L i).ι
  le : ∀ i, U ≤ (L i).U (c i)

  e : Fin s → Option (Fin d)
  inj : ∀ i j a, e i = some a → e j = some a → i = j

  u : Fin s → Γ(X, U)ˣ
  eq : ∀ i, resG X (le i) ((σ i).f (c i)) = (u i : Γ(X, U)) * (e i).elim 1 t

structure RelSnc (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) : Prop where
  isLB : ∀ i, (L i).IsLB
  chart : ∀ x : X, ∃ C : SncChart p d L σ, x ∈ C.U

end GlobalTheory.LogPair
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ProdFam
section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

section Pull

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E : Type} [AddCommGroup E] [Module k E]


open Classical in
def idxSign (τ : κ → ι) (S : Finset κ) : ℤ := (-1) ^ ((S ×ˢ S).filter fun x => x.1 < x.2 ∧ τ x.2 < τ x.1).card


open Classical in
def pullIdx (τ : κ → ι) (a : Finset ι → E) : Finset κ → E := fun S =>
  if Set.InjOn τ (S : Set κ) then idxSign τ S • a (S.image τ) else 0

end Pull

section Cross

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

def fstL : ι ×ₗ κ → ι := fun x => (ofLex x).1

def sndL : ι ×ₗ κ → κ := fun x => (ofLex x).2

def crossC {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') :
    Finset (ι ×ₗ κ) → E'' := fun u =>
  ∑ j ∈ u, μ (pullIdx fstL a (u.filter (· ≤ j))) (pullIdx sndL b (u.filter (j ≤ ·)))

def Disjoint₂ {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') : Prop :=
  ∀ I J, Function.Injective (TensorProduct.lift (μ.compl₁₂ (A I).subtype (B J).subtype))

end Cross

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

def SameDiv {X : Scheme.{0}} {L M : LB X} (σ : L.Sec) (τ : M.Sec) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (i : L.ι) (j : M.ι) (hi : U ≤ L.U i) (hj : U ≤ M.U j) (u : Γ(X, U)ˣ),
    x ∈ U ∧ resG X hi (σ.f i) = (u : Γ(X, U)) * resG X hj (τ.f j)

end GlobalTheory.LogPair
end
end

