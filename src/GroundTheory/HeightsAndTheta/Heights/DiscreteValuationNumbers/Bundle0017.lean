module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace IntNumPoint

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

def chartMonomial (i : ∀ k, ι k) (e : K → ℕ) : MRing ι F :=
  ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ e k

theorem isMultiHomog_chartMonomial (i : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) i e) e := by
  have h : IsWeightedHomogeneous (blockWeight ι) (chartMonomial (F := F) i e)
      (∑ k ∈ Finset.univ, e k • blockWeight ι ⟨k, i k⟩) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ =>
      (isWeightedHomogeneous_X (R := F) (blockWeight ι) ⟨k, i k⟩).pow (e k)
  have he : (∑ k ∈ Finset.univ, e k • blockWeight ι ⟨k, i k⟩) = e := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  exact h

def chartUnitIdeal (i : ∀ k, ι k) : Ideal (MRing ι F) :=
  Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι F) - 1)

theorem mk_X_chart (i : ∀ k, ι k) (k : K) :
    Ideal.Quotient.mk (chartUnitIdeal (F := F) i) (X ⟨k, i k⟩) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨k, rfl⟩

theorem mk_chartMonomial (i : ∀ k, ι k) (e : K → ℕ) :
    Ideal.Quotient.mk (chartUnitIdeal (F := F) i) (chartMonomial i e) = 1 := by
  simp [chartMonomial, map_prod, map_pow, mk_X_chart]

theorem exists_homog_congr (i : ∀ k, ι k) (p : MRing ι F) :
    ∃ N : K → ℕ, ∀ N', N ≤ N' → ∃ h : MRing ι F, IsMultiHomog h N' ∧
      Ideal.Quotient.mk (chartUnitIdeal i) p = Ideal.Quotient.mk (chartUnitIdeal i) h := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun N' _ => ⟨C a * chartMonomial i N', ?_, ?_⟩⟩
    · exact IsWeightedHomogeneous.C_mul (isMultiHomog_chartMonomial i N') a
    · rw [map_mul, mk_chartMonomial, mul_one]
  | add p q hp hq =>
    obtain ⟨Np, hp⟩ := hp
    obtain ⟨Nq, hq⟩ := hq
    refine ⟨Np ⊔ Nq, fun N' hN => ?_⟩
    obtain ⟨a, ha, ha'⟩ := hp N' (le_sup_left.trans hN)
    obtain ⟨b, hb, hb'⟩ := hq N' (le_sup_right.trans hN)
    exact ⟨a + b, IsWeightedHomogeneous.add ha hb, by rw [map_add (f := _), map_add (f := _), ha', hb']⟩
  | mul_X p s hp =>
    obtain ⟨Np, hp⟩ := hp
    refine ⟨Np + blockWeight ι s, fun N' hN => ?_⟩
    have h1 : Np ≤ N' - blockWeight ι s := fun k => Nat.le_sub_of_add_le (hN k)
    have h2 : N' - blockWeight ι s + blockWeight ι s = N' := by
      funext k
      exact Nat.sub_add_cancel (le_trans (Nat.le_add_left _ _) (hN k))
    obtain ⟨a, ha, ha'⟩ := hp _ h1
    refine ⟨a * X s, ?_, by rw [map_mul, map_mul, ha']⟩
    have := IsWeightedHomogeneous.mul ha (isWeightedHomogeneous_X (R := F) (blockWeight ι) s)
    rwa [h2] at this

section Dehom

variable (V : Ideal (MRing ι F)) [V.IsPrime]

def xc (p : Σ k, ι k) : FractionRing (MRing ι F ⧸ V) :=
  algebraMap (MRing ι F ⧸ V) _ (Ideal.Quotient.mk V (X p))

def cls : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ V) :=
  (IsScalarTower.toAlgHom F (MRing ι F ⧸ V) _).comp (Ideal.Quotient.mkₐ F V)

def dehom (i : ∀ k, ι k) : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ V) :=
  aeval fun p => xc V p / xc V ⟨p.1, i p.1⟩

theorem cls_apply (f : MRing ι F) :
    cls V f = algebraMap (MRing ι F ⧸ V) _ (Ideal.Quotient.mk V f) := rfl

theorem cls_eq_zero_iff (f : MRing ι F) : cls V f = 0 ↔ f ∈ V := by
  rw [cls_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

variable {V}

theorem xc_ne_zero {p : Σ k, ι k} (hp : (X p : MRing ι F) ∉ V) : xc V p ≠ 0 :=
  fun h => hp ((cls_eq_zero_iff V _).1 h)

variable (i : ∀ k, ι k) (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
include hi

theorem chartProd_ne_zero (a : K → ℕ) : ∏ k, xc V ⟨k, i k⟩ ^ a k ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (xc_ne_zero (hi k))

theorem dehom_monomial_mul (m : (Σ k, ι k) →₀ ℕ) :
    dehom V i (monomial m 1) * ∏ k, xc V ⟨k, i k⟩ ^ (Finsupp.weight (blockWeight ι) m k) =
      cls V (monomial m 1) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' =>
    rw [← mul_one (1 : F), ← monomial_mul, map_mul, map_mul, map_add (f := _), ← hm, ← hm']
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | single p n =>
    have hy : xc V ⟨p.1, i p.1⟩ ≠ 0 := xc_ne_zero (hi p.1)
    rw [← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single,
      Fintype.prod_eq_single p.1 (fun k hk => by simp [blockWeight, hk])]
    simp only [dehom, aeval_X, blockWeight, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, div_pow]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hy)]
    rfl

theorem dehom_mul_of_isMultiHomog {h : MRing ι F} {a : K → ℕ} (hh : IsMultiHomog h a) :
    dehom V i h * ∏ k, xc V ⟨k, i k⟩ ^ a k = cls V h := by
  conv_rhs => rw [h.as_sum]
  conv_lhs => rw [h.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (blockWeight ι) m = a := hh (mem_support_iff.mp hm)
  have hmon : monomial m (AddMonoidAlgebra.coeff h m) = AddMonoidAlgebra.coeff h m • monomial m (1 : F) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, map_smul, smul_mul_assoc, ← hw, dehom_monomial_mul i hi]

theorem dehom_chartUnitIdeal {f : MRing ι F} (hf : f ∈ chartUnitIdeal i) : dehom V i f = 0 := by
  have : chartUnitIdeal (F := F) i ≤ RingHom.ker (dehom V i) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, dehom, aeval_X]
    rw [div_self (xc_ne_zero (hi k)), sub_self]
  exact this hf

theorem dehom_eq_zero_of_mem (hV : IsMultiHomogIdeal V) {f : MRing ι F} (hf : f ∈ V) :
    dehom V i f = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  have h1 := dehom_mul_of_isMultiHomog i hi
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) (n := b) (φ := f))
  rw [(cls_eq_zero_iff V _).2 (hV f hf b)] at h1
  exact (mul_eq_zero.mp h1).resolve_right (chartProd_ne_zero i hi b)

theorem dehom_eq_zero_of_mem_chartIdeal (hV : IsMultiHomogIdeal V) {f : MRing ι F}
    (hf : f ∈ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) : dehom V i f = 0 := by
  have : ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i ≤ RingHom.ker (dehom V i) :=
    sup_le (fun g hg => dehom_eq_zero_of_mem i hi hV hg) (fun g hg => dehom_chartUnitIdeal i hi hg)
  exact this hf

theorem mem_chartIdeal_of_dehom_eq_zero {f : MRing ι F} (hf : dehom V i f = 0) :
    f ∈ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i := by
  obtain ⟨N, hN⟩ := exists_homog_congr i f
  obtain ⟨h, hh, hc⟩ := hN N le_rfl
  have hfh : f - h ∈ chartUnitIdeal i := Ideal.Quotient.eq.mp hc
  have h0 : dehom V i h = 0 := by
    have := dehom_chartUnitIdeal i hi hfh
    rwa [map_sub, hf, zero_sub, neg_eq_zero] at this
  have hV : h ∈ V := by
    rw [← cls_eq_zero_iff, ← dehom_mul_of_isMultiHomog i hi hh, h0, zero_mul]
  have : f = (f - h) + h := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_right hfh) (Ideal.mem_sup_left hV)

end Dehom

theorem finrank_chart_eq (V : Ideal (MRing ι F)) (hV : IsMultiProjPrime V) (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
    (hfin : haveI := hV.isPrime; FiniteDimensional F (FieldNumbers.homFracDegZero V)) :
    (haveI := hV.isPrime;
      Module.finrank F (MRing ι F ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) =
        Module.finrank F (FieldNumbers.homFracDegZero V)) := by
  haveI := hV.isPrime
  set H := FieldNumbers.homFracDegZero V
  let ρ := Ideal.Quotient.liftₐ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) (dehom V i)
    (fun a ha => dehom_eq_zero_of_mem_chartIdeal i hi hV.multiHomog ha)
  have hρ : ∀ f, ρ (Ideal.Quotient.mk _ f) = dehom V i f := fun f => rfl
  have hinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_zero ρ).2 fun a ha => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hρ] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_chartIdeal_of_dehom_eq_zero i hi ha)
  have hmemρ : ∀ f, dehom V i f ∈ ρ.range := fun f => ⟨Ideal.Quotient.mk _ f, hρ f⟩
  have hdH : ∀ f, dehom V i f ∈ H := by
    intro f
    have : (dehom V i).range ≤ H.toSubalgebra := by
      rw [dehom, aeval_range]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin F _
        ⟨blockWeight ι p, X p, X ⟨p.1, i p.1⟩, isWeightedHomogeneous_X (R := F) _ _,
          isWeightedHomogeneous_X (R := F) _ _, hi p.1, rfl⟩
    exact this ⟨f, rfl⟩
  have hle : ρ.range ≤ H.toSubalgebra := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hdH f
  let E : IntermediateField F (FractionRing (MRing ι F ⧸ V)) :=
    ρ.range.toIntermediateField fun x hx =>
      ρ.range.inv_mem_of_algebraic (x := ⟨x, hx⟩)
        ((IntermediateField.isAlgebraic_iff (x := (⟨x, hle hx⟩ : H))).1 (IsAlgebraic.of_finite F _))
  have hHE : H ≤ E := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨b, f, g, hf, hg, hgV, rfl⟩
    have h1 := dehom_mul_of_isMultiHomog i hi hf
    have h2 := dehom_mul_of_isMultiHomog i hi hg
    rw [← cls_apply, ← cls_apply, ← h1, ← h2, mul_div_mul_right _ _ (chartProd_ne_zero i hi b),
      div_eq_mul_inv]
    exact E.mul_mem (hmemρ f) (E.inv_mem (hmemρ g))
  have heq : ρ.range = H.toSubalgebra := le_antisymm hle fun x hx => hHE hx
  rw [(AlgEquiv.ofInjective ρ hinj).toLinearEquiv.finrank_eq, heq,
    IntermediateField.finrank_eq_finrank_subalgebra]

theorem proof (hBase : FieldNumbers.IntNumBase.Statement.{u}) : IntNumPoint.Statement.{u} := by
  intro F _ K _ _ ι _ V i hV hdim hi
  haveI := hV.isPrime
  have hrel : FieldNumbers.relDim V = 0 := by
    rw [FieldNumbers.relDim, hdim]
    have : (((0 + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = 0 := by simp
    exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
  obtain ⟨hfin, hnum⟩ := hBase F K ι V hV hrel
  rw [hnum, ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg, finrank_chart_eq V hV i hi hfin]

end IntNumPoint

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomogIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem VocabMultiHomogIdeal.proof (h1 : VocabMultiHomog.Statement.{u}) :
    VocabMultiHomogIdeal.Statement.{u} := by
  intro R _ K _ _ ι _ P
  let := weightedGradedAlgebra R (blockWeight ι)
  constructor
  · rintro ⟨S, hS, rfl⟩
    have hhom : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
      refine Ideal.homogeneous_span (weightedHomogeneousSubmodule R (blockWeight ι)) S
        fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 ((h1 R K ι x a).1 ha)⟩
    intro f hf b
    exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) hhom hf b
  · intro hP
    refine ⟨{c | ∃ f ∈ P, ∃ b, c = weightedHomogeneousComponent (blockWeight ι) b f}, ?_, ?_⟩
    · rintro c ⟨f, -, b, rfl⟩
      exact ⟨b, (h1 R K ι _ b).2 (weightedHomogeneousComponent_isWeightedHomogeneous b f)⟩
    · apply le_antisymm
      · intro f hf
        rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
          finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
        exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
      · rw [Ideal.span_le]
        rintro c ⟨f, hf, b, rfl⟩
        exact hP f hf b

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

section FrameBundle

variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω] {σ : Type*}
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

variable {o}

variable (o)

end FrameBundle

section GradedFrame

variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

end GradedFrame

section Point

variable {R : Type*} [CommRing R] [IsDomain R] {Ω : Type*} [Field Ω] [Algebra R Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end Point

section ModelInhabitants

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_C (c : O) : IsMultiHomog (C c : MRingOver O ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

def unif : O :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible O)

end ModelInhabitants

section Flags

variable {Ω : Type*} [Field Ω]

variable (o : Type*) [CommRing o] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end Flags

section FlagPairs

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end FlagPairs

section PointModel

abbrev ptIdx : Unit → Type := fun _ => Fin 1

variable {Ω : Type*} [Field Ω]

def ptCoord : (Σ k : Unit, ptIdx k) → Ω := fun _ => 1

end PointModel

section PointDVR

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end PointDVR

section FieldInhabitants

variable (F : Type*) [Field F]

variable {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end FieldInhabitants

section SubQuot

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end SubQuot

section PullBC

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end PullBC

section RankOne

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end RankOne

section Gaussian

end Gaussian

section FrobInhabitant

end FrobInhabitant

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairNumberExpansionIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (f g : Fin n → MRing ι O),
      (∀ i, IsVerticalDivisor P ϖ (z i - z' i) (f i) (g i)) →
    ∀ (m : ℕ) (A : MvPolynomial (Fin n) ℤ), A.IsHomogeneous m →
    ∀ (As Bs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ), IsPairExpansion m A As →
      IsPairExpansion m A Bs →
    ∀ Q : List (K → ℤ), Q.length + m = d + 1 →
      pairNum P z z' f g As Q = pairNum P z z' f g Bs Q

def hsymmTimes (N n a : ℕ) (R : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (N + n)) ℤ :=
  rename (Fin.castAdd n) (hsymm (Fin N) ℤ a) * rename (Fin.natAdd N) R

def HsymmPairFlagIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' v v' : Module.Basis (Fin N) Ω E) (x x' u u' : Fin N → K → ℤ)
      (f g f₂ g₂ : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g → IsFlagPair ϖ y B B' v v' u u' f₂ g₂ →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (a r : ℕ) (R : MvPolynomial (Fin n) ℤ), R.IsHomogeneous r →
    ∀ (As Bs : Fin (N + n) → MvPolynomial (Fin (N + n) ⊕ Fin (N + n)) ℤ),
      IsPairExpansion (a + r) (hsymmTimes N n a R) As →
      IsPairExpansion (a + r) (hsymmTimes N n a R) Bs →
    ∀ Q : List (K → ℤ), Q.length + (a + r) = d + 1 →
      pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
          (Fin.append g gz) As Q =
        pairNum (pointIdeal O y) (Fin.append u z) (Fin.append u' z') (Fin.append f₂ fz)
          (Fin.append g₂ gz) Bs Q

def SymmetricSpanHsymm.Statement : Prop :=
  ∀ (N m : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous m → G.IsSymmetric →
    G ∈ Submodule.span ℤ (Set.range fun μ : m.Partition => hsymmPart (Fin N) ℤ μ)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

