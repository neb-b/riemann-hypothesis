module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortIndependentIntegers
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroPointOfCotangentLinearMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamily
section
set_option autoImplicit false

noncomputable section

open NumberField Module

namespace GlobalTheory

theorem exists_isShortGen_of_short_span : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) →
    (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L →
    Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) →
    ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧
      abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧
      n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  intro K V _ _ _ _ _ _ _ N L s A hLfg h0 hsm hadd hsL hsp hA
  classical
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  haveI : IsScalarTower ℚ K V := ⟨fun q a x => by
    show (q • a) • x = (algebraMap ℚ K q) • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have hspL : Submodule.span K (L : Set V) = ⊤ := eq_top_iff.2 (hsp ▸ Submodule.span_mono hsL)
  have hrk : Formalism.HN.rkK L = Module.finrank K V := by
    rw [Formalism.HN.rkK, hspL, finrank_top]

  obtain ⟨t, hts, htsp, hti⟩ := exists_linearIndependent K s
  let vb : Basis t K V := Basis.mk hti (by rw [Subtype.range_coe, htsp, hsp])
  haveI : Finite t := Module.Finite.finite_basis vb
  haveI : Fintype t := Fintype.ofFinite t
  have hm : Fintype.card t = Formalism.HN.rkK L := by rw [hrk, finrank_eq_card_basis vb]

  obtain ⟨ω, hωi, hωb⟩ := exists_short_independent_integers K
  haveI : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let ob : Basis (Fin (finrank ℚ K)) ℚ K := basisOfLinearIndependentOfCardEqFinrank hωi (by simp)
  have hob : ∀ k, ob k = (ω k : K) := fun k => by
    simp [ob, coe_basisOfLinearIndependentOfCardEqFinrank]
  let E : Basis (Fin (finrank ℚ K) × t) ℚ V := ob.smulTower vb
  have hE : ∀ p, E p = ω p.1 • (p.2 : V) := fun p => by
    rw [Basis.smulTower_apply, hob, Basis.mk_apply]
    exact algebraMap_smul K (ω p.1) (p.2 : V)

  have hN0 : ∀ σ, N σ 0 = 0 := fun σ => by simpa using hsm σ 0 0
  have hsum : ∀ σ {ι : Type} (S : Finset ι) (f : ι → V), N σ (∑ i ∈ S, f i) ≤ ∑ i ∈ S, N σ (f i) := by
    intro σ ι S f
    induction S using Finset.induction_on with
    | empty => simp [hN0]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hadd σ _ _).trans (add_le_add le_rfl ih)
  have hq : ∀ σ (q : ℚ) x, N σ (q • x) = |(q : ℝ)| * N σ x := fun σ q x => by
    have := hsm σ (algebraMap ℚ K q) x
    rw [eq_ratCast, map_ratCast, Complex.norm_ratCast] at this
    exact this

  set C : ℝ := (finrank ℚ K : ℝ) ^ 3 * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A with hC
  have hEle : ∀ σ p, N σ (E p) ≤ C := fun σ p => by
    rw [hE p, ← algebraMap_smul K (ω p.1) (p.2 : V), hsm]
    have h1 := hA _ (hts p.2.2) σ
    exact mul_le_mul (hωb σ p.1) h1 (h0 _ _) ((norm_nonneg _).trans (hωb σ p.1))

  let red : V → V := fun x => ∑ p, Int.fract (E.repr x p) • E p
  have hred_sub : ∀ x, x - red x ∈ Submodule.span ℤ (Set.range E) := fun x => by
    have hx : x - red x = ∑ p, (⌊E.repr x p⌋ : ℤ) • E p := by
      rw [sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
      conv_lhs => rw [← E.sum_repr x]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.floor_add_fract]
    rw [hx]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  have hred_le : ∀ σ x, N σ (red x) ≤ ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C := fun σ x => by
    refine (hsum σ _ _).trans ?_
    have hle : ∀ p ∈ (Finset.univ : Finset (Fin (finrank ℚ K) × t)),
        N σ (Int.fract (E.repr x p) • E p) ≤ C := fun p _ => by
      rw [hq]
      have h1 : |((Int.fract (E.repr x p) : ℚ) : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (Rat.cast_nonneg.2 (Int.fract_nonneg _))]
        exact_mod_cast (Int.fract_lt_one _).le
      exact (mul_le_of_le_one_left (h0 _ _) h1).trans (hEle σ p)
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hm]
    push_cast; ring

  haveI : NoZeroSMulDivisors ℤ V := ⟨fun {c x} h => by
    rw [← Int.cast_smul_eq_zsmul K] at h
    exact (smul_eq_zero.1 h).imp_left Int.cast_eq_zero.1⟩
  let Lz := L.restrictScalars ℤ
  haveI : Module.Finite ℤ Lz := Module.Finite.iff_fg.2 hLfg.restrictScalars
  haveI : Module.Free ℤ Lz := Module.free_of_finite_type_torsion_free'
  let ZB := Module.Free.chooseBasis ℤ Lz
  let bZ : Module.Free.ChooseBasisIndex ℤ Lz → V := fun j => (ZB j : V)
  have hZq : LinearIndependent ℚ bZ := (LinearIndependent.iff_fractionRing ℤ ℚ).1
    (ZB.linearIndependent.map' Lz.subtype (Submodule.ker_subtype _))
  haveI : Module.Finite ℚ V := Module.Finite.of_basis E
  have hcardZ : Fintype.card (Module.Free.ChooseBasisIndex ℤ Lz) ≤ Fintype.card (Fin (finrank ℚ K) × t) := by
    rw [← finrank_eq_card_basis E]; exact hZq.fintype_card_le_finrank
  have hLz : Lz = Submodule.span ℤ (Set.range bZ) := by
    rw [show Set.range bZ = Lz.subtype '' Set.range ZB from Set.range_comp _ _, ← Submodule.map_span,
      ZB.span_eq, Submodule.map_top, Submodule.range_subtype]

  let F : (Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz → V := Sum.elim E (fun j => red (bZ j))
  let e := Fintype.equivFin ((Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz)
  have hEL : ∀ p, E p ∈ L := fun p => by rw [hE]; exact L.smul_mem _ (hsL (hts p.2.2))
  have hspanE : Submodule.span ℤ (Set.range E) ≤ Lz :=
    Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hEL p)
  have hrng : Set.range (F ∘ e.symm) = Set.range F := e.symm.surjective.range_comp F
  have hbig : ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C ≤ max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A) := by
    refine le_trans (le_of_eq ?_) (le_max_right _ _); rw [hC]; ring
  refine ⟨Fintype.card _, F ∘ e.symm, max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A),
    ⟨fun x => ?_, fun i σ => ?_, le_max_left _ _⟩, le_rfl, ?_⟩
  · rw [hrng]
    constructor
    · intro hx
      have hx' : x ∈ Lz := hx
      rw [hLz] at hx'
      refine (Submodule.span_le.2 ?_) hx'
      rintro _ ⟨j, rfl⟩
      have h1 : red (bZ j) ∈ Submodule.span ℤ (Set.range F) := Submodule.subset_span ⟨Sum.inr j, rfl⟩
      have h2 : bZ j - red (bZ j) ∈ Submodule.span ℤ (Set.range F) :=
        Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨Sum.inl p, rfl⟩) (hred_sub _)
      simpa using add_mem h2 h1
    · intro hx
      have : x ∈ Lz := (Submodule.span_le (p := Lz)).2 (by
        rintro _ ⟨q | j, rfl⟩
        · exact hEL q
        · have h1 : bZ j ∈ Lz := (ZB j).2
          have h2 := hspanE (hred_sub (bZ j))
          have e1 : red (bZ j) = bZ j - (bZ j - red (bZ j)) := by abel
          show red (bZ j) ∈ Lz
          rw [e1]; exact sub_mem h1 h2) hx
      exact this
  · refine le_trans ?_ hbig
    rw [Function.comp_apply]
    generalize e.symm i = q
    rcases q with q | j
    · have hC0 : 0 ≤ C := (h0 σ _).trans (hEle σ q)
      have hpos : 0 < Fintype.card t := Fintype.card_pos_iff.2 ⟨q.2⟩
      have h1 : (1 : ℝ) ≤ (finrank ℚ K : ℝ) * Formalism.HN.rkK L := by
        rw [← hm]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero Module.finrank_pos.ne' hpos.ne')
      exact (hEle σ q).trans (le_mul_of_one_le_left hC0 h1)
    · exact hred_le σ _
  · rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hm]
    rw [Fintype.card_prod, Fintype.card_fin, hm] at hcardZ
    linarith

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentRepresentationSmoothGroupScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanRepr

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

variable {R : Type} [CommRing R]

section Base

variable (R) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

def baseMap : TrivSqZeroExt R M →+* TrivSqZeroExt B M where
  toFun x := ((algebraMap R B x.fst, x.snd) : TrivSqZeroExt B M)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · change algebraMap R B (x * y).fst = algebraMap R B x.fst * algebraMap R B y.fst
      rw [TrivSqZeroExt.fst_mul, map_mul]
    · change (x * y).snd = (algebraMap R B x.fst) • y.snd + MulOpposite.op (algebraMap R B y.fst) • x.snd
      rw [TrivSqZeroExt.snd_mul, op_smul_eq_smul, op_smul_eq_smul, algebraMap_smul, algebraMap_smul]
  map_zero' := by ext <;> simp
  map_add' x y := by
    ext
    · change algebraMap R B (x + y).fst = algebraMap R B x.fst + algebraMap R B y.fst
      rw [TrivSqZeroExt.fst_add, map_add (f := _)]
    · rfl

theorem baseMap_isSum : IsSum (baseMap R B M) (algebraMap R B) id :=
  ⟨fun _ => rfl, fun _ => TrivSqZeroExt.ext (by change algebraMap R B 0 = 0; simp) rfl⟩

end Base

open GlobalTheory.SqZeroPt

section Pts

variable (A : Over (Sp R)) [GrpObj A]
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

theorem fst_comp_baseMap : (TrivSqZeroExt.fstHom B B M).toRingHom.comp (baseMap R B M) =
    (algebraMap R B).comp (TrivSqZeroExt.fstHom R R M).toRingHom := by
  ext x; rfl

theorem baseMap_comp_algebraMap : (baseMap R B M).comp (algebraMap R (TrivSqZeroExt R M)) =
    (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl, (baseMap_isSum R B M).1]
  rfl

theorem unit_w : (show Sp R ⟶ A.left from η[A].left) ≫ A.hom = 𝟙 (Sp R) := by
  have := Over.w η[A]
  simpa using this

theorem fst_baseMap_left (v : TM R M ⟶ A) (h : zeroSec R M ≫ v = η[A]) :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap (baseMap R B M) ≫ v.left =
      spMap (algebraMap R B) ≫ (show Sp R ⟶ A.left from η[A].left) := by
  rw [← Category.assoc, spMap_comp', fst_comp_baseMap, ← spMap_comp', Category.assoc]
  congr 1
  exact congrArg Over.Hom.left h

theorem left_eq (v₁ v₂ : TM R M ⟶ A) (h₁ : zeroSec R M ≫ v₁ = η[A]) (h₂ : zeroSec R M ≫ v₂ = η[A])
    (e : spMap (baseMap R B M) ≫ v₁.left = spMap (baseMap R B M) ≫ v₂.left) : v₁ = v₂ := by
  obtain ⟨z₀, _, hu⟩ := _root_.GlobalTheory.Pinch.pinch_main R B M (baseMap R B M) (baseMap_isSum R B M) A.left
    (show Sp R ⟶ A.left from η[A].left) (spMap (baseMap R B M) ≫ v₁.left) (fst_baseMap_left A v₁ h₁)
  have a₁ := hu v₁.left ⟨congrArg Over.Hom.left h₁, rfl⟩
  have a₂ := hu v₂.left ⟨congrArg Over.Hom.left h₂, e.symm⟩
  exact Over.OverMorphism.ext (a₁.trans a₂.symm)

theorem lifts_baseMap (v : TM R M ⟶ A) (h : zeroSec R M ≫ v = η[A]) :
    Lifts A.hom (unitPt A B) (spMap (baseMap R B M) ≫ v.left) := by
  refine ⟨?_, fst_baseMap_left A v h⟩
  rw [Category.assoc, Over.w v]
  change spMap (baseMap R B M) ≫ spMap (algebraMap R (TrivSqZeroExt R M)) = _
  rw [spMap_comp', baseMap_comp_algebraMap]

theorem exists_of_lifts (z : Sp (TrivSqZeroExt B M) ⟶ A.left) (hz : Lifts A.hom (unitPt A B) z) :
    ∃ (v : TM R M ⟶ A) (_ : zeroSec R M ≫ v = η[A]), spMap (baseMap R B M) ≫ v.left = z := by
  obtain ⟨h₁, h₂⟩ := hz
  obtain ⟨z₀, ⟨a₁, a₂⟩, -⟩ := _root_.GlobalTheory.Pinch.pinch_main R B M (baseMap R B M) (baseMap_isSum R B M) A.left
    (show Sp R ⟶ A.left from η[A].left) z h₂
  have hb : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z ≫ A.hom =
      spMap (algebraMap R B) ≫ 𝟙 (Sp R) := by
    rw [← Category.assoc, h₂, unitPt, Category.assoc, unit_w]
  obtain ⟨y, -, hu⟩ := _root_.GlobalTheory.Pinch.pinch_main R B M (baseMap R B M) (baseMap_isSum R B M) (Sp R)
    (𝟙 (Sp R)) (z ≫ A.hom) hb
  have e₁ := hu (z₀ ≫ A.hom) ⟨by rw [← Category.assoc, a₁, unit_w], by rw [← Category.assoc, a₂]⟩
  have e₂ := hu (spMap (algebraMap R (TrivSqZeroExt R M))) ⟨by
      rw [spMap_comp']
      have : (TrivSqZeroExt.fstHom R R M).toRingHom.comp (algebraMap R (TrivSqZeroExt R M)) =
          RingHom.id R := by ext x; rfl
      rw [this]; simp only [spMap]; first | (rw [CommRingCat.ofHom_id, Spec.map_id]) | simp, by
      rw [spMap_comp', baseMap_comp_algebraMap, h₁]⟩
  refine ⟨Over.homMk z₀ (e₁.trans e₂.symm), Over.OverMorphism.ext a₁, a₂⟩

def phiLin (v : TM R M ⟶ A) (h : zeroSec R M ≫ v = η[A]) : Wmod A →ₗ[R] M where
  toFun := Phi v h
  map_add' := map_add _
  map_smul' r w := (_root_.GlobalTheory.SqZeroPt.Phi_linear_natural R A M v h).1 r w

theorem phiLin_congr {v₁ v₂ : TM R M ⟶ A} (h₁ : zeroSec R M ≫ v₁ = η[A])
    (h₂ : zeroSec R M ≫ v₂ = η[A]) (e : v₁ = v₂) : phiLin A v₁ h₁ = phiLin A v₂ h₂ := by
  subst e; rfl


open Classical in
def phiOf (z : Sp (TrivSqZeroExt B M) ⟶ A.left) : Wmod A →ₗ[R] M :=
  if hz : ∃ (v : TM R M ⟶ A) (_ : zeroSec R M ≫ v = η[A]), spMap (baseMap R B M) ≫ v.left = z then
    phiLin A hz.choose hz.choose_spec.choose
  else 0

theorem phiOf_eq (v : TM R M ⟶ A) (h : zeroSec R M ≫ v = η[A]) :
    phiOf A (spMap (baseMap R B M) ≫ v.left) = phiLin A v h := by
  have hz : ∃ (v' : TM R M ⟶ A) (_ : zeroSec R M ≫ v' = η[A]),
      spMap (baseMap R B M) ≫ v'.left = spMap (baseMap R B M) ≫ v.left := ⟨v, h, rfl⟩
  rw [phiOf, dite_eq_left hz]
  exact phiLin_congr A _ _ (left_eq A _ _ hz.choose_spec.choose h hz.choose_spec.choose_spec)

theorem cotangentAtUnit_tangentBijection (hq : (GlobalTheory.LieVB.omega A).IsQuasicoherent) (l : Wmod A →ₗ[R] M) :
    ∃! z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z ∧ phiOf A z = l := by
  obtain ⟨v, h, hv⟩ := _root_.GlobalTheory.SqZeroPt.exists_Phi_eq_of_linearMap R A hq M l
  refine ⟨spMap (baseMap R B M) ≫ v.left, ⟨lifts_baseMap A v h,
    (phiOf_eq A v h).trans (LinearMap.ext hv)⟩, fun z' ⟨hl, hp⟩ => ?_⟩
  obtain ⟨v', h', rfl⟩ := exists_of_lifts A z' hl
  rw [phiOf_eq A v' h'] at hp
  have e : v' = v := _root_.GlobalTheory.SqZeroPt.eq_of_Phi_eq R A hq M v' v h' h fun w => by
    change phiLin A v' h' w = _
    rw [hp, hv]
  rw [e]

end Pts

section Nat

variable (A : Over (Sp R)) [GrpObj A]
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M'] [Module Rᵐᵒᵖ M'] [IsCentralScalar R M']

theorem cotangentAtUnit_tangentBijection_naturality (α : B →ₐ[R] B') (f : M →ₗ[R] M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M')
    (hβ : IsSum β α f) (z : Sp (TrivSqZeroExt B M) ⟶ A.left) (hz : Lifts A.hom (unitPt A B) z) :
    phiOf A (spMap β ≫ z) = f ∘ₗ phiOf A z := by
  obtain ⟨v, h, rfl⟩ := exists_of_lifts A z hz
  let g : TrivSqZeroExt R M →+* TrivSqZeroExt R M' := (TrivSqZeroExt.map f).toRingHom
  have hg : IsSum g id f := ⟨fun r => TrivSqZeroExt.map_inl f r, fun m => TrivSqZeroExt.map_inr f m⟩
  have hw : (spMap g ≫ v.left) ≫ A.hom = (TM R M').hom := by
    rw [Category.assoc, Over.w v]
    change spMap g ≫ spMap (algebraMap R (TrivSqZeroExt R M)) = spMap (algebraMap R (TrivSqZeroExt R M'))
    rw [spMap_comp']
    exact congrArg spMap (TrivSqZeroExt.map f).comp_algebraMap
  let v' : TM R M' ⟶ A := Over.homMk (spMap g ≫ v.left) hw
  have h' : zeroSec R M' ≫ v' = η[A] := by
    apply Over.OverMorphism.ext
    change spMap (TrivSqZeroExt.fstHom R R M').toRingHom ≫ spMap g ≫ v.left = η[A].left
    rw [← Category.assoc, spMap_comp']
    have : (TrivSqZeroExt.fstHom R R M').toRingHom.comp g = (TrivSqZeroExt.fstHom R R M).toRingHom := by
      ext x; simp [g]
    rw [this]
    exact congrArg Over.Hom.left h
  have hc : (baseMap R B' M').comp g = β.comp (baseMap R B M) := by
    refine RingHom.ext fun x => ?_
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    simp only [RingHom.comp_apply, map_add (f := _), hg.1, hg.2, (baseMap_isSum R B M).1, (baseMap_isSum R B M).2,
      (baseMap_isSum R B' M').1, (baseMap_isSum R B' M').2, hβ.1, hβ.2, id, AlgHom.commutes]
  have e : spMap β ≫ spMap (baseMap R B M) ≫ v.left = spMap (baseMap R B' M') ≫ v'.left := by
    change _ = spMap (baseMap R B' M') ≫ spMap g ≫ v.left
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', hc]
  rw [e, phiOf_eq A v' h', phiOf_eq A v h]
  ext w
  exact (_root_.GlobalTheory.SqZeroPt.Phi_linear_natural R A M v h).2 M' f g hg v' h' rfl w

end Nat

def tanRep (A : Over (Sp R)) [GrpObj A] (hq : (GlobalTheory.LieVB.omega A).IsQuasicoherent) :
    TanRep A (Wmod A) where
  Φ := @fun B M _ _ _ _ _ _ _ _ z =>
    letI := opModule R M; haveI := opModule_central R M; phiOf A z
  bij := @fun B M _ _ _ _ _ _ _ _ l => by
    letI := opModule R M; haveI := opModule_central R M
    exact cotangentAtUnit_tangentBijection A hq l
  nat := @fun B M _ _ _ _ _ _ _ _ B' M' _ _ _ _ _ _ _ _ α f β hβ z hz => by
    letI := opModule R M; haveI := opModule_central R M
    letI := opModule R M'; haveI := opModule_central R M'
    exact cotangentAtUnit_tangentBijection_naturality A α f β hβ z hz

theorem exists_tanRep : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], Smooth A.hom →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W), Module.Finite R W ∧ Module.Projective R W ∧
      Nonempty (TanRep A W) := by
  intro R _ A _ hs
  haveI := hs
  have hfr := _root_.GlobalTheory.ConormalFrame.exists_isFrame_omega R A
  have hq : (GlobalTheory.LieVB.omega A).IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames hfr
  obtain ⟨hfin, hproj⟩ := _root_.GlobalTheory.FramesFGP.finite_projective_wmod R A hfr
  exact ⟨Wmod A, inferInstance, inferInstance, hfin, hproj, ⟨tanRep A hq⟩⟩

end GlobalTheory.TanRepr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
section
noncomputable section

namespace GlobalTheory.ThK.EvUniq

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def FinRel (B : Base F E) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (v : Pl F)
    (T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ) : Prop :=
  (∀ z, At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)) φ φ₁ →
      ∀ χ₁ ∈ SB (Fin n × Fin d₁ → Fv F v), Acts (evFin F v) (M₁.co.rho B.ψ z) (T φ) χ₁ → T φ₁ = χ₁) ∧
  ∀ u ∈ iso0 (F := F) n H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
    ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → T φ₁ = T φ

def InfRel (B : Base F E) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁)
    (T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁)) : Prop :=
  (∀ z, At (evI F) z → ∀ f f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)) f f₁ →
      ∀ g₁ : SInf F (Fin n × Fin d₁), Acts (evI F) (M₁.co.rho B.ψ z) (T f) g₁ → T f₁ = g₁) ∧
  ∀ u ∈ iso0 (F := F) n H', At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (M.co.rho B.ψ u) f f₁ → T f₁ = T f

end GlobalTheory.ThK.EvUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicUnitRootsBoundedDenominatorNumberFiel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem monic_roots_norm_one_coeff_denom_finite : ∀ (E : Type) [Field E] [NumberField E] (n d : ℕ), d ≠ 0 → {P : E[X] | P.Monic ∧ P.natDegree = n ∧ (∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) ∧ ∀ k, ∃ a : 𝓞 E, (a : E) = d * P.coeff k}.Finite := by
  intro E _ _ n d hd
  set T := {P : E[X] | P.Monic ∧ P.natDegree = n ∧ (∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) ∧ ∀ k, ∃ a : 𝓞 E, (a : E) = d * P.coeff k} with hT
  set B : ℝ := max 1 1 ^ n * (n.choose (n / 2) : ℝ) with hB
  set S : Set E := {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ) * B} with hS
  have hSf : S.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ ((d : ℝ) * B)
  let F : E[X] → (Fin (n+1) → E) := fun P k => (d : E) * P.coeff k
  have hpi : (Set.pi Set.univ (fun _ : Fin (n+1) => S)).Finite := Set.Finite.pi (fun _ => hSf)
  have himg : F '' T ⊆ Set.pi Set.univ (fun _ : Fin (n+1) => S) := by
    rintro _ ⟨P, ⟨hm, hn, hr, hc⟩, rfl⟩ k _
    obtain ⟨a, ha⟩ := hc k
    refine ⟨?_, fun φ => ?_⟩
    · show IsIntegral ℤ ((d : E) * P.coeff k)
      rw [← ha]; exact a.isIntegral_coe
    · have hbd := Polynomial.coeff_bdd_of_roots_le (B := 1) (d := n) φ hm (IsAlgClosed.splits _) hn.le
        (fun z hz => (hr φ z hz).le) k
      rw [Polynomial.coeff_map] at hbd
      show ‖φ ((d : E) * P.coeff k)‖ ≤ (d : ℝ) * B
      rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg d)
  have hinj : Set.InjOn F T := by
    rintro P ⟨-, hP, -⟩ Q ⟨-, hQ, -⟩ hPQ
    ext k
    by_cases hk : k < n + 1
    · have := congrFun hPQ ⟨k, hk⟩
      simp only [F] at this
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hd) this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  exact Set.Finite.of_finite_image (hpi.subset himg) hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoordinatesActionOfIdentityOffPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coordinates_action_of_identity_off_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ x y, ι (x * y) = ι x * ι y) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L) (A : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin d) (Fin d) L)
        (g : UA σ X.J) (h : UA σ W.J),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι →
        mat h = (1 - ι 1) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι →
        ∀ x, actAB (cA σ) (g, h) (GlobalTheory.InertLocFrame.xm ι PV PW x) =
          (A * (PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ * Cᵀ).map ι := by
  first | exact @GlobalTheory.InertLocFrame.actAB_xm_frame | exact GlobalTheory.InertLocFrame.actAB_xm_frame | (intros; apply GlobalTheory.InertLocFrame.actAB_xm_frame <;> assumption)
end

