module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulKerMemSpanTrBasisDiff
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace GlobalTheory.FieldPair

section Graph

variable {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (ρ : κ →ₐ[ℂ] κ')

private def graphDiff (a : κ) : κ ⊗[ℂ] κ' := a ⊗ₜ[ℂ] (1 : κ') - (1 : κ) ⊗ₜ[ℂ] ρ a

private theorem tmul_one_mul (a b : κ) :
    (a * b) ⊗ₜ[ℂ] (1 : κ') = (a ⊗ₜ[ℂ] (1 : κ')) * (b ⊗ₜ[ℂ] (1 : κ')) := by
  simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem one_tmul_mul (a b : κ') :
    (1 : κ) ⊗ₜ[ℂ] (a * b) = ((1 : κ) ⊗ₜ[ℂ] a) * ((1 : κ) ⊗ₜ[ℂ] b) := by
  simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem graphDiff_mul (a b : κ) :
    graphDiff ρ (a * b) = (a ⊗ₜ[ℂ] (1 : κ')) * graphDiff ρ b + ((1 : κ) ⊗ₜ[ℂ] ρ b) * graphDiff ρ a := by
  simp only [graphDiff, map_mul, tmul_one_mul, one_tmul_mul]
  ring

private theorem graphDiff_mul' (a b : κ) :
    graphDiff ρ (a * b) - ((a ⊗ₜ[ℂ] (1 : κ')) * graphDiff ρ b + (b ⊗ₜ[ℂ] (1 : κ')) * graphDiff ρ a) =
      -(graphDiff ρ a * graphDiff ρ b) := by
  simp only [graphDiff, map_mul, tmul_one_mul, one_tmul_mul]
  ring

private theorem graphDiff_add (a b : κ) : graphDiff ρ (a + b) = graphDiff ρ a + graphDiff ρ b := by
  simp only [graphDiff, map_add (f := _), TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

private theorem graphDiff_algebraMap (r : ℂ) : graphDiff ρ (algebraMap ℂ κ r) = 0 := by
  simp only [graphDiff, AlgHom.commutes]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]

private theorem graphDiff_inv (a : κ) (ha : a ≠ 0) :
    graphDiff ρ a⁻¹ = -((a⁻¹ ⊗ₜ[ℂ] ρ a⁻¹) * graphDiff ρ a) := by
  have h1 : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  simp only [graphDiff, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ ha, mul_one,
    one_mul, h1]
  abel

private def closureField (L : Ideal (κ ⊗[ℂ] κ')) : IntermediateField ℂ κ where
  carrier := {a | graphDiff ρ a ∈ L}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, graphDiff_mul] at *
    exact L.add_mem (L.mul_mem_left _ hb) (L.mul_mem_left _ ha)
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, graphDiff_add] at *
    exact L.add_mem ha hb
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq, graphDiff_algebraMap]
    exact L.zero_mem
  inv_mem' a ha := by
    by_cases h : a = 0
    · subst h; simpa using ha
    · simp only [Set.mem_setOf_eq, graphDiff_inv ρ a h] at *
      exact L.neg_mem (L.mul_mem_left _ ha)

private theorem sub_mem_span (x : κ ⊗[ℂ] κ') :
    x - (1 : κ) ⊗ₜ[ℂ] (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x) ∈
      Ideal.span (Set.range (graphDiff ρ)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    have e : a ⊗ₜ[ℂ] b - (1 : κ) ⊗ₜ[ℂ] (ρ a * (AlgHom.id ℂ κ') b) = graphDiff ρ a * ((1 : κ) ⊗ₜ[ℂ] b) := by
      simp [graphDiff, sub_mul, Algebra.TensorProduct.tmul_mul_tmul]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, rfl⟩)
  | add x y hx hy =>
    rw [map_add (f := _), TensorProduct.tmul_add]
    convert Ideal.add_mem _ hx hy using 1
    abel

private theorem graphDiff_mem_ker (a : κ) :
    graphDiff ρ a ∈ RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) := by
  simp [graphDiff, RingHom.mem_ker, Algebra.TensorProduct.productMap_apply_tmul]

private theorem ker_le_span :
    RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) ≤
      Ideal.span (Set.range (graphDiff ρ)) := by
  intro x hx
  have h := sub_mem_span ρ x
  rw [RingHom.mem_ker] at hx
  rwa [hx, TensorProduct.tmul_zero, sub_zero] at h

private theorem graphDiff_mem_of_isAlgebraic (L : Ideal (κ ⊗[ℂ] κ'))
    (hL : RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) *
      RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) ≤ L)
    (K : IntermediateField ℂ κ) (hK : K ≤ closureField ρ L) [Algebra.IsAlgebraic K κ] (x : κ) :
    graphDiff ρ x ∈ L := by
  let D0 : κ →ₗ[ℂ] (κ ⊗[ℂ] κ') ⧸ L := (Ideal.Quotient.mkₐ ℂ L).toLinearMap ∘ₗ
    ((TensorProduct.mk ℂ κ κ').flip 1 - (TensorProduct.mk ℂ κ κ' 1) ∘ₗ ρ.toLinearMap)
  have hD0 : ∀ a, D0 a = Ideal.Quotient.mk L (graphDiff ρ a) := fun a => rfl
  have hsmul : ∀ (a : κ) (y : κ ⊗[ℂ] κ'),
      a • Ideal.Quotient.mk L y = Ideal.Quotient.mk L ((a ⊗ₜ[ℂ] (1 : κ')) * y) := by
    intro a y
    rw [← Ideal.Quotient.mkₐ_eq_mk κ, ← map_smul, Algebra.smul_def,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  let D : Derivation ℂ κ ((κ ⊗[ℂ] κ') ⧸ L) := Derivation.mk' D0 (fun a b => by
    rw [hD0, hD0, hD0, hsmul, hsmul, ← map_add (f := _), Ideal.Quotient.eq, graphDiff_mul']
    exact L.neg_mem (hL (Ideal.mul_mem_mul (graphDiff_mem_ker ρ a) (graphDiff_mem_ker ρ b))))
  have hD : ∀ a, D a = Ideal.Quotient.mk L (graphDiff ρ a) := fun a => rfl
  letI : Module K ((κ ⊗[ℂ] κ') ⧸ L) := Module.compHom _ (algebraMap K κ)
  have key := Derivation.apply_aeval_eq' (0 : Derivation ℂ K ((κ ⊗[ℂ] κ') ⧸ L)) D 0
    (fun c => by
      rw [LinearMap.zero_apply, hD, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact hK c.2) x (minpoly K x)
  simp only [minpoly.aeval, map_zero, LinearMap.zero_apply, zero_add] at key
  have hne := Polynomial.Separable.aeval_derivative_ne_zero (Algebra.IsSeparable.isSeparable K x)
    (minpoly.aeval K x)
  have h0 : D x = 0 := by
    have hz : ∀ q, PolynomialModule.map κ (0 : ((κ ⊗[ℂ] κ') ⧸ L) →ₗ[K] ((κ ⊗[ℂ] κ') ⧸ L)) q = 0 := by
      intro q
      ext i
      simp [PolynomialModule.map]
    have key' := key.symm
    rw [hz, map_zero, zero_add] at key'
    have h2 := congrArg (fun v => ((Polynomial.aeval x) (Polynomial.derivative (minpoly K x)))⁻¹ • v) key'
    simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] using h2
  rwa [hD, Ideal.Quotient.eq_zero_iff_mem] at h0

end Graph

theorem exists_mul_ker_mem_span_trBasis_diff :
    ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k : ℕ) (z : Fin k → κ) (ρ : κ →ₐ[ℂ] κ') (O : Subring κ), TrBasis (algebraMap ℂ κ) z → IsLocModel (algebraMap ℂ κ) O → ∃ e : TensorProduct ℂ κ κ', Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') e = 1 ∧ ∀ a ∈ RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')), e * a ∈ Ideal.span (Set.range fun i => (TensorProduct.tmul ℂ (z i) (1 : κ') - TensorProduct.tmul ℂ (1 : κ) (ρ (z i)))) := by
  intro κ κ' _ _ _ _ k z ρ O hz hO
  set J := RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) with hJ
  set I := Ideal.span (Set.range fun i =>
    (TensorProduct.tmul ℂ (z i) (1 : κ') - TensorProduct.tmul ℂ (1 : κ) (ρ (z i)))) with hI

  have hfg : J.FG := by
    letI := ((algebraMap ℂ κ).codRestrict O hO.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType
    obtain ⟨s, hs⟩ := Algebra.EssFiniteType.cond (R := ℂ) (S := O)
    set L₀ : Ideal (κ ⊗[ℂ] κ') := Ideal.span (graphDiff ρ '' ((↑) '' (s : Set O))) with hL₀
    have hadj : ∀ w : O, w ∈ Algebra.adjoin ℂ (s : Set O) → (w : κ) ∈ closureField ρ L₀ := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => exact Ideal.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      | algebraMap r => exact (closureField ρ L₀).algebraMap_mem r
      | add x y _ _ hx hy => exact (closureField ρ L₀).add_mem hx hy
      | mul x y _ _ hx hy => exact (closureField ρ L₀).mul_mem hx hy
    have hO' : ∀ y : O, (y : κ) ∈ closureField ρ L₀ := by
      intro y
      obtain ⟨⟨a, u⟩, e⟩ := @IsLocalization.surj _ _ _ _ _ _ hs y
      have hu : IsUnit ((u : Algebra.adjoin ℂ (s : Set O)) : O) := u.2
      have hu0 : (((u : Algebra.adjoin ℂ (s : Set O)) : O) : κ) ≠ 0 := by
        intro h0
        exact hu.ne_zero (Subtype.ext h0)
      have e' : (y : κ) * (((u : Algebra.adjoin ℂ (s : Set O)) : O) : κ) =
          ((a : O) : κ) := congrArg Subtype.val e
      rw [← eq_div_iff hu0] at e'
      rw [e', div_eq_mul_inv]
      exact (closureField ρ L₀).mul_mem (hadj _ a.2) ((closureField ρ L₀).inv_mem (hadj _ (u : Algebra.adjoin ℂ (s : Set O)).2))
    have hall : ∀ x : κ, x ∈ closureField ρ L₀ := by
      intro x
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hO.frac x
      rw [← eq_div_iff hb0] at e
      rw [e, div_eq_mul_inv]
      exact (closureField ρ L₀).mul_mem (hO' ⟨a, ha⟩) ((closureField ρ L₀).inv_mem (hO' ⟨b, hb⟩))
    have hJL : J = L₀ := le_antisymm
      ((ker_le_span ρ).trans (Ideal.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hall a)))
      (Ideal.span_le.2 (by rintro _ ⟨a, -, rfl⟩; exact graphDiff_mem_ker ρ a))
    rw [hJL, hL₀]
    exact Submodule.fg_span ((s.finite_toSet.image _).image _)

  have hle : J ≤ I ⊔ J * J := by
    have hz' : IsTranscendenceBasis ℂ z := by
      have e : (algebraMap ℂ κ).toAlgebra = ‹Algebra ℂ κ› := Algebra.algebra_ext _ _ fun _ => rfl
      unfold TrBasis at hz
      rwa [e] at hz
    haveI := hz'.isAlgebraic_field
    have hK : IntermediateField.adjoin ℂ (Set.range z) ≤ closureField ρ (I ⊔ J * J) := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
    refine (ker_le_span ρ).trans (Ideal.span_le.2 ?_)
    rintro _ ⟨a, rfl⟩
    exact graphDiff_mem_of_isAlgebraic ρ _ le_sup_right _ hK a
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl hle
  refine ⟨r, ?_, fun a ha => ?_⟩
  · rw [hJ, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hr1
    exact hr1
  · have := hr (Submodule.smul_mem_pointwise_smul a r J ha)
    rwa [smul_eq_mul] at this

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem lbIso_lam_pull_of_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₁ : Over S') [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G f β → ∃ β₂ : (G2 G₁).left ⟶ (G2 G).left, Geo.Tor.IsSquare β β₂ ∧ ∀ (L : LB G.left) (N : LB G₁.left) (X : Scheme.{0}) (Q : LB X) (h : (G2 G).left ⟶ X), L.IsLB → N.IsLB → Q.IsLB → LBIso N (L.pull β) → LBIso (abelian₂ G L) (Q.pull h) → LBIso (abelian₂ G₁ N) (Q.pull (β₂ ≫ h)) := by
  intro S S' f G _ _ G₁ _ _ β hpb
  let U : Over.mk ((G2 G₁).hom ≫ f) ⟶ G2 G := lift (pushPt hpb.1.w (fst G₁ G₁)) (pushPt hpb.1.w (snd G₁ G₁))
  have hU1 : U ≫ fst G G = pushPt hpb.1.w (fst G₁ G₁) := lift_fst _ _
  have hU2 : U ≫ snd G G = pushPt hpb.1.w (snd G₁ G₁) := lift_snd _ _
  refine ⟨U.left, ⟨congrArg (fun z => z.left) hU1, congrArg (fun z => z.left) hU2⟩, ?_⟩
  intro L N X Q h hL hN hQ hNL hLam
  have hx : ∀ i, pushPt hpb.1.w (x2 G₁ i) = U ≫ x2 G i := by
    intro i
    fin_cases i
    · exact hU1.symm
    · exact hU2.symm
  have e₁ : LBIso ((abelian₂ G L).pull U.left) (abelian₂ G₁ N) :=
    GlobalTheory.CM.TripleModel.lbIso_cube_pull hpb hL hN hNL.symm (x2 G₁) (x2 G) U hx
  have hLamL : (abelian₂ G L).IsLB := DVR.linComb_isLB _ hL _ _
  have e₂ : LBIso ((abelian₂ G L).pull U.left) (Q.pull (U.left ≫ h)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ G L) U.left U.left rfl)
      (chartPullSame Q (fun _ => U.left ≫ h) (fun _ => h) (fun _ => 1) U.left fun _ => rfl) hLam
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hLamL _) (pull_isLB hQ _) e₁.symm e₂

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatPosDefAddNsmulPosDefHermitian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem posn_quad_hom {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (r : ℝ) :
    (((r : ℂ) • z) ⬝ᵥ H.mulVec (star ((r : ℂ) • z))).re = r ^ 2 * (z ⬝ᵥ H.mulVec (star z)).re := by
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, ← _root_.mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  ring

theorem posn_quad_add {g : ℕ} (H₀ Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ) (z : Fin g → ℂ) :
    (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re
      = (z ⬝ᵥ Hm.mulVec (star z)).re + n * (z ⬝ᵥ H₀.mulVec (star z)).re := by
  have h1 : (n • H₀).mulVec (star z) = n • H₀.mulVec (star z) := by
    ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, _root_.mul_assoc]
  rw [Matrix.add_mulVec, dotProduct_add, h1, dotProduct_smul, Complex.add_re, nsmul_eq_mul,
    ← Complex.ofReal_natCast, Complex.re_ofReal_mul]

theorem posn_cont {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z : Fin g → ℂ => (z ⬝ᵥ H.mulVec (star z)).re := by
  fun_prop

theorem posn_main : ∀ (g : ℕ) (H₀ Hm : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) →
    ∃ n : ℕ, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re := by
  intro g H₀ Hm hpos

  have hnorm : ∀ z : Fin g → ℂ, z ≠ 0 →
      ((((‖z‖⁻¹ : ℝ) : ℂ) • z) ∈ Metric.sphere (0 : Fin g → ℂ) 1) := by
    intro z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

  have hred : ∀ (H : Matrix (Fin g) (Fin g) ℂ),
      (∀ w ∈ Metric.sphere (0 : Fin g → ℂ) 1, 0 < (w ⬝ᵥ H.mulVec (star w)).re) →
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re := by
    intro H hS z hz
    have h := hS _ (hnorm z hz)
    rw [posn_quad_hom] at h
    exact pos_of_mul_pos_right h (sq_nonneg _)
  by_cases hne : (Metric.sphere (0 : Fin g → ℂ) 1).Nonempty
  · have hK : IsCompact (Metric.sphere (0 : Fin g → ℂ) 1) := isCompact_sphere 0 1
    obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne (posn_cont H₀).continuousOn
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (posn_cont Hm).continuousOn
    have hw₀ne : w₀ ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hw₀; exact zero_ne_one hw₀
    set m := (w₀ ⬝ᵥ H₀.mulVec (star w₀)).re with hm
    have hm0 : 0 < m := hpos w₀ hw₀ne
    obtain ⟨n, hn⟩ := exists_nat_gt (C / m)
    refine ⟨n, hred _ ?_⟩
    intro w hw
    rw [posn_quad_add]
    have h1 : m ≤ (w ⬝ᵥ H₀.mulVec (star w)).re := hmin hw
    have h2 : |(w ⬝ᵥ Hm.mulVec (star w)).re| ≤ C := by
      simpa [Real.norm_eq_abs] using hC w hw
    have h3 : C < n * m := by rwa [div_lt_iff₀ hm0] at hn
    have h4 : (n : ℝ) * m ≤ n * (w ⬝ᵥ H₀.mulVec (star w)).re :=
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
    have h5 := neg_abs_le (w ⬝ᵥ Hm.mulVec (star w)).re
    linarith
  · refine ⟨0, fun z hz => absurd ⟨_, hnorm z hz⟩ hne⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalLiftOfDefectCoboundary
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_natLift_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → ∀ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) → (∀ (r : R) w, u (π r • w) = r • u w) → (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) → (∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T)) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar C' _ F' L L' n l hl κ u hκ hus hum hκd
  have hext : ∀ T : C', ∃! ξ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T,
      (∀ b w, ξ (L.p (n.G.obj T) b • w) = l T b * ξ w) ∧
      (∀ w, ξ w ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ w : GlobForm s₀, ξ (w.1 (n.G.obj T)) = u w T := fun T ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T) ((Pi.evalAddMonoidHom _ T).comp u)
      (fun r w ↦ by simp [hus]) (fun w ↦ hum w T)
  choose ξ hξ using fun T ↦ (hext T).exists
  have hψ : ∀ T : C', ∃ ψ : L.B (n.G.obj T) →ₐ[R] L'.B T,
      IsTheta I (L.p (n.G.obj T)) (l T) ψ (-ξ T) := fun T ↦
    (_root_.GlobalTheory.LiftSys.theta_classify R R₀ (L.B (n.G.obj T)) (Sec s₀ (n.G.obj T).unop.1) (L'.B T) I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T)).2 (-ξ T)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hξ T).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hξ T).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ T b, ψ T b = l T b + ξ T (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) := fun T b ↦ by
    have h := (hψ T).der b
    rw [AddMonoidHom.neg_apply] at h
    change -ξ T _ = l T b - ψ T b at h
    linear_combination h
  refine ⟨ψ, fun T b ↦ ?_, fun T T' a b ↦ ?_⟩
  · rw [hψv, map_add (f := _), hl, (L'.ker T _).2 ((hξ T).2.1 _), add_zero]
  · let α : L.B (n.G.obj T) →ₐ[R] L'.B T' := (L'.ρ a).comp (l T)
    let χ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T' := κ T T' a + (L'.ρ a).toAddMonoidHom.comp (ξ T) -
      (ξ T').comp (p1 (OAff s₀) (n.G.map a)).toAddMonoidHom
    have hχ : ∀ w, χ w = κ T T' a w + L'.ρ a (ξ T w) - ξ T' (p1 (OAff s₀) (n.G.map a) w) := fun _ ↦ rfl
    have hmemV : ∀ w, ξ T' w ∈ I.map (algebraMap R (L'.B T')) := (hξ T').2.1
    have hdiff : ∀ c : L.B (n.G.obj T), ∀ x ∈ I.map (algebraMap R (L'.B T')),
        l T' (L.ρ (n.G.map a) c) * x = α c * x := by
      intro c x hx
      have h1 := (hκ T T' a).der c
      have h2 : α c - l T' (L.ρ (n.G.map a) c) ∈ I.map (algebraMap R (L'.B T')) :=
        h1 ▸ (hκ T T' a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T') (L.p _)
      (L.semi _) (L.surj _) (L.ker _) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hκ T T' a).smul, (hξ T).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← L.nat (n.G.map a) b, (hξ T').1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hκ T T' a).mem w) (algHom_mem_map I _ ((hξ T).2.1 w))) (hmemV _)
      · rw [hχ, hκd, (hξ T).2.2, ← w.2 (n.G.map a), (hξ T').2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) (n.G.map a) (L.p _ b) = L.p _ (L.ρ (n.G.map a) b) := (L.nat (n.G.map a) b).symm
    rw [hn] at h0
    have h1 := (hκ T T' a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add (f := _)]
    linear_combination h0 - h1

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsCharacterUnitKernelAction
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem exists_nhds_charUnit : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∀ y : (A' ⊗ T).left, ∃ V : (A' ⊗ T).left.Opens, y ∈ V ∧ ∃ e : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ V)ˣ, ∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)) (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)), res h₁ (pullU (actMap i T).left _ e) = res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ e) := by
  intro S A A' N T _ _ _ i q χ hi hq hfin hflat hsurj hk hχ y
  have hpb := _root_.GlobalTheory.CharKer.pmap_isPullback_actMap S A A' N T i q hi hq hk
  have hpb' : IsPullback (prMap A N T).left (actMap i T).left (pmap q T).left (pmap q T).left :=
    hpb.map (Over.forget S)
  obtain ⟨W, m₁₂, m₂₃, m₁₃, h1, h2, h3, h4⟩ := _root_.GlobalTheory.CharKer.triOverlap S A N T i χ hi hχ
  have hpq : pmap q T = q ▷ T := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [pmap]
  have hsq := GlobalTheory.SemiRigid.isPullback_whiskerRight q T
  have hA : IsAffineHom (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  have hF : Flat (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  have hS : Surjective (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  exact _root_.GlobalTheory.CharKer.exists_local_charUnit _ _ _ _ (pmap q T).left (actMap i T).left (prMap A N T).left m₁₂ m₂₃ m₁₃ _
    hA hF hS hpb' h1 h2 h3 h4 y

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSolveMvPowerSeriesMatrixIdentityConst
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

open Matrix

theorem powerSeries_matrix_solve : ∀ (n : ℕ) (R : Type) [CommRing R] (J : Fin n → Fin n → MvPowerSeries (Fin n) R), (∀ i j, MvPowerSeries.constantCoeff (J i j) = if i = j then 1 else 0) → ∀ b : Fin n → MvPowerSeries (Fin n) R, ∃ G : Fin n → MvPowerSeries (Fin n) R, ∀ i, ∑ j, G j * J i j = b i := by
  intro n R _ J hJ b
  let M : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) R) := Matrix.of J
  have hM : (MvPowerSeries.constantCoeff (σ := Fin n) (R := R)).mapMatrix M = 1 := by
    ext i j
    simp [M, Matrix.one_apply, hJ]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hM, Matrix.det_one]
    exact isUnit_one
  refine ⟨M⁻¹ *ᵥ b, fun i => ?_⟩
  have h := congrFun (Matrix.mulVec_mulVec b M M⁻¹) i
  rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end GlobalTheory
end

