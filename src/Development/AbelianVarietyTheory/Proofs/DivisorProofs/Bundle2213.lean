module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorus
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.riemann_polarised_torus : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (A : Over (Sp ℂ)) (_ : GrpObj A), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧
      ∃ (L : LB A.left) (u : HolUnif A L g) (χ : u.Λ → ℂ), L.IsLB ∧ (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  intro g Λ Hm hd hf hH hpos hint
  obtain ⟨Λ₁, N, Ef, hle, hN, hNΛ, hd₁, hf₁, hE, hbij⟩ := _root_.GlobalTheory.UnimodOver.exists_unimodular_overlattice g Λ Hm hd hf hH hpos hint
  obtain ⟨P, u, χ, hPg, hu, hAH, -, -⟩ := GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd₁ hf₁ hH hpos hE hbij
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := fun z => u.ex ((N : ℂ)⁻¹ • z) with he
  have e_add : ∀ z w, e (z + w) = e z * e w := fun z w => by simp only [he, smul_add, u.ex_add]
  have e_zero : e 0 = 1 := by
    have h := e_add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have e_nsmul : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => simp [e_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, e_add, ih, pow_succ]
  have e_N : ∀ z, e ((N : ℂ) • z) = u.ex z := fun z => by
    simp only [he, smul_smul, inv_mul_cancel₀ hNc, one_smul]
  have e_sub : ∀ z w, e (z - w) * e w = e z := fun z w => by rw [← e_add, sub_add_cancel]
  let C : Subgroup (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { carrier := e '' (Λ : Set (Fin g → ℂ))
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, Λ.add_mem ha hb, e_add a b⟩
      one_mem' := ⟨0, Λ.zero_mem, e_zero⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨-a, Λ.neg_mem ha, ?_⟩
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← e_add, neg_add_cancel, e_zero] }
  have hCfin : Finite C := by
    have := (_root_.GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples g Λ _ e N hd hf e_add hN fun l hl => by
      rw [e_N, u.ker, hu]; exact hle hl).to_subtype
    exact this
  have hA := P.isAb
  have := hA.proper
  have := hA.comm
  obtain ⟨A, _, ψ, hA', hψ, hψf, hψe, hψs, hker⟩ := GlobalTheory.exists_quotient_abelian_by_finite_points ℂ P.A hA C hCfin
  have := hA'.smooth
  have hmon : IsMonHom (𝟙 P.A ^ N) := GlobalTheory.GrpTangent.mulN_eq_pow P.A _ ▸ GlobalTheory.GrpTangent.isMonHom_mulN P.A _
  obtain ⟨⟨φ, hφ, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ P.A A P.A ψ (𝟙 P.A ^ N) hψ hmon
    inferInstance hψs inferInstance fun T z hz => by
      rw [MonObj.comp_pow, Category.comp_id]
      refine GlobalTheory.SS.PrincIsog.pow_eq_one_of_etale ψ N (fun y hy => ?_) T z hz
      obtain ⟨c, ⟨l, hl, rfl⟩, rfl⟩ := (hker ℂ (𝟙 _) y).1 hy
      rw [← MonObj.comp_pow, ← e_nsmul, e_N, (u.ker l).2 (hu ▸ hle hl), MonObj.comp_one]
  have htu : toUnit (Over.mk (𝟙 (Sp ℂ))) = 𝟙 (𝟙_ (Over (Sp ℂ))) := toUnit_unique _ _
  let exA : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun z => e z ≫ ψ
  have exA_add : ∀ z w, exA (z + w) = exA z * exA w := fun z w => by
    simp only [exA, e_add, MonObj.mul_comp]
  have exA_onto : Function.Surjective exA := by
    intro x
    obtain ⟨b, hb⟩ := GlobalTheory.SS.PrincIsog.exists_lift_point (F := ℂ) ψ.left x.left
    let b' : 𝟙_ (Over (Sp ℂ)) ⟶ P.A := Over.homMk b (by
      rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w _)
    have hb' : b' ≫ ψ = x := Over.OverMorphism.ext hb
    obtain ⟨w, hw⟩ := u.ex_onto b'
    exact ⟨(N : ℂ) • w, by simp only [exA, e_N, hw, hb']⟩
  have exA_ker : ∀ z, exA z = 1 ↔ z ∈ Λ := by
    intro z
    constructor
    · intro h
      obtain ⟨c, ⟨l, hl, rfl⟩, hc'⟩ := (hker ℂ (𝟙 _) (e z)).1 h
      rw [htu] at hc'
      replace hc' : e z = e l := hc'.trans (Category.id_comp _)
      have h1 : e (z - l) = 1 := by
        have := e_sub z l
        rw [hc'] at this
        exact mul_eq_right.1 this
      have h2 := (u.ker _).1 h1
      rw [hu] at h2
      have h3 := hNΛ _ h2
      rw [smul_smul, mul_inv_cancel₀ hNc, one_smul] at h3
      have := Λ.add_mem h3 hl
      rwa [sub_add_cancel] at this
    · intro hz
      exact (hker ℂ (𝟙 _) (e z)).2 ⟨e z, ⟨z, hz, rfl⟩, by rw [htu]; exact (Category.id_comp _).symm⟩
  have hcl : Continuous (fun z : Fin g → ℂ => (N : ℂ)⁻¹ • z) := continuous_const_smul _
  have exA_hol : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (exA z).left U f) {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} := by
    intro U f
    have hs : {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} =
        (fun z => (N : ℂ)⁻¹ • z) ⁻¹' {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (ψ.left ⁻¹ᵁ U)} := by
      ext z
      simp only [exA, he, Over.comp_left, Scheme.Hom.comp_preimage, Set.mem_setOf_eq, Set.mem_preimage]
    have hv : (fun z => valAt' (exA z).left U f) =
        (fun w => valAt' (u.ex w).left (ψ.left ⁻¹ᵁ U) ((ψ.left.app U).hom f)) ∘ (fun z => (N : ℂ)⁻¹ • z) := by
      funext z
      simp only [Function.comp, exA, he, Over.comp_left, GlobalTheory.valAt'_comp]
    refine ⟨hs ▸ (u.hol _ ((ψ.left.app U).hom f)).1.preimage hcl, ?_⟩
    rw [hs, hv]
    exact (u.hol _ _).2.comp ((differentiable_id (𝕜 := ℂ) (E := Fin g → ℂ)).const_smul ((N : ℂ)⁻¹)).differentiableOn (fun z hz => hz)
  have hcomp : ∀ z, exA z ≫ φ = u.ex z := fun z => by
    simp only [exA, Category.assoc, hc, MonObj.comp_pow, Category.comp_id]
    rw [← e_nsmul, e_N]
  obtain ⟨uA, χA, hΛA, hAHA⟩ := _root_.GlobalTheory.PullUnifHom.exists_holUnif_pull_hom A P.A φ P.L g u exA Λ Hm χ exA_add exA_onto exA_ker hd hf
    exA_hol hcomp (hu ▸ hle) hAH
  have hsm : SmoothOfRelativeDimension g A.hom :=
    GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover ℂ _ _ ψ.left A.hom g hψe hψs inferInstance
      (by rw [Over.w]; exact hPg ▸ P.smoothDim)
  exact ⟨A, inferInstance, hA', hsm, P.L.pull φ.left, uA, χA, pull_isLB P.isLB _, hΛA, hAHA⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddEqOfTrBasis
section
set_option autoImplicit false

noncomputable section

open Algebra

namespace GlobalTheory.LocModelDim

theorem isAlgebraic_of_forall_mul {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ s : S, ∃ a b : R, algebraMap R S b ≠ 0 ∧ s * algebraMap R S b = algebraMap R S a) :
    Algebra.IsAlgebraic R S := by
  refine ⟨fun s => ?_⟩
  obtain ⟨a, b, hb, e⟩ := h s
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h0 => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 1) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_succ,
      sub_zero, Polynomial.coeff_zero, if_true] at h1
    rw [h1, map_zero]
  · rw [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C, mul_comm, e,
      sub_self]

theorem ringKrullDim_add_trdeg {k R Ω : Type} [Field k] [CommRing R] [IsDomain R]
    [IsLocalRing R] [Algebra k R] [Algebra.EssFiniteType k R] [Field Ω] [Algebra R Ω]
    [Algebra k Ω] [IsScalarTower k R Ω] (hχ : Function.Surjective (algebraMap R Ω)) {n m : ℕ}
    (hn : trdeg k Ω = n) (hm : trdeg k R = m) : ringKrullDim R + n = m := by
  set A := EssFiniteType.subalgebra k R
  set ι := algebraMap A R
  set f : A →+* Ω := (algebraMap R Ω).comp ι with hf
  set P := RingHom.ker f with hP
  haveI : P.IsPrime := RingHom.ker_isPrime f
  have hmax : RingHom.ker (algebraMap R Ω) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hχ)
  have hunit : ∀ r : R, IsUnit r ↔ algebraMap R Ω r ≠ 0 := by
    intro r
    have := congrArg (r ∈ ·) hmax
    simp only [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
    rw [Ne, this, not_not]
  have hM : EssFiniteType.submonoid k R = P.primeCompl := by
    ext x
    simp only [EssFiniteType.submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff,
      Ideal.mem_primeCompl_iff, hP, RingHom.mem_ker, hf, RingHom.comp_apply, hunit]
    rfl
  haveI : IsLocalization.AtPrime R P := by
    unfold IsLocalization.AtPrime
    rw [← hM]
    infer_instance

  have hdimR : ringKrullDim R = P.height := IsLocalization.AtPrime.ringKrullDim_eq_height P R
  have hform := GlobalTheory.height_add_ringKrullDim_quotient_of_finiteType k P
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
  haveI : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) Ideal.Quotient.mk_surjective
  obtain ⟨s', hs1', hs2'⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A ⧸ P)

  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (EssFiniteType.submonoid k R)
  have hAR := trdeg_add_eq k A (A := R)
  rw [trdeg_eq_zero (R := A) (A := R), add_zero, hs2, hm] at hAR

  letI : Algebra (A ⧸ P) Ω := (RingHom.kerLift f).toAlgebra
  haveI : IsScalarTower k (A ⧸ P) Ω := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap k Ω x = f (algebraMap k A x)
    rw [hf, RingHom.comp_apply, IsScalarTower.algebraMap_apply k R Ω]
    rfl
  haveI : FaithfulSMul (A ⧸ P) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective f)
  haveI : Algebra.IsAlgebraic (A ⧸ P) Ω := by
    apply isAlgebraic_of_forall_mul
    intro ω
    obtain ⟨r, rfl⟩ := hχ ω
    obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (EssFiniteType.submonoid k R) r
    refine ⟨Ideal.Quotient.mk P a, Ideal.Quotient.mk P t, ?_, ?_⟩
    · change f t ≠ 0
      exact (hunit _).1 t.2
    · change algebraMap R Ω r * f t = f a
      rw [hf, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      exact congrArg (algebraMap R Ω) e
  haveI hdom : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  haveI : Nontrivial (A ⧸ P) := hdom.toNontrivial
  haveI : FaithfulSMul k (A ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k (A ⧸ P)).injective
  have hPΩ := trdeg_add_eq k (A ⧸ P) (A := Ω)
  rw [trdeg_eq_zero (R := A ⧸ P) (A := Ω), add_zero, hs2', hn] at hPΩ
  have hss : s' = n := by exact_mod_cast hPΩ
  have hsm : s = m := by exact_mod_cast hAR
  rw [hdimR, ← hss, ← hsm, ← hs1', ← hs1]
  exact hform

end GlobalTheory.LocModelDim

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGenerated
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem fg_ringOn_of_isAffineOpen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → (M.ringOn U).FG :=
  fun _ _ _ _ _ _ _ hU hne => GlobalTheory.ZH.RatModel.fg_ringOn hU hne

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnPreimageIntegralOfFiniteModelMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

theorem GlobalTheory.Poinc.finite_preimage_integral : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ U : M₁.Z.Opens, IsAffineOpen U → (U : Set M₁.Z).Nonempty → ∀ b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z), ∃ f : Polynomial Ω₁, f.Monic ∧ (∀ i, f.coeff i ∈ M₁.ringOn (U : Set M₁.Z)) ∧ Polynomial.eval₂ (algebraMap Ω₁ Ω₂) b f = 0 := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hq hg U hUa hU b hb
  have hpt : ⊤ ≤ (M₂.pt ≫ q) ⁻¹ᵁ U := by
    rw [hg]
    exact fun x _ => M₁.top_le_preimage_pt hU (x := (spMap (algebraMap Ω₁ Ω₂)) x) trivial
  have hV : (((q ⁻¹ᵁ U : M₂.Z.Opens)) : Set M₂.Z).Nonempty :=
    ⟨M₂.pt (IsLocalRing.closedPoint Ω₂), hpt (x := IsLocalRing.closedPoint Ω₂) trivial⟩
  have h1 : ∀ a : Γ(M₁.Z, U), valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a) = algebraMap Ω₁ Ω₂ (valF M₁.pt U a) := by
    intro a
    refine (valR_comp M₂.pt q U a).symm.trans ?_
    rw [hg]
    exact valR_spMap_comp _ M₁.pt U (M₁.top_le_preimage_pt hU) a
  have hint : (q.app U).hom.IsIntegral := RingHom.IsIntegral.of_finite (hq.finite_app U hUa)
  obtain ⟨g, rfl⟩ := (RatModel.mem_ringOn_iff_exists hV).1 hb
  obtain ⟨P, hPm, hP⟩ := hint g
  refine ⟨P.map (M₁.res U hU), hPm.map _, fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    exact (RatModel.mem_ringOn_iff_exists hU).2 ⟨P.coeff i, (M₁.res_apply U hU _).symm⟩
  · have hc : (algebraMap Ω₁ Ω₂).comp (M₁.res U hU) = (M₂.res (q ⁻¹ᵁ U) hV).comp (q.app U).hom := by
      ext a
      simp only [RingHom.comp_apply, RatModel.res_apply]
      exact (h1 a).symm
    rw [Polynomial.eval₂_map, hc, ← RatModel.res_apply _ _ hV, ← Polynomial.hom_eval₂, hP, map_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionOfGrpPullbackSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RosatiPull

theorem sq_left_ext {H : Scheme.{0}} {G : Over H} {Z : Scheme.{0}} {a b : Z ⟶ (G ⊗ G).left}
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h1 h2

theorem rosatiFor_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (S H E : Scheme.{0}) (A₀ : Over S) [GrpObj A₀] (P : LB (G2 A₀).left), P.IsLB → ∀ (AH : Over H) [GrpObj AH] (AE : Over E) [GrpObj AE] (f : E ⟶ H) (φ : AE.left ⟶ AH.left) (φ₂ : (G2 AE).left ⟶ (G2 AH).left) (φ₂H : (G2 AH).left ⟶ (G2 A₀).left) (actH : OActN D.O AH) (actE : OActN D.O AE), IsGrpPullback AE AH f φ → IsSquare φ φ₂ → (∀ a : D.O, (actE.act a).left ≫ φ = φ ≫ (actH.act a).left) → RosatiFor D actH (P.pull φ₂H) → RosatiFor D actE (P.pull (φ₂ ≫ φ₂H)) := by
  intro p _ D S H E A₀ _ P hP AH _ AE _ f φ φ₂ φ₂H actH actE _ hsq hact hR c
  have hu : (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH ≫ actH.act c) (snd AH AH)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.1, Category.assoc]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
  have hv : (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH) (snd AH AH ≫ actH.act (D.star c).unop)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.2, Category.assoc]
  have hQ : (P.pull φ₂H).IsLB := pull_isLB hP _
  have hR' : (P.pull (φ₂ ≫ φ₂H)).IsLB := pull_isLB hP _
  have e3 := GlobalTheory.GenSpread.lbIso_pull_comp (L := P.pull φ₂H) (M := P.pull φ₂H) φ₂ hu hv (hR c)
  have e1u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left (a := φ₂ ≫ φ₂H) rfl
  have e2u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  have e1v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left (a := φ₂ ≫ φ₂H) rfl
  have e2v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  exact LBIso.trans (pull_isLB hR' _) (pull_isLB hP _) (pull_isLB hR' _) e1u.symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hQ _) (pull_isLB hR' _) e2u
      (LBIso.trans (pull_isLB hQ _) (pull_isLB hQ _) (pull_isLB hR' _) e3
        (LBIso.trans (pull_isLB hQ _) (pull_isLB hP _) (pull_isLB hR' _) e2v.symm e1v)))

end GlobalTheory.RosatiPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueAddEndomorphismsCubical
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RosAddPair

open GlobalTheory.TauBalAdd

theorem ros_val_padd : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (cu : CubicalStr A Lr), GlobalFnsSt →
    IsAbelianScheme A →
    ∀ (f₁ g₁ f₂ g₂ f g : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], f = padd A f₁ f₂ → g = padd A g₁ g₂ →
    ∀ (u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)) (u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε))
      (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)), u₁.IsGen → u₂.IsGen → u.IsGen →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (zero2 A)) (LB.oneGen Lr.L) →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₂ (zero2 A)) (LB.oneGen Lr.L) →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L) →
    ∀ {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → Lr.L.ι}, Good Lr.L z J → ∀ x y : T ⟶ A,
    val₂ u z J x y * cubV cu z J (y ≫ g₁) (y ≫ g₂) x =
      cubV cu z J (x ≫ f₁) (x ≫ f₂) y * (val₂ u₁ z J x y * val₂ u₂ z J x y) := by
  intro S A _ _ Lr cu hG hA f₁ g₁ f₂ g₂ f g _ _ _ _ hf hg u₁ u₂ u hu₁ hu₂ hu h₁ h₂ h₀ T z J hJ x y
  subst hf hg
  have key := ros_sum cu hG hA f₁ g₁ f₂ g₂ u₁ hu₁ h₁ u₂ hu₂ h₂ u hu h₀ hJ x y
  have C : IsCub (cubV cu z J) := isCub_cubV cu hJ
  rw [C.s01 x, C.s12 _ x] at key
  exact key

end GlobalTheory.RosAddPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueCompEndomorphisms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rosGen_comp_val : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}, GlobalFnsSt → IsAbelianScheme A → L.IsLB →
    ∀ (f₁ g₁ f₂ g₂ f g : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], f = f₂ ≫ f₁ → g = g₁ ≫ g₂ →
    ∀ (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f₁ g₁) rosatiε)) (u₂ : LB.Gen (LB.LinComb L (rosatiφ A f₂ g₂) rosatiε))
      (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u₁.IsGen → u₂.IsGen → u.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) →
    ∀ {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → L.ι}, Good L z J → ∀ x y : T ⟶ A,
    val₂ u z J x y = val₂ u₁ z J (x ≫ f₂) y * val₂ u₂ z J x (y ≫ g₁) := by
  intro S A _ _ L hG hA hL f₁ g₁ f₂ g₂ f g _ _ _ _ hf hg u₁ u₂ u hu₁ hu₂ hu h₁ h₂ h₀ T z J hJ x y
  subst hf hg
  have zl : ∀ (a b : A ⟶ A) [IsMonHom a] [IsMonHom b], zero2 A ≫ (lift (fst A A ≫ a) (snd A A ≫ b)).left = zero2 A := by
    intro a b _ _
    show (lift η[A] η[A]).left ≫ _ = (lift η[A] η[A]).left
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  have v0 : ∀ {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
      (t : LB.Gen (LB.LinComb L φ ε)), LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t (zero2 A)) (LB.oneGen L) →
      ∀ {y : S} {I}, Good L y I → val t (zero2 A) y I = 1 := by
    intro K _ φ ε t ht y I hI
    have := val_corr hI ht (𝟙 _)
    rwa [val_pull hI, Category.id_comp, val_one] at this
  have key := gen_unique' hL (u := u)
    (u' := LB.mulGen L _ _ _ _ (LB.pullGen L _ _ u₁ (lift (fst A A ≫ f₂) (snd A A)).left)
      (LB.pullGen L _ _ u₂ (lift (fst A A) (snd A A ≫ g₁)).left))
    (fun V _ k => by
      have p := prod_ros (f₂ ≫ f₁) (g₁ ≫ g₂) (fst A A) (snd A A) k
      rw [lift_fst_snd, Over.id_left] at p
      simp only [Category.id_comp] at p
      refine (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
        (prod_ros f₁ g₁ (fst A A ≫ f₂) (snd A A) k) (prod_ros f₂ g₂ (fst A A) (snd A A ≫ g₁) k)).trans
        (Eq.trans ?_ p.symm)
      simp only [Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    ((snd A A).left ≫ A.hom) (zero2 A) (by
      rw [Over.w (snd A A)]; exact Over.w (lift η[A] η[A]))
    (surj_comp (surj_snd hG hA _) (hG _ _ hA).2) hu
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₁ _) (DVR.pullGen_isGen _ _ _ _ hu₂ _))
    (fun y I hI => by
      rw [v0 u h₀ hI, val_mul hI, val_pull hI, val_pull hI]
      have e1 := zl f₂ (𝟙 A)
      have e2 := zl (𝟙 A) g₁
      simp only [Category.comp_id] at e1 e2
      rw [e1, e2, v0 u₁ h₁ hI, v0 u₂ h₂ hI, _root_.mul_one])
    T.left (lift x y).left z J hJ
  unfold val₂
  rw [key, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift,
    lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleSumPowMulStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_two_cocycle_sum_pow_mul : ∀ (Γ D : Type) [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D), (∀ x y, c x y = c y x) → (∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) → ∀ (n : ℕ) (x y : Γ), ∑ i ∈ Finset.range n, c ((x * y) ^ i) (x * y) + n • c x y = ∑ i ∈ Finset.range n, c (x ^ i) x + ∑ i ∈ Finset.range n, c (y ^ i) y + c (x ^ n) (y ^ n) - c 1 1 := by
  first | exact @GlobalTheory.TwoCocycle.sum_pow_mul | exact GlobalTheory.TwoCocycle.sum_pow_mul | (intros; apply GlobalTheory.TwoCocycle.sum_pow_mul <;> assumption)
end

