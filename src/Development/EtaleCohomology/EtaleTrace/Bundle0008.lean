module

public import Development.EtaleCohomology.EtaleTrace.Bundle0005
public import Development.EtaleCohomology.EtaleTrace.Bundle0006
public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
public import Development.EtaleCohomology.KummerTheory.Bundle0012
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.EtaleCohomology.KummerTheory.Bundle0001
public import Development.EtaleCohomology.EtaleSheaves.Bundle0026
public import Development.EtaleCohomology.EtaleTrace.Bundle0007

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleTrace.GenEtalePfBasic
section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem etaleOverBasic : EtaleOverBasic := by
  intro X P π U hU hU' a H
  have hle : π ⁻¹ᵁ P.basicOpen a ≤ π ⁻¹ᵁ U := π.preimage_mono (P.basicOpen_le a)
  have key : RingHom.Etale (π.app (P.basicOpen a)).hom := by
    letI := (π.app U).hom.toAlgebra
    letI : Algebra Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    letI : Algebra Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app _).hom.toAlgebra
    letI : Algebra Γ(P, U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    haveI : IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(P, U) Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      show (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom =
        (P.presheaf.map (homOfLE (P.basicOpen_le a)).op ≫ π.app (P.basicOpen a)).hom
      rw [π.naturality]; rfl
    have hA : IsLocalization.Away a Γ(P, P.basicOpen a) := hU.isLocalization_basicOpen a
    have gen : ∀ (W : X.Opens) (e : W ≤ π ⁻¹ᵁ U), W = X.basicOpen (π.app U a) →
        @IsLocalization.Away _ _ (π.app U a) Γ(X, W) _ (X.presheaf.map (homOfLE e).op).hom.toAlgebra := by
      rintro W e rfl; exact hU'.isLocalization_basicOpen _
    exact H _ _ hA (gen _ hle (π.preimage_basicOpen a))
  haveI : IsAffine (P.basicOpen a).toScheme := hU.basicOpen a
  haveI : IsAffine (π ⁻¹ᵁ P.basicOpen a).toScheme := by
    have := hU'.basicOpen (π.app U a); rw [← π.preimage_basicOpen a] at this; exact this
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
  have hW : (P.basicOpen a).ι ''ᵁ ⊤ = P.basicOpen a := by simp
  have gen2 : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = P.basicOpen a →
      RingHom.Etale (π.app W ≫ X.presheaf.map (eqToHom h).op).hom := by
    rintro W T h rfl
    subst h
    simpa using key
  exact gen2 _ _ _ hW

end LateralTheory.EtaleTrace.Cov
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenOutChartPfRing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem homog_div_mem {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K)
    (i : Fin (N + 1)) (_hi : w i ≠ 0) (R : Subring K) (hκ : ∀ c, κ c ∈ R) (hw : ∀ j, w j / w i ∈ R)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g.IsHomogeneous m) : eval₂ κ w g / w i ^ m ∈ R := by
  rw [eval₂_eq, Finset.sum_div]
  refine Subring.sum_mem _ fun d hd => ?_
  have hdeg : ∑ j, d j = m := by
    rw [← hg (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have : (κ (AddMonoidAlgebra.coeff g d) * ∏ j, w j ^ d j) / w i ^ m = κ (AddMonoidAlgebra.coeff g d) * ∏ j, (w j / w i) ^ d j := by
    rw [mul_div_assoc]; congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  have hsupp : ∏ j ∈ d.support, w j ^ d j = ∏ j, w j ^ d j :=
    Finset.prod_subset (Finset.subset_univ _) (fun j _ hj => by simp [Finsupp.notMem_support_iff.mp hj])
  rw [hsupp, this]
  exact Subring.mul_mem _ (hκ _) (Subring.prod_mem _ fun j _ => Subring.pow_mem _ (hw j) _)

def chartVal {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K) (i : Fin (N + 1))
    (hi : w i ≠ 0) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* K :=
  (IsLocalization.Away.lift (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) (g := eval₂Hom κ w)
    (by simpa using hi.isUnit)).comp
    (algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)))

theorem chartVal_mk {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K)
    (i : Fin (N + 1)) (hi : w i ≠ 0)
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)) :
    chartVal κ w i hi (HomogeneousLocalization.Away.mk _ hx m g hg) = eval₂ κ w g / w i ^ m := by
  simp only [chartVal, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [coe_eval₂Hom, eval₂_pow, eval₂_X]
  rw [mul_div_cancel₀ _ (pow_ne_zero _ hi)]

def SectOfLoc : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (R : Subring X.functionField),
  (∀ z ∈ R, ∀ y ∈ U, z ∈ loc X y) →
  ∃ φ : R →+* Γ(X, U), ∀ (z : R) (y : X) (hy : y ∈ U),
    algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy (φ z)) = z

theorem ChartRing_of (h : SectOfLoc) : ChartRing := by
  intro k _ X _ p N w i hi U hU hx
  let ψ := chartVal (kHom p) w i hi
  have hR : ∀ z ∈ ψ.range, ∀ y ∈ U, z ∈ loc X y := by
    rintro _ ⟨a, rfl⟩ y hy
    obtain ⟨m, g, hg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hx a
    rw [chartVal_mk]
    have hg' : g.IsHomogeneous m := by
      simpa using (mem_homogeneousSubmodule _ _).1 hg
    exact homog_div_mem (kHom p) w i hi (loc X y) (fun c => kHom_mem_loc p y c) (fun j => hU y hy j) m g hg'
  obtain ⟨φ, hφ⟩ := h X U ψ.range hR
  refine ⟨φ.comp ψ.rangeRestrict, fun y hy m g hg => ?_⟩
  rw [RingHom.comp_apply, hφ]
  exact chartVal_mk (kHom p) w i hi hx m g hg

theorem GenOutChart_of_sect (h1 : SectOfLoc) (h2 : ChartGen) : GenOutChart :=
  GenOutChart_of (ChartRing_of h1) h2

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LFinCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LFinCut

theorem normal_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) [Smooth p] : GlobalTheory.IsNormalScheme X := by
  rw [GlobalTheory.isNormalScheme_iff]
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p fun y => ?_
  have hf : IsField ((S k).presheaf.stalk y) := isField_stalk_of_closure_mem_irreducibleComponents (S k) y (by
    have : closure ({y} : Set (S k)) = Set.univ := Set.eq_univ_of_forall fun z => subset_closure (Subsingleton.elim z y)
    rw [this, irreducibleComponents_eq_singleton]; rfl)
  let := hf.toField
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleTrace.LFinCut

end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LPdCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.LPdCut

def Dp (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) : (PN k N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)

def LChart : Prop := ∀ (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)),
  ∃ j : Spec (CommRingCat.of (MvPolynomial (Fin N) k)) ⟶ PN k N, IsOpenImmersion j ∧
    j ≫ PNto k N = Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k)) ∧
    Set.range j = (Dp k N i : Set (PN k N))

def LProper : Prop := ∀ (k : Type) [Field k] (N : ℕ), IsProper (PNto k N)

def LSmooth : Prop := ∀ (k : Type) [Field k] (N : ℕ), SmoothOfRelativeDimension N (PNto k N)

def LEmpty : Prop := A5 → A9 → ∀ (R : Type) [CommRing R] (X : Scheme.{0}), IsEmpty X → ∀ (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj X) F n)

theorem unit_of {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) {q : ℕ} (h : IsUnit (q : k)) : IsUnit (q : Γ(X, ⊤)) := by
  simpa using (h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom

end LateralTheory.EtaleTrace.LPdCut

end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.PtCoverPf
section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

theorem PtCover_of : PtCover := by
  intro k _ _ T hT
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber k).jointly_surjective T hT (𝟙 (S k))
  have hy' : y ≫ g = 𝟙 (S k) := hy
  have := T.downward_closed hg y
  rwa [hy'] at this

end LateralTheory.EtaleTrace
end

-- bundled from Development.EtaleCohomology.EtaleTrace.TwZeroPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

def PrimSplit : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A), ∃ e : Fin q → A,
  (∀ i, IsIdempotentElem (e i)) ∧ ∑ i, e i = 1 ∧ (∀ i, e i * ξ.1 = e i * ζ.1 ^ (i : ℕ)) ∧ (∀ i : Fin q, ¬ Nat.Coprime (i : ℕ) q → e i = 0)

def SplitLoc : Prop := ∀ (U : Scheme.{0}) (n : ℕ) (e : Fin n → Γ(U, ⊤)), (∀ i, IsIdempotentElem (e i)) → ∑ i, e i = 1 →
  Loc U fun V g => ∃ i, g.appTop.hom (e i) = 1

theorem primLoc_of (hS : PrimSplit) (hL : SplitLoc) : PrimLoc := by
  intro q _ U ζ ξ
  obtain ⟨e, he, hs, hx, hc⟩ := hS q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hSc, hP⟩ := hL U q e he hs
  refine ⟨S, hSc, fun V g hg => ?_⟩
  obtain ⟨i, hi⟩ := hP V g hg
  have key : g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (i : ℕ) := by
    have := congrArg g.appTop.hom (hx i)
    simpa [map_mul, map_pow, hi] using this
  by_cases hcop : Nat.Coprime (i : ℕ) q
  · refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _
    rw [key, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
  · have h0 := hc i hcop
    rw [h0, map_zero] at hi
    have : Subsingleton Γ(V, ⊤) := subsingleton_of_zero_eq_one hi
    exact ⟨1, Subsingleton.elim _ _⟩

theorem TwZero_of (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) (hL : SplitLoc) : TwZero :=
  TwZero_of_primLoc hTw (primLoc_of hS hL)

end LateralTheory.EtaleTrace
end
end

