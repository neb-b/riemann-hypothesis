module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsEtaleAwayPf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_etale_away_pf {K A : Type} [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] {d : ℕ} (s : Fin d → A) (hs : AlgebraicIndependent K s)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range s)) A) :
    ∃ g : A, g ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale := by
  classical
  letI : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.aeval s).toRingHom.toAlgebra
  have hRA : algebraMap (MvPolynomial (Fin d) K) A = (MvPolynomial.aeval s).toRingHom := rfl
  have : IsScalarTower K (MvPolynomial (Fin d) K) A := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hRA, MvPolynomial.algebraMap_eq]
    simp
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) K) A) := by
    intro a b h
    exact hs h
  have : FaithfulSMul (MvPolynomial (Fin d) K) A :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin d) K) A).2 hinj
  have : Algebra.FiniteType (MvPolynomial (Fin d) K) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin d) K) A
  have : Algebra.FinitePresentation (MvPolynomial (Fin d) K) A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) A := by
    refine Algebra.IsAlgebraic.of_ringHom_of_comp_eq hs.aevalEquiv (RingHom.id A)
      hs.aevalEquiv.surjective Function.injective_id ?_
    ext p
    · simp [hRA]
    · simp [hRA]
  have hL : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := IsFractionRing.toField A
  have : FaithfulSMul (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq (MvPolynomial (Fin d) K) A (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective A _).comp hinj
  letI := FractionRing.liftAlgebra (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A))
  have : Algebra.IsAlgebraic A (Localization.AtPrime (⊥ : Ideal A)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.IsAlgebraic.trans (MvPolynomial (Fin d) K) A _
  have : Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (MvPolynomial (Fin d) K) _)
  have : CharZero (FractionRing (MvPolynomial (Fin d) K)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Fin d) K) _)
  have : Algebra.FormallyEtale (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FormallyEtale (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial (Fin d) K))
  have hE : Algebra.IsEtaleAt (MvPolynomial (Fin d) K) (⊥ : Ideal A) :=
    Algebra.FormallyEtale.comp (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) _
  obtain ⟨g, hg, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := MvPolynomial (Fin d) K) (⊥ : Ideal A)
  refine ⟨g, by simpa using hg, ?_⟩
  have heq : (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g) =
      algebraMap (MvPolynomial (Fin d) K) (Localization.Away g) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]
      simp [hRA, IsScalarTower.algebraMap_apply K A (Localization.Away g)]
    · intro i
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]
      simp [hRA]
  rw [heq]
  exact RingHom.etale_algebraMap.2 he

end CrystallineSemistableComparison.Pb
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsIntegralOfSmoothPf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIntegral_of_smooth_pf {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension n q] : IsIntegral X := by
  have hsm : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hE : ∀ (A : Type) [CommRing A] [Algebra K A] [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime],
      ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S :=
    fun A _ _ _ p _ => CrystallineSemistableComparison.Pb.EtaleIntegralityFacts.exists_away_isDomain_of_smooth (K := K) p
  choose W hxW hW using fun x => CrystallineSemistableComparison.Pb.EtaleIntegralityFacts.exists_integral_nbhd q hE x
  have hcov : TopologicalSpace.IsOpenCover W :=
    eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  have hredi : ∀ i, IsReduced ((X.openCoverOfIsOpenCover W hcov).X i) := by
    intro i
    rw [Scheme.openCoverOfIsOpenCover_X]
    have := hW i
    exact isReduced_of_isIntegral _
  have hred : IsReduced X := IsReduced.of_openCover X (X.openCoverOfIsOpenCover W hcov)
  have hirr : IrreducibleSpace X := by
    refine CrystallineSemistableComparison.Pb.EtaleIntegralityFacts.irreducibleSpace_of_connected_of_locally fun x => ⟨W x, (W x).isOpen, hxW x, ?_⟩
    have := hW x
    have hi := irreducibleSpace_of_isIntegral (W x : Scheme)
    have h2 := (IrreducibleSpace.isIrreducible_univ (↥(W x : Scheme))).image Subtype.val
      continuous_subtype_val.continuousOn
    rwa [Set.image_univ, Subtype.range_coe] at h2
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end CrystallineSemistableComparison.Pb
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison

def E.LineData.pb {X X' : Scheme.{0}} (D : E.LineData X) (f : X' ⟶ X) : E.LineData X' where
  Y := pullback D.f f
  f := pullback.snd D.f f
  sm := by have := D.sm; infer_instance
  surj := by have := D.surj; infer_instance
  u a b h := D.u (a ≫ pullback.fst _ _) (b ≫ pullback.fst _ _)
    (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc])
  nat g a b h := by
    have := D.nat g (a ≫ pullback.fst _ _) (b ≫ pullback.fst _ _)
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc])
    simpa only [Category.assoc] using this
  coc a b c h h' := D.coc _ _ _ _ _

namespace Pb

def plogK {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) (x : B) : B :=
  ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : B) * δ.dpow (k + 1) x

section K
variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

structure CLiftK {C : Type 1} [Category.{0} C] (g : C ⥤ Thick (smFun X q)) (D : E.LineData X) where
  p : ∀ c : C, Spec (CommRingCat.of ((g.obj c).B ⧸ (g.obj c).J)) ⟶ D.Y
  hp : ∀ c : C, p c ≫ D.f = pt (g.obj c)
  w : ∀ {c c' : C}, (c ⟶ c') → (g.obj c').Bˣ
  hw : ∀ {c c' : C} (φ : c ⟶ c')
    (h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f),
    Ideal.Quotient.mk (g.obj c').J (w φ) = (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c').B ⧸ (g.obj c').J))).hom.hom
      (D.u (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) (p c') h)

def CLiftK.r {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (s : ComposableArrows C 2) : (g.obj (s.obj (Fin.last 2))).Bˣ :=
  Units.map (g.map (s.map' 1 2)).φ.toMonoidHom (Λ.w (s.map' 0 1)) * Λ.w (s.map' 1 2) * (Λ.w (s.map' 0 2))⁻¹


variable (q) in
def IsFirstChernDeRham (D : E.LineData X) (x : HdR q 2) : Prop :=
  ∀ (s : ℕ) (C : Type 1) [Category.{0} C] (g : C ⥤ Thick (smFun X q)), (∀ c, (g.obj c).pdPow s = ⊥) →
    (∀ c, ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V (g.obj c)) →
    ∀ Λ : CLiftK g D, ∃ (z : CH.Cn (g ⋙ O (smFun X q)) 2) (hz : CH.d _ 2 z = 0),
      (∀ σ : ComposableArrows C 2, (show (g.obj (σ.obj (Fin.last 2))).B from z σ) =
        plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1)) ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict (O (smFun X q)) g).pull 2 x

end K

section O1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem X_mem (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 1 :=
  MvPolynomial.isHomogeneous_X R j

abbrev ChartR (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) : Type :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j)

def chart (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) : Spec (CommRingCat.of (ChartR R N j)) ⟶ PSpace R N :=
  Proj.awayι _ (MvPolynomial.X j) (X_mem R N j) one_pos

def ratio (R : Type) [CommRing R] (N : ℕ) (j k : Fin (N + 1)) : ChartR R N j :=
  HomogeneousLocalization.Away.mk _ (X_mem R N j) 1 (MvPolynomial.X k) (by simpa using X_mem R N k)

def IsTautologicalLineAt {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace R N) : Prop :=
  Etale D.f ∧ ∃ s : ∀ j : Fin (N + 1), pullback i (chart R N j) ⟶ D.Y,
    ∃ hs : ∀ j, s j ≫ D.f = pullback.fst _ _,
    ∀ (V : Scheme.{0}) (j k : Fin (N + 1)) (a : V ⟶ pullback i (chart R N j)) (b : V ⟶ pullback i (chart R N k))
      (h : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _),
      ((D.u (a ≫ s j) (b ≫ s k) (by rw [Category.assoc, Category.assoc, hs, hs, h]) : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) =
        (a ≫ pullback.snd _ _).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR R N j))).inv.hom (ratio R N j k))

def IsTautologicalLine {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (D : E.LineData X) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsClosedImmersion i ∧ i ≫ PSpace.str R N = p ∧ IsTautologicalLineAt D N i

end O1

end Pb

end CrystallineSemistableComparison
end
end

