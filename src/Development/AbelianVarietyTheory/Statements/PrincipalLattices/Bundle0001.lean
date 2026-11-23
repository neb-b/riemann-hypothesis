module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Statements.PrincipalLattices.EqZeroOfOppositeSign
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.PureTypeModel

open PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.PureTypeModel.exists_isTypeFn (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H p q ty := by
  classical
  let n : (E →+* ℂ) → ℕ := fun τ => if τ H.rt = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (n τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have hcard : ∀ τ, Nat.card {i // (e.symm i).1 = τ} = n τ := by
    intro τ
    rw [Nat.card_congr ((e.symm.subtypeEquiv (p := fun i => (e.symm i).1 = τ)
      (q := fun s => s.1 = τ) (fun i => Iff.rfl)).trans (Equiv.sigmaSubtype τ)),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]
    simp [n, h]
  · rw [hcard]
    simp [n, h]

section Linear

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

end Linear

section Mixed

open HostModel PeriodNonempty
open scoped TensorProduct

end Mixed

end GlobalTheory.PureTypeModel
end
end

-- bundled from Development.AbelianVarietyTheory.Statements.PrincipalLattices.PrimeSpectrumDualEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane

namespace GlobalTheory.CMCurveTest

variable {R : Type} [CommRing R]

def scaleVec {A : Over (Sp R)} (c : R) (v : epsR R ⟶ A) : epsR R ⟶ A :=
  Over.homMk (spMap (epsScaleR c) ≫ v.left) (by
    rw [Category.assoc, Over.w v]
    refine (spMap_comp_spMap _ _).trans ?_
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])

theorem isVecOver_scaleVec {R' : Type} [CommRing R'] {f : R →+* R'} {A : Over (Sp R)} {A' : Over (Sp R')}
    {φ : A'.left ⟶ A.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} (h : IsVecOver f φ v v') (c : R) :
    IsVecOver f φ (scaleVec c v) (scaleVec (f c) v') := by
  change (spMap (epsScaleR (f c)) ≫ v'.left) ≫ φ = spMap (Chart.dualMapR f) ≫ spMap (epsScaleR c) ≫ v.left
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc]
  congr 1
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem primeSpectrum_dual_eq (x y : PrimeSpectrum (DualNumber ℂ)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber ℂ), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem isDiff_scaleVec {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {w : Fin g → ℂ}
    {v : epsR ℂ ⟶ A} (h : u.IsDiff w v) (c : ℂ) : u.IsDiff (c • w) (scaleVec c v) := by
  intro U hU f
  have hU' : ⊤ ≤ v.left ⁻¹ᵁ U := fun x _ => by
    have := hU (Set.mem_univ x)
    have hx : (spMap (epsScaleR c)) x = x := primeSpectrum_dual_eq _ _
    change v.left ((spMap (epsScaleR c)) x) ∈ U at this
    rwa [hx] at this
  rw [map_smul, ← h U hU' f]
  have e : (scaleVec c v).left.appLE U ⊤ hU = v.left.appLE U ⊤ hU' ≫ (spMap (epsScaleR c)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (epsScaleR c)) v.left U ⊤ ⊤ hU' le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((v.left.appLE U ⊤ hU').hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (epsScaleR c)))
  rw [e]
  refine (congrArg TrivSqZeroExt.snd e2).trans ?_
  simp [epsScaleR]

end GlobalTheory.CMCurveTest
end
end

