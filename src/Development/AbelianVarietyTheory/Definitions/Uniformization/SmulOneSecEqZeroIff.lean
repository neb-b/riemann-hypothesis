module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU

def SecMod {F : Type} [CommRing F] {Y : Scheme.{0}} (_p : Y ⟶ Spec (CommRingCat.of F)) (N : LB Y) : Type := LB.Sec N
namespace SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}

def sec (s : SecMod p N) : LB.Sec N := s

def mk (p : Y ⟶ Spec (CommRingCat.of F)) (s : LB.Sec N) : SecMod p N := s

instance : Zero (SecMod p N) := ⟨DVR.SecOps.secZero⟩

instance : Add (SecMod p N) := ⟨DVR.SecOps.secAdd⟩

instance : Neg (SecMod p N) := ⟨DVR.SecOps.secNeg⟩

instance : SMul F (SecMod p N) := ⟨fun c s => DVR.SecOps.secScale (scal p c) s⟩

instance : AddCommGroup (SecMod p N) where
  add_assoc _ _ _ := DVR.SecOps.sec_ext fun _ => add_assoc _ _ _
  zero_add _ := DVR.SecOps.sec_ext fun _ => zero_add _
  add_zero _ := DVR.SecOps.sec_ext fun _ => add_zero _
  neg_add_cancel _ := DVR.SecOps.sec_ext fun _ => neg_add_cancel _
  add_comm _ _ := DVR.SecOps.sec_ext fun _ => add_comm _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module F (SecMod p N) where
  one_smul s := DVR.SecOps.sec_ext fun i => by
    show resTop _ (scal p 1) * s.f i = s.f i
    simp [scal]
  mul_smul a b s := DVR.SecOps.sec_ext fun i => by
    show resTop _ (scal p (a * b)) * s.f i = resTop _ (scal p a) * (resTop _ (scal p b) * s.f i)
    simp [scal, _root_.mul_assoc]
  smul_zero _ := DVR.SecOps.sec_ext fun _ => mul_zero _
  smul_add _ _ _ := DVR.SecOps.sec_ext fun _ => mul_add _ _ _
  add_smul a b s := DVR.SecOps.sec_ext fun i => by
    show resTop _ (scal p (a + b)) * s.f i = resTop _ (scal p a) * s.f i + resTop _ (scal p b) * s.f i
    simp [scal, add_mul]
  zero_smul s := DVR.SecOps.sec_ext fun i => by
    show resTop _ (scal p 0) * s.f i = 0
    simp [scal]

@[simp] theorem coord_zero (j : N.ι) : (0 : SecMod p N).sec.f j = 0 := rfl

@[simp] theorem coord_smul (c : F) (s : SecMod p N) (j : N.ι) :
    (c • s).sec.f j = resTop (N.U j) (scal p c) * s.sec.f j := rfl

@[simp] theorem coord_mk (s : LB.Sec N) (j : N.ι) : (mk p s).sec.f j = s.f j := rfl


theorem eq_zero_iff_coord (s : SecMod p N) : s = 0 ↔ ∀ j, s.sec.f j = 0 := by
  constructor
  · rintro rfl j
    exact coord_zero j
  · intro h
    exact DVR.SecOps.sec_ext fun j => (h j).trans (coord_zero j).symm

section Val
variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ

theorem value_smul (c : F) (s : SecMod p (LB.LinComb L φ ε)) :
    sval (c • s).sec r z J = gs r z ⊤ (scal p c) * sval s.sec r z J := by
  refine (congrArg (gs r z (LB.wchart L φ fun k => J (r ≫ φ k))) (coord_smul c s _)).trans ?_
  exact (gs_mul r z _ (hJ.mem φ r) _ _).trans
    (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) _))

end Val

def oneSec (F : Type) [CommRing F] :
    SecMod (𝟙 (Spec (CommRingCat.of F)))
      (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB (Spec (CommRingCat.of F))) :=
  mk _ ⟨fun _ => 1, fun _ _ => by simp⟩

theorem oneSec_ne_zero (F : Type) [CommRing F] [Nontrivial F] : oneSec F ≠ 0 := by
  intro h
  have h1 : ((1 : Γ(Spec (CommRingCat.of F), ⊤)) : Γ(Spec (CommRingCat.of F), ⊤)) = 0 := by
    have := congrArg (fun s => (SecMod.sec s).f PUnit.unit) h
    simpa [oneSec] using this
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h1
  rw [map_one, map_zero] at h2
  exact one_ne_zero h2

theorem smul_oneSec_eq_zero_iff (F : Type) [CommRing F] (c : F) : c • oneSec F = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun s => (SecMod.sec s).f PUnit.unit) h
    simp only [coord_smul, coord_zero, oneSec, coord_mk, _root_.mul_one] at h1
    simp [resTop, scal] at h1
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h1
    simpa using h2
  · rintro rfl
    exact zero_smul F _

end SecMod
end GlobalTheory.UU
end
