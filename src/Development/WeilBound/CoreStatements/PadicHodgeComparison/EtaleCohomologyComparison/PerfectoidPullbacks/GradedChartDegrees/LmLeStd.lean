module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ThickeningIdealNilpotent
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Diso

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}}

abbrev OMm (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) : Thick (Lm h q m) ⥤ ModuleCat.{0} O :=
  B.OM (Lm h q m) (Ideal.Quotient.mk _)

variable {q : X ⟶ Spec (CommRingCat.of O)}

theorem lm_le_std (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (T : Q.FullSubcategory) :
    lm (l := l) T.obj m ≤ (stdI Q none ((l : O) ^ m)).S T := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  refine Ideal.mem_sup_right (Ideal.subset_span ?_)
  change (l : T.obj.B) ^ m = T.obj.i ((l : O) ^ m)
  rw [map_pow, map_natCast]

def gMor (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m) :
    CH.Mor (OMm h q m) (sq (IdF.top (sP Q).A) (stdI Q none ((l : O) ^ m))) (RingHom.id O) where
  G := GF h Q m hQ
  τ T :=
    { toFun := fun x => ⟨Ideal.Quotient.factor (lm_le_std Q m T) (show GB (l := l) T.obj m from x), by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
        rw [← hy]
        exact Ideal.mem_map_of_mem _ trivial⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
        change Ideal.Quotient.factor (lm_le_std Q m T) (Ideal.Quotient.mk _ (T.obj.i c) * show GB (l := l) T.obj m from x) =
          Ideal.Quotient.mk _ (T.obj.i c) * Ideal.Quotient.factor (lm_le_std Q m T) (show GB (l := l) T.obj m from x)
        rw [map_mul]
        rfl) }
  nat φ x := by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) _ m from x)
    refine Subtype.ext ?_
    change Ideal.Quotient.factor (lm_le_std Q m _) (gφ φ.hom m (show GB (l := l) _ m from x)) = _
    rw [← hy]
    rfl

end CrystallineSemistableComparison.Pb.Diso
