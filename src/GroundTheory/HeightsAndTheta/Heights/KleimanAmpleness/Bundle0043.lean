module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurent
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurentCohom
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFree
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedPres
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreOnto
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem CechDSq.full : CechDSq.Statement.{u, v} := CechDSq.proof
theorem DegLocExact.full : DegLocExact.Statement.{u, v} := DegLocExact.proof
theorem CechExact.full : CechExact.Statement.{u, v} := CechExact.proof CechDSq.full DegLocExact.full
theorem CechTop.full : CechTop.Statement.{u, v} := CechTop.proof
theorem Cech.Cone.full : Cech.Cone.Statement.{u, v} := Cech.Cone.proof
theorem Cech.Transport.full : Cech.Transport.Statement.{u, v, w} := Cech.Transport.proof
theorem SerrePoly.Laurent.full : SerrePoly.Laurent.Statement.{u} := SerrePoly.Laurent.proof
theorem SerrePoly.LaurentCohom.full : SerrePoly.LaurentCohom.Statement.{u} :=
  SerrePoly.LaurentCohom.proof Cech.Cone.full
theorem SerrePoly.full : SerrePoly.Statement.{u} :=
  SerrePoly.proof SerrePoly.Laurent.full Cech.Transport.full SerrePoly.LaurentCohom.full
theorem SerreFree.full : SerreFree.Statement.{u, v} := SerreFree.proof SerrePoly.full
theorem GradedPres.full : GradedPres.Statement.{u, v} := GradedPres.proof
theorem GradedULift.full : GradedULift.Statement.{u, v} := GradedULift.proof
theorem CohomRetract.full : CohomRetract.Statement.{u, v, w} := CohomRetract.proof

theorem SerreFinite.full : SerreFinite.Statement.{u, v} :=
  SerreFinite.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreVanish.full : SerreVanish.Statement.{u, v} :=
  SerreVanish.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreOnto.full : SerreOnto.Statement.{u, v} :=
  SerreOnto.proof CechExact.full SerreFree.full SerreVanish.full

theorem SerreTail.full : SerreTail.Statement.{u, v} := SerreTail.proof SerreFinite.full SerreOnto.full

theorem Extension.full : Extension.Statement.{u, v, w} := Extension.proof
theorem Generated.full : Generated.Statement.{u, w} := Generated.proof Extension.full
theorem TwistFinite.full : TwistFinite.Statement.{u, w} := TwistFinite.proof Extension.full SerreFinite.full
theorem TwistSections.full : TwistSections.Statement.{u, w} := TwistSections.proof SerreOnto.full
theorem ProjDegreePositive.full : ProjDegreePositive.Statement.{u} := ProjDegreePositive.proof
theorem HilbertPositive.full : HilbertPositive.Statement.{u, w} :=
  HilbertPositive.proof ProjDegreePositive.full TwistSections.full
theorem PrimeFiltration.Point.full : PrimeFiltration.Point.Statement.{u, w} := PrimeFiltration.Point.proof
theorem PrimeFiltration.Restrict.full : PrimeFiltration.Restrict.Statement.{u, w} :=
  PrimeFiltration.Restrict.proof

theorem StepThree.Away.full : StepThree.Away.Statement.{u, w} := StepThree.Away.proof
theorem RestrictTwist.full : RestrictTwist.Statement.{u, w} := RestrictTwist.proof
theorem StepData.JProper.full : StepData.JProper.Statement.{u, w} := StepData.JProper.proof
theorem SubvarDrop.full : SubvarDrop.Statement.{u, w} := SubvarDrop.proof

theorem TwistVanish.assembled (hS : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} :=
  TwistVanish.proof Extension.full SerreVanish.full hS

theorem NefRestrict.assembled (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} :=
  NefRestrict.proof RestrictTwist.full hRL

theorem SectionCount.Drop.assembled (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} :=
  SectionCount.Drop.proof hF hT hH hR

theorem SectionCount.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w}) :
    SectionCount.Statement.{u, w} :=
  SectionCount.proof hTop (SectionCount.Drop.assembled hF hT hH hR)

theorem StepThree.assembled (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.Statement.{u, w} :=
  StepThree.proof StepThree.Away.full (StepThree.OnW.proof hL hG)

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellResMemLocPart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver mConeMapOver chartRingOver quotPart)

namespace CechPointVanish

set_option linter.unusedSectionVars false

section Cells

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

theorem face_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

theorem constD_congr {V : Type} [AddCommGroup V] (G : ∀ k, Finset (ι k)) (n : ℕ) {f f' : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → V}
    (h : ∀ J : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, (∀ k, J.1 k ⊆ G k) → f J = f' J) (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1)) (hI : ∀ k, I.1 k ⊆ G k) :
    constD K ι V n f I = constD K ι V n f' I := by
  unfold constD
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · exact congrArg _ (h _ fun l => (face_subset I.1 k i l).trans (hI l))
  · rfl

variable {S : Type} [CommRing S]

theorem cellMon_mono {J I : ∀ k, Finset (ι k)} (h : ∀ k, J k ⊆ I k) : cellMon S J ≤ cellMon S I := by
  apply Submonoid.closure_mono
  rintro f ⟨k, i, hi, rfl⟩
  exact ⟨k, i, h k hi, rfl⟩

theorem cellRes_mk {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J I : ∀ k, Finset (ι k)}
    (h : cellMon S J ≤ cellMon S I) (m : M) (t : cellMon S J) :
    cellRes S M J I (LocalizedModule.mk m t) = LocalizedModule.mk m ⟨t.1, h t.2⟩ := by
  unfold cellRes
  rw [dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']


open Classical in
theorem cechD_apply {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) (f : CechC S ι M n)
    (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1)) :
    cechD S ι M n f I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        faceSign I.1 k i • cellRes S M _ I.1 (f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  simp only [cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

end Cells

section Point

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω}

end Point

end CechPointVanish

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

section Frac

theorem coe_ne_zero_of_not_mem {A : Subalgebra S Ω} {p : Ideal A} {b : A} (hb : b ∉ p) : (b : Ω) ≠ 0 := by
  intro h
  apply hb
  have : b = 0 := Subtype.ext h
  rw [this]
  exact p.zero_mem

theorem one_not_mem_of_prime {A : Subalgebra S Ω} {p : Ideal A} (hp : p.IsPrime) : (1 : A) ∉ p :=
  fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)

def fracSub (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] : Subalgebra S Ω where
  carrier := {u | ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * b' + b * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [div_add_div _ _ (coe_ne_zero_of_not_mem hb) (coe_ne_zero_of_not_mem hb')]
  algebraMap_mem' r := ⟨algebraMap S A r, 1, one_not_mem_of_prime hp, by simp⟩

theorem mem_locIn {A : Subalgebra S Ω} {p : Ideal A} [p.IsPrime] {u : Ω} :
    u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p ↔ ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b := by
  constructor
  · intro h
    exact (Subring.closure_le (t := (fracSub A p).toSubring)).mpr (fun v hv => hv) h
  · intro h
    exact Subring.subset_closure h

theorem span_subset_span {A B : Subalgebra S Ω} (hAB : A ≤ B) (s : Set Ω) :
    (Submodule.span A s : Set Ω) ⊆ Submodule.span B s := by
  intro z (hz : z ∈ Submodule.span A s)
  induction hz using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul a z _ hz =>
    have e : a • z = (⟨a, hAB a.2⟩ : B) • z := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ hz

theorem exists_sum_eq_one {A : Subalgebra S Ω} {m : ℕ} (g : Fin m → Ω) (Q' : Submodule A Ω)
    (hQQ : Submodule.span A (Set.range g) * Q' = 1) :
    ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ (∀ a b, g a * w b ∈ A) ∧ ∑ b, g b * w b = 1 := by
  classical
  have hone : (1 : Ω) ∈ Submodule.span A (Set.range g) * Q' := by
    rw [hQQ]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_
    · intro q hq q' hq'
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hq
      refine ⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
    · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
      refine ⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_add]
  refine ⟨w, hwQ, fun a b => ?_, hsum⟩
  have h := Submodule.mul_mem_mul (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span A (Set.range g))
    (hwQ b)
  rw [hQQ, Submodule.mem_one] at h
  obtain ⟨y, hy⟩ := h
  rw [← hy]
  exact y.2

theorem chartRingOver_oneBlock_eq_chartRing {N : ℕ} (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) (h : x (c ()) ≠ 0) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c =
      Kleiman.chartRing (S := S) (x := x) (Kleiman.singleChart h) := by
  have hChart : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x (c ()) =
      Kleiman.chartRing (S := S) (x := x) (Kleiman.singleChart h) := by
    apply le_antisymm
    · rw [ReciprocityTheory.ChartRestriction.G.Geo.chartRing, Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact ⟨X j, X (c ()), 1, Kleiman.X_mem_monos (Finset.mem_singleton_self _),
        isHomogeneous_X S j, isHomogeneous_X S (c ()), by simp⟩
    · rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
      have hs₀ := Kleiman.eval_ne_zero_of_mem_monos (Kleiman.singleChart h) hs
      have hsne : s ≠ 0 := fun he => hs₀ (by rw [he, map_zero])
      obtain ⟨e', hse', hden⟩ := TranslateEq.pow_div_mem_chartRingI S x
        (Kleiman.singleChart h) (c ()) hs
      have he : e = e' := hse.inj_right hse' hsne
      subst e'
      change x (c ()) ^ e / aeval x s ∈
        IndefiniteRowSideFullHecke.Kleiman.chartRingI S x {c ()} at hden
      rw [IndefiniteRowSideFullHecke.Kleiman.chartRingI_singleton] at hden
      have hnum : aeval x f / x (c ()) ^ e ∈
          ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x (c ()) := by
        rw [← Kleiman.aeval_div_of_isHomogeneous hf, ReciprocityTheory.ChartRestriction.G.Geo.chartRing,
          ← MvPolynomial.aeval_range]
        exact ⟨f, rfl⟩
      have hquot : aeval x f / aeval x s = (aeval x f / x (c ()) ^ e) * (x (c ()) ^ e / aeval x s) := by
        field_simp
      rw [hquot]
      exact mul_mem hnum hden
  rw [← hChart]
  unfold chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

end Frac

section Dom

variable {N N' : ℕ}


end Dom

section Join

variable {N N' m : ℕ}



variable {x' : Fin (N' + 1) → Ω} {x : Fin (N + 1) → Ω}


end Join

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def NefEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    IsGraphGen Q n s → (Kleiman.Nef Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef k (graphVec x s) (graphDeg n))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def GraphModel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S (graphVec x s) baseBlock

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelCurvesDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
        relDim (baseComap F k₀ e W) = relDim W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver secOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelCurveNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      ∀ (W : Ideal (NumbersDVR.MRing ι F)) (W' : Ideal (NumbersDVR.MRing ι' F)),
        NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W → relDim W = ((1 : ℕ) : WithBot (WithTop ℤ)) →
        NumbersDVR.IsMultiProjPrime W' → mIdealOver F y' ≤ W' → relDim W' = ((1 : ℕ) : WithBot (WithTop ℤ)) →
        baseComap F k₀ e W = baseComap F k₀' e' W' →
        NumbersDVR.intNum F W ![β] = NumbersDVR.intNum F W' ![β']

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def VeryAmpleEq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    IsGraphGen Q n s →
      (Kleiman.IsVeryAmple Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple S (graphVec x s) (graphDeg n))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

