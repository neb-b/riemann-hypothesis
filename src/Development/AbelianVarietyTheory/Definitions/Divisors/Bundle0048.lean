module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FrameSignSimple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj.SumModel

open GlobalTheory.ChiGrid Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem readOK {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) : ReadOK σ := by
  obtain ⟨Φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ Φ fun F => (h F _).2 rfl

theorem finEmb_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) (x : GfC B)
    (h : EmbRel B A d.ι x.1 y.1) : finEmb d y = x :=
  Subtype.ext ((GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom y.1).unique (finEmb_rel d y) h)

theorem finEmb_mul {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y y' : GfC A) :
    finEmb d (y * y') = finEmb d y * finEmb d y' := by
  refine finEmb_eq d _ _ ⟨?_, fun v hv => ?_⟩
  · have h1 := (finEmb_rel d y).1
    have h2 := (finEmb_rel d y').1
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  · have h1 := (finEmb_rel d y).2 v hv
    have h2 := (finEmb_rel d y').2 v hv
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [← Matrix.mulVec_mulVec, h2, h1]

end GlobalTheory.FunObj.SumModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MeasureTheory Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CxPts GlobalTheory.TopForm GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B L : LB Y} {O : Y.Opens}

theorem CompHS.cval_mem_fibSec (f : H0 p B O) : cval σ f ∈ fibSec p σ B := by
  refine ⟨fun i j y hi hj => ?_, fun i y h => ev_of_notMem (fun e => h (mem_ptsIn_inf.1 e).2) _⟩
  by_cases hO : y ∈ ptsIn p σ O
  · rw [cval_eq_val σ f i y hO hi, cval_eq_val σ f j y hO hj, H0.val_change y.1 i j hO hi hj]
    exact congrArg (· * _) (ev_eq (mem_ptsIn_inf.2 ⟨hi, hj⟩) _).symm
  · exact (ev_of_notMem (fun e => hO (mem_ptsIn_inf.1 e).1) _).trans
      ((mul_zero _).symm.trans (congrArg _ (ev_of_notMem (fun e => hO (mem_ptsIn_inf.1 e).1) _).symm))

namespace CompHS

def divVal (σ : k →+* ℂ) (ω : H0 p (LB.div B L) O) : (tens B (dual L)).ι → CxPts p σ → ℂ := cval σ ω

theorem divVal_mem (ω : H0 p (LB.div B L) O) : divVal σ ω ∈ fibSec p σ (tens B (dual L)) := by
  have h := cval_mem_fibSec (σ := σ) ω
  refine ⟨fun i j y hi hj => (h.1 i j y hi hj).trans (congrArg (· * _) ?_), h.2⟩
  have hy := mem_ptsIn_inf.2 ⟨hi, hj⟩
  exact (ev_mul _ _ y).trans (Eq.trans (congrArg (_ * ·) ((ev_inv hy _).trans (Eq.symm ((ev_res _ hy _).trans
    ((ev_inv (mem_ptsIn_inf.2 ⟨(mem_ptsIn_inf.1 hi).2, (mem_ptsIn_inf.1 hj).2⟩) _).trans
      (congrArg (·⁻¹) (ev_res _ hy _).symm)))))) (ev_mul _ _ y).symm)

variable {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) (φ φ' : Weight p σ L)
  (ω : H0 p (LB.div K.bundle L) O)

def volDens (a : AlgChart p σ D) (y : CxPts p σ) : ℝ := a.topDens K φ.dual (divVal σ ω) y

def volMeasure : Measure (CxPts p σ) :=
  ((AnRead.all p σ D).topMeasure K φ.dual (divVal σ ω)).restrict (ptsIn p σ O)

variable {φ φ'}

theorem volDens_eq (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source) {i : K.bundle.ι} {j : L.ι}
    (hi : y ∈ ptsIn p σ (K.bundle.U i)) (hj : y ∈ ptsIn p σ (L.U j)) : volDens K φ ω a y =
      2 ^ D * (‖rv σ a.isFrame (K.isFrame i) y * cval σ ω (i, j) y‖ ^ 2 / Real.exp (-φ.φ j y)) := by
  rw [volDens, a.topDens_eq K φ.dual (divVal_mem ω) hy hi (b := j) hj, div_eq_mul_inv, ← Real.exp_neg]
  rfl

theorem volDens_pos (hω : NowhereZero ω) (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source)
    (hO : y ∈ ptsIn p σ O) : 0 < volDens K φ ω a y := by
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  have hm : y ∈ ptsIn p σ (O ⊓ (LB.div K.bundle L).U (_, _)) := mem_ptsIn_inf.2 ⟨hO, mem_ptsIn_inf.2 ⟨hi, hj⟩⟩
  have h₁ : cval σ ω (_, _) y ≠ 0 := (mem_ptsIn_basicOpen hm _).1 (mem_ptsIn.2
    ((Y.mem_basicOpen _ _ (mem_ptsIn.1 hm)).2 (hω _ (mem_ptsIn.1 hm).1 _ (mem_ptsIn.1 hm).2)))
  have h₂ := mul_ne_zero (rv_ne_zero a.isFrame (K.isFrame _) (a.source_subset hy) hi) h₁
  rw [volDens_eq K ω a hy hi hj]
  exact mul_pos (by positivity) (div_pos (pow_pos (norm_pos_iff.2 h₂) _) (Real.exp_pos _))

variable [SecondCountableTopology (CxPts p σ)]

theorem volMeasure_apply (a : AlgChart p σ D) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (h : A ⊆ a.e.source) :
    volMeasure K φ ω A = ∫⁻ v in a.e '' (A ∩ ptsIn p σ O), ENNReal.ofReal (volDens K φ ω a (a.e.symm v)) := by
  rw [volMeasure, Measure.restrict_apply hA]
  exact (AnRead.all p σ D).topMeasure_apply K _ _ a (hA.inter (isOpen_ptsIn O).measurableSet) (inter_subset_left.trans h)

theorem volMeasure_of_add {s : ℝ} (h : ∀ j, ∀ y ∈ ptsIn p σ O, y ∈ ptsIn p σ (L.U j) → φ'.φ j y = φ.φ j y + s) :
    volMeasure K φ' ω = ENNReal.ofReal (Real.exp s) • volMeasure K φ ω := by
  refine ext_of_cover _ (fun a : AlgChart p σ D => a.e.open_source) AlgChart.exists_mem_source fun a A hA hs => ?_
  have hA' := hA.inter (isOpen_ptsIn (p := p) (σ := σ) O).measurableSet
  rw [smul_apply, volMeasure_apply K ω a hA hs, volMeasure_apply K ω a hA hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_image a.e hA' (inter_subset_left.trans hs)) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  simp only [a.e.left_inv (hs hy.1)]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, volDens_eq K ω a (hs hy.1) hi hj, volDens_eq K ω a (hs hy.1) hi hj,
    h _ y hy.2 hj, neg_add, Real.exp_add, Real.exp_neg s]
  congr 1
  field_simp

theorem volMeasure_pos (hω : NowhereZero ω) (hφ : ∀ j, ContinuousOn (φ.φ j) (ptsIn p σ O ∩ ptsIn p σ (L.U j)))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ O) : 0 < volMeasure K φ ω univ := by
  obtain ⟨a, ha⟩ := AlgChart.exists_mem_source (D := D) y
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  set i := pick K.isLB y
  set j := pick φ.isLB y
  let S := a.e.source ∩ (ptsIn p σ (a.U ⊓ K.bundle.U i) ∩ ptsIn p σ (O ⊓ (LB.div K.bundle L).U (i, j)))
  have hS : IsOpen S := a.e.open_source.inter ((isOpen_ptsIn _).inter (isOpen_ptsIn _))
  have hO : S ⊆ ptsIn p σ O := fun z hz => (mem_ptsIn_inf.1 hz.2.2).1
  have hL : S ⊆ ptsIn p σ (L.U j) := fun z hz => (mem_ptsIn_inf.1 (mem_ptsIn_inf.1 hz.2.2).2).2
  have hc : ContinuousOn (volDens K φ ω a) S := (continuousOn_const.mul
    (((((continuousOn_ev _).mono (t := S) fun _ hz => hz.2.1).mul
      ((continuousOn_ev _).mono (t := S) fun _ hz => hz.2.2)).norm.pow 2).div
      ((hφ j).mono (subset_inter hO hL)).neg.rexp fun _ _ => (Real.exp_pos _).ne')).congr
    fun z hz => volDens_eq K ω a hz.1 (mem_ptsIn_inf.1 hz.2.1).2 (hL hz)
  have ho := a.e.isOpen_image_of_subset_source hS inter_subset_left
  have hm : MapsTo a.e.symm (a.e '' S) S := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [a.e.left_inv hz.1]
  have hc' := ENNReal.continuous_ofReal.comp_continuousOn (hc.comp (a.e.continuousOn_symm.mono (t := a.e '' S)
    (image_subset_iff.2 fun _ hz => a.e.map_source hz.1)) hm)
  refine lt_of_lt_of_le ?_ (measure_mono (subset_univ S))
  rw [volMeasure_apply K ω a hS.measurableSet inter_subset_left, inter_eq_left.2 hO, pos_iff_ne_zero]
  intro h
  have h₁ := (ae_restrict_iff' ho.measurableSet).1 ((lintegral_eq_zero_iff' (hc'.aemeasurable ho.measurableSet)).1 h)
  refine (ho.measure_pos volume ⟨_, y, ⟨ha, mem_ptsIn_inf.2 ⟨a.source_subset ha, hi⟩,
    mem_ptsIn_inf.2 ⟨hy, mem_ptsIn_inf.2 ⟨hi, hj⟩⟩⟩, rfl⟩).ne' (measure_mono_null ?_ (ae_iff.1 h₁))
  exact fun v hv hh => (ENNReal.ofReal_pos.2 (volDens_pos K ω hω a (hm hv).1 (hO (hm hv)))).ne' (hh hv)

end CompHS

end General

namespace CompHS

open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (exOf wtOf lieFacZ modelWt homN)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Good

variable {Y T : Scheme.{0}} {p : Y ⟶ Sp c.F} {σ σ' : c.F →+* ℂ} {B : LB Y}


end Good

section Fac

variable {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)


open Classical in
def diagChar (e : Ix Dw → ℤ) (t : Ix Dw → (CAt σ)ˣ) : ℂ := toC (∏ ix, t ix ^ e ix).val

def homFac (la : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) : ℝ :=
  lieFacZ Dw x (wtOf Dw la 0) * (U.X k).nfac (modelWt U (wtOf Dw la 0) k) w.1

theorem homN_eq_homFac (la : AllWt.Weight Dw) (f : Rul Xo c) (k : U.Comp) (w : (U.X k).dom) :
    homN U x (wtOf Dw la 0) f ⟨k, w.1⟩ = homFac U x la k w * ‖toC (evR Xo c f (U.un k w))‖ := by
  have e : rdU U f k w.1 = toC (evR Xo c f (U.un k w)) := dite_eq_left w.2
  change _ * (‖rdU U f k w.1‖ * (U.X k).nfac _ _) = _
  rw [e, homFac]
  ring

variable {U}

end Fac

end CompHS

end GlobalTheory
end
end

