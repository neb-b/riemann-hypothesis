module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CechPic GlobalTheory.Adelic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.QCoh

namespace GlobalTheory.ProjVar

structure Var (F : Type) [Field F] : Type where

  N : ℕ

  I : (PSpace F N).IdealSheafData

  dim : ℕ

  smooth : SmoothOfRelativeDimension dim (I.subschemeι ≫ PSpace.str F N)

  geomIntegral : GeometricallyIntegral (I.subschemeι ≫ PSpace.str F N)

namespace Var

variable {F : Type} [Field F] (Y : Var F)

def X : Scheme.{0} := Y.I.subscheme

def ι : Y.X ⟶ PSpace F Y.N := Y.I.subschemeι

def str : Y.X ⟶ Sp F := Y.ι ≫ PSpace.str F Y.N

theorem ι_str : Y.ι ≫ PSpace.str F Y.N = Y.str := rfl

instance isClosedImmersion_ι : IsClosedImmersion Y.ι :=
  inferInstanceAs (IsClosedImmersion Y.I.subschemeι)

instance smooth_str : SmoothOfRelativeDimension Y.dim Y.str := Y.smooth

instance geometricallyIntegral_str : GeometricallyIntegral Y.str := Y.geomIntegral

instance geometricallyConnected_str : GeometricallyConnected Y.str :=
  ⟨fun _ _ y _ fst snd h =>
    have := GeometricallyIntegral.geometrically_isIntegral (f := Y.str) y fst snd h
    inferInstance⟩

instance isIntegral_X : IsIntegral Y.X := GeometricallyIntegral.isIntegral_of_subsingleton Y.str

theorem isProjOver : IsProjOver Y.str := ⟨Y.N, Y.ι, inferInstance, rfl⟩

instance isProper_str : IsProper Y.str :=
  have := Geo.Tor.isProper_str F Y.N
  inferInstanceAs (IsProper (Y.ι ≫ PSpace.str F Y.N))

theorem isNormalScheme : IsNormalScheme Y.X :=
  have := SmoothOfRelativeDimension.smooth Y.dim Y.str
  isNormalScheme_of_smooth Y.str

theorem topologicalKrullDim_eq : topologicalKrullDim Y.X = Y.dim := by
  have hc (U : Y.X.Opens) (hU : IsAffineOpen U) (h : (U : Set Y.X).Nonempty) :
      topologicalKrullDim (U : Set Y.X) = Y.dim := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y.X, U))).trans
      (SmoothDim.ringKrullDim_affineOpen F _ Y.str _ inferInstance U hU h)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens (Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens
      (Opens.mem_top (genericPoint Y.X))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)


attribute [local instance] MvPolynomial.gradedAlgebra in
def coneIdeal : Ideal (MvPolynomial (Fin (Y.N + 1)) F) :=
  (show ProjectiveSpectrum (ProjSpace.grading F Y.N) from
    Y.ι (genericPoint Y.X)).asHomogeneousIdeal.toIdeal



section OfImmersion

variable {Z : Scheme.{0}} {N : ℕ} (i : Z ⟶ PSpace F N) [IsClosedImmersion i] (d : ℕ)
  [SmoothOfRelativeDimension d (i ≫ PSpace.str F N)] [GeometricallyIntegral (i ≫ PSpace.str F N)]


omit [SmoothOfRelativeDimension d (i ≫ PSpace.str F N)]
  [GeometricallyIntegral (i ≫ PSpace.str F N)] in
theorem subschemeι_ker : i.ker.subschemeι = inv i.toImage ≫ i := by
  rw [IsIso.eq_inv_comp]; exact i.toImage_imageι

def ofClosedImmersion : Var F where
  N := N
  I := i.ker
  dim := d
  smooth := by
    rw [subschemeι_ker, Category.assoc]
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} d
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩) ‹_›
  geomIntegral := by
    rw [subschemeι_ker, Category.assoc]
    exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩) ‹_›

def isoOfClosedImmersion : Z ≅ (ofClosedImmersion i d).X :=
  show Z ≅ i.image from asIso i.toImage

theorem isoOfClosedImmersion_ι :
    (isoOfClosedImmersion i d).hom ≫ (ofClosedImmersion i d).ι = i := i.toImage_imageι

end OfImmersion

theorem exists_iso {Z : Scheme.{0}} (p : Z ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p]
    [GeometricallyConnected p] (h : IsProjOver p) :
    ∃ (Y : Var F) (e : Z ≅ Y.X), Y.dim = d ∧ e.hom ≫ Y.str = p := by
  obtain ⟨N, i, _, rfl⟩ := h
  have := SmoothOfRelativeDimension.smooth d (i ≫ PSpace.str F N)
  have := geometricallyIntegral_of_smooth (i ≫ PSpace.str F N)
  exact ⟨ofClosedImmersion i d, isoOfClosedImmersion i d, rfl,
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (isoOfClosedImmersion_ι i d))⟩

instance algebraΓ : Algebra F Γ(Y.X, ⊤) := algebraΓOfHom Y.str

theorem algebraMap_Γ (a : F) :
    algebraMap F Γ(Y.X, ⊤) a = Y.str.appTop ((Scheme.ΓSpecIso (.of F)).inv a) := rfl

abbrev Fn : Type := Y.X.functionField

instance algebraFn : Algebra F Y.Fn := (Cartier.constFn Y.str).toAlgebra

instance isScalarTower_Fn : IsScalarTower F Γ(Y.X, ⊤) Y.Fn :=
  .of_algebraMap_eq fun a => congrArg (fnOf ⊤ trivial) (LB.resG_self (X := Y.X) le_top _)

theorem regAt_algebraMap (x : Y.X) (a : F) : RegAt x (algebraMap F Y.Fn a) :=
  regAt_fnOf (U := ⊤) trivial trivial _

abbrev Dv : Type := CartierDiv Y.X

def Eff (Δ : Y.Dv) : Prop := Δ.Eff

def H0 (Δ : Y.Dv) : Submodule F Y.Fn := Δ.sections.restrictScalars F


variable {Y} in
theorem mem_riemannRochSpace_iff_regularAt_everywhere {Δ : Y.Dv} {f : Y.Fn} : f ∈ Y.H0 Δ ↔ ∀ x, Δ.RegularAt x f := mem_sections



variable {Y} in
theorem eff_iff_one_mem {Δ : Y.Dv} : Y.Eff Δ ↔ (1 : Y.Fn) ∈ Y.H0 Δ := mem_riemannRochSpace_iff_regularAt_everywhere.symm

theorem eff_zero : Y.Eff 0 := CartierDiv.eff_zero

theorem eff_add (a b : Y.Dv) (ha : Y.Eff a) (hb : Y.Eff b) : Y.Eff (a + b) :=
  CartierDiv.Eff.add ha hb

theorem mul_mem_riemannRochSpace_add (Δ Δ' : Y.Dv) (f g : Y.Fn) (hf : f ∈ Y.H0 Δ) (hg : g ∈ Y.H0 Δ') :
    f * g ∈ Y.H0 (Δ + Δ') := mem_riemannRochSpace_iff_regularAt_everywhere.2 fun x => (mem_riemannRochSpace_iff_regularAt_everywhere.1 hf x).mul (mem_riemannRochSpace_iff_regularAt_everywhere.1 hg x)

theorem riemannRoch_mono (Δ Δ' : Y.Dv) (h : Y.Eff (Δ' - Δ)) : Y.H0 Δ ≤ Y.H0 Δ' := fun f hf => by
  simpa using Y.mul_mem_riemannRochSpace_add Δ (Δ' - Δ) f 1 hf (eff_iff_one_mem.1 h)

abbrev lb (Δ : Y.Dv) : LB Y.X := toLB Δ


variable {Y} in
def cohEquiv {Δ : Y.Dv} {L : LB Y.X} {r : L.ι → Y.Fnˣ} (h : Presents Δ L r) :
    coh (twist (structureModule Y.X) L) 0 ≃ₗ[F] Y.H0 Δ :=
  ((cohZeroTwistEquiv L).trans h.secEquiv).restrictScalars F


variable {Y} in
theorem finrank_sections_projectiveLine {Δ : Y.Dv} {L : LB Y.X} {r : L.ι → Y.Fnˣ} (h : Presents Δ L r) :
    Module.finrank F (Y.H0 Δ) = lbH0 F L := (cohEquiv h).finrank_eq.symm

instance finiteDimensional_riemannRochSpace (Δ : Y.Dv) : FiniteDimensional F (Y.H0 Δ) :=
  have := finite_coh_zero_twist_of_isProjOver Y.algebraMap_Γ Y.isProjOver (isLB_toLB Δ)
  .equiv (cohEquiv (presents_toLB Δ))

def KY : Y.Dv := canonical Y.str Y.dim

abbrev Cl : Type := Closeds Y.X

def properCl (Z : Y.Cl) : Prop := Z ≠ ⊤

def subCl (Z Z' : Y.Cl) : Prop := Z ≤ Z'

def supp (Δ : Y.Dv) : Y.Cl := Δ.supp

def bpf (Δ : Y.Dv) (V : Set Y.Fn) : Prop := Δ.BasePointFree V

def vanishOn (Δ : Y.Dv) (f : Y.Fn) (Z : Y.Cl) : Prop := Δ.VanishesOn f Z

def phiBir (Δ : Y.Dv) (V : Set Y.Fn) : Prop := Δ.Birational F V

def phiNoContr (Δ : Y.Dv) (V : Set Y.Fn) (bd : Y.Cl) : Prop := Δ.NoContract F V bd

theorem properCl_iff (Z : Y.Cl) : Y.properCl Z ↔ genericPoint Y.X ∉ Z :=
  not_congr ⟨fun h => h.ge (Set.mem_univ _), fun h => top_le_iff.1
    (((genericPoint_spec Y.X).mem_closed_set_iff Z.isClosed).1 h)⟩



theorem isCompleteCurve_iff (Z : Y.Cl) : IsCompleteCurve F Z ↔
    IsIrreducible (Z : Set Y.X) ∧ topologicalKrullDim (Z : Set Y.X) = 1 :=
  GlobalTheory.isCompleteCurve_iff Y.algebraMap_Γ

abbrev sysOf {L : LB Y.X} (hL : L.IsLB) {n : ℕ} (s : Fin n → L.Sec) : LinSys F where
  Y := Y.X
  str := Y.str
  D := Y.dim
  L := L
  isLB := hL
  N := n
  b := s



section LinSys

variable {Δ : Y.Dv} {n : ℕ} (b : Fin n → Y.H0 Δ)

end LinSys

section Hyperplane

open ProjSpace

abbrev O1 : LB Y.X := (ProjSpace.O1 F Y.N).pull Y.ι

theorem isLineBundle_twistingSheafOne : Y.O1.IsLB := LB.isLB_pull (O1_isLB F Y.N) _

theorem isAmple_projective_O_one : IsAmpleLB Y.O1 :=
  (GlobalTheory.isAmple_projective_O_one F Y.N).pull_of_isClosedImmersion _

def coordSec (j : Fin (Y.N + 1)) : Y.O1.Sec := secPull (coord F Y.N j) Y.ι

theorem nonzeroLocus_coordSec (j : Fin (Y.N + 1)) :
    nonzeroLocus (Y.coordSec j) = Y.ι ⁻¹ᵁ chart F Y.N j := by
  rw [coordSec, nonzeroLocus_secPull, nonzeroLocus_coord]
  rfl

abbrev coordSys : LinSys F := Y.sysOf Y.isLineBundle_twistingSheafOne Y.coordSec

def idx (i : Fin (Y.N + 1)) : Y.O1.ι := fun _ => i

theorem twistingSheafOne_chart_eq_preimage_standardChart (i : Fin (Y.N + 1)) : Y.O1.U (Y.idx i) = Y.ι ⁻¹ᵁ chart F Y.N i :=
  LB.pull_U (L := ProjSpace.O1 F Y.N) Y.ι (Y.idx i)

def chartHom (i : Fin (Y.N + 1)) :
    Γ(PSpace F Y.N, chart F Y.N i) →+* Γ(Y.X, Y.O1.U (Y.idx i)) :=
  (Y.ι.appLE _ _ (Y.twistingSheafOne_chart_eq_preimage_standardChart i).le).hom

theorem chartEval_coordSec (i : Fin (Y.N + 1)) (g : MvPolynomial (Fin (Y.N + 1)) F) :
    Twist.chartEval F Y.coordSec (Y.idx i) le_rfl g = Y.chartHom i (aeval (ratio F Y.N i) g) := by
  rw [Twist.chartEval, aeval_def, ← coe_eval₂Hom, map_eval₂Hom]
  congr 2
  · refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, ← resG_algebraMap le_top, chartHom, LB.appLE_resG,
      algebraMap_top_eq]
    rfl
  · exact funext fun l => LB.resG_self _ _


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem mem_nonzeroLocus_form {d : ℕ} {g : MvPolynomial (Fin (Y.N + 1)) F} (hg : g.IsHomogeneous d)
    (y : Y.X) : y ∈ nonzeroLocus (Y.coordSys.form hg) ↔
      Y.ι y ∈ Proj.basicOpen (grading F Y.N) g := by
  obtain ⟨i, hi⟩ := exists_mem_chart F Y.N (Y.ι y)
  have hj : y ∈ Y.O1.U (Y.idx i) := (Y.twistingSheafOne_chart_eq_preimage_standardChart i).ge hi
  have e := Twist.basicOpen_zfun (Y.coordSys.form hg) (Y.idx i)
  rw [LinSys.form, Twist.zfun_formSec, chartEval_coordSec, ← formOn_eq_aeval hg] at e
  replace e := (Scheme.basicOpen_appLE Y.ι _ _ (Y.twistingSheafOne_chart_eq_preimage_standardChart i).le _).symm.trans e
  rw [basicOpen_formOn] at e
  exact ⟨fun h => (e.ge ⟨hj, h⟩).2.2, fun h => (e.le ⟨hj, hi, h⟩).2⟩

theorem basePointFree_coordSys : Y.coordSys.BasePointFree := eq_top_iff.2 fun y _ =>
  have ⟨j, hj⟩ := exists_mem_chart F Y.N (Y.ι y)
  Opens.mem_iSup.2 ⟨j, (Y.nonzeroLocus_coordSec j).ge hj⟩


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem eq_of_sameImage {y y' : Y.X} (h : Y.coordSys.SameImage y y') : y = y' := by
  refine Y.ι.isClosedEmbedding.injective
    (ProjectiveSpectrum.ext (HomogeneousIdeal.ext' fun d g hg => ?_))
  replace hg : g.IsHomogeneous d := hg
  have := h d g hg
  rw [mem_nonzeroLocus_form, mem_nonzeroLocus_form] at this
  exact not_iff_not.1 this

theorem noContract_coordSys (bd : Set Y.X) : Y.coordSys.NoContract bd := fun C _ _ hC _ h => by
  have : Subsingleton C := ⟨fun a b => Subtype.ext (Y.eq_of_sameImage (h _ a.2 _ b.2))⟩
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hC] at this
  exact absurd this (by decide)

variable {i : Fin (Y.N + 1)} (hi : Y.ι (genericPoint Y.X) ∈ chart F Y.N i)


include hi in
theorem genericPoint_mem_twistingSheafOne_chart : genericPoint Y.X ∈ Y.O1.U (Y.idx i) := (Y.twistingSheafOne_chart_eq_preimage_standardChart i).ge hi

def hyp : Y.Dv := ofLB Y.isLineBundle_twistingSheafOne (Y.idx i) (Y.genericPoint_mem_twistingSheafOne_chart hi)

theorem presents_hyp : Presents (Y.hyp hi) Y.O1 (frameRat _ (Y.idx i) (Y.genericPoint_mem_twistingSheafOne_chart hi)) :=
  presents_ofLB _ _ _

def coordFn (j : Fin (Y.N + 1)) : Y.Fn := (Y.presents_hyp hi).rat (Y.coordSec j)

theorem aeval_coordFn (g : MvPolynomial (Fin (Y.N + 1)) F) : aeval (Y.coordFn hi) g =
    fnOf _ (Y.genericPoint_mem_twistingSheafOne_chart hi) (Y.chartHom i (aeval (ratio F Y.N i) g)) := by
  rw [← Y.chartEval_coordSec i, Twist.chartEval, map_eval₂Hom, aeval_def, coe_eval₂Hom]
  congr 1
  · exact RingHom.ext fun a => (IsScalarTower.algebraMap_apply F Γ(Y.X, ⊤) _ a).trans
      (fnOf_resG le_top _ _).symm
  · funext j
    rw [LB.resG_self, ← (Y.presents_hyp hi).rat_mul, frameRat_self Y.isLineBundle_twistingSheafOne, Units.val_one, mul_one,
      coordFn]

theorem coordFn_self : Y.coordFn hi i = 1 := by
  have := Y.aeval_coordFn hi (MvPolynomial.X i)
  rwa [aeval_X, aeval_X, ratio, ratioOn_self, map_one, map_one] at this

theorem coordFn_mem (j : Fin (Y.N + 1)) : Y.coordFn hi j ∈ Y.H0 (Y.hyp hi) :=
  (Y.presents_hyp hi).rat_mem _

theorem eff_hyp : Y.Eff (Y.hyp hi) := eff_iff_one_mem.2 (Y.coordFn_self hi ▸ Y.coordFn_mem hi i)

theorem bpf_hyp : Y.bpf (Y.hyp hi) (Set.range (Y.coordFn hi)) :=
  (Presents.basePointFree_iff (S := Y.coordSys) (Y.presents_hyp hi)).2 Y.basePointFree_coordSys

theorem phiNoContr_hyp (bd : Y.Cl) : Y.phiNoContr (Y.hyp hi) (Set.range (Y.coordFn hi)) bd :=
  (Presents.noContract_iff (S := Y.coordSys) (Y.presents_hyp hi) Y.basePointFree_coordSys _).2
    (Y.noContract_coordSys _)

end Hyperplane

theorem not_phiNoContr_of_constant (h : Y.dim = 1) {Δ : Y.Dv} {V : Set Y.Fn}
    (hV : ∀ f ∈ V, f ∈ Set.range (algebraMap F Y.Fn)) : ¬ Y.phiNoContr Δ V ⊥ := fun c =>
  c.2 Set.univ isClosed_univ (IrreducibleSpace.isIrreducible_univ _)
    ((topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans
      (Y.topologicalKrullDim_eq.trans (by rw [h]; rfl)))
    (Set.disjoint_empty _) (contracts_of_constant Y.regAt_algebraMap hV _)

end Var

def RiemannRochFinite (F : Type) [Field F] : Prop :=
  ∀ (Y : Var F) (Δ : Y.Dv), FiniteDimensional F (Y.H0 Δ)

theorem riemannRoch_finite (F : Type) [Field F] : RiemannRochFinite F := Var.finiteDimensional_riemannRochSpace

section Proj

open ProjSpace

variable (F : Type) [Field F] (n : ℕ)

instance smooth_id_str : SmoothOfRelativeDimension n (𝟙 _ ≫ PSpace.str F n) := by
  rw [Category.id_comp]; exact smoothOfRelativeDimension_pspace F n

instance geometricallyIntegral_id_str : GeometricallyIntegral (𝟙 _ ≫ PSpace.str F n) := by
  have := SmoothOfRelativeDimension.smooth n (𝟙 _ ≫ PSpace.str F n)
  have : GeometricallyConnected (𝟙 _ ≫ PSpace.str F n) := by
    rw [Category.id_comp]; exact geometricallyConnected_pspace F n
  exact geometricallyIntegral_of_smooth _

def proj : Var F := Var.ofClosedImmersion (𝟙 (PSpace F n)) n

theorem proj_dim : (proj F n).dim = n := rfl

instance isIso_proj_ι : IsIso (proj F n).ι :=
  have : IsIso ((Var.isoOfClosedImmersion (𝟙 (PSpace F n)) n).hom ≫ (proj F n).ι) :=
    (Var.isoOfClosedImmersion_ι (𝟙 (PSpace F n)) n).symm ▸ inferInstanceAs (IsIso (𝟙 _))
  IsIso.of_isIso_comp_left (Var.isoOfClosedImmersion (𝟙 (PSpace F n)) n).hom _

theorem proj_gen_mem (i : Fin (n + 1)) :
    (proj F n).ι (genericPoint (proj F n).X) ∈ chart F n i :=
  have h : genericPoint (PSpace F (proj F n).N) ∈ chart F n i := gen_mem (projSys.gen_mem F n i)
  (genericPoint_eq_of_isOpenImmersion (proj F n).ι).symm ▸ h

def projHyp : (proj F n).Dv := (proj F n).hyp (proj_gen_mem F n 0)

theorem finrank_riemannRoch_hyperplane : Module.finrank F ((proj F n).H0 (projHyp F n)) = n + 1 := by
  have := Geo.Tor.isProper_str F n
  have H : IsPullback (proj F n).ι (proj F n).str (PSpace.str F n)
      (Spec.map (CommRingCat.ofHom (algebraMap F F))) := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap F F)) = 𝟙 _ from Spec.map_id _]
    exact IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
  have h := FieldChangeInter.hdim_pull (f := PSpace.str F n) H (O1_isLB F n) 0
  refine (Var.finrank_sections_projectiveLine ((proj F n).presents_hyp _)).trans (h.trans ?_)
  have e := sectionDim_twistingSheaf_pow F n 1
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow (O1_isLB F n) 1) (O1_isLB F n)
    (by rw [cls_lbPow (O1_isLB F n), one_nsmul]), add_comm, Nat.choose_succ_self_right,
    ← projSys.algebraΓ_eq] at e
  exact e

theorem exists_nonconstant_line : ∃ f ∈ (proj F 1).H0 (projHyp F 1),
    f ∉ Set.range (algebraMap F (proj F 1).Fn) := by
  by_contra! h
  exact (proj F 1).not_phiNoContr_of_constant rfl
    (fun f hf => h f (((proj F 1).bpf_hyp _).mem f hf))
    ((proj F 1).phiNoContr_hyp (proj_gen_mem F 1 0) ⊥)

end Proj

end GlobalTheory.ProjVar
