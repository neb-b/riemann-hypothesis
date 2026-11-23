module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorDescendedBundleNearClosedPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArith
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem enat_add_natCast_eq_natCast_exists {c : ℕ∞} {a b : ℕ} (h : c + (a : ℕ∞) = (b : ℕ∞)) : ∃ n : ℕ, c = n ∧ n + a = b := by
  induction c using ENat.recTopCoe with
  | top => simp at h
  | coe n => exact ⟨n, rfl, by exact_mod_cast h⟩

theorem dimOne : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ,
    topologicalKrullDim Y = (e + 1 : ℕ) → (∀ z : Y, Order.coheight z = 1 ↔ HasDim z e) ∧
    ∀ (z : Y) (w : clo z), Order.coheight z = 1 →
      (topologicalKrullDim (clo z) = e ∧ (Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2)) := by
  intro k _ Y _ q hq e hY
  have hB := _root_.GlobalTheory.MixHt.hasDim_basic k Y q hq
  have hC := _root_.GlobalTheory.DimCoheight.coheight_add_eq k Y q hq (e + 1) hY
  have h1 : ∀ z : Y, Order.coheight z = 1 ↔ HasDim z e := by
    intro z
    obtain ⟨m, hm⟩ := hB.1
    obtain ⟨d, -, hd⟩ := hm z
    obtain ⟨n, hn, hnd⟩ := enat_add_natCast_eq_natCast_exists (hC z d hd)
    constructor
    · intro hz
      rw [hz] at hn
      have : n = 1 := by exact_mod_cast hn.symm
      subst this
      have : d = e := by omega
      exact this ▸ hd
    · intro hz
      have := hB.2.1 z d e hd hz
      subst this
      rw [hn]
      have : n = 1 := by omega
      simp [this]
  refine ⟨h1, fun z w hz => ?_⟩
  have hze : HasDim z e := (h1 z).1 hz
  have hgen : HasDim (genericPoint (clo z)) e := by
    rw [← hB.2.2.2.2.1 (clo z) (cloι z) (genericPoint (clo z)) e, cloι_genericPoint]
    exact hze
  have hdim : topologicalKrullDim (clo z) = e := (hB.2.2.2.2.2 (clo z) e).1 hgen
  refine ⟨hdim, ?_⟩
  have hq' : IsAmb (cloι z ≫ q) := hq.sub (cloι z)
  have hB' := _root_.GlobalTheory.MixHt.hasDim_basic k (clo z) (cloι z ≫ q) hq'
  obtain ⟨m, hm⟩ := hB'.1
  obtain ⟨d, -, hd⟩ := hm w
  have hd' : HasDim (cloι z w) d := (hB.2.2.2.2.1 (clo z) (cloι z) w d).2 hd
  obtain ⟨n, hn, hnd⟩ := enat_add_natCast_eq_natCast_exists (_root_.GlobalTheory.DimCoheight.coheight_add_eq k (clo z) (cloι z ≫ q) hq' e hdim w d hd)
  obtain ⟨n', hn', hnd'⟩ := enat_add_natCast_eq_natCast_exists (hC (cloι z w) d hd')
  have : n' = n + 1 := by omega
  rw [hn, hn', this]
  constructor
  · intro h
    have : n = 1 := by exact_mod_cast h
    simp [this]
  · intro h
    have : n + 1 = 2 := by exact_mod_cast h
    have : n = 1 := by omega
    simp [this]

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfKillsGeometricTorsionPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem comp_hom_eq_one_of_torsion_pts (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ)
    (hn : (n : K) ≠ 0) (hker : ∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1)
    (T : Over (Sp K)) (x : T ⟶ A.X) (hx : x ^ n = 1) : x ≫ f.hom = 1 := by
  have hA := A.ab
  have hC := C.ab
  have := hA.proper
  have := hC.proper
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨_, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion A.X hu
  have hι : torsion.ι A.X n ≫ mulN A.X n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ η[A.X]) (toUnit_unique _ _))
  set L := AlgebraicClosure K
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht
  let P := (Over.pullback t).obj (torsion A.X n)
  let C' := (Over.pullback t).obj C.X
  have hP : Etale P.hom := by
    change Etale (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hPf : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hC' : IsProper C'.hom := by
    change IsProper (pullback.snd C.X.hom t)
    infer_instance
  have hPr : IsReduced P.left := isReduced_of_smooth_of_isReduced P.hom
  have hfst : ∀ g : torsion A.X n ⟶ C.X, ((Over.pullback t).map g).left ≫ pullback.fst C.X.hom t =
      pullback.fst (torsion A.X n).hom t ≫ g.left := fun g => by
    simp
  have hEq : (Over.pullback t).map (torsion.ι A.X n ≫ f.hom) =
      (Over.pullback t).map (1 : torsion A.X n ⟶ C.X) := by
    refine TorsionDivisible.hom_ext_of_rationalPoints _ _ fun y => ?_
    let z : Sp L ⟶ (torsion A.X n).left := y.left ≫ pullback.fst (torsion A.X n).hom t
    have hz : z ≫ (torsion A.X n).hom = t := by
      have e1 : y.left ≫ P.hom = 𝟙 _ := by
        change y.left ≫ pullback.snd (torsion A.X n).hom t = _
        simpa using Over.w y
      simp only [z, Category.assoc, pullback.condition]
      rw [← Category.assoc]
      change (y.left ≫ P.hom) ≫ t = t
      rw [e1, Category.id_comp]
    let z' : ptOver K L ⟶ torsion A.X n := Over.homMk z hz
    have hw : (z' ≫ torsion.ι A.X n) ^ n = 1 := by
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have hk := hker (z' ≫ torsion.ι A.X n) hw
    have hk' : z' ≫ (torsion.ι A.X n ≫ f.hom) = z' ≫ (1 : torsion A.X n ⟶ C.X) := by
      rw [MonObj.comp_one, ← Category.assoc, hk]
    have hkl : z ≫ (torsion.ι A.X n ≫ f.hom).left = z ≫ (1 : torsion A.X n ⟶ C.X).left :=
      congrArg CommaMorphism.left hk'
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, hfst]
      simpa [z] using hkl
    · have w1 := Over.w (y ≫ (Over.pullback t).map (torsion.ι A.X n ≫ f.hom))
      have w2 := Over.w (y ≫ (Over.pullback t).map (1 : torsion A.X n ⟶ C.X))
      change _ ≫ pullback.snd C.X.hom t = _ at w1 w2
      rw [w1, w2]
  have hred : IsReduced (torsion A.X n).left := isReduced_of_smooth_of_isReduced (torsion A.X n).hom
  have hdom : IsDominant (pullback.fst (torsion A.X n).hom t) := inferInstance
  have h6 : torsion.ι A.X n ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated C.X.hom (by rw [Over.w, Over.w]) (pullback.fst (torsion A.X n).hom t) ?_
    rw [← hfst, ← hfst, hEq]
  have e : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
  obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion A.X n, y ≫ torsion.ι A.X n = x :=
    ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
  rw [← e', Category.assoc, h6, MonObj.comp_one]

end GlobalTheory.AV.AbVar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtFlagCellGradedLinePotential
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.CellPotSmooth

theorem upM_fb_contDiffAt_two {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (τ : ι) (w : V n) :
    MContDiffAt 2 (fun w => upM (fb ε w) τ) w := by
  intro a b
  simp only [upM, upU, Matrix.of_apply, fb]
  split_ifs with h1 h2
  · exact ((EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨τ, ⟨(b, a), h1⟩⟩))).contDiff.restrict_scalars ℝ).contDiffAt
  · exact contDiffAt_const
  · exact contDiffAt_const

theorem G_bsL_smooth {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (τ : ι)
    (hG : MContDiffAt 2 (fun v => G v τ) (bsL ε w)) : MContDiffAt 2 (fun w => G (bsL ε w) τ) w := by
  intro a b
  exact (hG a b).comp w (((bsL ε).contDiff.restrict_scalars ℝ).contDiffAt)

theorem upU_isUnit {s : ℕ} (y : Low s → ℂ) : IsUnit (upU y) := by
  rw [Matrix.isUnit_iff_isUnit_det, upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]
  exact isUnit_one

theorem leadMinor_re_pos {s : ℕ} {A : Matrix (Fin s) (Fin s) ℂ} (hA : A.PosDef) (j : ℕ) : 0 < (leadMinor A j).re := by
  have h := (hA.submatrix (Subtype.val_injective (p := fun a : Fin s => (a : ℕ) < j))).det_pos
  exact (Complex.pos_iff.1 h).1

theorem cellPot_contDiffAt : ∀ (ι : Type) (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → ContDiffAt ℝ 2 (cellPot ε G x) w ∧ 0 < grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 := by
  intro ι m n d ε G w x hP hG
  set A : V n → Matrix (Fin (m x.1)) (Fin (m x.1)) ℂ :=
    fun w => upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ with hAdef
  have hA : MContDiffAt 2 A w :=
    ((upM_fb_contDiffAt_two ε x.1 w).mul (G_bsL_smooth ε G w x.1 hG)).mul (upM_fb_contDiffAt_two ε x.1 w).conjTranspose
  have hPA : (A w).PosDef := by
    refine hP.mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2 (upU_isUnit _)
  have hm : ∀ j : ℕ, ContDiffAt ℝ 2 (fun w => (leadMinor (A w) j).re) w := fun j =>
    Complex.reCLM.contDiff.contDiffAt.comp w (hA.submatrix _ _).det
  have h1 := leadMinor_re_pos hPA (x.2 + 1)
  have h0 := leadMinor_re_pos hPA x.2
  have hpos : 0 < grD (A w) x.2 := div_pos h1 h0
  refine ⟨?_, hpos⟩
  have hd : ContDiffAt ℝ 2 (fun w => grD (A w) x.2) w := (hm _).div (hm _) h0.ne'
  exact (hd.log hpos.ne').neg

end GlobalTheory.CellPotSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalBundleModificationDescendsToGroup
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeDesc

theorem app_bijective (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (M : Modif R) (G' : Over M.S) (G : Over (Sp R)) (β : G'.left ⟶ G.left) (hf : Flat G.hom)
    (hp : IsPullback β G'.hom G.hom M.π) : ∀ V : G.left.Opens, Function.Bijective (β.app V).hom := by
  obtain ⟨hN, -, hI, -⟩ := hR
  haveI := M.proper
  exact _root_.GlobalTheory.Mum.app_bijective_of_flat_baseChange R M.S G.left G'.left M.π G.hom β G'.hom inferInstance inferInstance
    (_root_.GlobalTheory.Mum.Modif.appTop_bijective_surjective R M).1 hf hp

theorem exists_closed_spec (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) (hG : QuasiCompact G.hom)
    (y : G.left) (hy : G.hom y = closedPoint R) :
    ∃ z : G.left, IsClosed ({z} : Set G.left) ∧ y ⤳ z ∧ G.hom z = closedPoint R := by
  haveI : CompactSpace G.left := by
    haveI := hG
    exact QuasiCompact.compactSpace_of_compactSpace G.hom
  obtain ⟨z, hz, hzc⟩ := (isClosed_closure (s := ({y} : Set G.left))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  have hyz : y ⤳ z := specializes_iff_mem_closure.2 hz
  refine ⟨z, hzc, hyz, ?_⟩
  have h := hyz.map G.hom.base.hom.continuous
  rw [hy] at h
  have hc : IsClosed ({closedPoint R} : Set (PrimeSpectrum R)) := isClosed_singleton_closedPoint R
  have h' := specializes_iff_mem_closure.1 h
  exact hc.closure_subset h'

theorem cubicalBundle_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∃ L : LB G.left, L.IsLB ∧ LBIso P'.L.L (L.pull β) := by
  intro R _ _ _ hR M G' _ _ hG' P' G _ _ β hG hpb θ O hO hθ
  have hflat : Flat G.hom := by haveI := hG.smooth; infer_instance
  have hbij := app_bijective R hR M G' G β hflat hpb.1
  have hloc : ∀ y : G.left, ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
    intro y
    by_cases hy : G.hom y = closedPoint R
    · obtain ⟨z, hzc, hyz, hz⟩ := exists_closed_spec R G hG.quasiCompact y hy
      obtain ⟨V, hzV, t⟩ := _root_.GlobalTheory.Mum.ClosedPt.exists_gen_near_closed_point R hR M G' hG' P' G β hG hpb θ O hO hθ z hzc hz
      exact ⟨V, hyz.mem_open V.isOpen hzV, t⟩
    · exact _root_.GlobalTheory.Mum.OffClosed.exists_gen_off_closed R hR M G' hG' P' G β hG hpb θ O hO hθ y hy
  exact _root_.GlobalTheory.Mum.lb_descend _ _ β hbij P'.L.L P'.L.isLB hloc

end GlobalTheory.Mum.CubeDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixPowProductEntrySmoothDbarClosed
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.PowCurv

def Good (n : ℕ) (v : V n) (f : V n → Ev n) : Prop :=
  (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((f x : Alt n)) S) v) ∧ dbarAt (fun x => (f x : Alt n)) v = 0

variable {n : ℕ} {v : V n}

theorem diff_of_smooth {α : V n → Alt n} (h : ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) (S) :
    DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v := by
  have h1 := h S
  exact h1.differentiableAt (by simp)

theorem good_const (c : Ev n) : Good n v (fun _ => c) := by
  refine ⟨fun S => (_root_.GlobalTheory.ChernCalc.smooth_coeff_closure n v).1 (c : Alt n) S, ?_⟩
  exact (_root_.GlobalTheory.CxForm.dbarAt_local_calculus n v).2.2.2.1 (c : Alt n)

theorem good_sum {J : Type} (s : Finset J) (f : J → V n → Ev n) (h : ∀ j ∈ s, Good n v (f j)) :
    Good n v (fun x => ∑ j ∈ s, f j x) := by
  have hfun : ∀ x, ((∑ j ∈ s, f j x : Ev n) : Alt n) = ∑ j ∈ s, (f j x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(_root_.GlobalTheory.ChernCalc.smooth_coeff_closure n v).2.1 J s (fun j x => (f j x : Alt n)) (fun j hj => (h j hj).1), ?_⟩
  rw [(_root_.GlobalTheory.CxForm.dbarAt_local_calculus n v).2.1 J s (fun j x => (f j x : Alt n))
    (fun j hj S => diff_of_smooth (α := fun x => (f j x : Alt n)) (h j hj).1 S)]
  exact Finset.sum_eq_zero fun j hj => (h j hj).2

theorem good_mul (f g : V n → Ev n) (hf : Good n v f) (hg : Good n v g) : Good n v (fun x => f x * g x) := by
  have hfun : ∀ x, ((f x * g x : Ev n) : Alt n) = (f x : Alt n) * (g x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(_root_.GlobalTheory.ChernCalc.smooth_coeff_closure n v).2.2.2 (fun x => (f x : Alt n)) (fun x => (g x : Alt n)) hf.1 hg.1, ?_⟩
  rw [(_root_.GlobalTheory.CxForm.dbarAt_local_calculus n v).2.2.2.2 f (fun x => (g x : Alt n))
    (diff_of_smooth (α := fun x => (f x : Alt n)) hf.1) (diff_of_smooth (α := fun x => (g x : Alt n)) hg.1)]
  rw [hf.2, hg.2]
  simp

variable {r : Type} [Fintype r] [DecidableEq r]

theorem goodM_mul (M N : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j))
    (hN : ∀ i j, Good n v (fun x => N x i j)) (i j : r) : Good n v (fun x => (M x * N x) i j) := by
  have hfun : (fun x => (M x * N x) i j) = fun x => ∑ k ∈ Finset.univ, M x i k * N x k j := by
    funext x
    rw [Matrix.mul_apply]
  rw [hfun]
  exact good_sum Finset.univ (fun k x => M x i k * N x k j) fun k _ => good_mul _ _ (hM i k) (hN k j)

theorem goodM_pow (M : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j)) (k : ℕ) (i j : r) :
    Good n v (fun x => (M x ^ k) i j) := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero]
    exact good_const _
  | succ k ih =>
    simp only [pow_succ]
    exact goodM_mul (fun x => M x ^ k) M (fun a b => ih a b) hM i j

theorem goodM_curv (G : V n → Matrix r r ℂ) (hG : MContDiffAt ∞ G v) (hd : IsUnit (G v).det) (i j : r) :
    Good n v (fun x => curvEv G x i j) := ⟨((_root_.GlobalTheory.CurvSmooth.curvEv_entry_smooth n r G v hG hd) i j).2, _root_.GlobalTheory.ChernCalc.CurvClosed.dbarAt_curvEv n r G v hG hd i j⟩

end GlobalTheory.PowCurv


open GlobalTheory.PowCurv in
theorem GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ (k l : ℕ) (i j : r), (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) S) v) ∧ dbarAt (fun x => ((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) v = 0 := by
  intro n r _ _ G G' v hG hd hG' hd' k l i j
  exact goodM_mul (fun x => curvEv G x ^ k) (fun x => curvEv G' x ^ l)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G hG hd c d) k a b)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G' hG' hd' c d) l a b) i j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerPullbackHolomorphic
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc.HoloPull

noncomputable def subst {n n' : ℕ} (L : V n' →L[ℂ] V n) :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ :=
  aeval fun x : Fin n × Fin n => ∑ c, ∑ d, C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) *
    (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ)

variable {n n' : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n' → V n} {w : V n'}

theorem curvPoly_comp (hφ : ContDiffAt ℂ 2 φ w) (hG : MContDiffAt ∞ G (φ w)) (hu : IsUnit (G (φ w)).det) :
    curvPoly (fun x => G (φ x)) w = (subst (fderiv ℂ φ w)).mapMatrix (curvPoly G (φ w)) := by
  first
  | exact @_root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback
  | exact _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback
  | (apply _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> assumption)
  | (intros; apply _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback ..)

theorem curvEv_eq (G : V n → Matrix r r ℂ) (v : V n) :
    curvEv G v = (aeval sym : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n).mapMatrix (curvPoly G v) := rfl

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix r r R) :
    Matrix.charpolyRev (M.map f) = (Matrix.charpolyRev M).map f := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext1 i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

end GlobalTheory.ChernCalc.HoloPull

namespace GlobalTheory.ChernCalc


open HoloPull in
theorem curv_pow_chern_comp_holo : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → (∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') = pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n)) ∧ ∀ k, (powAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (powAt G (φ w) k) ∧ (chernAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (chernAt G (φ w) k) := by
  intro n n' r _ _ G φ w hφ hG hu
  have key : ∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det →
      ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') =
        pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n) := by
    intro k l i j G' hG' hu'
    simp only [curvEv_eq, curvPoly_comp hφ hG hu, curvPoly_comp hφ hG' hu', ← map_pow, ← map_mul]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply]
    exact (pull_aeval_sym _ _ _ _).symm
  refine ⟨key, fun k => ⟨?_, ?_⟩⟩
  · have := fun i => key k 0 i i G hG hu
    simp only [pow_zero, mul_one] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [powAt, Matrix.trace, Matrix.diag_apply, AddSubmonoidClass.coe_finsetSum, map_sum, this]
  · have e : chernPoly (fun x => G (φ x)) w k = subst (fderiv ℂ φ w) (chernPoly G (φ w) k) := by
      rw [chernPoly, chernPoly, curvPoly_comp hφ hG hu, ← map_neg]
      exact (congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k)
        (charpolyRev_map (subst (fderiv ℂ φ w)).toRingHom _)).trans (Polynomial.coeff_map _ _)
    rw [chernAt, chernAt, e, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, pull_aeval_sym]
    rfl

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullbackStatement
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_dbar_chainRule_holomorphicPullback : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (β : V n → Alt n) (v : V m), IsOpen U → v ∈ U → DifferentiableOn ℂ τ U →
    (∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (β y) S) (τ v)) →
    delAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (delAt β (τ v)) ∧
    dbarAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (dbarAt β (τ v)) := by
  first | exact @GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp | exact GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp | (intros; apply GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatTransLiftsOverAffinePairsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∃ θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G, ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a) := by
  first | exact @GlobalTheory.PDForm.exists_lift_pair_natTrans | exact GlobalTheory.PDForm.exists_lift_pair_natTrans | (intros; apply GlobalTheory.PDForm.exists_lift_pair_natTrans <;> assumption)
end

