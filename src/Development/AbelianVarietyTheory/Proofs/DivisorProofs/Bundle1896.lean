module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullPres

theorem fnOf_app {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} (h : genericPoint X ∈ q ⁻¹ᵁ U) (a : Γ(W, U)) :
    fnOf (q ⁻¹ᵁ U) h ((q.app U).hom a) =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) h) a) := by
  rw [← algebraMap_germ h, ← algebraMap_germ (show q (genericPoint X) ∈ U from h),
    functionFieldMap_algebraMap, Scheme.Hom.germ_stalkMap_apply]

theorem fnOf_res_pullU {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} {V : X.Opens} (le : V ≤ q ⁻¹ᵁ U) (hV : genericPoint X ∈ V) (u : Γ(W, U)ˣ) :
    fnOf V hV (res le (pullU q U u)).val =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) (le hV)) u.val) :=
  (fnOf_resG le hV _).trans (fnOf_app q (le hV) _)

theorem presents_pull {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W)
    (hDE : ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) :
    Presents D ((toLB E).pull q) fun J => Units.map (functionFieldMap q).toMonoidHom (J PUnit.unit).1.2 := by
  refine ⟨pull_isLB (isLB_toLB E) q, fun J K h => ?_, fun J x hx => hDE _ _ ((J PUnit.unit).2.2 _ (mem_pull.1 hx)) x rfl⟩
  have le : ((toLB E).pull q).U J ⊓ ((toLB E).pull q).U K ≤
      q ⁻¹ᵁ ((toLB E).U (J PUnit.unit) ⊓ (toLB E).U (K PUnit.unit)) :=
    fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  have hg : ((toLB E).pull q).g J K = res le (pullU q _ ((toLB E).g (J PUnit.unit) (K PUnit.unit))) := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    rfl
  rw [hg, fnOf_res_pullU, fnOf_toLB_g]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_div₀]
  exact (div_mul_cancel₀ _ ((map_ne_zero _).2 (Units.ne_zero _))).symm

theorem pull_cls_toLB : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W),
    (∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    CechPic.pull q (cls (toLB E) (isLB_toLB E)) = cls (toLB D) (isLB_toLB D) := by
  intro X W _ _ q _ D E hDE
  rw [← cls_pull (isLB_toLB E) q (pull_isLB (isLB_toLB E) q), ← (presents_pull q D E hDE).toPic_eq,
    toPic_apply]

end GlobalTheory.Cartier.PullPres
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLE
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem chartPull_g_appLE : ∀ (Y Y' : Scheme.{0}) (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) (cp : ChartPull A' A h) (i j : A'.ι), ((A'.g i j : Γ(Y', A'.U i ⊓ A'.U j)ˣ) : Γ(Y', A'.U i ⊓ A'.U j)) = (h.appLE (A.U (cp.idx i) ⊓ A.U (cp.idx j)) (A'.U i ⊓ A'.U j) (le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j)))).hom ((A.g (cp.idx i) (cp.idx j) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))ˣ) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))) := by
  intro Y Y' A' A h cp i j
  have e : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (cp.idx i) ⊓ A.U (cp.idx j)) :=
    le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j))
  apply TopCat.Presheaf.section_ext Y'.sheaf (A'.U i ⊓ A'.U j)
  intro y hy
  have h1 := congrArg Units.val (cp.g y i j hy.1 hy.2)
  rw [gm_val _ y _ hy, gm_val h y _ (e hy)] at h1
  refine h1.trans ?_
  show _ = (Y'.presheaf.germ _ y hy).hom ((Y'.presheaf.map (homOfLE e).op).hom ((h.app _).hom _))
  exact (TopCat.Presheaf.germ_res_apply Y'.presheaf _ y hy _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm

namespace GlobalTheory.FlatModel

theorem exists_affine_normal_domain {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (V : X.Opens) {z : X}
    (hz : z ∈ V) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : IsDomain Γ(X, U)),
      z ∈ U ∧ U ≤ V ∧ IsIntegrallyClosed Γ(X, U) := by
  have hC : IsOpen (irreducibleComponent z) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨U, hU, hzU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z)
    (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩
  have hpre : IsPreirreducible (U : Set X) := (isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2
    fun q hq => (hle hq).2
  have hirr : IsIrreducible (U : Set X) := ⟨⟨z, hzU⟩, hpre⟩
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom ⟨z, hzU⟩⟩
  have : IsIntegral (Spec Γ(X, U)) := isIntegral_of_isOpenImmersion hU.isoSpec.inv
  have hd : IsDomain Γ(X, U) := (affine_isIntegral_iff _).1 this
  exact ⟨U, hU, hd, hzU, fun q hq => (hle hq).1,
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩

end GlobalTheory.FlatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTuple
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceFlatLevel

open GlobalTheory.TraceLevelPf

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem traceLevel_flat (R : RealDat D A Ks) (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)) (hB : B.Good) (hBo : BaseOf R i B)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c))
    (hU : ∀ g, e g ∈ B.G.P.H ↔ g ∈ U)
    (hchi : ∀ (u : U) (hu : e u ∈ B.G.P.H), ((B.G.P.chi ⟨e u, hu⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ u : D.what₂.LLˣ) : D.what₂.LL))
    (τ : Twist D Circle) (hτ : τ.Good) (hQ : B.admitted τ.Q) (ω : PairRep (Vc D i) (Wc D i)) (hω : B.IsWeil τ.chi ω)
    (hh : GA D (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    levelTrace R i U ψ (series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P) = series B.F ω (B.vecFlat τ) hh P := by
  classical
  have hW : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) _ _ ω := hω
  have hlift := fun g => exists_lift_datWp hB hBo e hent g
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  have hQ' : (GlobalTheory.FlatVecSum.princ B).admitted τ.Q := hQ
  have hfθ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
      (Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) hQ' _) hB.frame.vac.2.theta
  have hsum : B.vecFlat τ = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) •
      ω (1, (hlift (e.symm p)).choose) ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) :=
    GlobalTheory.FlatVecSum.vecFlat_eq_sum_princ hB (D.sp.V_sig _) hτ hQ hω (fun p => (hlift (e.symm p)).choose) (fun p => by
      have := lifts_of_datWp hBo e hent (hlift (e.symm p)).choose_spec
      rwa [MulEquiv.apply_symm_apply] at this)
  funext x
  have hL : levelTrace R i U ψ (series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P) x =
      ∑ g, (if hg : g ∈ U then D.what₂.embLL (((ψ ⟨g, hg⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0) *
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P (x * (hlift g).choose) := by
    unfold levelTrace gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    show Lev.actG0 _ _ _ _ _ x = _
    rw [Lev.actG0]
    split_ifs with hk
    · rw [GlobalTheory.CuspMult.EqCut.levChi_flag rfl rfl, inv_one]
      exact one_mul _
    · exact absurd (hlift g) hk
  have hR : series B.F ω (B.vecFlat τ) hh P x = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) *
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P (x * (hlift (e.symm p)).choose) := by
    rw [hsum, GlobalTheory.SpecFac.series_sum hB ω _ _ _ (fun p _ => hW.om_pres _ _ hfθ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [series_om_fin hB hW hfθ hh P x (hlift (e.symm p)).choose_spec.1]
  rw [hL, hR]
  symm
  refine Fintype.sum_of_injective (fun p : B.G.P.H => e.symm p) (fun p q hpq => Subtype.ext (e.symm.injective hpq)) _ _
    (fun g hg => ?_) (fun p => ?_)
  · rw [dite_eq_right, zero_mul]
    intro hgU
    exact hg ⟨⟨e g, (hU g).2 hgU⟩, e.symm_apply_apply g⟩
  · have hp : e.symm p ∈ U := (hU _).1 (by rw [MulEquiv.apply_symm_apply]; exact p.2)
    have key : ((B.G.P.chi p : ℂˣ) : ℂ) = D.what₂.embLL ((ψ ⟨e.symm p, hp⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have hp' : e (e.symm p) ∈ B.G.P.H := by rw [MulEquiv.apply_symm_apply]; exact p.2
      have := hchi ⟨e.symm p, hp⟩ hp'
      have hpe : (⟨e (e.symm p), hp'⟩ : B.G.P.H) = p := Subtype.ext (e.apply_symm_apply p)
      rw [hpe] at this
      exact this
    rw [dite_eq_left hp, Units.val_inv_eq_inv_val, key, Units.val_inv_eq_inv_val, map_inv₀]

end GlobalTheory.TraceFlatLevel

namespace GlobalTheory.BigOn.Exp.TupLe

end GlobalTheory.BigOn.Exp.TupLe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCubeAbelianPointThetaFaceEqPartialSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def pt3 (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) : Sp ℂ ⟶ (G3 D.P.A).left :=
  (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left

def wI (x y z : Fin g → ℂ) (I : thK) : Fin g → ℂ := ∑ a ∈ I.down, ![x, y, z] a

abbrev cubW (D : DegPre R) (j : thK → D.P.L.ι) : (G3 D.P.A).left.Opens :=
  LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j

theorem psum_eA (ν : NumOf D ℂ N) (d : AB N.toNumB g) {n : ℕ} (w : Fin n → Fin g → ℂ) (I : Finset (Fin n)) :
    psum D.P.A (fun k => ν.eA (d.ex (w k))) I = ν.eA (d.ex (∑ i ∈ I, w i)) := by
  have e0 : ν.eA (d.ex 0) = 1 := by
    have h := d.ex_add 0 0
    rw [add_zero] at h
    have h1 : d.ex 0 = 1 := left_eq_mul.mp h
    rw [h1, map_one]
  have hl : ∀ l : List (Fin n),
      l.foldr (fun k acc => padd D.P.A (ν.eA (d.ex (w k))) acc) (pzero D.P.A _) = ν.eA (d.ex (l.map w).sum) := by
    intro l
    induction l with
    | nil =>
      rw [List.foldr_nil, List.map_nil, List.sum_nil, e0, CategoryTheory.Hom.one_def]
      rfl
    | cons k l ih =>
      rw [List.foldr_cons, ih, List.map_cons, List.sum_cons, d.ex_add, map_mul, padd, CategoryTheory.Hom.mul_def]
  have hI : ((List.finRange n).filter (· ∈ I)).toFinset = I := by
    ext i
    simp
  unfold psum
  rw [hl, ← List.sum_toFinset w ((List.nodup_finRange n).filter _), hI]

theorem complexCubeAbelianPoint_thetaFace_eq_partialSum (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK) :
    pt3 ν d x y z ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (wI x y z I))).left := by
  have e := psum_hom (preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))))) (x3 D.P.A) I.down
  have e' : psum D.P.A (fun i => preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))) (x3 D.P.A i))
      I.down = psum D.P.A (fun k => ν.eA (d.ex (![x, y, z] k))) I.down :=
    congrArg (fun q => psum D.P.A q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])
  rw [e', psum_eA] at e
  rw [pt3, thφ, ← Over.comp_left]
  exact congrArg (fun q => q.left) e

end GlobalTheory.MBLow.Cl.CubHol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open IsLocalRing

namespace GlobalTheory.NsmulPull

variable {R : Type} [CommRing R] [IsDomain R]

theorem one_left (D : DegPre R) : (1 : D.P.A ⟶ D.P.A).left = D.P.A.hom ≫ eSec D.P.A := by
  have e : (toUnit D.P.A).left = D.P.A.hom := by simpa using Over.w (toUnit D.P.A)
  show (toUnit D.P.A ≫ η[D.P.A]).left = _
  rw [Over.comp_left, e]
  rfl

theorem unit_left (D : DegPre R) : (toUnit D.P.A ≫ η[D.P.A]).left = D.P.A.hom ≫ eSec D.P.A := one_left D

theorem comp_padd (D : DegPre R) (a x : D.P.A ⟶ D.P.A) :
    a ≫ padd D.P.A (𝟙 D.P.A) x = padd D.P.A a (a ≫ x) := by
  simp only [padd, ← Category.assoc, comp_lift, Category.comp_id]

theorem gen_shape (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k' k : ℕ) (hk : k ≤ k') (χ' χ : D.X)
    (κ : LB.Gen (kapLB D a k' k)) (hκ : κ.IsGen)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 D.P.A) χ') (D.Oφ a χ)) (Sum.elim Oε Oinvε))) (hu : u.IsGen) :
    ∃ eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB χ') (fun i => a.left ≫ D.famφB χ i))
        (Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i))), eB.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
        val eB r z J = val κ r z J * rigV D (r ≫ D.P.A.hom) z J ^ ((k' : ℤ) - k) * val u r z J := by
  have hL := D.P.isLB
  let ρ := LB.pullGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ D.rig_gen _
  let t := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ (GeneratorPullback.powGen D.P.L _ _ ρ (k' - k))) u
  have ht : t.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hκ (powGen_isGen _ _ _ _ hρ _)) hu
  have e₁ := comp_padd D a (toUnit D.P.A ≫ D.c χ)
  have e₂ : a ≫ toUnit D.P.A = toUnit D.P.A := toUnit_unique _ _
  have e₃ : a.left ≫ D.P.A.hom = D.P.A.hom := Over.w a
  obtain ⟨eB, he, hv⟩ := exists_gen hL (φ' := Sum.elim (D.famφB χ') (fun i => a.left ≫ D.famφB χ i))
    (ε' := Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, Finset.univ_unique,
        Finset.prod_singleton, DegPre.famφB, DegPre.famε, DegPre.Oφ, Oε, Oinvε, kapLB, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Category.comp_id, ← Over.comp_left, e₁, ← Category.assoc, e₂, one_left, unit_left, Over.id_left, Nat.cast_sub hk, e₃, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, mul_one, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) t ht
  refine ⟨eB, he, fun Z r z J hJ => ?_⟩
  rw [hv Z r z J hJ, val_mul hJ, val_mul hJ, val_pow, val_pull hJ, show ((k' : ℤ) - k) = ((k' - k : ℕ) : ℤ) by omega, zpow_natCast]
  rfl

end GlobalTheory.NsmulPull

namespace GlobalTheory.NsmulPull

end GlobalTheory.NsmulPull

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportWeilDatumCmExtension
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.WeilContF

theorem continuous_transportF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsContOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr
  have hfin := _root_.GlobalTheory.WeilContF.exists_local_finite_parts_F F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hpt := _root_.GlobalTheory.WeilContF.continuous_transportF_apply F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hbd := _root_.GlobalTheory.WeilContF.slice_bounds F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hpres := (GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr).1
  refine GlobalTheory.WeilCont.isContOn_of_local F hfin (fun Φ hΦ y => ?_)
  choose s hs using fun p => GlobalTheory.WeilCont.exists_slice F (hpres p Φ hΦ) y
  refine ⟨s, continuous_iff_continuousAt.2 fun p0 => GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded s p0 (fun v => ?_) (fun k n => ?_), hs⟩
  · simp_rw [hs]
    exact (hpt Φ hΦ _).continuousAt
  · obtain ⟨C, hC⟩ := hbd Φ hΦ y p0 k n
    refine ⟨C, hC.mono fun p hp v => ?_⟩
    have e : (⇑(s p)) = fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y) := funext (hs p)
    rw [e]
    exact hp v

end GlobalTheory.WeilContF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartz
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical

namespace GlobalTheory.WeilCont

theorem continuous_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om → GlobalTheory.WeilM.IsContOn (GlobalTheory.WeilM.adeleClass D.host.F) om := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om htr
  have hfin := _root_.GlobalTheory.WeilCont.exists_local_finite_parts D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hpt := _root_.GlobalTheory.WeilCont.continuous_transport_apply D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hbd := _root_.GlobalTheory.WeilCont.slice_bounds D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hpres := (GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr).1
  refine GlobalTheory.WeilCont.isContOn_of_local D.host.F hfin (fun Φ hΦ y => ?_)
  choose s hs using fun p => GlobalTheory.WeilCont.exists_slice D.host.F (hpres p Φ hΦ) y
  refine ⟨s, continuous_iff_continuousAt.2 fun p0 => _root_.GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded s p0 (fun v => ?_) (fun k n => ?_), hs⟩
  · simp_rw [hs]
    exact (hpt Φ hΦ _).continuousAt
  · obtain ⟨C, hC⟩ := hbd Φ hΦ y p0 k n
    refine ⟨C, hC.mono fun p hp v => ?_⟩
    have e : (⇑(s p)) = fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y) := funext (hs p)
    rw [e]
    exact hp v

end GlobalTheory.WeilCont
end

