module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FinKer

theorem finite_of_isClosed_of_finite_closedPoints {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {S : Set T} (hS : IsClosed S) (h : (S ∩ closedPoints T).Finite) :
    S.Finite := by
  have hc : IsClosed (S ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (S ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← JacobsonSpace.closure_inter_closedPoints hS, hc.closure_eq]
  exact h

theorem locallyQuasiFinite_of_finite_closedFibres {Y X : Scheme.{0}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {f y}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  refine subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_
  have : Finite (f.fiber (f y)) := (f.fiberHomeo (f y)).finite_iff.mpr (h y hy)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem exists_lift_of_isClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] {X Y : Scheme.{0}} (g : X ⟶ Y)
    [LocallyOfFiniteType g] (u : Sp Ω ⟶ Y) (z : X) (hz : IsClosed ({z} : Set X))
    (h : u (IsLocalRing.closedPoint Ω) = g z) :
    ∃ w : Sp Ω ⟶ X, w ≫ g = u ∧ w (IsLocalRing.closedPoint Ω) = z := by
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := u) (g := g) _ z h
  have : JacobsonSpace ↥(pullback u g) := LocallyOfFiniteType.jacobsonSpace (pullback.fst u g)
  have hcl : IsClosed (closure ({p} : Set ↥(pullback u g))) := isClosed_closure
  have hne : (closure ({p} : Set ↥(pullback u g)) ∩ closedPoints _).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have := JacobsonSpace.closure_inter_closedPoints hcl
    rw [hc, closure_empty] at this
    exact (this.symm ▸ subset_closure (Set.mem_singleton p) : p ∈ (∅ : Set _))
  obtain ⟨q, hqp, hq₀⟩ := hne
  have hq : IsClosed ({q} : Set ↥(pullback u g)) := mem_closedPoints_iff.mp hq₀
  refine ⟨pointOfClosedPoint (pullback.fst u g) q hq ≫ pullback.snd u g, ?_, ?_⟩
  · rw [Category.assoc, ← pullback.condition, pointOfClosedPoint_comp_assoc]
  · change (pullback.snd u g) (pointOfClosedPoint (pullback.fst u g) q hq _) = z
    erw [pointOfClosedPoint_apply]
    have hs : p ⤳ q := specializes_iff_mem_closure.mpr hqp
    have := (hs.map (pullback.snd u g).continuous).mem_closed hz (by rw [hp2]; rfl)
    exact this

end GlobalTheory.AV.FinKer

namespace GlobalTheory.AV.AbVar


open GlobalTheory.AV.FinKer in
theorem isFinite_iff_finite_ker : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    IsFinite f.hom.left ↔ Finite (ptMap f).ker := by
  intro K _ A B f
  have : IsProper A.X.hom := A.ab.proper
  have : IsProper B.X.hom := B.ab.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : LocallyOfFiniteType (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp _ B.X.hom
  let pt : Sp (AlgebraicClosure K) := IsLocalRing.closedPoint (AlgebraicClosure K)
  constructor
  · intro hf
    let u : Sp (AlgebraicClosure K) ⟶ B.X.left := (1 : B.Pt).left
    have : IsFinite (pullback.fst u f.hom.left) := inferInstance
    have hfin := ((pullback.fst u f.hom.left).finite_preimage_singleton pt).to_subtype
    have hmem : ∀ x : (ptMap f).ker, 𝟙 _ ≫ u = x.1.left ≫ f.hom.left := fun x ↦ by
      rw [Category.id_comp, ← Over.comp_left]
      exact congrArg CommaMorphism.left (MonoidHom.mem_ker.mp x.2).symm
    refine Finite.of_injective (β := (pullback.fst u f.hom.left) ⁻¹' {pt})
      (fun x ↦ ⟨pullback.lift (𝟙 _) x.1.left (hmem x) pt, Subsingleton.elim _ _⟩) fun x y hxy ↦ ?_
    have e := ext_of_apply_closedPoint_eq (pullback.fst u f.hom.left) (pullback.lift_fst _ _ _)
      (pullback.lift_fst _ _ _) (congrArg Subtype.val hxy)
    have e2 := congrArg (· ≫ pullback.snd u f.hom.left) e
    simp only [pullback.lift_snd] at e2
    exact Subtype.ext (Over.OverMorphism.ext e2)
  · intro hker
    have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    have : IsProper f.hom.left := IsProper.of_comp _ B.X.hom
    have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
    have : LocallyQuasiFinite f.hom.left := by
      refine locallyQuasiFinite_of_finite_closedFibres f.hom.left fun y hy ↦ ?_
      obtain ⟨a, ha, hay⟩ := exists_lift_of_isClosed A.X.hom (spMap (algebraMap K (AlgebraicClosure K)))
        y hy (Subsingleton.elim _ _)
      let x : A.Pt := Over.homMk a ha
      have hcl : IsClosed (f.hom.left ⁻¹' {f.hom.left y}) := by
        have := f.hom.left.isClosedMap _ hy
        rw [Set.image_singleton] at this
        exact this.preimage f.hom.left.continuous
      refine finite_of_isClosed_of_finite_closedPoints hcl ?_
      refine (Set.finite_range (fun k : (ptMap f).ker ↦ (x * k.1).left pt)).subset ?_
      rintro z ⟨hzS, hz⟩
      have hzS' : f.hom.left z = f.hom.left y := hzS
      obtain ⟨w, hw1, hw2⟩ := exists_lift_of_isClosed f.hom.left (a ≫ f.hom.left) z hz
        (by change f.hom.left (a pt) = _; rw [hay, hzS'])
      let w' : A.Pt := Over.homMk w (by
        change w ≫ A.X.hom = _
        rw [← hw, ← Category.assoc, hw1, Category.assoc, hw]; exact ha)
      have hk : x⁻¹ * w' ∈ (ptMap f).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
        exact Over.OverMorphism.ext hw1.symm
      refine ⟨⟨_, hk⟩, ?_⟩
      change (x * (x⁻¹ * w')).left pt = z
      rw [mul_inv_cancel_left]
      exact hw2
    exact IsFinite.of_isProper_of_locallyQuasiFinite _

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinement
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
open GlobalTheory.GoodMetric.RepBundle

namespace GlobalTheory.ChernCalc

theorem isMetricFr_pullGram : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → IsMetricFr E' (pullGram E H φ f hf) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH
  have key := _root_.GlobalTheory.ChernCalc.pullGram_eq_of_frame F σ X Y ι m E E' φ f hf hR H hH
  refine ⟨fun y B hB τ => ?_, fun y B hB τ i j => ?_, fun y B hB B' hB' τ => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) y
    obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have hT := ((hR.sub _ B hB A hA).map_of (ratVal · y) ψ hψ).det_ne τ
    rw [(key y).2 A hA B hB τ]
    exact (hH.posDef _ mem_ptsIn_top A ((key y).1 ▸ hA) τ).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hT.isUnit))
  · obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have hA' : A ∈ E.S (under (ptMap σ f hf y)) := (key y).1 ▸ hA
    have hC := hR.sub _ B hB A hA
    have hc : Continuous (ptMap σ f hf) := GlobalTheory.Points.PtsOver.continuous_map f hf _
    have hev : ∀ᶠ z in 𝓝 y, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ *
        H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
      filter_upwards [hc.continuousAt.eventually (_root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m 0 E _ A hA'),
        _root_.GlobalTheory.ChernCalc.frame_eventually_near F σ Y ι m m E' y B hB] with z hAz hBz
      exact (key z).2 A ((key z).1 ▸ hAz) B hBz τ
    have hT : ∀ k l, CS (fun z => (B * (A.map φ)⁻¹).map (ratVal · z) τ k l) y := fun k l =>
      cs_ratVal (mem_O_ratOf.1 ((hC τ).1 k l))
    have hS : ∀ k l, CS (fun z => H A (ptMap σ f hf z) τ k l) y := fun k l =>
      ⟨CInfAt.pull f hf (hH.smooth _ mem_ptsIn_top A hA' τ k l).1,
        CInfAt.pull f hf (hH.smooth _ mem_ptsIn_top A hA' τ k l).2⟩
    exact CS.congr (v := fun z => pullGram E H φ f hf B z τ i j) (cs_conj_entry hT hS i j)
      (hev.mono fun z hz => by simp only [hz])
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) y
    obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have e := Par.map_mul_of ((Fr.mem_iff hB).1 hB') (hR.sub _ B hB A hA) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    rw [(key y).2 A hA B hB τ, (key y).2 A hA B' hB' τ, e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfIsGrpPullbackFst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isMonHom_of_isGrpPullback_fst {S S' : Scheme.{0}} {s : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (bc : G' ≅ (Over.pullback s).obj G) (h : IsGrpPullback G' G s (bc.hom.left ≫ pullback.fst G.hom s)) :
    IsMonHom bc.hom := by
  obtain ⟨e, me, he⟩ := grpPullback_iso h (isGrpPullback_pullback G s)
  have : e.hom = bc.hom := Over.OverMorphism.ext (pullback.hom_ext he ((Over.w e.hom).trans (Over.w bc.hom).symm))
  exact this ▸ me

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefRationalFibreOfNefFiniteFieldFibres
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem GlobalTheory.GenNef.isNef_ratFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, NefFib L → (letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))); GlobalTheory.IsNef ℚ (L.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))))) := by
  intro k _ X _ p D hX L hL
  haveI := hX.finite
  letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
  refine ⟨LB.isLB_pull L.isLB _, fun Z hZ => ?_⟩
  obtain ⟨W, w, z, _, hW, hzw, hpb⟩ := _root_.GlobalTheory.CurveClosure.exists_closure_arith_surface_rat k X p D hX Z hZ
  have e := _root_.GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed k X p Z hZ W w z hW hzw hpb L.B L.isLB
  have h0 := NefGeneric.ratDeg_nonneg k W (w ≫ p) (L.pull w rfl) hW
    (ArInt.nefFib_pull k X W p (w ≫ p) hX.isProjOver hW.isProjOver w rfl L hL)
  change 0 ≤ ratDeg (w ≫ p) (L.B.pull w) at h0
  rw [e] at h0
  exact h0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegular
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem isOpen_setOf_mem_frames {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] [Finite ι] {m k : ι → ℕ}
    {M : GlobalTheory.ZH.RatModel F Ω} (S : Fr M m k) (B : Mat m Ω) : IsOpen {z : M.Z | B ∈ S.S z} := by
  have hP (g : Mat m Ω) : IsOpen {z : M.Z | Par k (M.O z).toSubring g} := by
    have : {z : M.Z | Par k (M.O z).toSubring g} = ⋂ τ, ((⋂ i, ⋂ j, {z : M.Z | g τ i j ∈ M.O z}) ∩
        ({_z : M.Z | (g τ).det ≠ 0} ∩ ({z : M.Z | (g τ).det⁻¹ ∈ M.O z} ∩
          {_z : M.Z | ∀ i j : Fin (m τ), (i : ℕ) < k τ → i < j → g τ i j = 0}))) := by
      ext z
      simp only [Par, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      rfl
    rw [this]
    exact isOpen_iInter_of_finite fun τ => (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      M.isOpen_setOf_mem_O _).inter (isOpen_const.inter ((M.isOpen_setOf_mem_O _).inter isOpen_const))
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨U, A, hzU, -, hU⟩ := S.loc z
  exact ⟨(U : Set M.Z) ∩ {z' | Par k (M.O z').toSubring (B * A⁻¹)}, fun w hw => (hU w hw.1 B).2 hw.2,
    U.isOpen.inter (hP _), hzU, (hU z hzU B).1 hz⟩

theorem isOpen_inCell_and_regAt : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f →
    ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), IsOpen {y : Y.X | InCell E E' φ f A u y} ∧
      ∀ y, InCell E E' φ f A u y → ∀ j, RegAt y (u j) := by
  intro F _ X Y ι _ m E E' φ f hR A u
  refine ⟨((isOpen_setOf_mem_frames E A).preimage f.continuous).inter (isOpen_setOf_mem_frames E' _), ?_⟩
  rintro y ⟨hA, hu⟩ ⟨τ, ⟨b, a⟩, hab⟩
  have h := hR.sub y _ hu A hA
  have hd : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
    have := Mat.det_map A (φ : X.Fn →+* Y.Fn) τ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA τ))
  rw [mul_assoc, Mat.mul_inv hd, mul_one] at h
  have h2 := (h τ).1 a b
  have hab' : a < b := hab
  have e : upM u τ a b = u ⟨τ, ⟨(b, a), hab⟩⟩ := by
    simp only [upM, upU, Matrix.of_apply, dif_pos hab']
  rw [e] at h2
  exact mem_O_ratOf.1 h2

end GlobalTheory.FlagCell2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwist
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem gm_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (f ≫ g) z U a = Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U a) := by
  apply Units.ext
  rw [gm_val (f ≫ g) z U h, Units.coe_map, gm_val g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h ((g.app U).hom a.val)).symm

theorem val_comp_stalkMap {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ W) (r : W ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val t (f ≫ r) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val t r (f z) (fun ψ => J (f ≫ ψ))) := by
  rw [val_of t (f ≫ r) z J (fun k => J (f ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_stalkMap f r z _ (Set.mem_iInter.2 fun k => hJ (f ≫ r ≫ φ k)) _

theorem good_comp {X Z W : Scheme.{0}} {L : LB X} (f : Z ⟶ W) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (f z) (fun ψ => J (f ≫ ψ)) := fun ψ => hJ (f ≫ ψ)

end GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem txFrame_frTw (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) : GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p₀ (frTw D τ h w) := by
  rintro ⟨hg, h2, hN⟩
  set f : (TF (R := R) (Kb R)).left ⟶ (TF (R := R) (Kb R)).left := spMap τ.toRingHom with hf
  have hfr : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (frTw D τ h w) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val w (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [frTw, val_genCast, val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap w f (𝟙 _) z J hJ
  have hsy : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (p₀.g.s p₀.y) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val (p.g.s p.y) (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [h.1, val_corr hJ (h.2.2 p.y), val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap _ f (𝟙 _) z J hJ
  refine ⟨genCast_isGen _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen D.P.L _ _ w hg _), ?_, ?_⟩
  · intro ν hν z J hJ
    rw [hfr z J hJ, hsy z J hJ, h.2.1, val_comp_stalkMap ν f _ z J hJ, ← map_pow, ← map_mul,
      h2 ν hν (f z) _ (good_comp f hJ)]
  · intro κ hκ z J hJ
    have hpsi : val (D.psi p₀.y) (jFK (R := R) (Kb R)) z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (val (D.psi p.y) (jFK (R := R) (Kb R)) (f z) (fun ψ => J (f ≫ ψ))) := by
      have e := val_comp_stalkMap (D.psi p.y) f (jFK (R := R) (Kb R)) z J hJ
      rw [h.1]
      refine Eq.trans ?_ e
      exact congrArg (fun r => val (D.psi p.y) r z J) (spMap_jFK τ).symm
    have hrig : GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom (f z) (fun ψ => J (f ≫ ψ))) := by
      unfold GlobalTheory.UT.rigV
      rw [← val_comp_stalkMap _ f _ z J hJ]
      exact congrArg (fun r => val D.rig r z J) (spMap_jFKR τ).symm
    rw [id_eq, hfr z J hJ, hpsi, hrig, h.2.1, val_comp_stalkMap κ f _ z J hJ, ← map_pow,
      ← map_mul, ← map_mul]
    exact congrArg _ (hN κ hκ (f z) _ (good_comp f hJ))

end GlobalTheory.Mum.Conj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarie
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ArithTrdeg

theorem trdeg_functionField_eq {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (h : IsArithVar p D) :
    Algebra.trdeg ℤ X.functionField = D := by
  have hft := DimCoheight.finiteType_of_isAmb (MixHt.isAmb_of_isArithVar h)
  have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat

  have key : ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
      ringKrullDim Γ(X, U) =
        ((Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) : WithBot ℕ∞) := by
    intro U hU hne
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    have : CharZero Γ(X, U) :=
      ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hc0
    have hinj : Function.Injective (algebraMap ℤ Γ(X, U)) := RingHom.injective_int _
    have : FaithfulSMul ℤ Γ(X, U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one _ hinj,
      ← DimCoheight.trdeg_eq_of_isFractionRing ℤ Γ(X, U) X.functionField]
  have hdim : ((Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) : WithBot ℕ∞) =
      ((D + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← h.dim_eq]
    apply le_antisymm
    · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
      have hU : IsAffineOpen U := hU
      rw [← key U hU ⟨⟨_, hxU⟩⟩, ← Published.dim_affineOpen hU]
      exact topologicalKrullDim_subspace_le X (U : Set X)
    · refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      have hU : IsAffineOpen U := hU
      refine ⟨(U : Set X), U.isOpen, hyU, ?_⟩
      rw [Published.dim_affineOpen hU, key U hU ⟨⟨y, hyU⟩⟩]
  have h2 : Cardinal.toENat (Algebra.trdeg ℤ X.functionField) = D := by
    have h3 : (Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) = ((D : ℕ∞) + 1) := by
      exact_mod_cast hdim
    exact (WithTop.add_right_cancel (ENat.one_ne_top) h3)
  exact Cardinal.toENat_eq_natCast.1 h2

theorem isTranscendenceBasis_functionField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    (∃ x : Fin D → X.functionField, IsTranscendenceBasis ℤ x) ∧
      ∀ x : Fin D → X.functionField, AlgebraicIndependent ℤ x → IsTranscendenceBasis ℤ x := by
  intro k _ X _ p D h
  have htr := trdeg_functionField_eq h
  refine ⟨?_, fun x hx => hx.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr]; simp)⟩
  have : FaithfulSMul ℤ X.functionField := by
    have : CharZero X.functionField := by
      have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat
      exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 hc0
    exact (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective_int _)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ X.functionField
  have hcard := hs.cardinalMk_eq_trdeg
  rw [htr] at hcard
  have : Finite s := Cardinal.lt_aleph0_iff_finite.1 (by rw [hcard]; exact Cardinal.natCast_lt_aleph0)
  have : Fintype s := Fintype.ofFinite s
  have e : s ≃ Fin D := Fintype.equivFinOfCardEq (by
    rw [Cardinal.mk_fintype] at hcard; exact_mod_cast hcard)
  exact ⟨_, hs.comp_equiv e.symm⟩

end GlobalTheory.ArithTrdeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerOneFormEqZeroOfUniformisedValues
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem form_eq_zero_of_evForm_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (ξ : Ω[Sec (str A) U.1⁄ℂ]), (∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ = 0) → ξ = 0 := by
  intro A _ g L u hA U ξ hξ
  obtain ⟨d, ω, -, -, -, hsum, hev⟩ := _root_.GlobalTheory.CechPer.kaehler_frame A g L u hA U
  have hz : ∀ a, (d a).liftKaehlerDifferential ξ = 0 := by
    intro a
    apply _root_.GlobalTheory.ValInj.eq_zero_of_val_eq_zero A g L u hA U.1
    intro z hz
    rw [← hev a ξ z hz, hξ z hz]
    rfl
  rw [hsum ξ]
  simp [hz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsInducedAllEmbeddingsOfGaloisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labels_induced_all_embeddings_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∀ (hD : IsPullDeg φ D.toPre D'.toPre) (j : ℕ), (∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧  ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x') → Induces lab φ U' hD a (n ^ j) := by
  first | exact @GlobalTheory.Mum.AllEmb.induces_of_one_embedding | exact GlobalTheory.Mum.AllEmb.induces_of_one_embedding | (intros; apply GlobalTheory.Mum.AllEmb.induces_of_one_embedding <;> assumption)
end

