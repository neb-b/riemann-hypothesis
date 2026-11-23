module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechLBExactAtOfDimLt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbLaw

theorem cechLB_exactAt_of_dim_lt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (Y : Scheme.{0}) [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of K)) (g : ℕ) (M : LB Y), SmoothOfRelativeDimension g f → IsProjBy f → IsSeparated f → M.IsLB → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, g < n → (cechLB f M D).ExactAt n := by
  intro K _ _ Y _ f g M hf hp hs hM κ _ _ D hD hc n hn
  obtain ⟨E, hE, hEc⟩ := GlobalTheory.AffineCover.exists_cover_of_isProjBy K Y f g hf hp
  obtain ⟨e⟩ := _root_.GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers K Y f M κ D (Fin (g + 1)) E hM hs hD hc hE hEc n
  have hz : IsZero ((cechLB f M E).X n) := isZero_cechLB_X f M E (by simpa using hn)
  have hE0 : IsZero ((cechLB f M E).homology n) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((cechLB f M E).homology n) := ModuleCat.isZero_iff_subsingleton.1 hE0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDim
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem dim_eq_rank_add_dim :
    LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => A.g = D.toPre.rank + D.toPre.P.g := by
  rintro ⟨hL, hL₂, -, -, -⟩ R _ _ _ I hadm D A G _ _ hG U
  haveI := hG.geomConnected
  have h₁ := GlobalTheory.finrank_fam_of_expBij hL.secBaseChange R I hadm D A G U.toUnifPre 2 (by norm_num)
    (U.expand 2 (by norm_num))
  have h₂ := (GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) 2
    (by norm_num)).2
  exact Nat.pow_right_injective (le_refl 2) (h₁.symm.trans h₂)

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCoverNonzeroLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CubeFree

section General
variable {X Y : Scheme.{0}} {L : LB X}

theorem gs_g_single (φ : Y ⟶ X) (n : ℤ) (j j' : Fin 1 → L.ι) (y : Y)
    (h : y ∈ LB.wchart L (fun _ : Fin 1 => φ) j) (h' : y ∈ LB.wchart L (fun _ : Fin 1 => φ) j') :
    (trF (L := L) (fun _ : Fin 1 => φ) (fun _ => n) (𝟙 Y) y j j').val =
      gs (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) ((pw L n).g (j 0) (j' 0)).val := by
  have hm : (𝟙 Y ≫ φ) y ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.1 h' 0⟩
  refine Eq.trans ?_ (gs_unit _ y _ hm _).symm
  rw [trF, Fin.prod_univ_one]
  exact congrArg Units.val (map_zpow _ _ n).symm

theorem unitAt_of_pw {n : ℤ} (s : LB.Sec (pw L n)) (φ : Y ⟶ X) (y : Y) (i : L.ι)
    (h : φ y ∈ X.basicOpen (s.f i)) : UnitAt L (K := Fin 1) (fun _ => φ) (fun _ => n) y := by
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L _ j 0
  have v : ∀ (j : Fin 1 → L.ι) (z : Y), z ∈ LB.wchart L (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z _ ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) =
        gs (𝟙 Y ≫ φ) z (L.U (j 0)) (s.f (j 0)) := fun j z hj =>
    (gs_res _ z _ hj _).trans (gs_pull _ φ z _ (l j hj) _)
  let s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => n)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        have hm : (𝟙 Y ≫ φ) z ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨l j hz.1, l j' hz.2⟩
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            ((congrArg Units.val (gm_linComb L _ _ (𝟙 Y) z j j' hz.1 hz.2)).trans
              (gs_g_single φ n j j' z hz.1 hz.2))) ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        exact (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg _ (gs_res _ z _ hm _)))) }
  refine ⟨s', fun J hJ => isUnit_sval s' (𝟙 Y) y hJ (fun _ => i) ?_⟩
  have hi : y ∈ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => i) :=
    Set.mem_iInter.2 fun _ => X.basicOpen_le _ h
  change y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (l fun _ => i)).op).hom ((φ.app _).hom (s.f i)))
  rw [Scheme.basicOpen_res]
  exact ⟨hi, (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f i)) y).1 h⟩

theorem exists_sec_of_unitAt (hL : L.IsLB) {n : ℤ} {x : X}
    (h : UnitAt L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => n) x) :
    ∃ t : LB.Sec (pw L n), x ∈ nonzeroLocus t := by
  obtain ⟨s, hs⟩ := h
  have l : ∀ i : L.ι, L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  let t : LB.Sec (pw L n) :=
    { f := fun i => (X.presheaf.map (homOfLE (l i)).op).hom (s.f fun _ => i)
      compat := fun i i' => fn_ext fun z hz => by
        refine ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (l i) hz.1 _)).trans (Eq.trans ?_
          ((gs_mul (𝟙 X) z _ hz _ _).trans (congrArg _
            ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (l i') hz.2 _)))).symm)
        refine (sec_trans s (𝟙 X) z (l i hz.1) (l i' hz.2)).trans ?_
        rw [gs_g_single (𝟙 X) n _ _ z (l i hz.1) (l i' hz.2), Category.id_comp]
        rfl }
  obtain ⟨i, hi⟩ := exists_chart hL x
  refine ⟨t, TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩⟩
  obtain ⟨J, hJ, e⟩ := sval_trans hL s x (fun _ => i) (l i hi)
  have u : IsUnit (gs (𝟙 X) x (L.U i) (t.f i)) :=
    (congrArg IsUnit ((gs_res _ x (l i) hi _).trans e)).mpr ((Units.isUnit _).mul (hs J hJ))
  exact (X.mem_basicOpen _ x hi).2 ((congrArg IsUnit (gs_eq (𝟙 X) x _ hi _)).mp u)

theorem unitAt_of_triv (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {ε : I → ℤ}
    (h : Triv (LB.LinComb L φ ε)) {Y' : Scheme.{0}} (e : Y' ⟶ Y) (k : ℕ) (y : Y') :
    UnitAt L (fun i => e ≫ φ i) (fun i => k * ε i) y := by
  obtain ⟨t, ht⟩ := h
  refine UnitAt.congr hL ?_ ⟨powSec (I := Fin k) fun _ => pullSec (genSec t ht) e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_smul, natCast_zsmul]
  · rw [sval_powSec _ _ _ hJ]
    refine IsUnit.prod_univ_iff.2 fun _ => ?_
    rw [sval_pullSec _ _ _ _ hJ, sval_genSec _ _ _ _ hJ]
    exact Units.isUnit _

end General

theorem exists_cover_nonzeroLocus : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (k : ℕ) (s : LB.Sec (pw L.L k)), (∃ j, s.f j ≠ 0) → ∃ (n : ℕ) (t : Fin (n + 1) → LB.Sec (pw L.L (2 * k : ℕ))), ⨆ i, nonzeroLocus (t i) = ⊤ := by
  intro K _ _ B _ _ hB L c k s ⟨j, hj⟩
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  let T : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  have : IsIntegral (T ⊗ B).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 _) _ _ (IsPullback.of_hasPullback (𝟙 _) B.hom).flip
  have : IsIntegral B.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)
  let q : B ⟶ T := Over.homMk B.hom (Category.comp_id _)
  let e : B ⟶ T ⊗ B := lift q (𝟙 B)
  have he : e ≫ snd T B = 𝟙 B := lift_snd _ _
  have hD : ((((snd T B).left ⁻¹ᵁ B.left.basicOpen (s.f j)) : (T ⊗ B).left.Opens) : Set (T ⊗ B).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((B.left.basicOpen (s.f j) : B.left.Opens) : Set B.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨e.left d, ?_⟩
    show (snd T B).left (e.left d) ∈ B.left.basicOpen (s.f j)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, he]
    exact hd
  have key : ∀ (x : T ⟶ B) (p : T.left), ∃ t : LB.Sec (pw L.L (2 * k : ℕ)), x.left p ∈ nonzeroLocus t := by
    intro x p
    have hq : x ≫ q = 𝟙 T := Over.OverMorphism.ext (Over.w x)
    have good : ∀ a : T ⟶ B, (ptSecT B (a * x)).left p ∈ (snd T B).left ⁻¹ᵁ B.left.basicOpen (s.f j) →
        UnitAt L.L (K := Fin 1) (fun _ => e.left ≫ (translPt B a).left) (fun _ => (k : ℤ)) (x.left p) := by
      intro a ha
      refine unitAt_of_pw s _ _ j ?_
      have E : x ≫ e ≫ translPt B a = ptSecT B (a * x) ≫ snd T B := by
        simp [e, ptSecT, NoBasePoint.translPt_eq, MonObj.comp_mul, reassoc_of% hq]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, E]
      exact ha
    obtain ⟨a, h₁, h₂⟩ := NoBasePoint.exists_two_points (𝟙 _) _ hD x x
    have sq := unitAt_of_triv L.isLB (Square.triv_square c a a⁻¹) e.left k (x.left p)
    have e1 : translPt B (1 : T ⟶ B) = snd _ _ := by
      rw [NoBasePoint.translPt_eq, MonObj.comp_one, _root_.one_mul]
    have e2 : e.left ≫ (snd T B).left = 𝟙 _ := by rw [← Over.comp_left, he]; rfl
    refine exists_sec_of_unitAt L.isLB (UnitAt.congr L.isLB (formEq_of_add fun U _ hh => ?_)
      (((good a (h₁ p)).mul (good a⁻¹ (h₂ p))).mul sq))
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, Fin.sum_univ_four,
      Matrix.cons_val, _root_.mul_inv_cancel]
    rw [e1, e2]
    push_cast
    module
  have top : ⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t = ⊤ := by
    have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
    by_contra h
    have hne : ((⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h' => h (SetLike.coe_injective h')
    obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints hne
      (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed
    obtain ⟨t, ht⟩ := key (Over.homMk (pointOfClosedPoint B.hom z hc) (pointOfClosedPoint_comp B.hom z hc))
      (IsLocalRing.closedPoint K)
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨t,
      (congrArg (· ∈ nonzeroLocus t) (pointOfClosedPoint_apply B.hom z hc _)).mp ht⟩)
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun t : LB.Sec (pw L.L (2 * k : ℕ)) => (nonzeroLocus t : Set B.left)) (fun t => (nonzeroLocus t).isOpen)
    (fun z _ => by
      have : z ∈ (⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t) := by rw [top]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 this))
  refine ⟨F.card, Fin.cons (secZero _) (fun i => (F.equivFin.symm i).1), top_unique fun z _ => ?_⟩
  obtain ⟨t, ht, hz⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ z))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨t, ht⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hz

end GlobalTheory.CubeFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatSec

theorem exists_equiv_of_isPushout {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A A' : CommRingCat.{0}}
    [Algebra R A] (p : A ⟶ A') (s' : R' →+* A')
    (H : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R')) p
      (CommRingCat.ofHom s')) :
    ∃ e : R' ⊗[R] A ≃+ A', ∀ c v, e (c ⊗ₜ v) = s' c * p.hom v := by
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra R' A' := s'.toAlgebra
  let _ : Algebra R A' := (s'.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout R R' A A' := (CommRingCat.isPushout_iff_isPushout.mp H).symm
  exact ⟨h.out.equiv.toAddEquiv, fun c v => (h.out.equiv_tmul c v).trans (Algebra.smul_def _ _)⟩

theorem exists_comb_ker {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {I J : Type} [Fintype I] [Fintype J] {A : I → Type} {B : J → Type} {A' : I → Type} {B' : J → Type}
    [∀ a, AddCommGroup (A a)] [∀ a, Module R (A a)] [∀ b, AddCommGroup (B b)] [∀ b, Module R (B b)]
    [∀ a, AddCommGroup (A' a)] [∀ b, AddCommGroup (B' b)]
    (e : ∀ a, R' ⊗[R] A a ≃+ A' a) (e' : ∀ b, R' ⊗[R] B b ≃+ B' b) (d : (∀ a, A a) →ₗ[R] (∀ b, B b))
    (x : ∀ a, A' a)
    (hx : ∀ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), (∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a)) →
      ∀ b, ∑ i, e' b (c i ⊗ₜ d (v i) b) = 0) :
    ∃ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), (∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a)) ∧ ∀ i, d (v i) = 0 := by
  classical
  obtain ⟨t, ht⟩ := (TensorProduct.piRight R R R' A).surjective (fun a => (e a).symm (x a))
  have key : ∀ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), t = ∑ i, c i ⊗ₜ v i →
      ∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a) := fun n c v h a => by
    have := congrFun ht a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum, Finset.sum_apply, AddEquiv.eq_symm_apply, map_sum] at this
    rw [← this]
    rfl
  have h0 : d.lTensor R' t = 0 := by
    obtain ⟨n, c, v, h⟩ := TensorProduct.exists_sum_tmul_eq t
    apply (TensorProduct.piRight R R R' B).injective
    funext b
    apply (e' b).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, Pi.zero_apply, map_zero, ← hx n c v (key n c v h) b, h, map_sum, map_sum, Finset.sum_apply, map_sum]
    rfl
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map d) t).1 h0
  obtain ⟨n, c, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq w
  refine ⟨n, c, fun i => (v i).1, key n c _ ?_, fun i => (v i).2⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hw, map_sum]
  rfl

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Z : Scheme.{0}}

theorem isPushout_app {g : R →+* R'} (hg : g.Flat) {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {U : X.Opens} (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) :
    IsPushout (CommRingCat.ofHom (cst f U)) (CommRingCat.ofHom g) (π.app U)
      (CommRingCat.ofHom (cst f' (π ⁻¹ᵁ U))) := by
  have : Flat (Spec.map (CommRingCat.ofHom g)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact hg
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU hU')
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl

theorem gs_sum (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by simp only [gs_eq r z U h, map_sum]

theorem gs_cst (f : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst f U c) = gs r z ⊤ (cst f ⊤ c) := by
  rw [← rs_cst f (le_top : U ≤ ⊤) c]
  exact gs_res r z _ h _

theorem gs_comb (f' : X' ⟶ Spec (CommRingCat.of R')) (π : X' ⟶ X) (U : X.Opens) (z : X') (h : π z ∈ U) {n : ℕ}
    (c : Fin n → R') (v : Fin n → Γ(X, U)) :
    gs (𝟙 X') z (π ⁻¹ᵁ U) (∑ i, cst f' (π ⁻¹ᵁ U) (c i) * (π.app U).hom (v i)) =
      ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z U (v i) := by
  rw [gs_sum (𝟙 X') z (π ⁻¹ᵁ U) h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul (𝟙 X') z (π ⁻¹ᵁ U) h, gs_cst f' (𝟙 X') z (π ⁻¹ᵁ U) h, gs_pull (𝟙 X') π z U h, Category.id_comp]

theorem gs_pull_trans {M : LB X} {π : X' ⟶ X} (σ : LB.Sec (M.pull π)) (z : X') {k l : M.ι} (hk : π z ∈ M.U k)
    (hl : π z ∈ M.U l) : gs (𝟙 X') z _ (σ.f (fun _ => k)) =
      (gm π z (M.U k ⊓ M.U l) (M.g k l)).val * gs (𝟙 X') z _ (σ.f (fun _ => l)) := by
  refine (sec_trans σ (𝟙 X') z (j := fun _ => k) (j' := fun _ => l) (Set.mem_iInter.2 fun _ => hk)
    (Set.mem_iInter.2 fun _ => hl)).trans ?_
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
  rfl

theorem gs_sec_trans {M : LB X} (s : LB.Sec M) (r : Z ⟶ X) (z : Z) {k l : M.ι} (hk : r z ∈ M.U k)
    (hl : r z ∈ M.U l) : gs r z _ (s.f k) = (gm r z (M.U k ⊓ M.U l) (M.g k l)).val * gs r z _ (s.f l) := by
  have hm : r z ∈ M.U k ⊓ M.U l := ⟨hk, hl⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat k l)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem gs_diff {M : LB X} {V W : X.Opens} {k l : M.ι} (hV : V ≤ M.U k) (hW : W ≤ M.U l) (a : Γ(X, V)) (b : Γ(X, W))
    (r : Z ⟶ X) (z : Z) (h : r z ∈ V ⊓ W) :
    gs r z (V ⊓ W) (rs X inf_le_left a - rs X (inf_le_inf hV hW) (M.g k l).val * rs X inf_le_right b) =
      gs r z V a - (gm r z (M.U k ⊓ M.U l) (M.g k l)).val * gs r z W b := by
  rw [LBGerm.gs_sub r z _ h, gs_mul r z _ h, gs_res r z _ h, gs_res r z _ h, gs_res r z _ h,
    gs_unit r z (M.U k ⊓ M.U l) ⟨hV h.1, hW h.2⟩]

theorem exists_comb_of_flat : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R'), g.Flat → ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (CommRingCat.of R)) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → ∀ M : LB X, M.IsLB → ∀ σ : LB.Sec (M.pull π), ∃ (n : ℕ) (c : Fin n → R') (u : Fin n → LB.Sec M), ∀ (z : X') (k : M.ι), π z ∈ M.U k → gs (𝟙 X') z _ (σ.f (fun _ => k)) = ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ ((u i).f k) := by
  intro R R' _ _ g hg X _ _ f X' π f' H M hM σ
  obtain ⟨α, _, W, j, hA, hW, hc⟩ := exists_finite_affine_refinement hM
  let _ : Algebra R R' := g.toAlgebra
  have : Module.Flat R R' := hg
  let _ : ∀ U : X.Opens, Algebra R Γ(X, U) := fun U => (cst f U).toAlgebra
  choose e he using fun a => exists_equiv_of_isPushout (R := R) (π.app (W a)) (cst f' (π ⁻¹ᵁ W a))
    (isPushout_app hg H (hA a).isCompact (hA a).isQuasiSeparated)
  choose e' he' using fun p : α × α => exists_equiv_of_isPushout (R := R) (π.app (W p.1 ⊓ W p.2))
    (cst f' (π ⁻¹ᵁ (W p.1 ⊓ W p.2))) (isPushout_app hg H
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hA p.1).isCompact (W p.2).isOpen (hA p.2).isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _))
  let d : (∀ a, Γ(X, W a)) →ₗ[R] (∀ p : α × α, Γ(X, W p.1 ⊓ W p.2)) :=
    { toFun := fun v p => rs X inf_le_left (v p.1) -
        rs X (inf_le_inf (hW p.1) (hW p.2)) (M.g (j p.1) (j p.2)).val * rs X inf_le_right (v p.2)
      map_add' := fun v w => funext fun p => by
        simp only [Pi.add_apply, map_add (f := _)]; ring
      map_smul' := fun r v => funext fun p => by
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, rs_cst,
          RingHom.id_apply]; ring }
  have hx : ∀ {n : ℕ} {c : Fin n → R'} {v : Fin n → ∀ a, Γ(X, W a)},
      (∀ a, rs X' (le_pull M π (hW a)) (σ.f fun _ => j a) = ∑ i, e a (c i ⊗ₜ v i a)) →
      ∀ a z, π z ∈ W a → gs (𝟙 X') z _ (σ.f fun _ => j a) =
        ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ (v i a) := fun {n c v} h a z hz => by
    have h' := congrArg (gs (𝟙 X') z (π ⁻¹ᵁ W a)) (h a)
    simp only [he] at h'
    rw [gs_comb f' π _ z hz] at h'
    exact (gs_res (𝟙 X') z _ hz _).symm.trans h'
  obtain ⟨n, c, v, hv, hd⟩ := exists_comb_ker e e' d (fun a => rs X' (le_pull M π (hW a)) (σ.f fun _ => j a))
    (fun n c v h p => fn_ext fun z hz => by
      simp only [he']
      rw [gs_comb f' π _ z hz, LBGerm.gs_zero (𝟙 X') z _ hz]
      have h₁ := gs_pull_trans σ z (hW _ hz.1) (hW _ hz.2)
      rw [hx h p.1 z hz.1, hx h p.2 z hz.2, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
      refine (congrArg _ (gs_diff (hW p.1) (hW p.2) (v i p.1) (v i p.2) π z hz)).trans ?_
      ring)
  choose u hu using fun i => exists_sec_of_refinement hM W j hW hc (v i) fun y a b ha hb => by
    have h := congrArg (gs (𝟙 X) y (W a ⊓ W b)) (congrFun (hd i) (a, b))
    exact sub_eq_zero.1 ((gs_diff (hW a) (hW b) (v i a) (v i b) (𝟙 X) y ⟨ha, hb⟩).symm.trans
      (h.trans (LBGerm.gs_zero (𝟙 X) y _ ⟨ha, hb⟩)))
  have hu' : ∀ i a, rs X (hW a) ((u i).f (j a)) = v i a := fun i a => fn_ext fun y hy => by
    rw [gs_res (𝟙 X) y _ hy, hu i y (j a) a (hW a hy) hy, gm_self hM (𝟙 X) y (hW a hy), Units.val_one,
      _root_.one_mul]
  refine ⟨n, c, u, fun z k hk => ?_⟩
  obtain ⟨a, ha⟩ := hc (π z)
  rw [gs_pull_trans σ z hk (hW a ha), hx hv a z ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_sec_trans (u i) π z hk (hW a ha), ← hu' i a, gs_res π z _ ha]
  ring

end GlobalTheory.FlatSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.EvenTriv

theorem exists_even_cubTriv_specialFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (P : CP G) (w : G ⟶ G), IsMonHom w → LBIso P.L.L (cubeLB G ![𝟙 G, w] P.L.L) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q₀ : TQ (thickObj V (maximalIdeal V) 0 G) X) (P₀ : CP (thickObj V (maximalIdeal V) 0 G)), IsLevelCP (maximalIdeal V) 0 P₀ P → ∃ σ : CubTriv P₀.c Q₀.i, σ.Even := by
  intro _ V _ _ _ _ A G _ _ hG gen _ P w _ hw X _ _ _ Q₀ P₀ ⟨v, hv⟩
  have hp : IsProper (pullback.snd G.hom (jK V)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK V) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hm : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (V ⧸ maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  have hS := IsSemiAbelian.pullback (thick V (maximalIdeal V) 0) G hG
  have := hS.smooth
  have := hS.geomConnected
  have := Q₀.i_hom
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (V ⧸ maximalIdeal V ^ (0 + 1)) X (thickObj V (maximalIdeal V) 0 G) P₀.L P₀.c Q₀.i
    Q₀.i_hom
  exact exists_even_of_surjective (surjective_cube_of_generic G hG hp) P w hw P₀
    (IsPullback.of_hasPullback G.hom (thick V (maximalIdeal V) 0)) hv Q₀.i s

end GlobalTheory.EvenTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericFibreCardTorsionCubicalPairingPerfectStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.generic_fibre_card_torsion_cubical_pairing_perfect : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → Nat.card {x : TF (R := V) F ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧ ∀ x : TF (R := V) F ⟶ G, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ G, y ^ N = 1 → CubWeil s.P.c N x y 1) → x = 1 := by
  first | exact @GlobalTheory.UU.generic_card_and_nondeg | exact GlobalTheory.UU.generic_card_and_nondeg | (intros; apply GlobalTheory.UU.generic_card_and_nondeg <;> assumption)
end

