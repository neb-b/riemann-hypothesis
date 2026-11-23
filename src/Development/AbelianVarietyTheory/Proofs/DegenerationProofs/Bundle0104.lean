module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTestModelToClosure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteSplitTorusExtensionOfTorusExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SS

theorem exists_finite_torusExtension_of_torusExt : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  intro k _ G _ ⟨T⟩
  have := T.q_hom
  have := T.i_hom
  obtain ⟨-, k', _, _, hfin, X, _, hfree, hX, e, he⟩ := GlobalTheory.torus_isAffineHom_and_splits_finite k T.T₀ T.isTorus
  refine ⟨k', inferInstance, inferInstance, hfin, ?_⟩
  let f : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hq := isPullback_overPullback_map_left f T.q
  have : IsMonHom e.inv := inferInstance
  refine ⟨{ X := X
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.inv ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem GlobalTheory.ZH.exists_geoTest_tMap_and_centre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), Nonempty (Q.TMap t c)) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y := by
  intro hL o Ω _ _ _ hA S ρ M U₀ EE hB Q hbig hgeo
  refine ⟨fun p _ y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨y₀, Fs, hn, hF⟩ := _root_.GlobalTheory.ZH.exists_fac_of_large_test o Ω S ρ M U₀ EE hB Q p y hy
    obtain ⟨t, ht⟩ := hgeo p y₀ hn Fs
    obtain ⟨c⟩ := hF t.u ht
    exact ⟨y₀, t, c, _root_.GlobalTheory.ZH.TestMap.nonempty_tMap hL o Ω S ρ M U₀ EE hB Q p y y₀ t c hbig⟩
  · haveI := hA.ft
    haveI := hA.char
    exact ((GlobalTheory.ZH.classical_points_and_local_regularity o Ω M U₀ hB.ov.normal).1 U₀ le_rfl hB.ov.ne z hz).1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymplecticLevelBaseChangePolarisedAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory

theorem exists_level_baseChange : Laws → ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → P'.g = P.g → ∀ (k : ℕ) (ze : Γ(S, ⊤)ˣ) (ze' : Γ(S', ⊤)ˣ), f.appTop.hom ze.val = ze'.val → IsPrimitiveRoot ze' k → ∀ lev : Out.Level P k ze, ∃ lev' : Out.Level P' k ze', ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev'.pt i').left ≫ φ = f ≫ (lev.pt i).left := by
  intro hL S S' _ _ f P P' φ h hiso hg k ze ze' hz hprim lev
  have e : 2 * P'.g = 2 * P.g := congrArg (2 * ·) hg
  have cast : ∀ {n n' : ℕ} (e : n' = n) {T : Over S} (y : Fin n → (T ⟶ P.A)) (a : Fin n' → ℕ),
      linComb (fun i => y (Fin.cast e i)) a = linComb y (fun i => a (Fin.cast e.symm i)) := by
    intro n n' e T y a
    subst e
    rfl
  choose pt hpt using fun i => ThetaObjPull.exists_sec h (lev.pt (Fin.cast e i))
  have hpt' : ∀ i, (pt i).left ≫ φ = f ≫ (lev.pt (Fin.cast e i)).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have key : ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ S') (c : Fin (2 * P'.g) → ℕ),
      pushHom h (Over.mk x) (linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S') ≫ pt i) c) =
      linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ baseOver S) ≫ lev.pt i)
        (fun i => c (Fin.cast e.symm i)) := fun K _ x c => by
    rw [ThetaObjPull.map_linComb]
    refine Eq.trans ?_ (cast e _ c)
    congr 1
    funext i
    apply Over.OverMorphism.ext
    show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (lev.pt _).left
    rw [Category.assoc, hpt', Category.assoc]
  have := P.isAb.comm
  refine ⟨{ pt := pt
            prim := hprim
            torsion := fun i => ThetaObjPull.pushHom_injective h _ ?_
            indep := fun K _ _ x c c' hc => ?_
            span := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_ }, fun i i' hi => ?_⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (ThetaObjPull.toBase f)) _ _).symm.trans (by rw [lev.torsion, map_one])
  · have q := lev.indep K (x ≫ f) (fun i => c (Fin.cast e.symm i)) (fun i => c' (Fin.cast e.symm i))
      ((key K x _).symm.trans ((congrArg (pushHom h (Over.mk x)) hc).trans (key K x _)))
    funext i
    exact congrFun q (Fin.cast e i)
  · have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc⟩ := lev.span K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨fun i => c (Fin.cast e i), ThetaObjPull.pushHom_injective h _ ((key K x _).trans hc)⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ P.isLB P'.isLB h hiso (baseOver S') k (pt i) (pt j)
      (ThetaObjPull.toBase f ≫ lev.pt _) (ThetaObjPull.toBase f ≫ lev.pt _) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (ThetaObjPull.toBase f)
      (lev.pairing (Fin.cast e i) (Fin.cast e j))
    rw [map_zpow] at w
    have e₁ : Units.map (ThetaObjPull.toBase f).left.appTop.hom.toMonoidHom ze = ze' := Units.ext hz
    have e₂ : stdSymp P.g (Fin.cast e i) (Fin.cast e j) = stdSymp P'.g i j := by
      simp only [stdSymp, Fin.val_cast, hg]
    rw [e₁, e₂] at w
    exact w
  · obtain rfl : i = Fin.cast e i' := Fin.ext hi
    exact hpt' i'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiRing

theorem basis_prod_famφT_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (U : Type) [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k, h (famφT D T 0 k) ^ DegPre.famε 1 k = h (snd T D.P.A).left := by
  have := D.P.isAb.comm
  rw [PsiExists.famφT_eq, PsiExists.cT_zero, _root_.mul_one]
  simp [Fin.prod_univ_four, DegPre.famε]

theorem exists_basis_fibNZ : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ th : SecBT D (𝟙_ _) 1 0, FibNZ (𝟙_ _ ⊗ D.P.A).hom th ∧ ∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b := by
  intro hT R _ _ _ D
  have := D.P.isAb.comm
  let T : Over (Spec (CommRingCat.of R)) := 𝟙_ _
  have e : translPt D.P.A (1 : T ⟶ D.P.A) = snd T D.P.A := by
    show (fst T D.P.A ≫ 1) * snd T D.P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P 1 le_rfl R (𝟙 _) (1 : T ⟶ D.P.A)
  change Fin (1 ^ D.P.g) → LB.Sec (twistLB D.P.A D.P.L 1 (1 : T ⟶ D.P.A)) at b
  change IsSecBasis (T := T) (A := D.P.A) _ b at hb
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have H : FormEq (K := Fin 2) ![(snd T D.P.A).left, (translPt D.P.A (1 : T ⟶ D.P.A)).left] ![((1 : ℕ) : ℤ) - 1, 1]
      (famφT D T 0) (DegPre.famε 1) := fun U _ h => by
    rw [basis_prod_famφT_zero, e]
    simp [Fin.prod_univ_two]
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB H (b i₀)
  have hf : (fst T D.P.A).left = (T ⊗ D.P.A).hom :=
    (Category.comp_id _).symm.trans (Over.w (fst T D.P.A))
  have key : ∀ g : SecBT D T 1 0, ∃ c : R, Mult D th g c := fun g => by
    obtain ⟨s, hs⟩ := exists_sec D.P.isLB (fun U _ h => (H U h).symm) g
    obtain ⟨c, hc, -⟩ := hb s
    have hc' := fun j => (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c i₀), fun Z r z J hJ => ?_⟩
    refine (hs Z r z J hJ).symm.trans (Eq.trans ?_ (congrArg _ (hth Z r z J hJ).symm))
    refine (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans ((gs_pull r (fst T D.P.A).left z ⊤ trivial _).trans ?_)) rfl))
    exact congrArg₂ (fun (q : Z ⟶ Spec (CommRingCat.of R)) (a : Γ(Spec (CommRingCat.of R), ⊤)) => gs q z ⊤ a)
      (congrArg (r ≫ ·) hf) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (c i₀)).symm
  refine ⟨th, fun y => ?_, key⟩
  have hp : IsPullback (snd T D.P.A).left (T ⊗ D.P.A).hom D.P.A.hom (𝟙 _) := by
    rw [← hf]
    exact (IsPullback.of_hasPullback T.hom D.P.A.hom).flip
  obtain ⟨t, ht⟩ := KeyPow.exists_sec_fibre_ne_zero hT D.P hp
  obtain ⟨z, hz, hz'⟩ := ht y
  obtain ⟨g, hg⟩ := exists_sec D.P.isLB (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    (φ' := famφT D T 0) (ε' := DegPre.famε 1) (fun U _ h => by
      rw [basis_prod_famφT_zero]; simp) t
  obtain ⟨c, hc⟩ := key g
  choose J hJ using fun χ : (T ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  refine ⟨z, hz, (MulPullSec.mem_nonzeroLocus_iff th (𝟙 _) z hJ).2 ?_⟩
  have u := (MulPullSec.mem_nonzeroLocus_iff (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    t (𝟙 _) z hJ).1 hz'
  rw [← hg _ _ z J hJ, hc _ _ z J hJ] at u
  exact isUnit_of_mul_isUnit_right u

end GlobalTheory.PsiRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationDataOfSemiAbelianSymmetry
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem exists_setting_of_hypS : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G)) → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∃ s : GlobalTheory.UU.HidaSetting V A G, s.gen = gen := by
  intro laws hext V _ _ hd _ hc A G _ _ hG hE hS gen hgen
  have hV : GlobalTheory.UU.CDVR V := ⟨hd, hc, inferInstance⟩
  obtain ⟨L, hL⟩ := GlobalTheory.UU.polarisation_extends laws V A G hG gen hgen
  obtain ⟨P, rfl⟩ := GlobalTheory.CubicalPackage.exists_package laws V hV A G hG gen hgen L hL
  obtain ⟨w, -, hw, -, -, hiso, -⟩ := _root_.GlobalTheory.SymExtendDvr.hypS_of_generic hext V A G hG hS gen hgen P.L hL
  obtain ⟨E, ⟨d⟩⟩ := hE
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := Functor.isCommMonObj_obj
  obtain ⟨r, hr⟩ := GlobalTheory.UU.thick_zero_factor V
  obtain ⟨Q₀⟩ := GlobalTheory.UU.nonempty_tq_pullback_comp r _ hr G (GlobalTheory.UU.TQ.ofGtDatum d)
  obtain ⟨P₀, h₀⟩ := GlobalTheory.UU.exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P
  obtain ⟨wA, hwA⟩ := hL
  have := E.free
  have := E.finite
  exact ⟨⟨hV, hG, gen, hgen, P, wA, hwA, E.X, Q₀, P₀, h₀,
    _root_.GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre laws V hV A G hG gen hgen P w hw hiso E.X Q₀ P₀ h₀⟩, rfl⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitGeneratingSectionPullbackField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenSecField

open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR

theorem flat_of_injective {R K : Type} [CommRing R] [IsDomain R] [Field K] {φ : R →+* K}
    (hφ : Function.Injective φ) : φ.Flat := by
  have e : φ = (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap hφ x).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  · let _ := (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).toAlgebra
    exact (inferInstance : Module.Flat (FractionRing R) K)

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem exists_pow_one (u : LB.Sec L) : ∃ s : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
    sval s r z J = gs r z _ (u.f (J r)) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (u.f (j 0)), fun j j' => fn_ext fun y hy => ?_⟩,
    fun Z r z J hJ => ?_⟩
  · refine (gs_res (𝟙 X) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2)))
      (gs_res (𝟙 X) y _ hy _))).symm)
    refine (gs_res (𝟙 X) y (le j) hy.1 _).trans ((FlatSec.gs_sec_trans u (𝟙 X) y (le j hy.1) (le j' hy.2)).trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 X) y (le j') hy.2 _).symm))
    simp
  · rw [sval_of _ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact gs_res r z (le fun _ => J r) (Set.mem_iInter.2 fun _ => hJ r) _

theorem cst_zero' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  rw [cst, map_zero, gs_eq q z ⊤ trivial, map_zero, map_zero]

theorem sval_eq_zero {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] {f : X ⟶ Sp R} {π : X' ⟶ X} {f' : X' ⟶ Sp R'}
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull π)} (hw : w.IsGen) {th : H0 L 1} (hth : ∀ s : H0 L 1, ∃ a, SecIsMul f a s th)
    (h₀ : ∀ y J, Good L y J → sval th π y J = 0) (s : H0 L' 1) (y : X') {J'} (hJ' : Good L' y J') :
    sval s (𝟙 X') y J' = 0 := by
  obtain ⟨t, ht⟩ := exists_sec hL' (φ' := fun _ : PUnit => 𝟙 X') (ε' := fun _ => 1)
    (fun U _ h => by simp) s
  obtain ⟨σ, hσ⟩ := ArcPull.exists_up_sec ((isGen_iff w).1 hw) hL hL' (fun _ : PUnit => 𝟙 X') (fun _ => π)
    (fun _ => 1) (𝟙 X') (fun _ => by simp) t
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H L hL σ
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have e := hσ _ (𝟙 X') y J J' hJ hJ'
  rw [ht _ _ y J' hJ', sval_of σ _ y J (fun _ => J π) (fun _ => by rw [Category.id_comp]), Category.id_comp] at e
  have z : ∀ i, gs π y _ ((u i).f (J π)) = 0 := fun i => by
    obtain ⟨v, hv⟩ := exists_pow_one (u i)
    obtain ⟨a, ha⟩ := hth v
    rw [← hv _ π y J hJ, sval_of_secIsMul ha π y hJ, h₀ y J hJ, mul_zero]
  have e' := (hu y (J π) (hJ π)).symm.trans e
  simp only [z, mul_zero, Finset.sum_const_zero] at e'
  exact (Units.mul_right_eq_zero _).1 e'.symm

end GlobalTheory.GenSecField

namespace GlobalTheory


open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.GenSecField in
theorem exists_unit_generating_section_pull : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (th : H0 D.P.L 1) (th' : H0 D'.P.L 1), (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D'.P.L 1, ∃ r : K, ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → ∃ c : Kˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval th (r ≫ PsiEvenPull.proj hD) z J = (TauTwist.unitAt (r ≫ D'.P.A.hom) z c * ArcPull.om hD.w z J J' r).val * sval th' r z J' := by
  intro R K _ _ _ φ hφ D D' hD th th' hth hth'
  have hc : ∀ _ : Fin 1, 𝟙 D'.P.A.left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ 𝟙 D.P.A.left :=
    fun _ => (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L _ D.P.isLB D'.P.isLB hD.w hD.w_gen (Fin 1)
    (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)) (PsiEvenPull.proj hD) hc th
  obtain ⟨c, hac⟩ := hth' a
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      sval th (r ≫ PsiEvenPull.proj hD) z J =
        cst (r ≫ D'.P.A.hom) z c * (ArcPull.om hD.w z J J' r).val * sval th' r z J' := fun Z r z J J' hJ hJ' => by
    have e := FamFieldPull.IsSecPull.val ha hc r z hJ hJ'
    rw [sval_of_secIsMul (p := D'.P.A.hom) hac r z hJ', Fin.prod_univ_one, Category.comp_id, zpow_natCast,
      pow_one] at e
    exact e.trans ((mul_left_comm _ _ _).trans (_root_.mul_assoc _ _ _).symm)
  by_cases h : c = 0
  · subst h
    have : IsProper D.P.A.hom := D.P.isAb.proper
    have : CompactSpace D.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.P.A.hom
    have : QuasiSeparatedSpace D.P.A.left := quasiSeparatedSpace_of_quasiSeparated D.P.A.hom
    have h₀ : SecIsMul D'.P.A.hom (0 : K) th' th' := secIsMul_of_sval D'.P.isLB fun y J' hJ' => by
      rw [cst_zero', zero_mul]
      refine sval_eq_zero (flat_of_injective hφ) (pull_grp hD).1 D.P.isLB D'.P.isLB hD.w_gen hth
        (fun x J hJ => ?_) th' y hJ'
      obtain ⟨I, hI⟩ := DegPull.exists_good' D'.P.isLB x
      have e := key _ (𝟙 _) x J I hJ hI
      rwa [Category.id_comp, cst_zero', zero_mul, zero_mul] at e
    refine ⟨1, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', sval_of_secIsMul h₀ r z hJ', cst_zero', zero_mul, zero_mul, zero_mul, mul_zero]
  · refine ⟨Units.mk0 c h, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', Units.val_mul, TauTwist.unitAt_val]
    rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormVanishesOfTorsionTorusExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TorsionVanish

theorem form_vanishes_of_torsion : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ v, Crd (Φ.H 1) F x.left v ∧ MvPolynomial.eval v Pf = 0) → ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, MvPolynomial.eval v Pf = 0) := by
  intro L1 L2 k _ _ Φ g N N' q J _ cls F π hBig hGood hg hN' d Pf hd hPf hx v hv
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · obtain ⟨v0, -, hv0⟩ := hx 1 (one_pow _)
    have hC : Pf = MvPolynomial.C (Pf.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hPf.totalDegree_le)
    rw [hC] at hv0 ⊢
    simpa using hv0
  obtain ⟨φ, -, hsupp, hval⟩ := GlobalTheory.ZH.FormSec.exists_formSec k Φ J F d Pf hPf
  obtain ⟨hpart, hfin, -, hsum⟩ := GlobalTheory.ZH.WtPart.weight_parts k Φ d
  obtain ⟨-, -, hsep⟩ := GlobalTheory.exists_basis_unique_min_and_sums_separated Φ.E.X q hGood.pos _ g N N'
    (N ^ g * g.factorial) rfl (by omega) hBig.lll hBig.sep
  have hdist : ∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + N' • w) → α = β := by
    rintro α hα β hβ ⟨w, hw⟩
    obtain ⟨a, ha, rfl⟩ := hsupp α hα
    obtain ⟨b, hb, rfl⟩ := hsupp β hβ
    have h0 : w = 0 := hsep d a b hd
      (fun j => by obtain ⟨i, hi⟩ := ha j; exact (hGood.supp i _ hi).1)
      (fun j => by obtain ⟨i, hi⟩ := hb j; exact (hGood.supp i _ hi).1) w hw
    rw [hw, h0, smul_zero, add_zero]
  have htor : ∀ x : Φ.Pt, x ^ N' = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ := fun x hx1 => by
    obtain ⟨v0, hc, h0⟩ := hx x hx1
    exact (hval x v0 hc).1 h0
  choose ψ hψ using hpart φ
  have hψ0 : ∀ α l, (ψ α).f l = 0 := fun α =>
    GlobalTheory.PureZero.pure_eq_zero_of_vanishing_on_torsion L1 L2 k Φ g N N' d π hBig hN' (by omega) hd1 hd α (ψ α) (hψ α).1
      (_root_.GlobalTheory.TorsionFourier.part_vanishes_on_torsion k Φ d N' hN' φ hdist htor α (ψ α) (hψ α))
  have hφ0 : ∀ l, φ.f l = 0 := fun l => by
    rw [hsum φ (hfin φ).toFinset ψ (by simp) (fun α _ => hψ α) l]
    exact Finset.sum_eq_zero fun α _ => hψ0 α l
  obtain ⟨x, hxp, hc⟩ := hv
  refine (hval (Over.homMk x hxp) v hc).2 fun h => ?_
  have hb : Out.nonzeroLocus φ = ⊥ := by
    simp [Out.nonzeroLocus, hφ0]
  rw [hb] at h
  obtain ⟨p⟩ : Nonempty (Sp k) := (inferInstance : Nonempty (PrimeSpectrum k))
  exact h (Set.mem_univ p)

end GlobalTheory.ZH.TorsionVanish
end

