module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionTranslationActsOnExpansions
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.UniformizationBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

variable {S : Scheme.{0}}

def powPolOf (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) : PolAV S :=
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI : IsCommMonObj A' := PowGrp.comm_of_isPowGrp p P.isAb.comm
  { A := A'
    isAb := (PowGrp.powers S A' P.A j p).2.2.2.1 P.isAb
    g := j * P.g
    smoothDim := (PowGrp.powers S A' P.A j p).2.2.1 P.g P.smoothDim
    L := boxLB P.L p.pr
    isLB := LB.isLB_linComb P.isLB _ _
    rigid := (rigidified_sym_boxLB S A' P.A j p P.L P.isLB).1 P.rigid
    sym := (rigidified_sym_boxLB S A' P.A j p P.L P.isLB).2 P.sym
    ample := _root_.GlobalTheory.relAmple_boxLB S A' P.A j p P.L P.isLB P.ample
    ktriv := _root_.GlobalTheory.kTriv_boxLB S A' P.A j p P.L P.isLB P.ktriv }

def isPowPolAV_powPolOf (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) :
    IsPowPolAV (powPolOf P A' p) P j where
  toIsPowGrp := p
  w := CubePf.idIsoL (boxLB P.L p.pr)
  w_gen := CubePf.idIsoL_isGen (LB.isLB_linComb P.isLB _ _)

def powPol (P : PolAV S) (j : ℕ) : PolAV S :=
  powPolOf P (powObj P.A j) (powIsPowGrp P.A j)

def isPowPolAV_powPol (P : PolAV S) (j : ℕ) : IsPowPolAV (powPol P j) P j :=
  isPowPolAV_powPolOf P (powObj P.A j) (powIsPowGrp P.A j)

theorem exists_powPolAV : ∀ (S : Scheme.{0}) (P : PolAV S) (j : ℕ),
    ∃ (P' : PolAV S) (_ : IsPowPolAV P' P j), P'.g = j * P.g :=
  fun _ P j => ⟨powPol P j, isPowPolAV_powPol P j, rfl⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbeddingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qkToAkU_iff_galois_equivariant : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (F' : Type) [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (p' : QkPt D.toPre F' k) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R) F' ⟶ A.A), QkExt σ.toRingHom p p' → x'.left = spMap σ.toRingHom ≫ x.left → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F' k p' x') := by
  first | exact @GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt | exact GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt | (intros; apply GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem relAmple_of_veryAmpleBy {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
    {L : LB A.left} (hL : L.IsLB) {N : ℕ} (hN : 1 ≤ N) {M : ℕ} (s : Fin (M + 1) → LB.Sec (pw L N))
    (hA : VeryAmpleBy A.hom (pw L N) s) : RelAmple A L := by
  intro U hU
  obtain ⟨hcov, hs⟩ := hA
  let ψ := (A.hom ⁻¹ᵁ U).ι
  have H : IsPullback ψ (A.hom ∣_ U) A.hom U.ι := (isPullback_morphismRestrict A.hom U).flip
  have : IsAffine U := hU
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := isLB_pw hL N
  have hP' := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have h₀ : LBIso (LB.LinComb L (K := Fin N) (fun _ => 𝟙 A.left) (fun _ => 1)) (pw L N) :=
    LBIso.chartPull (chartPullId _) (chartPullPw L N)
      ⟨_, idIso_isGen (linComb_isLB L hL (K := Fin N) (fun _ => 𝟙 A.left) (fun _ => 1))⟩
  obtain ⟨W, hW⟩ := LBIso.chartPull
    (chartPullSame L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 𝟙 A.left) (fun _ => 1) ψ
      fun _ => (Category.comp_id _).symm) (chartPullPull (pw L N) ψ ψ rfl) h₀
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A L U N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1
        ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (pw L N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A L U N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((U.ι.appLE ⊤ ⊤ le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      have e : ((A.hom ∣_ U).appLE ⊤ (nonzeroLocus (M := powOver A L U N) (s' i)) le_top).hom.comp
          ((U.ι.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) =
          (ψ.appLE _ _ (loc i).le).hom.comp (cst A.hom (nonzeroLocus (s i))) := by
        ext x
        exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) po.w.symm
      exact (congrArg (fun q => MvPolynomial.eval₂Hom q _ p) e).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

theorem relAmple_iff_veryAmpleBy : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), L.IsLB → (RelAmple B L ↔ ∃ d : ℕ, 1 ≤ d ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (pw L d)), VeryAmpleBy B.hom (pw L d) s) := by
  intro R _ B L hL
  refine ⟨fun h => ?_, fun ⟨d, hd, n, s, hs⟩ => relAmple_of_veryAmpleBy hL hd s hs⟩
  obtain ⟨d, hd, n, s, -, hs⟩ := veryAmpleBy_of_relAmple hL h (𝟙 _) (Category.id_comp _) hL
    (LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _) (𝟙 _) rfl) ⟨_, idIso_isGen hL⟩)
  exact ⟨d, hd, n, s, hs⟩

end GlobalTheory.Unif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveAppTopOfInjective
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.CubicalPackage

theorem surjective_appTop_of_injective {X S P S' : Scheme.{0}} {p : X ⟶ S} {q : P ⟶ S'} {d : P ⟶ X} {f : S' ⟶ S}
    (w : d ≫ p = q ≫ f) {e : S ⟶ X} {e' : S' ⟶ P} (he' : e' ≫ q = 𝟙 _) (hee : e' ≫ d = f ≫ e)
    (hd : Function.Injective d.appTop.hom) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective p.appTop.hom := by
  intro a
  obtain ⟨b, hb⟩ := hq (d.appTop.hom a)
  have c : ∀ {A B C : Scheme.{0}} (g : A ⟶ B) (h : B ⟶ C) (x : Γ(C, ⊤)),
      g.appTop.hom (h.appTop.hom x) = (g ≫ h).appTop.hom x := fun g h x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  refine ⟨e.appTop.hom a, hd ?_⟩
  rw [c, w, ← c, c f e, ← hee, ← c, ← hb, c e' q, he', Scheme.Hom.id_appTop]
  rfl

variable {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {A : Over (Spec (CommRingCat.of K))} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem surjective_cube_of_generic [Flat G.hom] (gp : IsGrpPullback A G (etaK V K) F)
    (h : Function.Surjective (G3 A).hom.appTop.hom) : Function.Surjective (G3 G).hom.appTop.hom := by
  have hp := gp.1
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd (G3 G).hom (etaK V K))
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
  have hx : ∀ i, (x i).left ≫ F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
  let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
  have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have hl : l.left ≫ (cubeMapOf gp).F3 = pullback.fst (G3 G).hom (etaK V K) := hom_ext_triple _ fun i => by
    rw [Category.assoc, f3, ← Category.assoc, ← Over.comp_left, lx, hx]
  have inj : Function.Injective (l.left ≫ (cubeMapOf gp).F3).appTop.hom := by
    rw [hl]
    exact Exist.CubicalExtension.app_injective_generic (IsPullback.of_hasPullback _ _) ⊤
  refine surjective_appTop_of_injective (d := (cubeMapOf gp).F3) (f := etaK V K)
    (Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2)))))
    (e := eSec (G3 G)) (e' := eSec (G3 A)) (Over.w η[G3 A]) ?_ ?_ h
  · rw [CubeExtension.eSec_three, CubeExtension.eSec_three]
    refine hom_ext_triple _ fun i => ?_
    have a : ∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B],
        (lift (1 : 𝟙_ (Over S) ⟶ B) (lift (1 : 𝟙_ (Over S) ⟶ B) (1 : 𝟙_ (Over S) ⟶ B))).left ≫ (x3 B i).left =
          eSec B := fun B _ _ => by
      rw [← Over.comp_left, eSec]
      fin_cases i <;> simp [x3, Hom.one_def]
    rw [Category.assoc, f3, ← Category.assoc, a, Category.assoc, a]
    exact (cubeMapOf gp).e_comm
  · rw [Scheme.Hom.comp_appTop] at inj
    exact Function.Injective.of_comp (f := l.left.appTop.hom) inj

theorem exists_package : Laws → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G), LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → ∃ P : CP G, P.L = L) := by
  intro laws V _ _ _ hV A G _ _ hG eA hA L h₁
  have := hV.1
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := A.isAb.comm
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK V) (eA.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  have hi : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨w, hw⟩ : LBIso A.L (L.L.pull (eA.inv.left ≫ pullback.fst G.hom (jK V))) :=
    LBIso.chartPull (chartPullSec A.L _ eA.inv.left hi) (chartPullSame L.L _ _ _ eA.inv.left fun _ => rfl) h₁
  obtain ⟨c⟩ := (laws.cube _ A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  obtain ⟨c'⟩ := PolExtension.nonempty_cubical laws.cubicalExtends gp L c w hw
  obtain ⟨s, hs, hs'⟩ := PolExtension.exists_symmetry gp L.isLB A.isLB A.sym w hw
  exact ⟨CP.ofSurjective (surjective_cube_of_generic gp (surjective_cube laws.globalFns A.isAb)) L c' s hs hs', rfl⟩

end GlobalTheory.CubicalPackage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (gs_eq r z _ (hJ.mem φ r) _).trans ?_
  exact (congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), AdmBase R I → ∀ (s : U.SecK k) (F : Fam D.toPre (FractionRing R) k), (∀ jj, s.f jj = 0) → U.Expands k s F → F = 0 := by
  intro R _ _ I D A G _ _ U k hR s F hs hE
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  obtain ⟨r, hr, σ, f, h₁, hf, hE⟩ := hE
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hσ : ∀ j, σ.f j = 0 := fun j => by
    refine ExpInt.generic_app_injective G _ (Eq.trans (fn_ext fun y hy => ?_) (map_zero _).symm)
    obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB y
      (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
    have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left) = j a := fun a => by
      rw [Subsingleton.elim a 0]; exact e ()
    have e₂ := ExpInt.secScal_sval h₁ (𝟙 _) y hJ
    rw [sval_eq_zero hs _ y hJ, mul_zero, sval_of σ _ y J j ej] at e₂
    refine ((gs_pull (𝟙 _) _ y _ hy _).trans e₂).trans ((gs_eq _ y _ hy _).trans ?_).symm
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  have hf0 : ∀ α j, (f α).f j = 0 := fun α => by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
      (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (f α) fun e j => ?_
    refine (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k σ f (fun j => ?_) (hE e) α j)
    exact (congrArg _ (hσ j)).trans (map_zero _)
  refine fam_ext fun α j => ?_
  refine sec_ext_val D.toPre.P.isLB (s' := SecOps.secZero) (fun y J hJ => ?_) j
  have e₁ := ExpInt.secScal_sval (hf α) (𝟙 _) y hJ
  rw [sval_eq_zero (hf0 α) _ y hJ, ExpInt.gs_scal] at e₁
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing R)).hom =
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
  rw [e₃] at e₁
  refine Eq.trans ?_ (sval_eq_zero (fun _ => rfl) _ y hJ).symm
  exact (IsUnit.mul_right_eq_zero (ExpInt.isUnit_cst _ y hr)).1 e₁.symm

end GlobalTheory.ExpZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionTranslationActsOnExpansionsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionTranslation_acts_on_expansions : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W) (N : ℕ), 1 ≤ N → ∀ (x : TA V W ⟶ G) (g' : GtPt D (TA V W)) (g : GtPtF D F) (xA : TFK (R := V) F ⟶ A.A), x ^ N = 1 → U.Red x g' → GtPt.IsPullF F φ.left g' g → U.SamePt xA (φ ≫ x) → U.Acts F N 0 g xA) := by
  first | exact @GlobalTheory.UU.Transl.main | exact GlobalTheory.UU.Transl.main | (intros; apply GlobalTheory.UU.Transl.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPullSubsingleton
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifPullCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange (CarriesFam GrpPull RigPull UnifPull GenericInPsiLocus UnifBaseChange)
open GlobalTheory.PullDegCompare
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Bundle

end Bundle

section Main

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']

omit [IsDomain R] [IsDomain R'] in
theorem isGrpPullback_of_bc (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom) :
    IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
  ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl


variable [IsCommMonObj G] [IsCommMonObj G']

variable {I : Ideal R} {I' : Ideal R'}

variable {D : DegData R I} {D' : DegData R' I'} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}

end Main

end GlobalTheory.UnifPullCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisedArcIsoMatchesLevelPointsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisedArc_iso_matches_levelPoints : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) := by
  first | exact @GlobalTheory.ArcLevel.level_match | exact GlobalTheory.ArcLevel.level_match | (intros; apply GlobalTheory.ArcLevel.level_match <;> assumption)
end

