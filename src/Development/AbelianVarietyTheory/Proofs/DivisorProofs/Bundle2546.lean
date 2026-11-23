module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangent
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem lie_psi_cl_eq_tanVal (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A)
    (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
    (ψ : PrimitiveSubmodule A →ₗ[R] G.omega)
    (hψ : ∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c)))
    (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A)
    (hF : (⟨_, hβ⟩ : primDR A) ∈ PrimitiveSubmodule A) (x : G.Lie) (v : epsR R ⟶ A)
    (hx : t.LieCorr x v) : x (ψ ⟨_, hF⟩) = tanVal v β := by
  obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hβ
  have hw : ψ ⟨_, hF⟩ = w :=
    PDivGroup.rigOfOmega_injective_of_pow p R N hN G
      (isCan_unique R A p G t ⟨_, hβ⟩ hA _ _ (hψ ⟨_, hF⟩) hw2)
  rw [hw]
  exact lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 x v hx

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomLiftOneId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd

private theorem torusHomOf_iff_appTop₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

private theorem torus_eq₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) {s s' : splitTorus S X ⟶ splitTorus S X'} (hs : TorusHomOf h s) (hs' : TorusHomOf h s') :
    s = s' := by
  apply (GlobalTheory.splitTorusPointsEquiv S X' (splitTorus S X)).injective
  refine MonoidHom.ext fun χ => Units.ext ?_
  rw [show χ = Multiplicative.ofAdd χ.toAdd from rfl, GlobalTheory.splitTorusPointsEquiv_val,
    GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop₂ h s).1 hs, (torusHomOf_iff_appTop₂ h s').1 hs']

private theorem torus_eq_one₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    {s : splitTorus S X ⟶ splitTorus S X'} (hs : TorusHomOf (fun _ => (0 : X)) s) :
    s = toUnit _ ≫ η[splitTorus S X'] := by
  have h0 : (charUnit S X 0).val = 1 := by
    have k := GlobalTheory.splitTorusPointsEquiv_val S X (splitTorus S X) (𝟙 _) 0
    rw [ofAdd_zero, map_one, Units.val_one] at k
    rw [k]
    simp
  have : s = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv S X' (splitTorus S X)).injective
    rw [map_one]
    refine MonoidHom.ext fun χ => Units.ext ?_
    rw [show χ = Multiplicative.ofAdd χ.toAdd from rfl, GlobalTheory.splitTorusPointsEquiv_val,
      (torusHomOf_iff_appTop₂ _ s).1 hs, h0]
    rfl
  rw [this, Hom.one_def]

private theorem pullback_prod_ext₂ {S₀ C : Scheme.{0}} (f : C ⟶ S₀) {X Y : Over S₀} {Z : Over C}
    {a b : Z ⟶ (Over.pullback f).obj (X ⊗ Y)}
    (h₁ : a ≫ (Over.pullback f).map (fst X Y) = b ≫ (Over.pullback f).map (fst X Y))
    (h₂ : a ≫ (Over.pullback f).map (snd X Y) = b ≫ (Over.pullback f).map (snd X Y)) : a = b :=
  (isLimitOfPreserves (Over.pullback f) (tensorProductIsBinaryProduct X Y)).hom_ext (by
    rintro ⟨⟨⟩⟩
    · exact h₁
    · exact h₂)

private theorem map_eta₂ {S₀ C : Scheme.{0}} (f : C ⟶ S₀) (G : Over S₀) [MonObj G] :
    (Over.pullback f).map η[G] = toUnit _ ≫ η[(Over.pullback f).obj G] := by
  rw [Functor.obj.η_def, ← Category.assoc]
  have : toUnit ((Over.pullback f).obj (𝟙_ _)) ≫ Functor.LaxMonoidal.ε (Over.pullback f) = 𝟙 _ :=
    (IsTerminal.isTerminalObj (Over.pullback f) _ isTerminalTensorUnit).hom_ext _ _
  rw [this, Category.id_comp]

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem linHom_lift_one_id : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → LinHom U₂ U i₂ q₂ (lift 1 (𝟙 G₂)) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hS hU i₂ hi₁ hi₂
  have := hS.lim
  let xe : D.toPre.X ≃+ D₁.toPre.X × D₂.toPre.X := AddEquiv.ofBijective (q₁.prod q₂) hS.xsum
  have hxe : ∀ x, xe x = (q₁ x, q₂ x) := fun x => rfl
  let j₁ : D₁.toPre.X → D.toPre.X := fun y => xe.symm (y, 0)
  let j₂ : D₂.toPre.X → D.toPre.X := fun y => xe.symm (0, y)
  have hj₁ : ∀ y, q₁ (j₁ y) = y ∧ q₂ (j₁ y) = 0 := fun y => by
    have k := hxe (j₁ y); simp only [j₁, AddEquiv.apply_symm_apply] at k
    exact ⟨(congrArg Prod.fst k).symm, (congrArg Prod.snd k).symm⟩
  have hj₂ : ∀ y, q₁ (j₂ y) = 0 ∧ q₂ (j₂ y) = y := fun y => by
    have k := hxe (j₂ y); simp only [j₂, AddEquiv.apply_symm_apply] at k
    exact ⟨(congrArg Prod.fst k).symm, (congrArg Prod.snd k).symm⟩
  have hone : IsMonHom (1 : G₂ ⟶ G₁) := by rw [Hom.one_def]; infer_instance
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  ·
    have hq₁ := (U₁.gt e).q_hom
    have hq₂ := (U₂.gt e).q_hom
    have hiso : IsIso ((Over.pullback (thick R I e)).map (lift p₁ p₂)) := inferInstance
    rw [← cancel_mono ((Over.pullback (thick R I e)).map (lift p₁ p₂))]
    apply pullback_prod_ext₂
    · simp only [Category.assoc, ← Functor.map_comp, lift_fst]
      rw [hU.q_pr₁ e, ← Category.assoc, ← Functor.map_comp, lift_fst, hi₁, Hom.one_def]
      simp only [Functor.map_comp, map_eta₂, Category.assoc, IsMonHom.one_hom, comp_toUnit_assoc]
    · simp only [Category.assoc, ← Functor.map_comp, lift_snd]
      rw [hU.q_pr₂ e, ← Category.assoc, ← Functor.map_comp, lift_snd, hi₂]
      simp
  ·
    refine ⟨GlobalTheory.SplitTorusPow.torusMap _ q₂, (torusHomOf_iff_appTop₂ _ _).2 fun χ =>
      GlobalTheory.SplitTorusPow.torusMap_char q₂ χ, ?_⟩
    have hT : TorusHomOf q₂ (GlobalTheory.SplitTorusPow.torusMap (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) q₂) :=
      (torusHomOf_iff_appTop₂ _ _).2 fun χ => GlobalTheory.SplitTorusPow.torusMap_char q₂ χ
    obtain ⟨t₁, ht₁, e₁⟩ := hU.i_pr₁ e j₁ (fun y => (hj₁ y).1) (fun y => (hj₁ y).2)
    obtain ⟨t₂, ht₂, e₂⟩ := hU.i_pr₂ e j₂ (fun y => (hj₂ y).1) (fun y => (hj₂ y).2)
    have c₁ : GlobalTheory.SplitTorusPow.torusMap _ q₂ ≫ t₁ = toUnit _ ≫ η[splitTorus _ D₁.toPre.X] := by
      refine torus_eq_one₂ ?_
      have k := TorusHomOf.comp hT ht₁
      simp only [(hj₁ _).2] at k
      exact k
    have c₂ : GlobalTheory.SplitTorusPow.torusMap _ q₂ ≫ t₂ = 𝟙 _ := by
      refine torus_eq₂ (fun χ => χ) ?_ (TorusHomOf.id _)
      have k := TorusHomOf.comp hT ht₂
      simp only [(hj₂ _).2] at k
      exact k
    have hi₁' := (U₁.gt e).i_hom
    apply pullback_prod_ext₂
    · simp only [Category.assoc]
      rw [e₁, ← Category.assoc _ t₁, c₁, ← Functor.map_comp, lift_fst, Hom.one_def]
      simp only [Functor.map_comp, map_eta₂, Category.assoc, IsMonHom.one_hom, comp_toUnit_assoc]
    · simp only [Category.assoc]
      rw [e₂, ← Category.assoc _ t₂, c₂, ← Functor.map_comp, lift_snd]
      simp

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLocalSectionEqOfGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

theorem genPt_dom {S : Scheme.{0}} [IsIntegral S] {K : Type} [Field K] (ξ : Sp K ⟶ S)
    (hξ : Set.range ξ = {genericPoint S}) : QuasiCompact ξ ∧ IsSchemeTheoreticallyDominant ξ := by
  have hd : IsDominant ξ := ⟨by
    show Dense (Set.range ξ)
    rw [hξ]
    exact dense_iff_closure_eq.2 (genericPoint_spec S)⟩
  refine ⟨⟨fun U _ _ => (Set.subsingleton_of_subsingleton).isCompact⟩, ?_⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant ξ

theorem app_snd_injective {S : Scheme.{0}} [IsIntegral S] (G : Over S) [Flat G.hom] {K : Type} [Field K]
    (ξ : Sp K ⟶ S) (hξ : Set.range ξ = {genericPoint S}) (O : G.left.Opens) :
    Function.Injective ((snd (Over.mk ξ) G).left.app O).hom := by
  obtain ⟨_, _⟩ := genPt_dom ξ hξ
  have hP : IsPullback (fst (Over.mk ξ) G).left (snd (Over.mk ξ) G).left ξ G.hom := .of_hasPullback _ _
  have : IsSchemeTheoreticallyDominant (snd (Over.mk ξ) G).left := IsSchemeTheoreticallyDominant.of_isPullback hP
  have : QuasiCompact (snd (Over.mk ξ) G).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hP inferInstance
  exact (snd (Over.mk ξ) G).left.app_injective O

theorem locSec_eq_of_genIs : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S), Set.range ξ = {genericPoint S} →
    ∀ (N N' : S.Opens) (s : LocSec G L N) (s' : LocSec G L N') (v : SecM G L 1 (Over.mk ξ)),
      GenIs ξ s v → GenIs ξ s' v → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i) := by
  intro S _ G _ _ hG L K _ ξ hξ N N' s s' v ⟨h₁, e₁⟩ ⟨h₂, e₂⟩ i
  have := hG.smooth
  have hfl : Flat G.hom := inferInstance
  have e := congrFun (e₁.trans e₂.symm) (fun _ => i)
  have h₃ : Set.range ξ ⊆ ((N ⊓ N' : S.Opens) : Set S) := fun x hx => ⟨h₁ hx, h₂ hx⟩
  set O : G.left.Opens := L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') with hO
  set W : (Over.mk ξ ⊗ G).left.Opens := (LPow G L 1 (Over.mk ξ)).U (fun _ => i) with hW
  have hle : W ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ O := lpow_U_le h₃ (fun _ => i)
  have hge : (snd (Over.mk ξ) G).left ⁻¹ᵁ O ≤ W := fun y hy => Set.mem_iInter.2 fun _ => hy.1
  have hinj : Function.Injective ((snd (Over.mk ξ) G).left.appLE O W hle).hom := by
    have hEq : W = (snd (Over.mk ξ) G).left ⁻¹ᵁ O := le_antisymm hle hge
    clear_value W
    subst hEq
    rw [← Scheme.Hom.app_eq_appLE]
    exact app_snd_injective G ξ hξ O
  apply hinj
  have k₁ : ((snd (Over.mk ξ) G).left.appLE O W hle).hom
      (resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : O ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i)) = genPull h₁ s (fun _ => i) := by
    dsimp only [resG]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have k₂ : ((snd (Over.mk ξ) G).left.appLE O W hle).hom
      (resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : O ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) = genPull h₂ s' (fun _ => i) := by
    dsimp only [resG]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  exact k₁.trans (e.trans k₂.symm)

end GlobalTheory.UMin.ThBdl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsAlgClosureFieldBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

section
variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R)))

theorem noetherianSpace_prod_field (F : Type) [Field F] [Algebra (FractionRing R) F] :
    TopologicalSpace.NoetherianSpace (TFK (R := R) F ⊗ A.A).left := by
  have := A.isAb.proper
  let b : (TFK (R := R) F ⊗ A.A).left ⟶ Spec (CommRingCat.of F) := (fst (TFK (R := R) F) A.A).left
  have : IsProper b := inferInstanceAs (IsProper (pullback.fst _ _))
  have : IsLocallyNoetherian (TFK (R := R) F ⊗ A.A).left := LocallyOfFiniteType.isLocallyNoetherian b
  have : CompactSpace (TFK (R := R) F ⊗ A.A).left := QuasiCompact.compactSpace_of_compactSpace b
  have : IsNoetherian (TFK (R := R) F ⊗ A.A).left := {}
  infer_instance

theorem isPullback_baseEm_whiskerRight {F : Type} [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) :
    IsPullback (baseEm em ▷ A.A).left (fst (TFK (R := R) F) A.A).left (fst (TFK (R := R) (Kb R)) A.A).left
      (baseEm em).left := by
  have h₁ : IsPullback (snd (TFK (R := R) (Kb R)) A.A).left (fst (TFK (R := R) (Kb R)) A.A).left
      A.A.hom (TFK (R := R) (Kb R)).hom := (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (snd (TFK (R := R) F) A.A).left (fst (TFK (R := R) F) A.A).left
      A.A.hom (TFK (R := R) F).hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (congrArg (fun q => q.left) (whiskerRight_fst (baseEm em) A.A)) h₁
  have e₁ : (baseEm em ▷ A.A).left ≫ (snd (TFK (R := R) (Kb R)) A.A).left =
      (snd (TFK (R := R) F) A.A).left := congrArg (fun q => q.left) (whiskerRight_snd (baseEm em) A.A)
  have e₂ : (baseEm em).left ≫ (TFK (R := R) (Kb R)).hom = (TFK (R := R) F).hom := Over.w (baseEm em)
  rw [e₁, e₂]
  exact h₂

end

theorem isExtension_secExt : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), letI : Algebra (Kb R) F := em.toRingHom.toAlgebra; GlobalTheory.FieldBaseChange.IsExtension (secExt A em N) := by
  intro R _ _ A F _ _ em N
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  have := noetherianSpace_prod_field A (Kb R)
  exact GlobalTheory.FieldBaseChange.isExtension_pullOver (K := Kb R) (F := F) (isPullback_baseEm_whiskerRight A em) A.isLB _ _

end GlobalTheory.Mum.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocExt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.ClosedExt

theorem locExt {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (hp : IsProjOver p) (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ)
    (hu : ∀ y, CInfAt u y) (x : CxPts p σ) :
    ∃ (O : Set (CxPts p σ)) (v : CxPts p σ → ℝ), IsOpen O ∧ x ∈ O ∧ (∀ z ∈ O, CInfAt v z) ∧
      ∀ y : CxPts q σ, ptMap π hπ σ y ∈ O → v (ptMap π hπ σ y) = u y := by
  have := GlobalTheory.LocExt.isSeparated_of_isProjOver hp
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, hπ]⟩
  have hemb : IsClosedEmbedding (ptMap π hπ σ) := by
    have : CompactSpace (CxPts q σ) := GlobalTheory.CxPts.compactSpace σ hq
    have hc : Continuous (ptMap π hπ σ) := continuous_of_comp (f := π) fun _ => rfl
    refine hc.isClosedEmbedding fun y y' h => Subtype.ext ?_
    exact (cancel_mono π).1 (congrArg Subtype.val h)
  by_cases hx : ∃ y : CxPts q σ, ptMap π hπ σ y = x
  · obtain ⟨y₀, rfl⟩ := hx
    obtain ⟨W, ι, _, g, F, O₀, h₁, h₂, h₃, h₄, h₅⟩ := hu y₀
    obtain ⟨t, ht, htW⟩ := (π.isClosedEmbedding.isInducing.isOpen_iff).1 W.2
    let W₁ : X.Opens := ⟨t, ht⟩
    have hW₁ : π ⁻¹ᵁ W₁ = W := Opens.ext htW
    have hz₀ : π (y₀.1 (IsLocalRing.closedPoint ℂ)) ∈ W₁ := by
      have := mem_ptsIn.1 h₁
      rw [← hW₁] at this
      exact this
    obtain ⟨W', hW'a, hzW', hW'le⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hz₀
    have hle : π ⁻¹ᵁ W' ≤ W := by
      rw [← hW₁]
      exact fun a ha => hW'le ha
    choose g' hg' using fun a => π.app_surjective W' hW'a (resG Y hle (g a))
    have hval (y : CxPts q σ) (hy : y ∈ ptsIn q σ (π ⁻¹ᵁ W')) (a : ι) :
        ev p σ W' (g' a) (ptMap π hπ σ y) = ev q σ W (g a) y := by
      rw [← ev_res hle hy, ← hg' a]
      exact valR_comp y.1 π W' (g' a)
    obtain ⟨s, hs, hsu⟩ := h₅.exists_mem
    obtain ⟨N, hNs, hN, hy₀N⟩ := mem_nhds_iff.1 hs
    obtain ⟨N', hN', hNN'⟩ := (hemb.isInducing.isOpen_iff).1 hN
    have hE : IsOpen (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀) :=
      (continuousOn_pi.2 fun a => continuousOn_ev (g' a)).isOpen_inter_preimage (isOpen_ptsIn W') h₂
    have hy₀W' : y₀ ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 hzW'
    refine ⟨N' ∩ (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀),
      fun z => F fun a => ev p σ W' (g' a) z, hN'.inter hE, ⟨?_, ?_, ?_⟩, fun z hz => ?_, fun y hy => ?_⟩
    · have : y₀ ∈ ptMap π hπ σ ⁻¹' N' := hNN'.symm ▸ hy₀N
      exact this
    · exact mem_ptsIn.2 hzW'
    · simp only [Set.mem_preimage, hval y₀ hy₀W']
      exact h₃
    · exact ⟨W', ι, inferInstance, g', F, O₀, hz.2.1, h₂, hz.2.2, h₄, EventuallyEq.rfl⟩
    · have hyN : y ∈ N := by
        have : y ∈ ptMap π hπ σ ⁻¹' N' := hy.1
        rwa [hNN'] at this
      have hyW' : y ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 (mem_ptsIn.1 hy.2.1)
      simp only [hval y hyW']
      exact (hsu (hNs hyN)).symm
  · exact ⟨(Set.range (ptMap π hπ σ))ᶜ, fun _ => 0, hemb.isClosed_range.isOpen_compl, hx,
      fun z _ => cInfAt_const 0 z, fun y hy => absurd (Set.mem_range_self y) hy⟩

theorem exists_extension : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ), (∀ y, CInfAt u y) → ∃ v : CxPts p σ → ℝ, (∀ y, CInfAt v y) ∧ ∀ y, v (ptMap π hπ σ y) = u y := by
  intro k _ X Y p q σ hp π _ hπ u hu
  exact GlobalTheory.CInfGlue.glue k X p hp σ (CxPts q σ) (ptMap π hπ σ) u (locExt hp π hπ u hu)

end GlobalTheory.ClosedExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormRationalSectionArchIntegrable
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

open Set Filter Topology

namespace GlobalTheory.LogNormIntGen

theorem archIntegrable : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ}, IsArithVar p D → GenSmooth p D → ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ}
      (hr : GlobalTheory.Cartier.IsRatSec N.B r), M.ArchIntegrable N D hr := by
  intro k _ X _ p D hX hs M N r hr σ
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hs σ
  have hσ : Function.Injective σ := ChernNull.injective_of_arithVar hX σ
  have key (ε : ℤˣ) : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr))
      ((M.φ σ).chernPart D ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm (N.φ σ) r)
        (offSupp p σ (N.div hr) ∩ O) ((M.φ σ).chernPart D ε) :=
      have ⟨_, hi⟩ := R.cover y
      LogNormInt.exists_integrableOn hσ (M.cInf σ) (N.cInf σ) hr ε _ hi
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
    obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.LogNormIntGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackTraitGenericConditionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicationPullback_trait_genericCondition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ) (a : W)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ₀ (p ≫ (mulA C.A.A m).left) z J) →
    ∀ (σ : SecK C.P.L.L T.β 1) (σ₂ : SecK C.P.L.L T.β (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval θ₀ p' z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ₂ p z J = gs p z ⊤ (scal T.G.hom a) * sval S p' z J := by
  first | exact @GlobalTheory.Mum.pullMul_trait_generic | exact GlobalTheory.Mum.pullMul_trait_generic | (intros; apply GlobalTheory.Mum.pullMul_trait_generic <;> assumption)
end

