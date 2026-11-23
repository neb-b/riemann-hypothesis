module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExist
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_smoothOfRelativeDimension_of_isAbelianScheme :
    ∀ (K : Type) [Field K] (X : Over (Sp K)) [GrpObj X], IsAbelianScheme X →
      ∃ g : ℕ, SmoothOfRelativeDimension g X.hom := by
  intro K _ X _ hX
  haveI := hX.smooth
  haveI := hX.geomConnected
  haveI : ConnectedSpace X.left := GeometricallyConnected.connectedSpace X.hom X.hom.isOpenMap
  obtain ⟨x₀⟩ := (inferInstance : ConnectedSpace X.left).toNonempty
  exact exists_dim_of_preconnected X.hom x₀

end GlobalTheory.AV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndPrimitiveOneForms
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem hasFrame_and_primF_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ PrimF A := by
  intro R _ A _ g hA hg
  obtain ⟨M, _, _, j, hfin, hproj, hb⟩ := _root_.GlobalTheory.InvFormBC.exists_invariant_frame R A g hA hg
  exact ⟨hasFrame_of_isBaseChange R (AffOp A.left) (OAff A.hom) M j fun U ↦ ⟨_, fun _ ↦ rfl, hb U⟩,
    _root_.GlobalTheory.AbCoh.primF_of_isAbelianScheme R A g hA hg⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackSemiAbelianOverNormalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem link_of_normal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Algebra O Ω] [IsFractionRing O Ω] (x : Sp O ⟶ M.Z) (u : S.R →+* O), spMap (algebraMap O Ω) ≫ x = M.pt → (algebraMap O Ω).comp u = S.R.val.toRingHom → ∃ gm : ((Over.pullback (spMap u)).obj ρ.P.A).left ⟶ FinalForm.G.left, Link FinalForm x (spMap u) ((Over.pullback (spMap u)).obj ρ.P.A) (pullback.fst ρ.P.A.hom (spMap u)) gm := by
  intro o Ω _ _ _ _ S ρ M U₀ EE FinalForm hU O _ _ _ _ _ _ x u hx hu

  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x₀ : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx₀ : x₀ ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x₀ ≫ FinalForm.u₀ = spMap S.R.val.toRingHom := FinalForm.u₀_gen x₀ hx₀
  let j : Sp Ω ⟶ Sp O := spMap (algebraMap O Ω)
  have hju : j ≫ spMap u = spMap S.R.val.toRingHom := (spMap_comp u (algebraMap O Ω)).symm.trans (congrArg spMap hu)

  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let A₀ := (Over.pullback M.pt).obj FinalForm.G
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x₀)
             (by rw [pullback.condition, Category.assoc, hx₀])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x₀ := FinalForm.cart.1.lift_snd _ _ _
  have gη : IsGrpPullback A₀ FinalForm.G (x₀ ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx₀.symm hν₁.symm
  have gν : IsGrpPullback A₀ Q x₀ ν := FinalForm.cart.cancel gη hν₂
  have gψ : IsGrpPullback A₀ ρ.P.A (j ≫ spMap u) (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) :=
    (gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)).congr (by rw [hju, hxu]) rfl

  let A := (Over.pullback (spMap u)).obj ρ.P.A
  have hA := isGrpPullback_pullback ρ.P.A (spMap u)
  have wA : (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ ρ.P.A.hom = (A₀.hom ≫ j) ≫ spMap u := by
    rw [gψ.1.w, Category.assoc]
  let φ₂ : A₀.left ⟶ A.left := hA.1.lift _ _ wA
  have eφ₂ : φ₂ ≫ pullback.fst ρ.P.A.hom (spMap u) = ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ := hA.1.lift_fst _ _ _
  have sφ₂ : φ₂ ≫ A.hom = A₀.hom ≫ j := hA.1.lift_snd _ _ _
  have hφ₂ : IsGrpPullback A₀ A j φ₂ := hA.cancel (gψ.congr rfl eφ₂.symm) sφ₂

  let GO := (Over.pullback x).obj FinalForm.G
  have hGO := isGrpPullback_pullback FinalForm.G x
  have gη' : IsGrpPullback A₀ FinalForm.G (j ≫ x) (pullback.fst FinalForm.G.hom M.pt) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx.symm rfl
  have wG : pullback.fst FinalForm.G.hom M.pt ≫ FinalForm.G.hom = (A₀.hom ≫ j) ≫ x := by rw [gη'.1.w, Category.assoc]
  let φ₁ : A₀.left ⟶ GO.left := hGO.1.lift _ _ wG
  have eφ₁ : φ₁ ≫ pullback.fst FinalForm.G.hom x = pullback.fst FinalForm.G.hom M.pt := hGO.1.lift_fst _ _ _
  have hφ₁ : IsGrpPullback A₀ GO j φ₁ := hGO.cancel (gη'.congr rfl eφ₁.symm) (hGO.1.lift_snd _ _ _)
  have sA : IsSemiAbelian A := IsSemiAbelian.pullback _ _ (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ ρ.P.isAb)
  have sG : IsSemiAbelian GO := IsSemiAbelian.pullback _ _ FinalForm.semi
  obtain ⟨E, ⟨hE, hEφ⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O) (GlobalTheory.IsGenericPointHom.fractionField O Ω) sA sG hφ₂ hφ₁
  haveI := hE
  let gm : A.left ⟶ FinalForm.G.left := E.hom.left ≫ pullback.fst FinalForm.G.hom x
  have hgm : IsGrpPullback A FinalForm.G x gm := ((isGrpPullback_of_iso E).comp hGO).congr (Category.id_comp _) rfl
  have key : φ₂ ≫ gm = ν ≫ FinalForm.φ := by
    show φ₂ ≫ E.hom.left ≫ pullback.fst FinalForm.G.hom x = _
    rw [← Category.assoc, hEφ, eφ₁, hν₁]
  have hgmw : gm ≫ FinalForm.G.hom = A.hom ≫ x := hgm.1.w
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ sA
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ FinalForm.semi
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing O Ω
  haveI : IsSchemeTheoreticallyDominant φ₂ := .of_isPullback hφ₂.1.flip
  refine ⟨gm, hgm, ?_, ?_⟩
  · intro f Fm hf T' p p' h₁ h₂
    let fO := (Over.pullback (spMap u)).map f
    let fQ := (Over.pullback FinalForm.u₀).map f
    have hfO₁ : fO.left ≫ pullback.fst ρ.P.A.hom (spMap u) = pullback.fst ρ.P.A.hom (spMap u) ≫ f.left :=
      pullback.lift_fst _ _ _
    have hfQ₁ : fQ.left ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = pullback.fst ρ.P.A.hom FinalForm.u₀ ≫ f.left :=
      pullback.lift_fst _ _ _
    have hfO₂ : fO.left ≫ A.hom = A.hom := Over.w fO
    have hp' : p' = p ≫ fO.left := by
      apply pullback.hom_ext
      · rw [h₂, Category.assoc, hfO₁]
      · show p' ≫ A.hom = (p ≫ fO.left) ≫ A.hom
        rw [Category.assoc, hfO₂, h₁]
    have wk : (ν ≫ fQ.left) ≫ Q.hom = A₀.hom ≫ x₀ := by
      rw [Category.assoc, Over.w fQ, gν.1.w]
    let k : A₀.left ⟶ A₀.left := gν.1.lift _ _ wk
    have hk₁ : k ≫ ν = ν ≫ fQ.left := gν.1.lift_fst _ _ _
    have hk₂ : k ≫ A₀.hom = A₀.hom := gν.1.lift_snd _ _ _
    have hφk : φ₂ ≫ fO.left = k ≫ φ₂ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, hfO₁, eφ₂, reassoc_of% eφ₂, reassoc_of% hk₁, hfQ₁]
      · show (φ₂ ≫ fO.left) ≫ A.hom = (k ≫ φ₂) ≫ A.hom
        rw [Category.assoc, hfO₂, Category.assoc, sφ₂, ← Category.assoc, hk₂]
    have main : fO.left ≫ gm = gm ≫ Fm.left := by
      refine GlobalTheory.ExtUnique.hom_ext_of_dominant FinalForm.G.hom ?_ φ₂ ?_
      · rw [Category.assoc, hgmw, ← Category.assoc, hfO₂, Category.assoc, Over.w Fm, hgmw]
      · calc φ₂ ≫ fO.left ≫ gm = k ≫ φ₂ ≫ gm := by rw [← Category.assoc, hφk, Category.assoc]
          _ = (k ≫ ν) ≫ FinalForm.φ := by rw [key, Category.assoc]
          _ = ν ≫ FinalForm.φ ≫ Fm.left := by rw [hk₁, Category.assoc, hf]
          _ = φ₂ ≫ gm ≫ Fm.left := by rw [← Category.assoc, ← key, Category.assoc]
    rw [hp', Category.assoc, main]
  · intro a Wo h hs T' p x' h₁ h₂
    have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := by simpa [baseOver] using Over.w (ρ.pt a)
    let σ : Sp O ⟶ A.left := pullback.lift (spMap u ≫ (ρ.pt a).left) (𝟙 (Sp O))
      (by rw [Category.assoc, hpa]; simp)
    have hσ₁ : σ ≫ pullback.fst ρ.P.A.hom (spMap u) = spMap u ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
    have hσ₂ : σ ≫ A.hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hp : p = (p ≫ A.hom) ≫ σ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hσ₁, h₂, Category.assoc]
      · show p ≫ A.hom = ((p ≫ A.hom) ≫ σ) ≫ A.hom
        rw [Category.assoc, hσ₂, Category.comp_id]
    let O' := x ⁻¹ᵁ Wo
    have hpb := isPullback_morphismRestrict x Wo
    let q : T' ⟶ O'.toScheme := hpb.lift x' (p ≫ A.hom) (by rw [h₁, Category.assoc])
    have hq₁ : q ≫ (x ∣_ Wo) = x' := hpb.lift_fst _ _ _
    have hq₂ : q ≫ O'.ι = p ≫ A.hom := hpb.lift_snd _ _ _
    have hmain : O'.ι ≫ σ ≫ gm = (x ∣_ Wo) ≫ h := by
      by_cases hO : (O' : Set (Sp O)).Nonempty
      · have hr' : Set.range j ⊆ Set.range O'.ι := by
          rw [Scheme.Opens.range_ι, (GlobalTheory.IsGenericPointHom.fractionField O Ω).range_eq, Set.singleton_subset_iff]
          exact ((genericPoint_spec (Sp O)).mem_open_set_iff O'.isOpen).2 (by simpa using hO)
        let jO : Sp Ω ⟶ O'.toScheme := IsOpenImmersion.lift O'.ι j hr'
        have hjO : jO ≫ O'.ι = j := IsOpenImmersion.lift_fac _ _ _
        haveI : IsDominant (jO ≫ O'.ι) := by rw [hjO]; infer_instance
        haveI : IsDominant jO := IsDominant.of_comp_of_isOpenImmersion jO O'.ι
        refine ext_of_isDominant_of_isSeparated FinalForm.G.hom ?_ jO ?_
        · simp only [Category.assoc]
          rw [hgmw, ← Category.assoc σ, hσ₂, Category.id_comp, hs.1, morphismRestrict_ι]
        · let x'' : Sp Ω ⟶ pullback ρ.P.A.hom FinalForm.u₀ := pullback.lift (spMap S.R.val.toRingHom ≫ (ρ.pt a).left) x₀
            (by rw [Category.assoc, hpa, hxu]; simp)
          have hx''₁ : x'' ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left :=
            pullback.lift_fst _ _ _
          have hx''₂ : x'' ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = x₀ := pullback.lift_snd _ _ _
          have hsec := hs.2 (jO ≫ (x ∣_ Wo)) x''
            (by rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hjO, hx])
            (by rw [FinalForm.cart.1.w, ← Category.assoc]; erw [hx''₂]; exact hx₀) hx''₁
          let e : Sp Ω ⟶ A₀.left := hφ₂.1.lift (j ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ₂, Category.comp_id, Category.id_comp])
          have he₁ : e ≫ φ₂ = j ≫ σ := hφ₂.1.lift_fst _ _ _
          have he₂ : e ≫ A₀.hom = 𝟙 _ := hφ₂.1.lift_snd _ _ _
          have heν : e ≫ ν = x'' := by
            apply pullback.hom_ext
            · rw [hx''₁, Category.assoc, ← eφ₂, ← Category.assoc, he₁, Category.assoc, hσ₁, ← Category.assoc, hju]
            · rw [hx''₂, Category.assoc]
              erw [hν₂]
              rw [← Category.assoc]
              erw [he₂]
              rw [Category.id_comp]
          calc jO ≫ O'.ι ≫ σ ≫ gm = (e ≫ φ₂) ≫ gm := by rw [← Category.assoc, hjO, he₁, Category.assoc]
            _ = (e ≫ ν) ≫ FinalForm.φ := by rw [Category.assoc, key, Category.assoc]
            _ = jO ≫ (x ∣_ Wo) ≫ h := by rw [heν, ← Category.assoc, hsec]
      · haveI : IsEmpty O'.toScheme := ⟨fun y => hO ⟨y.1, y.2⟩⟩
        exact isInitialOfIsEmpty.hom_ext _ _
    rw [hp, ← hq₂, ← hq₁, Category.assoc, Category.assoc, hmain, Category.assoc]

end GlobalTheory.Poinc.Sep.Spz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimension
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AbFieldDim

theorem exists_smoothOfRelativeDimension : ∀ (k : Type) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A],
    IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  intro k _ A _ hA
  exact GlobalTheory.AbelianDim.exists_relDim k A hA

end GlobalTheory.AbFieldDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleClsIff

theorem isAmpleCls_cls_iff : ∀ (K : Type) [Field K] (A : AbVar K) (L : LB A.X.left) (hL : L.IsLB),
    IsAmpleCls (cls L hL) ↔ IsAmpleLB L := by
  intro K _ A L hL
  have : IsProper A.X.hom := A.ab.proper
  constructor
  · rintro ⟨M, hM, hr, he⟩
    have hM' : IsAmpleLB M := (relAmple_iff_isAmpleLB_of_isAffine A.X hM).1 hr
    exact hM'.of_lbIso hL ((CechPic.cls_eq_iff hL hM).1 he.symm)
  · intro h
    exact ⟨L, hL, (relAmple_iff_isAmpleLB_of_isAffine A.X hL).2 h, rfl⟩

end GlobalTheory.AmpleClsIff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_isAmpleCls : ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c := by
  intro K _ A
  obtain ⟨L, hL, hamp⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy
    (GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A.X A.ab)
  exact ⟨cls L hL, L, hL, hamp, rfl⟩

end GlobalTheory.AV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNat
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerKill

theorem flat_of_isFinite_field (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] (hf : IsFinite H.hom) :
    Flat H.hom := by
  have haff : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (G := Grp.mk H)).2 haff
  let B : Type := A.unop
  letI : HopfAlgebra K B := A.unop.hopfAlgebra
  let G : Over (Spec (CommRingCat.of K)) :=
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of K))
  letI : GrpObj G := instGrpObjSpecAsOverSpec (R := CommRingCat.of K) (A := CommRingCat.of B)
  let i : G ≅ H := (Grp.forget _).mapIso e
  obtain ⟨j, hj, hw⟩ : ∃ j : Spec (CommRingCat.of B) ⟶ H.left, IsIso j ∧
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = j ≫ H.hom :=
    ⟨i.hom.left, inferInstanceAs (IsIso ((Over.forget _).map i.hom)), (Over.w i.hom).symm⟩
  haveI h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have e : H.hom = inv j ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
    rw [hw, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

theorem kernel_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left →
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  intro K _ A B f hf
  let H := pullback f.hom η[B.X]
  let i : H ⟶ A.X := pullback.fst _ _
  have hp : IsPullback i (toUnit H) f.hom η[B.X] := by
    rw [toUnit_unique (toUnit _) (pullback.snd f.hom η[B.X])]
    exact IsPullback.of_hasPullback _ _
  haveI : Mono i := ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩
  let lift {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) : W ⟶ H :=
    GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift hp g hg
  have lift_comp {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) :
      lift g hg ≫ i = g := GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp g hg
  have kills (W : Over (Sp K)) (x : W ⟶ H) : (x ≫ i) ≫ f.hom = 1 := by
    rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]
  letI : GrpObj H :=
    { one := lift η[A.X] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
      mul := lift (fst H H ≫ i * snd H H ≫ i) (by
        rw [MonObj.mul_comp, kills, kills, _root_.mul_one])
      inv := lift (i ≫ ι[A.X]) (by
        have e : i ≫ f.hom = 1 := by simpa using kills H (𝟙 H)
        have h : (i⁻¹ * i) ≫ f.hom = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
        rw [MonObj.mul_comp, e, _root_.mul_one] at h
        exact h)
      one_mul := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (fst (𝟙_ (Over (Sp K))) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (snd H (𝟙_ (Over (Sp K)))) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        exact _root_.mul_assoc _ _ _
      left_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact inv_mul_cancel i
      right_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact mul_inv_cancel i }
  haveI : IsMonHom i := by
    refine { one_hom := lift_comp _ _, mul_hom := ?_ }
    refine (lift_comp _ _).trans ?_
    rw [Hom.mul_def]
    simp
  haveI : IsCommMonObj A.X := A.ab.comm
  haveI : IsCommMonObj H := by
    refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
    rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  have hHf : IsFinite H.hom := by
    have hl := hp.map (Over.forget _)
    have h1 : IsFinite (toUnit H).left := MorphismProperty.of_isPullback (P := @IsFinite) hl hf
    have h2 : H.hom = (toUnit H).left ≫ (𝟙_ (Over (Sp K))).hom := (Over.w _).symm
    rw [h2]
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
  have hfl : Flat H.hom := flat_of_isFinite_field K H hHf
  obtain ⟨N, hN, h⟩ := GlobalTheory.FiniteFlatKilled.main K H hHf hfl
  refine ⟨N, hN, fun T x hx => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y : T ⟶ H, y ≫ i = x := ⟨_, GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp x hx⟩
  rw [← MonObj.comp_pow, ← Category.id_comp i,
    ← MonObj.pow_comp, h, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.AV.KerKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomExtPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem ext_of_pt_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f g : A ⟶ B),
    (∀ x : A.Pt, x ≫ f.hom = x ≫ g.hom) → f = g := by
  intro K _ A B f g h
  have := A.ab.smooth
  have := B.ab.proper
  have : IsReduced A.X.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.X.hom
  let Ω := AlgebraicClosure K
  let q : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  have : Surjective q := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have : JacobsonSpace ↥(pullback A.X.hom q) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd A.X.hom q)
  have hd : Dense (closedPoints ↥(pullback A.X.hom q)) := dense_iff_closure_eq.2 closure_closedPoints
  have hD := (pullback.fst A.X.hom q).surjective.denseRange.dense_image
    (pullback.fst A.X.hom q).continuous hd
  have hdom : IsDominant (equalizer.ι f.hom.left g.hom.left) := by
    refine ⟨hD.mono ?_⟩
    rintro _ ⟨w, hw₀, rfl⟩
    have hw : IsClosed ({w} : Set ↥(pullback A.X.hom q)) := hw₀
    let y : Sp Ω ⟶ A.X.left :=
      pointOfClosedPoint (pullback.snd A.X.hom q) w hw ≫ pullback.fst A.X.hom q
    have hy : y ≫ A.X.hom = q := by
      simp only [y, Category.assoc, pullback.condition]
      rw [← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
    let x : A.Pt := Over.homMk y hy
    have hx : y ≫ f.hom.left = y ≫ g.hom.left := congrArg CommaMorphism.left (h x)
    refine ⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩
    change (equalizer.lift y hx ≫ equalizer.ι f.hom.left g.hom.left) (IsLocalRing.closedPoint Ω) = _
    rw [equalizer.lift_ι]
    exact congrArg (pullback.fst A.X.hom q) (pointOfClosedPoint_apply (pullback.snd A.X.hom q) w hw _)
  have : IsDominant (equalizer.ι f.hom.left g.hom.left) := hdom
  have heq : f.hom = g.hom := Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated B.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) (equalizer.ι _ _) (equalizer.condition _ _))
  exact Subtype.ext heq

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntersectionEqLineBundleIntersecti
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_cls_eq_interNum : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J] (L : J → LB A.X.left) (hL : ∀ j, (L j).IsLB), inter A (fun j => cls (L j) (hL j)) = (letI := A.algΓ; interNum K (structureModule A.X.left) L) := by
  intro K _ A J _ L hL
  letI := A.algΓ
  exact (interNum_eq_multiDiff K (structureModule A.X.left) hL).symm

end GlobalTheory.AV.AbVar
end

