module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeSectionFacesAndDoubling
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SeriesApplyEqZeroOfFace
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsGlobalFrameOfLocal
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFiniteFree
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM

namespace GlobalTheory.GenFree

theorem exists_free_away (A M : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] : ∃ g : A, g ≠ 0 ∧ Module.Free (Localization.Away g) (LocalizedModule.Away g M) := by
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨g, hg, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  exact ⟨g, nonZeroDivisors.ne_zero hg, hfree⟩

theorem free_basicOpen {X Y : Scheme.{0}} (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V)) (g : Γ(Y, V))
    (hfree : letI := (f.app V).hom.toAlgebra
      Module.Free (Localization.Away g) (LocalizedModule.Away g Γ(X, f ⁻¹ᵁ V))) :
    letI := (f.app (Y.basicOpen g)).hom.toAlgebra
    Module.Free Γ(Y, Y.basicOpen g) Γ(X, f ⁻¹ᵁ Y.basicOpen g) := by
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have hpre : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen _ _
  let A := Γ(Y, V)
  let M := Γ(X, f ⁻¹ᵁ V)
  let R := Γ(Y, Y.basicOpen g)
  let N := Γ(X, f ⁻¹ᵁ Y.basicOpen g)
  letI : Algebra A R := (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  haveI : IsLocalization.Away g R := hV.isLocalization_basicOpen g
  have hle : f ⁻¹ᵁ Y.basicOpen g ≤ f ⁻¹ᵁ V := f.preimage_mono (Y.basicOpen_le g)
  letI : Algebra M N := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  haveI : IsLocalization.Away (algebraMap A M g) N :=
    hV'.isLocalization_of_eq_basicOpen (f.app V g) (homOfLE hle) hpre
  letI : Algebra R N := (f.app (Y.basicOpen g)).hom.toAlgebra
  letI : Algebra A N := ((algebraMap R N).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A M N := IsScalarTower.of_algebraMap_eq fun a => by
    change (f.app _).hom ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom a) =
      (X.presheaf.map (homOfLE hle).op).hom ((f.app V).hom a)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid M (Submonoid.powers g)) N := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers g) (IsScalarTower.toAlgHom A M N).toLinearMap :=
    isLocalizedModule_iff_isLocalization.2 inferInstance
  let l := IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (IsScalarTower.toAlgHom A M N).toLinearMap
  let b₀ := Module.Free.chooseBasis (Localization.Away g) (LocalizedModule.Away g M)
  let τ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) R
  let Ψ := l.symm ≪≫ₗ b₀.repr.restrictScalars A ≪≫ₗ Finsupp.mapRange.linearEquiv τ.toLinearEquiv
  let Ψ' := Ψ.extendScalarsOfIsLocalization (Submonoid.powers g) R
  exact Module.Free.of_basis (Module.Basis.ofRepr Ψ')

theorem exists_dim_eq (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp F) [LocallyOfFiniteType q] :
    ∃ n : ℕ, topologicalKrullDim Y = n := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top (genericPoint Y))
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ q)
  have hφ : Spec.map φ = hU.fromSpec ≫ q := Spec.map_preimage _
  letI : Algebra F Γ(Y, U) := φ.hom.toAlgebra
  have : Algebra.FiniteType F Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  obtain ⟨d, h₁, -⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  refine ⟨d, ?_⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F q U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec

theorem exists_affine_finite_free : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (sY : Y ⟶ Sp k) (f : X ⟶ Y), IsProjOver (f ≫ sY) → IsProjOver sY → f (genericPoint X) = genericPoint Y → topologicalKrullDim X ≤ topologicalKrullDim Y → ∀ n : ℕ, f.residueDegree (genericPoint X) = n → ∃ V : Y.Opens, genericPoint Y ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (f ⁻¹ᵁ V) ∧ (letI := (f.app V).hom.toAlgebra; Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n) := by
  intro k _ X Y _ _ sY f hX hY hη hdim n hn
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hX
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hY
  have : IsProper f := IsProper.of_comp f sY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsDominant f := ⟨(dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
    (Set.singleton_subset_iff.2 ⟨_, hη⟩)⟩
  have hs := surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  obtain ⟨d, hdY⟩ := exists_dim_eq k sY
  have hdX : topologicalKrullDim X = d :=
    (le_antisymm hdim (PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective)).trans hdY
  have hd : f.residueDegree (genericPoint X) ≠ 0 :=
    GenFinite.residueDegree_genericPoint_ne_zero k X Y sY f d inferInstance inferInstance hs hdX hdY
  obtain ⟨V₀, hV₀, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f
    (genericPoint Y) ((Set.finite_singleton (genericPoint X)).subset
      fun y hy => GenFiniteEtale.eq_genericPoint f hη hd hy)
  obtain ⟨V, hV, hxV, hle⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV₀
  replace hV : IsAffineOpen V := hV
  haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
  obtain ⟨hW, hf⟩ := GenFiniteEtale.finite_app_of_le f hV hle
  letI := (f.app V).hom.toAlgebra
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hf
  obtain ⟨g, hg, hfree⟩ := exists_free_away Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
  have hU := hV.basicOpen g
  have hxU := GenFiniteEtale.genericPoint_mem_basicOpen hg
  obtain ⟨hW', hf'⟩ := GenFiniteEtale.finite_app_of_le f hU ((Y.basicOpen_le g).trans hle)
  refine ⟨Y.basicOpen g, hxU, hU, hW', free_basicOpen f hV hW g hfree, hf', ?_⟩
  have := (GenFiniteEtale.affine_pair f hη hd hU hW' le_rfl (show f _ ∈ Y.basicOpen g from hη ▸ hxU)).2.2.1
  rw [← f.app_eq_appLE] at this
  exact this.trans hn

end GlobalTheory.GenFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleDivSymm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SymDiv

theorem exists_ampleDiv_symm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → ∃ D : CartierDiv A.left, AmpleDiv D ∧ LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) := by
  intro R _ A _ _ hA L hL hamp
  classical
  have hprop : IsProper A.hom := hA.proper
  set σ := (GrpObj.inv : A ⟶ A).left with hσ
  have hii : (GrpObj.inv : A ⟶ A) ≫ (GrpObj.inv : A ⟶ A) = 𝟙 A := by
    have h := IsIso.hom_inv_id (GrpObj.inv : A ⟶ A)
    rwa [GrpObj.inv_inv] at h
  have hii' : σ ≫ σ = 𝟙 A.left := by
    rw [hσ, ← Over.comp_left, hii, Over.id_left]
  have : IsIso σ := ⟨⟨σ, hii', hii'⟩⟩
  set L' := LB.LinComb L (K := Fin 2) ![𝟙 A.left, σ] ![1, 1] with hL'def
  have hL' : L'.IsLB := LB.isLB_linComb hL (K := Fin 2) ![𝟙 A.left, σ] ![1, 1]
  have hamL : IsAmpleLB L := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  have hamσ : IsAmpleLB (L.pull σ) := hamL.pull_of_isAffineHom σ
  have hamL' : IsAmpleLB L' := by
    refine hamL.tensor hamσ hL' ?_
    have hM := pull_isLB hL σ
    have hD1 := LB.isLB_div hL' hL
    have hD2 := LB.isLB_div hD1 hM
    refine (CechPic.cls_eq_zero_iff hD2).1 ?_
    rw [CechPic.cls_div hD1 hM, CechPic.cls_div hL' hL, CechPic.cls_linComb hL _ _ hL', CechPic.cls_pull hL σ hM]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_zsmul,
      CechPic.pull_id]
    abel
  have : CompactSpace A.left := hamL'.compactSpace
  obtain ⟨i₀, h₀⟩ := exists_chart hL' (genericPoint A.left)
  refine ⟨ofLB hL' i₀ h₀, ?_, ?_⟩
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    exact (ampleDiv_iff_isAmpleLB _ _).2 (hamL'.of_lbIso hT e.symm)
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    have hs : LBIso (L'.pull σ) L' := GlobalTheory.SymLB.pull_inv_symm_iso _ A L hL
    have e₁ : LBIso ((toLB (ofLB hL' i₀ h₀)).pull σ) (L'.pull σ) := GlobalTheory.FamRep.lbIso_pull e.symm σ
    exact LBIso.trans (pull_isLB hT σ) hL' hT (LBIso.trans (pull_isLB hT σ) (pull_isLB hL' σ) hL' e₁ hs) e

end GlobalTheory.SymDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfLineBundleIso
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

variable {X : Scheme.{0}}

theorem pspec_eq (p q : PrimeSpectrum ℂ) : p = q :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p.asIdeal).trans (Ideal.eq_bot_of_prime q.asIdeal).symm)

theorem chart_pt (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) : ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := pspec_eq q p0
  rw [this]
  exact hj

theorem val_res_unit (x : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    valAt' x V (res hVU a : Γ(X, V)) = valAt' x U (a : Γ(X, U)) :=
  ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res x hVU h (a : Γ(X, U))

theorem val_inv_unit (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U ((a⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) = (valAt' x U (a : Γ(X, U)))⁻¹ :=
  map_units_inv (valHom x U h) a

theorem val_unit_ne (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U (a : Γ(X, U)) ≠ 0 :=
  (a.isUnit.map (valHom x U h)).ne_zero

theorem val_gen {L L' : LB X} (w : LB.Iso L' L) (hw : w.IsGen) (x : Sp ℂ ⟶ X) (i i₂ : L.ι) (j j₂ : L'.ι)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L'.U j)) (h₂ : ⊤ ≤ x ⁻¹ᵁ (L.U i₂ ⊓ L'.U j₂)) :
    valAt' x (L.U i ⊓ L'.U j) (w.s (i, j)).val =
      valAt' x (L.U i ⊓ L.U i₂) (L.g i i₂).val * (valAt' x (L'.U j ⊓ L'.U j₂) (L'.g j j₂).val)⁻¹ *
        valAt' x (L.U i₂ ⊓ L'.U j₂) (w.s (i₂, j₂)).val := by
  have hW : ⊤ ≤ x ⁻¹ᵁ ((L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)) := fun p hp => ⟨h₁ hp, h₂ hp⟩
  have E : res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left)
      (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ) =
      (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L.U i₂ from
          le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (L.g i i₂) *
        (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L'.U j ⊓ L'.U j₂ from
          le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (L'.g j j₂))⁻¹) *
      res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right)
        (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ) := hw (i, j) (i₂, j₂)
  have e := congrArg (fun a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂))ˣ =>
    valAt' x _ (a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)))) E
  simp only [Units.val_mul, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul, val_inv_unit x _ hW, val_res_unit x _ hW] at e
  have a1 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left) hW
    (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ)
  have a2 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right) hW
    (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ)
  exact a1.symm.trans (e.trans (congrArg (fun t => _ * t) a2))

end GlobalTheory.TransportFrame

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem val_g_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) (i : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    valAt' x (L.U i ⊓ L.U i) (L.g i i).val = 1 := by
  have e := val_res_unit x (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) h (L.g i i)
  rw [hL.g_self i, Units.val_one, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_one x _ h] at e
  exact e.symm

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L L' : LB A.left}

def chartOf (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : L'.ι := (chart_pt L' hL' y).choose

theorem chartOf_spec (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : ⊤ ≤ y ⁻¹ᵁ L'.U (chartOf hL' y) :=
  (chart_pt L' hL' y).choose_spec

def frT (u' : HolUnif A L' g) (hL' : L'.IsLB) (w : LB.Iso L' L) (i : L.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u'.ex z).left (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) (w.s (i, chartOf hL' (u'.ex z).left)).val *
    u'.fr (chartOf hL' (u'.ex z).left) z

theorem frT_eq (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) (j : L'.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) (hj : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U j) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z := by
  have h0 := chartOf_spec hL' (u'.ex z).left
  have hij0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) := fun p hp => ⟨hi hp, h0 hp⟩
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  have h0j : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L'.U (chartOf hL' (u'.ex z).left) ⊓ L'.U j) := fun p hp => ⟨h0 hp, hj hp⟩
  have G := val_gen w hw (u'.ex z).left i i (chartOf hL' (u'.ex z).left) j hij0 hij
  have C := u'.fr_compat (chartOf hL' (u'.ex z).left) j z h0j
  have hne := val_unit_ne (u'.ex z).left _ h0j (L'.g (chartOf hL' (u'.ex z).left) j)
  have hs := val_g_self hL (u'.ex z).left i hi
  unfold frT
  rw [G, hs, C]
  have hc := inv_mul_cancel₀ hne
  linear_combination (valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z) * hc

theorem frT_hol (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) :
    DifferentiableOn ℂ (frT u' hL' w i) {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i} := by
  intro z0 hz0
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z0).left
  have hT := u'.hol (L.U i ⊓ L'.U j) (w.s (i, j)).val
  have hz0' : ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ L.U i := hz0
  have hz0T : z0 ∈ {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    show ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ (L.U i ⊓ L'.U j) from fun p hp => ⟨hz0' hp, hj hp⟩
  have hd : DifferentiableOn ℂ (fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z)
      {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    hT.2.mul ((u'.fr_hol j).mono fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) p hp => (hz hp).2)
  have hev : frT u' hL' w i =ᶠ[nhds z0]
      fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z :=
    Filter.eventually_of_mem (hT.1.mem_nhds hz0T) fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) =>
      frT_eq u' hL hL' w hw i j z (fun p hp => (hz hp).1) (fun p hp => (hz hp).2)
  exact (((hd z0 hz0T).differentiableAt (hT.1.mem_nhds hz0T)).congr_of_eventuallyEq hev).differentiableWithinAt

theorem frT_ne (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) : frT u' hL' w i z ≠ 0 := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  rw [frT_eq u' hL hL' w hw i j z hi hj]
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  exact mul_ne_zero (val_unit_ne _ _ hij (w.s (i, j) : Γ(A.left, L.U i ⊓ L'.U j)ˣ)) (u'.fr_ne j z hj)

theorem frT_compat (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i i₂ : L.ι)
    (z : Fin g → ℂ) (h : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i₂)) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L.U i₂) (L.g i i₂).val * frT u' hL' w i₂ z := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := fun p hp => (h hp).1
  have hi₂ : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i₂ := fun p hp => (h hp).2
  rw [frT_eq u' hL hL' w hw i j z hi hj, frT_eq u' hL hL' w hw i₂ j z hi₂ hj,
    val_gen w hw (u'.ex z).left i i₂ j j (fun p hp => ⟨hi hp, hj hp⟩) (fun p hp => ⟨hi₂ hp, hj hp⟩),
    val_g_self hL' (u'.ex z).left j hj]
  ring

def transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) :
    HolUnif A L g where
  ex := u'.ex
  ex_add := u'.ex_add
  ex_onto := u'.ex_onto
  Λ := u'.Λ
  ker := u'.ker
  discrete := u'.discrete
  full := u'.full
  hol := u'.hol
  fr := frT u' hL' w
  fr_hol := frT_hol u' hL hL' w hw
  fr_ne := frT_ne u' hL hL' w hw
  fr_compat := frT_compat u' hL hL' w hw

theorem isFactorAH_transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ' : u'.Λ → ℂ} (h : GlobalTheory.TorusRM.IsFactorAH u' Hm χ') :
    GlobalTheory.TorusRM.IsFactorAH (transport u' hL hL' w hw) Hm χ' := by
  refine ⟨h.1, h.2.1, fun (l : u'.Λ) i z hz => ?_⟩
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have he : u'.ex (z + l) = u'.ex z := by rw [u'.ex_add, (u'.ker l).2 l.2, _root_.mul_one]
  have hz0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := hz
  have hz' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L.U i := he ▸ hz0
  have hj' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L'.U j := he ▸ hj
  show frT u' hL' w i z = χ' l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * frT u' hL' w i (z + l)
  rw [frT_eq u' hL hL' w hw i j z hz0 hj, frT_eq u' hL hL' w hw i j (z + l) hz' hj', h.2.2 l j z hj, he]
  ring

theorem exists_holUnif_isFactorAH_of_lbIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L L' : LB A.left)
    (u' : HolUnif A L' g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), L.IsLB → L'.IsLB → LBIso L L' →
    GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → ∃ (u : HolUnif A L g) (χ : u.Λ → ℂ), u.ex = u'.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ g L L' u' Hm χ' hL hL' hiso h
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨transport u' hL hL' w hw, χ', rfl, isFactorAH_transport u' hL hL' w hw h⟩

end GlobalTheory.TransportFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isFactorAH_frame_of_unif :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L₀ : LB A.left) (g : ℕ) (u₀ : HolUnif A L₀ g)
    (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      u.ex = u₀.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ hA L₀ g u M hL
  have hval := @valAt'_rules
  have hholprod := @holFamily_lift hval
  have hcubet := @cube_trivialisation_on_uniformising_space hval hholprod
  have hdbl := @exists_doubling_solution_pi
  have hdblu := @eventually_eq_zero_of_isBigO_cube_of_doubling
  have hlock := @LocalCube.exists_third_difference hdbl hdblu
  have hface := @cube_section_faces_and_doubling
  have hloc := @exists_localFrame_compatible_cube @hface hlock
  have hglob := @CubeFrame.exists_global_frame
  have hfac := @automorphyFactor_exp_linear_of_cube
  have hnf := @appellHumbert_normal_form_of_linear_exponent
  obtain ⟨t, ht⟩ := exists_gen_theta_of_isAbelianScheme ℂ A hA M hL
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hcubet A L₀ M g u hL t ht _ _ rfl rfl
  obtain ⟨fr, κ, hfr, hκ⟩ := hglob g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3
    (hloc g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u.Λ u.discrete u.full h6 h7 hT4)
  obtain ⟨a, B, ha, hab, hfa⟩ := hfac g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u.Λ u.discrete u.full
    h6 h7 hT4 fr κ hfr hκ
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hE, hQ, hQ0, hQn⟩ := hnf g u.Λ u.discrete u.full a B ha hab
  obtain ⟨f1, f2, f3⟩ := hfr
  refine ⟨{ ex := u.ex, ex_add := u.ex_add, ex_onto := u.ex_onto, Λ := u.Λ, ker := u.ker,
            discrete := u.discrete, full := u.full, hol := u.hol,
            fr := fun i z => fr i z * Complex.exp (Q z),
            fr_hol := fun i => ?_, fr_ne := fun i z hz => ?_, fr_compat := fun i j z hz => ?_ },
    Hm, χ, rfl, hH, hχ, ?_⟩
  · have := f1 i
    rw [Set.inter_univ] at this
    exact this.mul hQ.cexp.differentiableOn
  · exact mul_ne_zero (f2 i z hz trivial) (Complex.exp_ne_zero _)
  · have := f3 i j z (le_trans hz (fun _ h => h.1)) (le_trans hz (fun _ h => h.2)) trivial
    rw [this]
    ring
  · intro l i z hz
    show fr i z * Complex.exp (Q z) = _ * (fr i (z + l) * Complex.exp (Q (z + l)))
    rw [← hQn l z, hfa l i z hz, Complex.exp_sub]
    have := Complex.exp_ne_zero (Q (z + l))
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_arithBase_rootOfUnity : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] (K : ℕ) (ζ : Ω₂ˣ), 0 < K → IsPrimitiveRoot ζ K → ∃ (o₂ : Type) (_ : CommRing o₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (κ : o₁ →+* o₂) (ze : o₂ˣ), κ.Finite ∧ (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) ∧ Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze = ζ := by
  intro o₁ Ω₁ _ _ _ hb Ω₂ _ _ K ζ hK hζ
  haveI := hb.ded
  haveI := hb.ft
  haveI := hb.char
  haveI hc₂ : CharZero Ω₂ := charZero_of_injective_algebraMap (algebraMap Ω₁ Ω₂).injective
  let f : o₁ →+* Ω₂ := (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)
  have hf : Function.Injective f := (algebraMap Ω₁ Ω₂).injective.comp hb.inj
  letI : Algebra o₁ Ω₂ := f.toAlgebra
  let Q := FractionRing o₁
  letI : Algebra Q Ω₂ := (IsFractionRing.lift (K := Q) hf).toAlgebra
  haveI : IsScalarTower o₁ Q Ω₂ := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsFractionRing.lift_algebraMap (K := Q) hf x).symm)
  haveI : CharZero Q := (algebraMap Q Ω₂).charZero
  have hpow : (ζ : Ω₂) ^ K = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  have hint : IsIntegral o₁ (ζ : Ω₂) := IsIntegral.of_pow hK (by rw [hpow]; exact isIntegral_one)
  let F : IntermediateField Q Ω₂ := IntermediateField.adjoin Q {(ζ : Ω₂)}
  haveI : FiniteDimensional Q F := IntermediateField.adjoin.finiteDimensional hint.tower_top
  haveI : IsDedekindDomain (integralClosure o₁ F) := integralClosure.isDedekindDomain o₁ Q F
  haveI hfin : Module.Finite o₁ (integralClosure o₁ F) := IsIntegralClosure.finite o₁ Q F _
  let g : integralClosure o₁ F →+* Ω₂ := (algebraMap F Ω₂).comp (algebraMap (integralClosure o₁ F) F)
  have hg : Function.Injective g := (algebraMap F Ω₂).injective.comp Subtype.val_injective
  let zF : F := ⟨ζ, IntermediateField.mem_adjoin_simple_self Q _⟩
  have hzF : zF ^ K = 1 := Subtype.ext (by simpa using hpow)
  let z : integralClosure o₁ F :=
    ⟨zF, IsIntegral.of_pow hK (by rw [hzF]; exact isIntegral_one)⟩
  have hz : z ^ K = 1 := Subtype.ext (by simpa using hzF)
  refine ⟨integralClosure o₁ F, inferInstance, g.toAlgebra,
    @ArithBase.mk _ _ _ _ g.toAlgebra inferInstance ?_ hc₂ hg,
    algebraMap o₁ (integralClosure o₁ F), Units.ofPowEqOne z K hz hK.ne', ?_, ?_, ?_⟩
  · exact Algebra.FiniteType.trans (S := o₁) inferInstance inferInstance
  · exact RingHom.finite_algebraMap.mpr hfin
  · ext x
    rfl
  · ext
    rfl

end GlobalTheory.Poinc
end

