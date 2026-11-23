module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifAlongFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.TraitExt


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in
theorem exists_pull_gen {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (U' : Unif I' D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left)
      (πK : pullback ((Over.pullback (spMap g)).obj G).hom (jK R') ⟶ pullback G.hom (jK R)),
      IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) ∧
      πK ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (spMap g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) ∧
      U'.gen.hom.left ≫ gA = πK ≫ U.gen.hom.left := by
  have hP : PolBaseChangeSt := polBaseChange_holds
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hU', -⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  refine ⟨D', hD, A', U', gA, eA.hom.left ≫ gA ≫ U.gen.inv.left, gpA, LBIso.symm tA, ?_, ?_⟩
  · simpa only [Category.assoc] using heA
  · rw [hU']; simp only [Category.assoc, hgi, Category.comp_id]

end GlobalTheory.TraitExt

namespace GlobalTheory.TraitExt

end GlobalTheory.TraitExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFormsFunctionalAbelianBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.BaseChangeForm

theorem existsUnique_of_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    {G G' : Type} {F F' : Type 1} [AddCommGroup G] [Module R G] [AddCommGroup G'] [Module R' G']
    [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R' F']
    (c : F →ₗ[R] G) (hc : Function.Surjective c) (c' : F' →ₗ[R'] G')
    (p : F →ₛₗ[algebraMap R R'] F') (e : R' ⊗[R] G ≃ₗ[R'] G') (hp : ∀ f, c' (p f) = e (1 ⊗ₜ c f))
    (l : G →ₗ[R] R') :
    ∃! ψ : F' →ₗ[R'] R', (∀ f, c' f = 0 → ψ f = 0) ∧ ∀ f, ψ (p f) = l (c f) := by
  have key : ∀ x : R' ⊗[R] G, ∃ f' : F', c' f' = e x ∧
      ∀ ψ : F' →ₗ[R'] R', (∀ f, ψ (p f) = l (c f)) → ψ f' = LinearMap.liftBaseChange R' l x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, fun ψ _ ↦ by simp⟩
    | tmul b y =>
      obtain ⟨f, rfl⟩ := hc y
      refine ⟨b • p f, ?_, fun ψ hψ ↦ ?_⟩
      · rw [map_smul, hp, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      · rw [map_smul, hψ, LinearMap.liftBaseChange_tmul]
    | add x y hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb],
        fun ψ hψ ↦ by rw [map_add (f := _), map_add (f := _), ha' ψ hψ, hb' ψ hψ]⟩
  refine ⟨LinearMap.liftBaseChange R' l ∘ₗ e.symm.toLinearMap ∘ₗ c', ⟨fun f hf ↦ ?_, fun f ↦ ?_⟩,
    fun ψ hψ ↦ LinearMap.ext fun f ↦ ?_⟩
  · simp [hf]
  · simp [hp]
  · obtain ⟨f', h1, h2⟩ := key (e.symm (c' f))
    have h3 : ψ (f - f') = 0 := hψ.1 _ (by rw [map_sub, h1, LinearEquiv.apply_symm_apply, sub_self])
    rw [map_sub, sub_eq_zero] at h3
    rw [h3, h2 ψ hψ.2]
    rfl


set_option maxHeartbeats 1600000 in
theorem existsUnique_functional : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) → ∀ (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (l : GlobForm (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R'), ∃! ψ : Form (A'.hom ≫ 𝟙 (Sp R')) →ₗ[R'] R', (∀ f, cmpForm (A'.hom ≫ 𝟙 (Sp R')) f = 0 → ψ f = 0) ∧ ∀ f, ψ (m.pullForm f) = l (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)) f) := by
  intro hC hH R _ A _ g hab hdim R' _ _ A' φ hφ m l
  obtain ⟨e, he⟩ : ∃ e : R' ⊗[R] GlobForm (A.hom ≫ 𝟙 (Sp R)) ≃ₗ[R'] GlobForm (A'.hom ≫ 𝟙 (Sp R')),
      ∀ c, IsPullForm m.w c (e (1 ⊗ₜ c)) :=
    ((hH R A g hab hdim).2.2.2.2.2 R' A'.left A'.hom φ hφ).2.1
  have hp : ∀ f, GlobalTheory.LieDual.glob _ (m.pullForm f) = e (1 ⊗ₜ GlobalTheory.LieDual.glob _ f) := fun f ↦
    (_root_.GlobalTheory.CechDR.pairRes_injective φ (A'.hom ≫ 𝟙 (Sp R'))).2.1 ((GlobalTheory.LieDual.isPullForm_glob m f).symm.trans (he _))
  obtain ⟨ψ, hψ, hu⟩ := existsUnique_of_baseChange (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)))
    (GlobalTheory.LieDual.glob_surjective hC hH A g hab hdim) (GlobalTheory.LieDual.glob (A'.hom ≫ 𝟙 (Sp R')))
    m.pullForm e hp l
  exact ⟨ψ, ⟨fun f hf ↦ hψ.1 f (congrArg Subtype.val hf), hψ.2⟩,
    fun χ hχ ↦ hu χ ⟨fun f hf ↦ hχ.1 f (Subtype.ext hf), hχ.2⟩⟩

end GlobalTheory.BaseChangeForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem DefNode.inRange {X : Node} (h : DefNode D.R.m X) : X.InRange D.R.m := by
  rcases X with ⟨i, j⟩ | i | j
  · exact ⟨h.1, h.2.le⟩
  · exact h.elim
  · exact h

theorem DefNode.sigOK (G : GridData L sc) {X : Node} (h : DefNode D.R.m X) : (G.V X).SigOK := by
  rcases X with ⟨_ | i, j⟩ | i | j
  · obtain rfl := h.2
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e]
    exact D.sp.X'_sig
  · exact (G.isV (X := .grid (i + 1) j) ⟨h.1, h.2.le⟩ (by simp)).sigOK
  · exact h.elim
  · exact (G.isV (X := .top j) h (by simp)).sigOK

theorem vac_exists_of_defPair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (p : Pair T), GlobalTheory.FunObj.DefPair D.R.m p → ∃ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) f := by
  intro D T L sc G W U N p hp
  obtain ⟨h1, h2⟩ := hp.nodes
  rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
  · exact GlobalTheory.VacuumO.vacExists D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _
      (GlobalTheory.ChiGrid.WeilOver.sigOK_negSp (h2.sigOK G)) (h1.sigOK G)
      (fun τ => isCartanInv_neg (W.cart_is _ h2.inRange τ)) (fun τ => W.cart_is _ h1.inRange τ) _ _
      (isSelfDualC_neg (N.selfDual h2)) (N.selfDual h1)
  · exact hp.elim
  · exact hp.elim
  · exact GlobalTheory.VacuumO.vacExists D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ (h1.sigOK G) (h2.sigOK G)
      (fun τ => W.cart_is _ h1.inRange τ) (fun τ => W.cart_is _ h2.inRange τ) _ _ (N.selfDual h1) (N.selfDual h2)

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterNorm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConsEta
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infSign_ideleMap_finPartI (b : Neutral.B1.Ideles (maximalRealSubfield E)) :
    infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (GlobalTheory.Mem.Chr.finPartI _ b)) = 1 := by
  rw [infSign]
  change (MonoidHom.eval _) (∏ w, _) = 1
  rw [map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have : Units.map (GlobalTheory.IdeleNormChar.infEval w)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (GlobalTheory.Mem.Chr.finPartI _ b)) = 1 := by
    refine Units.ext ?_
    change (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E 1) w = 1
    rw [map_one]; rfl
  change unitDir (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom
    (Units.map (GlobalTheory.IdeleNormChar.infEval w) _)) = 1
  rw [this, map_one, map_one]

theorem eta_eq_infSign (hU : Unr E) (b : Neutral.B1.Ideles (maximalRealSubfield E))
    (hb : b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E)) :
    (GlobalTheory.GalOfCusp.quadChar E).1 b = infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  set f := GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b
  have h1 : ∀ v, ((b * f⁻¹ : Neutral.B1.Ideles _) : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1 := by
    intro v
    have e : f⁻¹ = GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b⁻¹ := (map_inv _ b).symm
    rw [e]
    exact congrArg (fun z : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) => z.2 v) b.mul_inv
  have h2 := _root_.GlobalTheory.EtaInfSign.quadChar_eq_infSign E _ h1
  have h3 := _root_.GlobalTheory.EtaFinUnit.quadChar_finPartI_eq_one E hU b hb
  have e1 : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 (b * f⁻¹) * (GlobalTheory.GalOfCusp.quadChar E).1 f := by
    rw [← map_mul, inv_mul_cancel_right]
  have e2 : infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (b * f⁻¹)) *
        infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E f) := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  rw [e1, e2, h2, h3, infSign_ideleMap_finPartI, mul_one]

end GlobalTheory.ConsEta


open GlobalTheory.ConsEta in
theorem GlobalTheory.ConsEta.exists_open_subgroup_eta_consistent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∃ (U : Subgroup (Neutral.B1.Ideles E)) (ψ : Neutral.B1.Ideles E →* ℂˣ), IsOpen (U : Set (Neutral.B1.Ideles E)) ∧
      Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (k : Eˣ) (b : Neutral.B1.Ideles (maximalRealSubfield E)) (u : Neutral.B1.Ideles E), u ∈ GlobalTheory.MuExist.nsUnits E →
        Neutral.B1.diagUnits E k * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b * u ∈ U →
        (GlobalTheory.GalOfCusp.quadChar E).1 b =
          ψ (Neutral.B1.diagUnits E k * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b * u) := by
  intro E _ _ _ hUnr
  obtain ⟨w0, hw0⟩ := _root_.GlobalTheory.SplitPlaceExists.exists_isSplitAt E
  obtain ⟨V, hVo, hV⟩ := _root_.GlobalTheory.RootOpen.exists_open_subgroup_no_roots E w0
  have hC : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) :=
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  refine ⟨GlobalTheory.Mem.Chr.unitIdl E ⊓ (GlobalTheory.Mem.Chr.unitIdl E).comap (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) ⊓
    V.comap (conjQuot E w0), infSign E, ?_, continuous_infSign, norm_infSign E, ?_⟩
  · exact (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.preimage hC)).inter
      (hVo.preimage (continuous_conjQuot w0))
  intro k b u hu hx
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  have hu1 := nsUnits_le_unitIdl hu
  have hCu := _root_.GlobalTheory.ConjUnit.ideleConj_mem_unitIdl E u hu1
  set C := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E with hCdef
  set I := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b with hI
  set c : Eˣ →* Eˣ := Units.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toMonoidHom with hc
  have hCx : C (Neutral.B1.diagUnits E k * I * u) = Neutral.B1.diagUnits E (c k) * I * C u := by
    rw [map_mul, map_mul, hI, _root_.GlobalTheory.ConjIdeleReal.ideleConj_ideleMap]
    congr 2
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele (maximalRealSubfield E) E k
  set x := Neutral.B1.diagUnits E k * I * u with hxdef
  set t : Eˣ := k / c k with ht
  have hdt : Neutral.B1.diagUnits E t = (x / C x) * (u / C u)⁻¹ := by
    rw [hCx, hxdef, ht, _root_.map_div]
    exact commGroup_div_eq_mul_div_mul_inv_div _ _ _ _ _
  have htu : Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E := by
    rw [hdt]; exact mul_mem (div_mem hx1 hx2) (inv_mem (div_mem hu1 hCu))
  have hnorm : ∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1 := by
    intro φ
    have h0 : φ (k : E) ≠ 0 := by simp
    have e : φ ((c k : Eˣ) : E) = starRingEnd ℂ (φ k) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k
    rw [ht, Units.val_div_eq_div_val, map_div₀, e, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]
  have htor := _root_.GlobalTheory.UnitTorsion.principal_unit_idele_torsion E t htu hnorm
  have hcqu := _root_.GlobalTheory.ConsEta.conjQuot_nsUnits_eq_one E w0 hw0 u hu
  have hmem : Units.map (algebraMap E (w0.adicCompletion E)).toMonoidHom t ∈ V := by
    have e1 : Units.map (algebraMap E (w0.adicCompletion E)).toMonoidHom t =
        Units.map (GlobalTheory.IdeleNormChar.finEval w0) (Neutral.B1.diagUnits E t) := Units.ext rfl
    have e2 : conjQuot E w0 x = Units.map (GlobalTheory.IdeleNormChar.finEval w0) (x / C x) := rfl
    have e3 : conjQuot E w0 u = Units.map (GlobalTheory.IdeleNormChar.finEval w0) (u / C u) := rfl
    rw [e1, hdt, map_mul, map_inv, ← e2, ← e3, hcqu, inv_one, mul_one]
    exact hx3
  have ht1 := hV t htor hmem
  have hck : c k = k := (div_eq_one.1 ht1).symm
  have hkF : (k : E) ∈ maximalRealSubfield E := by
    refine (IsCMField.complexConj_eq_self_iff E _).1 ?_
    exact congrArg Units.val hck
  set k' : (maximalRealSubfield E)ˣ := Units.mk0 ⟨(k : E), hkF⟩ (fun h => k.ne_zero (congrArg Subtype.val h)) with hk'
  have hdk : Neutral.B1.diagUnits E k =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (Neutral.B1.diagUnits (maximalRealSubfield E) k') := by
    refine (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele (maximalRealSubfield E) E k').trans ?_ |>.symm
    exact congrArg (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E) (Units.ext rfl)
  set b' := Neutral.B1.diagUnits (maximalRealSubfield E) k' * b with hb'
  have hxb : x = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' * u := by
    rw [hxdef, hdk, hb', map_mul]
  have hηb : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 b' := by
    rw [hb', map_mul, (GlobalTheory.GalOfCusp.quadChar E).2.2 k', one_mul]
  have hb'E : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' ∈ GlobalTheory.Mem.Chr.unitIdl E := by
    have : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' = x * u⁻¹ := by rw [hxb, mul_inv_cancel_right]
    rw [this]; exact mul_mem hx1 (inv_mem hu1)
  rw [hηb, eta_eq_infSign hUnr b' (_root_.GlobalTheory.UnitDown.unit_down E b' hb'E), hxb, (infSign E).map_mul _ u, infSign_nsUnits hu, mul_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionModIdealPowBoxProductEqBoxProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionModIdealPow_boxProduct_eq_boxProduct : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)), Function.Bijective (q₁.prod q₂) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)) (e k : ℕ), (U.gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → (U.gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → (∀ x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left) (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x))) → BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → ∀ (σ : H0 U.LG.L k) (σ₁ : H0 U₁.LG.L k) (σ₂ : H0 U₂.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (f₁ : ∀ α : D₁.toPre.X, D₁.toPre.SecB k α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB k α), IsBoxSec wL (fst G₁ G₂).left (snd G₁ G₂).left σ σ₁ σ₂ → (∀ α, IsBoxSec wM p₁.left p₂.left (f α) (f₁ (q₁ α)) (f₂ (q₂ α))) → U₁.ExpandsAt e k σ₁ f₁ → U₂.ExpandsAt e k σ₂ f₂ → U.ExpandsAt e k σ f := by
  first | exact @GlobalTheory.ProdUnif.expandsAt_boxProd | exact GlobalTheory.ProdUnif.expandsAt_boxProd | (intros; apply GlobalTheory.ProdUnif.expandsAt_boxProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibresAbelianOfPsiUnitOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UnifFibre

theorem fibres_abelian_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G :=
  fun R _ _ _ hB D A G _ _ hG U W hW => _root_.GlobalTheory.Mum.PsiUnitAb.subset_abLocus_of_psiUnitOn R hB D A G hG U W hW

end GlobalTheory.Mum.UnifFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleAwayFromPEqZeroOfDivisibleCoprime
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped RestrictedProduct

namespace GlobalTheory.AfPZero

theorem natCast_eq_algebraMap (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) (n : ℤ) :=
  (map_natCast (algebraMap ℤ (v.adicCompletion ℚ)) n).symm

theorem valued_natCast (v : HeightOneSpectrum ℤ) (n : ℕ) :
    Valued.v (n : v.adicCompletion ℚ) = v.intValuation (n : ℤ) := by
  rw [natCast_eq_algebraMap]
  have := valuedAdicCompletion_eq_valuation (K := ℚ) v (n : ℤ)
  rw [← valuation_of_algebraMap (K := ℚ)]
  exact this

theorem eq_zero_of_dvd (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ)
    (h : ∀ k : ℕ, ∃ n : ℕ, (n : ℤ) ∈ v.asIdeal ^ k ∧
      ∃ y ∈ v.adicCompletionIntegers ℚ, x = (n : v.adicCompletion ℚ) * y) : x = 0 := by
  by_contra hx
  have hγ : Valued.v x ≠ 0 := by simpa using hx
  set L : ℤ := log (Valued.v x) with hL
  obtain ⟨n, hn, y, hy, hxe⟩ := h ((-L).toNat + 1)
  have h1 : Valued.v x ≤ exp (-(((-L).toNat + 1 : ℕ) : ℤ)) := by
    rw [hxe, map_mul]
    calc Valued.v (n : v.adicCompletion ℚ) * Valued.v y ≤ Valued.v (n : v.adicCompletion ℚ) * 1 :=
          by gcongr; exact (mem_adicCompletionIntegers ℤ ℚ v).1 hy
      _ = v.intValuation (n : ℤ) := by rw [_root_.mul_one, valued_natCast]
      _ ≤ _ := (intValuation_le_pow_iff_mem v _ _).2 hn
  rw [← exp_log hγ, ← hL] at h1
  have h2 := exp_le_exp.1 h1
  omega

open GlobalTheory.LKTrip GlobalTheory.LKGeo

theorem exists_prime (p : ℕ) [Fact p.Prime] (v : AwayP p) :
    ∃ l : ℕ, l.Prime ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
  set q : ℤ := Submodule.IsPrincipal.generator v.1.asIdeal with hq
  have hspan : v.1.asIdeal = Ideal.span {q} := (Submodule.IsPrincipal.span_singleton_generator v.1.asIdeal).symm
  have hq0 : q ≠ 0 := by
    intro h0
    apply v.1.ne_bot
    rw [hspan, h0, Ideal.span_singleton_eq_bot]
  have hqp : Prime q := by
    have := v.1.isPrime
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hq0).1 this
  have hl : q.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan' : v.1.asIdeal = Ideal.span {((q.natAbs : ℕ) : ℤ)} := by
    rw [hspan, Int.span_natAbs]
  refine ⟨q.natAbs, hl, (Nat.coprime_primes hl (Fact.out)).2 ?_, ?_⟩
  · intro he
    apply v.2
    rw [hspan', he]
  · rw [hspan']
    exact Ideal.subset_span rfl

theorem main : ∀ (p : ℕ) [Fact p.Prime] (α : AfP p),
    (∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = n • β) → α = 0 := by
  intro p _ α h
  have hloc : ∀ v : AwayP p, AfP.eval v α = 0 := by
    intro v
    obtain ⟨l, hl, hlp, hlv⟩ := exists_prime p v
    apply eq_zero_of_dvd v.1
    intro k
    obtain ⟨β, hβ, hαβ⟩ := h (l ^ k) (pow_pos hl.pos k) (Nat.Coprime.pow_left k hlp)
    refine ⟨l ^ k, by push_cast; exact Ideal.pow_mem_pow hlv k, AfP.eval v β, hβ v, ?_⟩
    rw [hαβ, map_nsmul, nsmul_eq_mul]
  exact Subtype.ext (funext fun v => hloc v)

end GlobalTheory.AfPZero
end
end

