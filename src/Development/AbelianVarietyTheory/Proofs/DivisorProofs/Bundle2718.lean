module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralDataFramedTorsionPointTorusExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.LiesData

theorem isPullF_gtExt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' : Type} [Field F]
    [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    {g' : GtPt D (𝟙_ (Over (Sp R)))} {g₁ : GtPtF D F} (H : GtPt.IsPullF F (toUnit (TF (R := R) F)).left g' g₁) :
    GtPt.IsPullF F' (toUnit (TF (R := R) F')).left g' (GlobalTheory.TorusExt.gtExt D f hf g₁) := by
  have e : GlobalTheory.TorusExt.extMap f hf ≫ toUnit (TF (R := R) F) = toUnit (TF (R := R) F') := comp_toUnit _
  refine (GlobalTheory.FieldRestrictionTest.isPullF_iff (toUnit (TF (R := R) F')) g' _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · have b₁ : g₁.b = toUnit (TF (R := R) F) ≫ g'.b :=
      ((GlobalTheory.FieldRestrictionTest.isPullF_iff (toUnit (TF (R := R) F)) g' g₁).1 H).1
    exact (GlobalTheory.TorusExt.gtExt_b f hf g₁).trans ((congrArg (GlobalTheory.TorusExt.extMap f hf ≫ ·) b₁).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g'.b) e)))
  · refine (GlobalTheory.TorusExt.gtExt_val f hf g₁ χ hJ).trans ((val_corr hJ (H.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_))
    have e' : (GlobalTheory.TorusExt.extMap f hf).left ≫ (toUnit (TF (R := R) F)).left = (toUnit (TF (R := R) F')).left := by
      rw [← Over.comp_left, e]
    rw [← e']

theorem exists_data : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∃ (h : (𝟙_ (Over (Sp V))) ⟶ G) (g' : GtPt D.toPre (𝟙_ (Over (Sp V)))) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h).left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, (g'.b).left] (DegPre.lineε 1))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g' ∧ IntTerm.Ext U.toUnifPre x h ∧ GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g' g ∧ f.IsGen ∧ t.IsGen ∧ ∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U.toUnifPre h g'.b f t e := by
  intro V _ _ _ hCN D A G _ _ hG U w₀ hw₀ N hN g w x fr hg hw hfr hlies
  haveI : CharZero V := hCN.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hB := D.tau_bimult
  obtain ⟨p, hy, rfl, hp⟩ :=
    GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver V hCN D A G hG U w₀ hw₀ N hN _ w x fr hg hw hfr hlies
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap _ _ := RingHom.comp_id _
  obtain ⟨p', hp', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB _ hf p
  have hq := (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN hp' x).1 hp
  obtain ⟨h, g', -, -, hform, hext, hpull⟩ := GlobalTheory.Poinc.TorsLift.lift V hCN D A G hG U N hN x _ _ rfl (hp'.1.trans hy) hq
  have eg : p'.g = GlobalTheory.TorusExt.gtExt D.toPre _ hf p.g :=
    (GlobalTheory.TorusExt.eq_gtExt_iff _ hf _ _).2 hp'.2
  rw [eg] at hpull
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) g'
  have e : g₁ = p.g := GlobalTheory.Balanced.gtExt_injective _ hf D.toPre
    (GlobalTheory.FieldRestrictionTest.isPullF_unique (isPullF_gtExt _ hf hg₁) hpull)
  obtain ⟨i, hi⟩ := exists_chart U.LG.isLB (h.left (cpt V))
  obtain ⟨f, hf₀⟩ := GlobalTheory.TorsFrameInt.exists_gen_of_chart U.LG.isLB (K := Fin 1) (fun _ => h.left) (fun _ => 1)
    (fun _ => i) (fun y => Set.mem_iInter.2 fun _ => (top_le_iff_cpt (A := V) h.left _).2 hi (show y ∈ ⊤ from trivial))
  obtain ⟨t, ht, hrel⟩ := GlobalTheory.Poinc.IntEval.exists_integral_frame V hCN D A G U.toUnifPre h g' hform f hf₀
  exact ⟨h, g', f, t, hform, hext, e ▸ hg₁, hf₀, ht, hrel⟩

end GlobalTheory.Poinc.Sep.LiesData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsogenyKernelFiniteAlgebraFinrankEqDegree
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

open CategoryTheory.Limits MonoidalCategory

theorem one_left_eq {k : Type} [Field k] {X : Over (Sp k)} [MonObj X] (T : Over (Sp k)) :
    (1 : T ⟶ X).left = T.hom ≫ (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ X).left := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left]
  rfl

theorem isoSpec_hom_comp_spec {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (g : X ⟶ Spec R) :
    X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop) = g := by
  rw [Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem exists_kerPow_zero_finrank_eq_deg : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B), IsIsogeny f →
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f 0 H i ∧ Module.finrank k H = deg f := by
  intro k _ A B f hf
  obtain ⟨-, hflat, -, hrank⟩ := isogeny_flat_finrank k A B f hf
  haveI : IsFinite f.hom.left := hf.1
  haveI := hflat
  let e : Sp k ⟶ B.X.left := (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ B.X)
  let P := pullback f.hom.left e
  let g : P ⟶ Sp k := pullback.snd f.hom.left e
  haveI : IsAffine P := isAffine_of_isAffineHom g
  let H : Type := Γ(P, ⊤)
  letI : Algebra k H := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom.toAlgebra
  have hg : P.isoSpec.hom ≫ spMap (algebraMap k H) = g := isoSpec_hom_comp_spec g
  have hig : P.isoSpec.inv ≫ g = spMap (algebraMap k H) := by rw [← hg, Iso.inv_hom_id_assoc]
  have hw : (P.isoSpec.inv ≫ pullback.fst f.hom.left e) ≫ A.X.hom = spMap (algebraMap k H) := by
    rw [← Over.w f.hom, Category.assoc, pullback.condition_assoc, he, Category.comp_id, hig]
  let i : ptOver k H ⟶ A.X := Over.homMk (P.isoSpec.inv ≫ pullback.fst f.hom.left e) hw
  have hi : i.left = P.isoSpec.inv ≫ pullback.fst f.hom.left e := rfl
  refine ⟨H, inferInstance, inferInstance, i, ⟨⟨?_, pow_zero i⟩, ?_⟩, ?_⟩
  · ext1
    rw [Over.comp_left, one_left_eq, hi, Category.assoc, pullback.condition, ← Category.assoc, hig]
    rfl
  · intro R _ _ x hx _
    have hx' : x.left ≫ f.hom.left = spMap (algebraMap k R) ≫ e := by
      have := congrArg Over.Hom.left hx
      rw [Over.comp_left, one_left_eq] at this
      exact this
    let l : Sp R ⟶ P := pullback.lift x.left (spMap (algebraMap k R)) hx'
    obtain ⟨φ0, hφ0⟩ := Spec.map_surjective (l ≫ P.isoSpec.hom)
    have hc : CommRingCat.ofHom (algebraMap k H) ≫ φ0 = CommRingCat.ofHom (algebraMap k R) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ0, Category.assoc, hg]
      exact pullback.lift_snd _ _ _
    let φ : H →ₐ[k] R :=
      { φ0.hom with commutes' := fun c => congrArg (fun u => u.hom c) hc }
    have hφ : spMap φ.toRingHom = l ≫ P.isoSpec.hom := hφ0
    refine ⟨φ, ?_, fun ψ hψ => ?_⟩
    · change spMap φ.toRingHom ≫ i.left = x.left
      rw [hφ, hi, Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.lift_fst _ _ _
    · have h1 : spMap ψ.toRingHom ≫ P.isoSpec.inv = l := by
        apply pullback.hom_ext
        · rw [Category.assoc, ← hi]
          exact hψ.trans (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, hig, pullback.lift_snd]
          change Spec.map _ ≫ Spec.map _ = Spec.map _
          rw [← Spec.map_comp]
          congr 1
          ext c
          exact ψ.commutes c
      have h2 : spMap ψ.toRingHom = spMap φ.toRingHom := by
        rw [hφ, ← h1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have h3 := Spec.map_injective h2
      exact AlgHom.ext fun a => congrArg (fun u => u.hom a) h3
  · haveI : IsFinite (spMap (algebraMap k H)) := by rw [← hig]; infer_instance
    haveI : Flat (spMap (algebraMap k H)) := by rw [← hig]; infer_instance
    haveI : Module.Finite k H := by
      rw [← RingHom.finite_algebraMap]
      exact (IsFinite.SpecMap_iff _).1 ‹_›
    let pt : Sp k := IsLocalRing.closedPoint k
    have h1 := Scheme.Hom.finrank_pullback_snd f.hom.left e pt
    rw [hrank] at h1
    rw [← h1]
    change _ = Scheme.Hom.finrank g pt
    rw [← hg, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl

end GlobalTheory.AV.KerPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianLiftLieSquareZeroHarrisTaylor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem exists_lagrangian_lift_lie : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (φ : LinearMap.BilinForm C H), (∀ x y, φ x y = -φ y x) → Function.Bijective φ → (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ E : Submodule C H, (∃ M : Submodule C H, IsCompl E M) ∧ E ⊔ I • ⊤ = F ∧ (∀ (c : D.O), ∀ x ∈ E, ρ c x ∈ E) ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ E → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E := by
  intro p _ D R _ b C _ _ _ I hI tR H _ _ _ _ ρ hproj φ hskew hbij hadj F hIF hFO hFiso hFlag hE' hLie
  obtain ⟨e, he, hρe, hφe, hωe, ⟨v, hv, hωk⟩, hestab⟩ := GlobalTheory.T.exists_idempotent_imaginaryQuadratic_eigen_crystal p D R b C tR H ρ φ hadj
  have hFe := hestab F hFO
  have hLie' : ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F := by
    rintro d ⟨y, rfl⟩
    exact hLie _ (by rw [hωe, sub_self]; exact F.zero_mem)
  have hcore : ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
    by_cases hp : IsUnit (p : C)
    · exact GlobalTheory.T.exists_liftSummand_lie_residueCharZero p D R b C I hI hp tR H ρ hproj e he hρe hωe F hIF hFO hFe hE' hLie'
    · exact GlobalTheory.T.exists_lieCondition_summand_residueCharP p D R b C I hI ((IsLocalRing.mem_maximalIdeal _).2 hp) tR H ρ hproj e he hρe hωe F hIF hFO hFe hE' hLie'
  obtain ⟨G, M, hGM, hGMr, hGO, hGF, hGLie⟩ := hcore
  obtain ⟨E, hEc, hEe, hEF, hEiso, hEO, hEst⟩ := GlobalTheory.T.lagrangianCompletion_sup_ideal_smul_eq C I H D.O ρ (fun a => (D.star a).unop) φ e he hρe hskew (fun a => D.star_star a) hadj hφe hbij F hIF hFiso hFlag hFe G M hGM hGMr hGO hGF
  refine ⟨E, hEc, hEF, hEO, hEiso, ?_⟩
  intro d hd
  have hGE : G ≤ E := hEe ▸ inf_le_left
  set k := d - e d with hkdef
  have hek : e k = 0 := by
    have := LinearMap.congr_fun he d
    simp only [Module.End.mul_apply] at this
    simp [hkdef, this]
  have hkE : k ∈ E := by
    set x := ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d with hx
    have h1 : x - e x ∈ E := E.sub_mem hd (hEst _ hd)
    have h2 : x - e x = ρ (algebraMap (𝓞 D.F) D.O D.ω) k - tR b.ρ • k := by
      have hc := LinearMap.congr_fun (hρe (algebraMap (𝓞 D.F) D.O D.ω)) d
      simp only [Module.End.mul_apply] at hc
      simp only [hx, hkdef, map_sub, LinearMap.map_smul, smul_sub, hc]
      abel
    rw [h2, hωk k hek] at h1
    obtain ⟨u, rfl⟩ := hv
    have := E.smul_mem (↑u⁻¹ : C) h1
    rwa [smul_smul, Units.inv_mul, one_smul] at this
  obtain ⟨w, hw, hdw⟩ := hGLie (e d) ⟨d, rfl⟩
  refine ⟨w, fun i c => hGE (hw i c), ?_⟩
  have : d - ∑ i, w i = (e d - ∑ i, w i) + k := by rw [hkdef]; abel
  rw [this]
  exact E.add_mem (hGE hdw) hkE

end GlobalTheory.HTSummand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalArchIntegralChernPower
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixFun

theorem exists_linear_of_rel {α V : Type} [AddCommGroup V] [Module ℝ V] (v : α → V) (f : α → ℝ)
    (h : ∀ c : α →₀ ℝ, Finsupp.linearCombination ℝ v c = 0 → Finsupp.linearCombination ℝ f c = 0) :
    ∃ Ψ : V →ₗ[ℝ] ℝ, ∀ a, Ψ (v a) = f a := by
  set A := Finsupp.linearCombination ℝ v
  set F := Finsupp.linearCombination ℝ f
  have hker : LinearMap.ker A ≤ LinearMap.ker F := fun c hc => h c hc
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (((LinearMap.ker A).liftQ F hker).comp A.quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, fun a => ?_⟩
  have e1 : v a = A (Finsupp.single a 1) := by simp [A]
  have e2 := LinearMap.congr_fun hg ⟨A (Finsupp.single a 1), LinearMap.mem_range_self _ _⟩
  rw [e1]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply] at e2
  rw [e2]
  simp [F]

end GlobalTheory.MixFun

namespace GlobalTheory.MixFun

theorem exists_functional_archInt : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (e : ℕ) (ι : Type) [Fintype ι] (L : ι → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb L n).ArchIntegrable M e hr) → ∃ Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb L n).archInt M e hr := by
  intro k _ Y _ q hq e ι _ L M r hr hint
  classical
  have := hq.finite
  haveI : Finite (k →+* ℂ) := .of_equiv _ (RingHom.equivIntAlgHom k ℂ).symm
  letI := Fintype.ofFinite (k →+* ℂ)
  refine GlobalTheory.MixFun.exists_linear_of_rel (fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ e)
    (fun n => (comb L n).archInt M e hr) ?_
  intro c hc
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
  simp only [HermLB.archInt, finsum_eq_sum_of_fintype, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [← Finset.sum_coe_sort c.support]
  refine GlobalTheory.ChernLinRel.sum_chernInt_eq_zero k Y q hq.isProjOver σ e c.support (fun j => c j)
    (fun j => comb L j) ?_ _ _ (fun j => hint j σ)
  intro ch y hy
  have key : ∀ n : ι → ℤ, ch.chernDens ((comb L n).φ σ) y = e.factorial / Real.pi ^ e *
      (Matrix.det (∑ l, ((n l : ℝ) : ℂ) • ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)).re := by
    intro n
    rw [AlgChart.chernDens, GlobalTheory.Mean4O.ReadsProj.hess_comb L n σ ch hy _ (mem_pick _ y) _ (fun l => mem_pick _ y)]
  simp only [key]
  have hrel : ∑ j : c.support, MvPolynomial.C (c j) *
      (∑ i, MvPolynomial.C ((j.1 i : ℝ)) * MvPolynomial.X i : MvPolynomial ι ℝ) ^ e = 0 := by
    rw [← hc, ← Finset.sum_coe_sort c.support]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.C_mul']
    rfl
  have h0 := GlobalTheory.MxDet.re_det_relation ι c.support e (fun j => c j) (fun j i => (j.1 i : ℝ)) hrel
    (fun l => ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)
  simp_rw [mul_left_comm _ ((e.factorial : ℝ) / Real.pi ^ e)]
  rw [← Finset.mul_sum, h0, mul_zero]

end GlobalTheory.MixFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNearGaloisQuotient
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_near_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ N : Near (spMap ρ) G', N.Law ∧ ∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ) := by
  intro R _ _ _ hR R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS U' a
  obtain ⟨H, hH, hall, hc, horb⟩ := _root_.GlobalTheory.Mum.exists_invariant_nbhd_closedFibre R hR R' ρ hF hG D D' hD A' G' hS U' a
  obtain ⟨X, π, hX, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.Mum.exists_galois_quotient R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Mum.GlueNear.glue_near R hR R' ρ hF hG D D' hD A' G' hS U' a H hH hall hc X π hX h1 h2 h3 h4 h5
    (_root_.GlobalTheory.Mum.quotient_smooth_and_baseChange_iso R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb X π hX h1 h2 h3 h4 h5)
  exact ⟨N, _root_.GlobalTheory.Mum.law_of_galAct_invariant R hR R' ρ hF hG D D' hD A' G' hS U' a N hN, hN⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdThetaMapOnNormalCharZeroAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_nbhd_thetaMap : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    ∀ (U : X.affineOpens), IsDomain Γ(X, U) → IsNoetherianRing Γ(X, U) → IsIntegrallyClosed Γ(X, U) → CharZero Γ(X, U) →
    ∀ x ∈ (U : X.Opens), ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧ ThMap G L ρ m (W.ι ≫ q) h := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hu hn hP U hD hN hI hC x hx
  let R : Type := Γ(X, U)
  have hU : IsAffineOpen (U : X.Opens) := U.2

  let β : o →+* R := (Spec.preimage (hU.fromSpec ≫ s)).hom
  have hβ : spMap β = hU.fromSpec ≫ s := Spec.map_preimage _
  let p : PrimeSpectrum R := hU.primeIdealOf ⟨x, hx⟩
  obtain ⟨r, hr, θ, hθ⟩ := _root_.GlobalTheory.UMin.exists_basicOpen_genSec_fibres S G L hL g R (hU.fromSpec ≫ q) (hP R hU.fromSpec) p
  let Rr := Localization.Away r
  have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hle : Submonoid.powers r ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  haveI : IsDomain Rr := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rr := IsLocalization.isNoetherianRing (Submonoid.powers r) Rr hN
  haveI : IsIntegrallyClosed Rr := isIntegrallyClosed_of_isLocalization Rr _ hle
  have hinj : Function.Injective (algebraMap R Rr) := IsLocalization.injective Rr hle
  haveI : CharZero Rr := charZero_of_injective_algebraMap hinj
  let β' : o →+* Rr := (algebraMap R Rr).comp β
  have hu' : IsUnit (m : Rr) := by
    have := hu.map β'
    simpa using this
  have hP' : PolFib G L g (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) := by
    have := hP Rr (spMap (algebraMap R Rr) ≫ hU.fromSpec)
    simpa [Category.assoc] using this
  obtain ⟨f, hf, hT⟩ := _root_.GlobalTheory.UMin.MapAff.theta_map_aff S G L ρ hL hρ g m n o Rr β' (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) θ
    hmo hm3 hu' hn hP' hθ

  let Wo : X.Opens := X.basicOpen r
  have hW : IsAffineOpen Wo := hU.basicOpen r
  have hxW : x ∈ Wo := by
    have h1 : hU.fromSpec p ∈ X.basicOpen r := by
      show p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
      rw [hU.fromSpec_preimage_basicOpen]; exact hr
    rwa [hU.fromSpec_primeIdealOf] at h1
  have hle' : Wo ≤ (U : X.Opens) := X.basicOpen_le r
  let res : R →+* Γ(X, Wo) := (X.presheaf.map (homOfLE hle').op).hom
  have hres : IsUnit (res r) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace r
  let lft : Rr →+* Γ(X, Wo) := IsLocalization.Away.lift r hres
  have hlft : lft.comp (algebraMap R Rr) = res := IsLocalization.Away.lift_comp r hres
  let e : Wo.toScheme ⟶ Sp Rr := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lft)
  have he : e ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec = Wo.ι := by
    have : Spec.map (CommRingCat.ofHom lft) ≫ spMap (algebraMap R Rr) =
        Spec.map (X.presheaf.map (homOfLE hle').op) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlft]
      rfl
    simp only [e, Category.assoc]
    rw [reassoc_of% this, hU.map_fromSpec hW, hW.isoSpec_hom_fromSpec]
  refine ⟨Wo, e ≫ f, hxW, ?_, ?_⟩
  · rw [Category.assoc, hf, show spMap β' = spMap (algebraMap R Rr) ≫ spMap β from by
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl, hβ, ← he]
    simp only [Category.assoc]
  · intro K _ x' c hc
    have hc' : HasTh G L ρ m ((x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) c := by
      have : (x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q = x' ≫ Wo.ι ≫ q := by
        rw [← he]; simp only [Category.assoc]
      rw [this]; exact hc
    have := hT K (x' ≫ e) c hc'
    simpa [Category.assoc] using this

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductSmallTwistedFunctionalEqnFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_product_small_twistedFunctionalEqn_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → TFE h h' f → TFE h h' g → ∃ F : ∀ β, SecT D.toPre a n'' j'' β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) n j) (τ' : SecE U.toUnifPre (b e) n' j'), TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → ∃ τ'' : SecE U.toUnifPre (b e) n'' j'', (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  first | exact @GlobalTheory.TwFam.exists_prod_family | exact GlobalTheory.TwFam.exists_prod_family | (intros; apply GlobalTheory.TwFam.exists_prod_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackIntegralExpansionFormalEndomorphisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_integralExpansion_formalEndomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k : ℕ) (σ : H0 U.LG.L k) (f : IntFam (maximalIdeal R) D.toPre k), (∀ e, U.ExpandsAt e k σ f.f) → ∃ ρ : ∀ β, SecT D.toPre a 0 k β, Small (maximalIdeal R) (w := id) ρ ∧ TFE h h' ρ ∧ ∀ e, ∃ τ : SecE U.toUnifPre (b e) 0 k, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') ∧ TExp U.toUnifPre τ (w := id) ρ := by
  first | exact @GlobalTheory.TwFam.exists_pull_expansion | exact GlobalTheory.TwFam.exists_pull_expansion | (intros; apply GlobalTheory.TwFam.exists_pull_expansion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacterStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.exists_pushout_torsor_nTorsion_character :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      (n : R) = 0 → HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b →
        ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧
          ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), (x ^ n : Pt A D) = 1 →
            GlobalTheory.PtExt.chi n g D x = b D x :=
  @GlobalTheory.PtExt.exists_pushout_torsor
end

