module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeIffPulledBackIdentity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem tjAt_pull_one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have e := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at e
  have hxx : x₀ * x₀ = x₀ := by
    ext
    exact e
  have h1 : x₀ = 1 := mul_eq_right.mp hxx
  exact congrArg Over.Hom.left h1

theorem tjAt_iff_tjAt_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (TjAt r w j o ψ t ↔ TjAt r w j o₁ ψ₁ (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ r w j hB hψ
  have key : ∀ (k : Type) [Field k] (σ : Sp k ⟶ T),
      ((∀ g : Over.mk (σ ≫ t) ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
        Nat.card {g : Over.mk (σ ≫ t) ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)) ↔
      ((∀ g : Over.mk σ ⟶ o₁.A, g ≫ ψ₁ = 1 → (∃ e : ℕ, KilledBy o₁ (uIdeal D r ^ e) g) → KilledBy o₁ w g) ∧
        Nat.card {g : Over.mk σ ⟶ o₁.A // g ≫ ψ₁ = 1 ∧ KilledBy o₁ w g} = Ideal.absNorm w ^ (D.m * j)) := by
    intro k _ σ
    obtain ⟨e, he, -⟩ := m.exists_ptEquiv (Over.mk (σ ≫ t)) σ rfl
    have hker : ∀ g : Over.mk σ ⟶ o₁.A, e g ≫ ψ = 1 ↔ g ≫ ψ₁ = 1 := by
      intro g
      have h1 : (e g ≫ ψ).left = (g ≫ ψ₁).left ≫ θ := by
        rw [Over.comp_left, he, Category.assoc, hψ, Over.comp_left, Category.assoc]
      have h2 : (1 : Over.mk (σ ≫ t) ⟶ B).left = (1 : Over.mk σ ⟶ B₁).left ≫ θ :=
        (tjAt_pull_one_left hB (Over.mk σ)).symm
      constructor
      · intro h
        apply Over.OverMorphism.ext
        apply hB.1.hom_ext
        · rw [← h1, ← h2, h]
        · rw [Over.w, Over.w]
      · intro h
        apply Over.OverMorphism.ext
        rw [h1, h2, h]
    have hact : ∀ (g : Over.mk σ ⟶ o₁.A) (c : D.O), e g ≫ o.act.act c = e (g ≫ o₁.act.act c) := fun g c => by
      ext
      rw [Over.comp_left, he, he, Over.comp_left, Category.assoc, Category.assoc, m.act]
    have hkill : ∀ (v : Ideal (𝓞 D.F)) (g : Over.mk σ ⟶ o₁.A), KilledBy o v (e g) ↔ KilledBy o₁ v g :=
      fun v g => forall₂_congr fun a _ => by rw [hact]; exact map_eq_one_iff _ e.injective
    refine and_congr ⟨fun h g hg hu => ?_, fun h g hg hu => ?_⟩ ?_
    · rw [← hkill]
      rw [← hker] at hg
      obtain ⟨n, hn⟩ := hu
      exact h (e g) hg ⟨n, (hkill _ g).2 hn⟩
    · obtain ⟨g₀, rfl⟩ := e.surjective g
      rw [hkill]
      rw [hker] at hg
      obtain ⟨n, hn⟩ := hu
      exact h g₀ hg ⟨n, (hkill _ g₀).1 hn⟩
    · rw [Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv fun g₀ => by
        change _ ↔ e g₀ ≫ ψ = 1 ∧ KilledBy o w (e g₀)
        rw [hker, hkill]).symm)]
  constructor
  · intro h k _ _ _ x₁ _
    exact (key k x₁).1 (h k (x₁ ≫ t) ⟨x₁, rfl⟩)
  · intro h k _ _ _ x ⟨σ, hσ⟩
    subst hσ
    exact (key k σ).2 (h k σ ⟨σ, Category.comp_id σ⟩)

end GlobalTheory.UPel.HT.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGeneratorLambdaPullbackComplexPointOfEqOnOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointDesc

theorem hasGen_of_comp {X Y Z : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (h : Z ⟶ Y) (m : Z ⟶ X)
    (hm : h ≫ f = m) (H : HasGen (L.pull f)) : HasGen (L.pull m) := by
  obtain ⟨t, ht⟩ := H
  subst hm
  exact ⟨LB.pullGen L (fun _ : PUnit => f) (fun _ => 1) t h,
    DVR.pullGen_isGen L (fun _ : PUnit => f) (fun _ => 1) t ht h⟩

theorem hasGen_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (h : Z ⟶ Y)
    (H : HasGen (L.pull (h ≫ f))) : HasGen ((L.pull f).pull h) := by
  obtain ⟨t, ht⟩ := H
  exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hL _) (pull_isLB (pull_isLB hL f) h)
    (GlobalTheory.FamRep.lbIso_pull_pull hL f h).symm t ht

theorem hasGen_lam_pull_of_eq_on_open : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A) (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (t : T.left), t ∈ U →
      U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) := by
  intro A _ hA M hM T x U y t ht hU H
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _

  let x0 : U.toScheme := ⟨t, ht⟩
  let K : Type := U.toScheme.residueField x0
  letI : Field K := inferInstanceAs (Field (U.toScheme.residueField x0))
  let q : Sp K ⟶ U.toScheme := U.toScheme.fromSpecResidueField x0
  let p : Sp K ⟶ T.left := q ≫ U.ι
  let φ := Spec.preimage (p ≫ T.hom)
  let β : ℂ →+* K := φ.hom
  have hβ : spMap β = p ≫ T.hom := Spec.map_preimage _
  let Tk : Over (Sp ℂ) := Over.mk (spMap β)
  let pk : Tk ⟶ T := Over.homMk p hβ.symm
  have hxy : pk ≫ x = toUnit Tk ≫ y := by
    ext1
    simp only [Over.comp_left, Over.homMk_left, pk, Over.toUnit_left]
    show (q ≫ U.ι) ≫ x.left = Tk.hom ≫ y.left
    simp only [Tk, Over.mk_hom, hβ, p, Category.assoc, hU]
  let e : A ⟶ A ⊗ 𝟙_ (Over (Sp ℂ)) := lift (𝟙 A) (toUnit A)
  let g := lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)
  have sq : (A ◁ pk) ≫ lift (fst A T) (snd A T ≫ x) = fst A Tk ≫ e ≫ g := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [e, g]
    · simp only [Category.assoc, lift_snd, e, g, lift_fst_assoc, lift_snd_assoc]
      rw [whiskerLeft_snd_assoc, hxy, ← Category.assoc, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
  have H₁ : HasGen ((abelian₂ A M).pull ((fst A Tk).left ≫ (e ≫ g).left)) :=
    hasGen_of_comp _ (A ◁ pk).left _ (by rw [← Over.comp_left, sq, Over.comp_left]) H
  have H₂ := hasGen_pull_pull hL (e ≫ g).left (fst A Tk).left H₁
  have hpb : IsPullback (fst A Tk).left (snd A Tk).left A.hom (spMap β) := IsPullback.of_hasPullback _ _
  obtain ⟨u, hu⟩ := GlobalTheory.FieldTriv.exists_gen_of_field_extension ℂ K β A hA _ (fst A Tk).left (snd A Tk).left hpb
    ((abelian₂ A M).pull (e ≫ g).left) (pull_isLB hL _) H₂
  refine hasGen_of_comp (e ≫ g).left (fst A (𝟙_ (Over (Sp ℂ)))).left _ ?_ ⟨u, hu⟩
  rw [← Over.comp_left]
  congr 1
  rw [← Category.assoc]
  have : fst A (𝟙_ (Over (Sp ℂ))) ≫ e = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [e]
    · simp only [e, Category.assoc, lift_snd, Category.id_comp]
      exact toUnit_unique _ _
  rw [this, Category.id_comp]

end GlobalTheory.PointDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOfSubsingleton
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem has_of_subsingleton : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ D : DegData R (maximalIdeal R), Subsingleton D.toPre.X → Has D := by
  intro R _ _ _ hR D hX
  haveI : IsNoetherianRing R := hR.1
  let A : PolAV (Spec (CommRingCat.of (FractionRing R))) := GlobalTheory.AmpleSpecialisation.baseChange D.toPre.P (jK R)
  let eA : (Over.pullback (jK R)).obj D.toPre.P.A ≅ A.A := by
    with_unfolding_all exact Iso.refl _
  have hA : IsMonHom eA.hom := by
    refine ⟨?_, ?_⟩
    · exact Category.comp_id _
    · show μ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ
      rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
      rfl
  have hw : ∃ w : LB.Iso (A.L.pull eA.hom.left) (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK R))), w.IsGen := by
    obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.toPre.P.isLB (pullback.fst D.toPre.P.A.hom (jK R)))
    exact ⟨GlobalTheory.PtTie.isoFromPullId w, GlobalTheory.PtTie.isoFromPullId_isGen hw⟩
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  exact ⟨D.toPre.P.A, inferInstance, inferInstance, A, GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D.toPre.P.isAb,
    ⟨⟨GlobalTheory.SelfUnif.selfPre D A eA hA hw, fun k _ =>
      GlobalTheory.SelfUnif.expBij D A eA hA hw GlobalTheory.globalFns_holds hI k⟩⟩⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegComp

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_generic_lift {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'}
    (hi : Function.Injective i) {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D') :
    ∃ s : (TK R).left ⟶ p.W.toScheme, s ≫ p.W.ι = jK R := by
  have H : Set.range (jK R).base ⊆ Set.range p.W.ι.base := by
    rintro _ ⟨y, rfl⟩
    let z' : (TK R').left := (default : PrimeSpectrum (FractionRing R'))
    have e₁ : (genMap hi).base z' = y := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    have e₂ : (jK R' ≫ spMap i).base z' = (genMap hi ≫ jK R).base z' := by
      rw [← fracMap_sq hi, Category.id_comp]
    refine ⟨(p.g).base z', ?_⟩
    rw [← Scheme.Hom.comp_apply, p.g_comm]
    exact e₂.trans (by rw [Scheme.Hom.comp_apply, e₁])
  exact ⟨IsOpenImmersion.lift p.W.ι (jK R) H, IsOpenImmersion.lift_fac _ _ _⟩

theorem nonempty_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hi : Function.Injective i) (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    Nonempty (IsPullDeg (j.comp i) D D'') := by
  have hji : Function.Injective (j.comp i) := hj.comp hi
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨s, hs⟩ := exists_generic_lift hi p
  obtain ⟨r, -⟩ := GlobalTheory.DvrDeg.exists_isPullDeg_of_val hji D D'' p.psiW s hs gp w (T.pgen_comp D'.P.isLB g₁ g₂) hr
    (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
      have s' : genMap hj ≫ jK R' ≫ spMap i = genMap hji ≫ jK R :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sj.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) sc).trans ((Category.id_comp _).symm.trans (fracMap_sq hji)))))
      have v₁ := psi_val p _ _ s' hJ hJ' (q.xe x)
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r⟩

end GlobalTheory.PullDegComp

namespace GlobalTheory.Mum

theorem hasFin_of_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')),
    Nonempty (IsPullDeg ρ D.toPre D'.toPre) → HasFin D' → HasFin D := by
  intro R R' _ _ _ _ _ _ ρ hρ D D' ⟨p⟩ ⟨R'', _, _, _, σ, D'', hσ, ⟨q⟩, hH⟩
  exact ⟨R'', _, _, _, σ.comp ρ, D'', ⟨hσ.1, hσ.2.1.comp hρ.2.1, hσ.2.2.comp hρ.2.2⟩,
    GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ.2.1 hσ.2.1 p q, hH⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLoc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section

namespace GlobalTheory.Mum

theorem has_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R (maximalIdeal R) → AdmBase R' (maximalIdeal R') → Function.Injective ρ → IsLocalHom ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D.toPre D'.toPre) → Has D → Has D' := by
  intro R R' _ _ _ _ _ _ ρ hR hR' hinj hloc D D' ⟨hD⟩ ⟨G, _, _, A, hsa, ⟨U⟩⟩
  have hP := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT := GlobalTheory.twistBaseChange
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal x).1 hx (isUnit_of_map_unit ρ x h)
  have sq : spMap (fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hinj).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hinj)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf ρ)).obj G)) G
      (spMap (fracMap hinj) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf ρ)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap ρ))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ) =
      pullback.fst G.hom (spMap ρ) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf ρ)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf ρ)).obj G) ≫ (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf ρ) = specOf ρ ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap ρ))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf ρ)).obj G) _ (specOf ρ) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf ρ) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf ρ)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf ρ)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf ρ)).obj G) _ (specOf ρ) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom := by
    show IsMonHom (𝟙 _); infer_instance
  have hgD : D'.toPre.P.g = D.toPre.P.g := H1.dim_unique _ D'.toPre.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp hD).1 D.toPre.P.smoothDim)
    (eSec D'.toPre.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R'))
  obtain ⟨U', -, -, -⟩ := GlobalTheory.TorsionFormCompare.exists_unif_pull_of_deg hP hG hS hT R R' _ _ hR hR' ρ hI D A G hsa
    U D' hD hgD ((Over.pullback (specOf ρ)).obj G) (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he
    (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨(Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance, A', IsSemiAbelian.pullback _ G hsa, ⟨U'⟩⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOnePrimePrincipalLocal
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

theorem heightOne_prime_locallyPrincipal_of_factorial_localization : ∀ (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S] [Algebra R S] (p P : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [UniqueFactorizationMonoid S], P.IsPrime → P ≤ p → P ≠ ⊥ → (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → Q ≤ P → Q = P) → ∃ a ∈ P, a ≠ 0 ∧ ∃ t ∉ p, ∀ g ∈ P, ∃ r, t * g = a * r := by
  intro R S _ _ _ _ _ _ p P _ _ _ hP hPp hP0 hmin
  classical
  have hdisj : Disjoint (p.primeCompl : Set R) (P : Set R) := by
    rw [Set.disjoint_left]; intro x hx hxP; exact hx (hPp hxP)
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors p)
  have hPSprime : (P.map (algebraMap R S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S P hP hdisj
  have hcomap : (P.map (algebraMap R S)).comap (algebraMap R S) = P :=
    IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hP hdisj
  have hPS0 : P.map (algebraMap R S) ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    intro h
    have hx : algebraMap R S x ∈ P.map (algebraMap R S) := Ideal.mem_map_of_mem _ hxP
    rw [h, Ideal.mem_bot] at hx
    exact hx0 (hinj (by rw [hx, map_zero]))
  obtain ⟨w, hwPS, hw⟩ := hPSprime.exists_mem_prime_of_ne_bot hPS0
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl (S := S) w
  replace has : IsLocalization.mk' S a s = w := has
  have hwa : algebraMap R S a = w * algebraMap R S s := by
    have h := IsLocalization.mk'_spec S a s
    rw [has] at h
    exact h.symm
  haveI : (Ideal.span {w}).IsPrime := (Ideal.span_singleton_prime hw.ne_zero).mpr hw
  have hQprime : ((Ideal.span {w}).comap (algebraMap R S)).IsPrime := inferInstance
  have haQ : a ∈ (Ideal.span {w}).comap (algebraMap R S) := by
    rw [Ideal.mem_comap, hwa]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self w)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hwa
    exact hw.ne_zero ((IsLocalization.map_units S s).mul_left_eq_zero.mp hwa.symm)
  have hQP : (Ideal.span {w}).comap (algebraMap R S) ≤ P := by
    rw [← hcomap]
    exact Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hwPS)
  have hQ0 : (Ideal.span {w}).comap (algebraMap R S) ≠ ⊥ := by
    intro h
    rw [h] at haQ
    exact ha0 (Ideal.mem_bot.mp haQ)
  have hQeq := hmin _ hQprime hQ0 hQP
  have haP : a ∈ P := by rw [← hQeq]; exact haQ
  have key : ∀ g : R, ∃ u : p.primeCompl, ∃ r : R, g ∈ P → (u : R) * g = a * r := by
    intro g
    by_cases hg : g ∈ P
    · have hgQ : g ∈ (Ideal.span {w}).comap (algebraMap R S) := by rw [hQeq]; exact hg
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hgQ
      obtain ⟨y, hy⟩ := hgQ
      obtain ⟨⟨r, u⟩, hru⟩ :=
        IsLocalization.mk'_surjective p.primeCompl (S := S) (y * IsLocalization.mk' S (1 : R) s)
      replace hru : IsLocalization.mk' S r u = y * IsLocalization.mk' S (1 : R) s := hru
      refine ⟨u, r, fun _ => hinj ?_⟩
      have h1 := IsLocalization.mk'_spec S r u
      have h2 := IsLocalization.mk'_spec' S (1 : R) s
      rw [map_one] at h2
      rw [hru] at h1
      rw [map_mul, map_mul, ← hy, hwa, ← h1]
      linear_combination (-(w * y * algebraMap R S u)) * h2
    · exact ⟨1, 0, fun h => absurd h hg⟩
  choose u r hur using key
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian P : P.FG)
  refine ⟨a, haP, ha0, ∏ x ∈ G, (u x : R), ?_, ?_⟩
  · show _ ∈ p.primeCompl
    exact Submonoid.prod_mem p.primeCompl fun x _ => (u x).2
  · intro g hg
    rw [← hG] at hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
        have hxP : x ∈ P := by rw [← hG]; exact Submodule.subset_span hx
        obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => (u x : R)) hx
        refine ⟨k * r x, ?_⟩
        rw [hk, mul_comm (u x : R) k, mul_assoc, hur x hxP]
        ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨r1, h1⟩ := hx
        obtain ⟨r2, h2⟩ := hy
        exact ⟨r1 + r2, by rw [mul_add, h1, h2, mul_add]⟩
    | smul c x _ hx =>
        obtain ⟨r1, h1⟩ := hx
        exact ⟨c * r1, by rw [smul_eq_mul, mul_left_comm, h1]; ring⟩

end GlobalTheory
end

