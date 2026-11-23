module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQuotientAbelianByFinitePoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

namespace FiniteQuot

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

lemma translHom_eq (c : 𝟙_ (Over (Sp K)) ⟶ A) : (transl c).hom = (toUnit A ≫ c) * 𝟙 A := rfl

lemma comp_translHom {Z : Over (Sp K)} (g : Z ⟶ A) (c : 𝟙_ (Over (Sp K)) ⟶ A) :
    g ≫ (transl c).hom = (toUnit Z ≫ c) * g := by
  rw [translHom_eq, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]

lemma translHom_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  rw [translHom_eq, MonObj.comp_one, _root_.one_mul]

lemma translHom_mul (a c : 𝟙_ (Over (Sp K)) ⟶ A) :
    (transl (a * c)).hom = (transl a).hom ≫ (transl c).hom := by
  rw [comp_translHom, translHom_eq, translHom_eq, MonObj.comp_mul, ← _root_.mul_assoc,
    _root_.mul_comm (toUnit A ≫ c)]

end FiniteQuot


open FiniteQuot PointQuot AbelianQuotient in
theorem exists_quotient_abelian_by_finite_points :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ C : Subgroup (𝟙_ (Over (Sp k)) ⟶ A), Finite C → ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (x : Over.mk t ⟶ A), x ≫ ψ = 1 ↔ ∃ c ∈ C, x = toUnit _ ≫ c := by
  open FiniteQuot PointQuot in
  intro k _ _ A _ hA C hC
  have := hA.comm
  have hq : IsQProjOver A.hom := by
    obtain ⟨N, i, hi, e⟩ := (ProjSpace.isProjBy_iff_isProjOver A.hom).1
      (AbelianProjective.isProjBy_of_isAbelianScheme k A hA)
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  obtain ⟨Y, π, sY, hw, hG, hsep, hlft, -⟩ :=
    ZM.exists_isGaloisCover_of_isQProjOver k A.left A.hom C (fun c => ((transl c.1).hom).left) hq
      (congrArg CommaMorphism.left (translHom_one (A := A)))
      (fun a c => congrArg CommaMorphism.left (translHom_mul a.1 c.1))
      (fun a => Over.w _) (by
        intro K _ _ y a h
        let y' : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
        have h' : y' ≫ (transl a.1).hom = y' := Over.OverMorphism.ext h
        have : Nonempty (Over.mk (y ≫ A.hom)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
        have := epi_toUnit (Over.mk (y ≫ A.hom))
        rw [comp_translHom, mul_eq_right, ← MonObj.comp_one (toUnit _), cancel_epi] at h'
        exact Subtype.ext h')
  let B : Over (Sp k) := Over.mk sY
  let q : A ⟶ B := Over.homMk π hw
  have hfin : IsFinite q.left := hG.fin
  have het : Etale q.left := hG.etale
  have hsurj : Surjective q.left := hG.onto
  have hinv : ∀ c : C, (transl c.1).hom ≫ q = q := fun c => Over.OverMorphism.ext (hG.inv c)
  let x : C → (𝟙_ (Over (Sp k)) ⟶ A) := Subtype.val
  have hmono := mono_constDesc x Subtype.val_injective
  obtain ⟨_, hi⟩ := exists_grpObj_constObj x C Subtype.range_coe
  obtain ⟨_, hcomm, hhom, -⟩ := grpObj_of_flat_coset_quotient _ A _ B (constDesc x) q hi hmono
    inferInstance hsurj inferInstance (by
      intro Z g g'
      constructor
      · intro h
        obtain ⟨t, ht⟩ := exists_lift x (g' / g) fun z => by
          obtain ⟨V, a, hV, e⟩ :=
            hG.exists_local_geom g.left g'.left (congrArg CommaMorphism.left h) z
          have e' : openι Z V ≫ g ≫ (transl a.1).hom = openι Z V ≫ g' := Over.OverMorphism.ext e
          refine ⟨V, hV, a, ?_⟩
          rw [GrpObj.comp_div, ← e', ← Category.assoc, comp_translHom, mul_div_cancel_right]
        exact ⟨t, by rw [ht, div_mul_cancel]⟩
      · rintro ⟨t, rfl⟩
        refine hom_ext_local _ _ fun z => ?_
        obtain ⟨V, hV, c, hc⟩ := locally_const_desc x t z
        refine ⟨V, hV, ?_⟩
        rw [← Category.assoc _ (_ * _), MonObj.comp_mul, hc, ← comp_translHom, Category.assoc,
          Category.assoc, hinv])
  refine ⟨B, inferInstance, q, ?_, hhom, hfin, het, hsurj, fun K _ _ t y => ⟨fun hy => ?_, ?_⟩⟩
  · have hw' : q.left ≫ B.hom = A.hom := Over.w q
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated B.hom := hsep
    have : LocallyOfFiniteType B.hom := hlft
    have : UniversallyClosed (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyReduced (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyConnected (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have := UniversallyClosed.of_comp_surjective q.left B.hom
    have := AbelianQuotient.geometricallyReduced_of_comp q.left B.hom
    have : LocallyOfFinitePresentation B.hom := inferInstance
    exact ⟨hcomm, AbelianQuotient.smooth_of_grpObj_of_flat B, ⟨⟩, AbelianQuotient.geometricallyConnected_of_comp q.left B.hom⟩
  · have h1 : (1 : Over.mk t ⟶ A) ≫ q = y ≫ q := by rw [hy, MonObj.one_comp]
    obtain ⟨a, ha, -⟩ := hG.fibre K (1 : Over.mk t ⟶ A).left y.left
      (congrArg CommaMorphism.left h1)
    have ha' : (1 : Over.mk t ⟶ A) ≫ (transl a.1).hom = y := Over.OverMorphism.ext ha
    exact ⟨a.1, a.2, by rw [← ha', comp_translHom, _root_.mul_one]⟩
  · rintro ⟨c, hc, rfl⟩
    rw [← _root_.mul_one (toUnit _ ≫ c), ← comp_translHom, Category.assoc, hinv ⟨c, hc⟩,
      MonObj.one_comp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.ProjFinite

theorem exists_relAmple_of_isProjBy {R : Type} [CommRing R] {A : Over (Sp R)} (h : GlobalTheory.AbLaw.IsProjBy A.hom) :
    ∃ H : LB A.left, H.IsLB ∧ Out.RelAmple A H := by
  obtain ⟨H, hH, m, s, hs⟩ := h
  have e : GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ) = H := by
    cases H
    simp [GlobalTheory.AbLaw.pw]
  have k : ∀ s : Fin (m + 1) → LB.Sec (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy A.hom (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)) s → Out.RelAmple A H :=
    fun s hs => GlobalTheory.Unif.relAmple_of_veryAmpleBy hH le_rfl s hs
  rw [e] at k
  exact ⟨H, hH, k s hs⟩

theorem isProjBy_of_fieldExtension {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)}
    {A : Over (Sp K)} [IsProper A₀.hom] {φ : A.left ⟶ A₀.left} (h : IsPullback φ A.hom A₀.hom (spMap i))
    {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB) (hw : LBIso L (L₀.pull φ))
    (hA : Out.RelAmple A L) : GlobalTheory.AbLaw.IsProjBy A₀.hom := by
  have : Subsingleton (Spec (CommRingCat.of K₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Flat (Out.specOf i) := inferInstance
  have : Surjective (Out.specOf i) := inferInstance
  have : IsProper A.hom := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom
  have h₀ : Out.RelAmple A₀ L₀ :=
    (relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (AmpleDescent.isAmpleLB_of_pull i h hL₀
      ((isAmpleLB_of_relAmple_of_isAffine A hL hA).of_lbIso (LB.isLB_pull hL₀ φ) hw.symm))
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K₀ A₀ L₀ hL₀).1 h₀
  exact ⟨_, GlobalTheory.AbLaw.isLB_pw hL₀ d, n, s, hs⟩

theorem exists_isPullback {S X T₁ T₂ X₁ X₂ : Scheme.{0}} {f : X ⟶ S} {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ T₁} {t₁ : T₁ ⟶ S}
    {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ T₂} {t₂ : T₂ ⟶ S} (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂)
    (u : T₂ ⟶ T₁) (hu : u ≫ t₁ = t₂) : ∃ φ : X₂ ⟶ X₁, φ ≫ π₁ = π₂ ∧ IsPullback φ f₂ f₁ u := by
  have w : π₂ ≫ f = (f₂ ≫ u) ≫ t₁ := by rw [Category.assoc, hu, h₂.w]
  refine ⟨h₁.lift _ _ w, h₁.lift_fst _ _ _, IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rw [h₁.lift_fst, hu]
  exact h₂

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_finite_isProjBy : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
  intro K _ A _ hA
  have := hA.proper
  have := hA.comm
  let Ω := AlgebraicClosure K
  let a : K →+* Ω := algebraMap K Ω
  let B : Over (Sp Ω) := (Over.pullback (spMap a)).obj A
  have sqB : IsPullback (pullback.fst A.hom (spMap a)) B.hom A.hom (spMap a) := IsPullback.of_hasPullback _ _
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }
  obtain ⟨H, hH, hamp⟩ := exists_relAmple_of_isProjBy
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme Ω B hB)
  let K₀ : Subfield Ω := a.fieldRange
  let j : K →+* K₀ := a.rangeRestrictField
  have sq₀ := IsPullback.of_hasPullback A.hom (spMap j)
  obtain ⟨φ, hφ, sq⟩ := exists_isPullback sq₀ sqB (spMap K₀.subtype) (spMap_comp _ _)
  obtain ⟨s, hs⟩ := GlobalTheory.LBDescent.exists_lb_subfield Ω K₀ _ _ _ _ φ H hH sq
  let L : IntermediateField K Ω := IntermediateField.adjoin K (s : Set Ω)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have h : K₀ ≤ L.toSubfield := by
    rintro _ ⟨x, rfl⟩
    exact L.algebraMap_mem x
  refine ⟨L, inferInstance, inferInstance, hfin, ?_⟩
  let C : Over (Sp L) := (Over.pullback (spMap (algebraMap K L))).obj A
  have sqC : IsPullback (pullback.fst A.hom (spMap (algebraMap K L))) C.hom A.hom (spMap (algebraMap K L)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨φ₁, hφ₁, sq₁⟩ := exists_isPullback sq₀ sqC (spMap (Subfield.inclusion h)) (spMap_comp _ _)
  obtain ⟨ψ, hψ, sq₂⟩ := exists_isPullback sqC sqB (spMap L.toSubfield.subtype) (spMap_comp _ _)
  obtain ⟨L₁, hL₁, hw⟩ := hs L.toSubfield h (IntermediateField.subset_adjoin K _) C.left C.hom φ₁ ψ sq₁
    (sq₀.hom_ext (by rw [Category.assoc, hφ₁, hψ, hφ]) (by
      rw [Category.assoc, sq₁.w, ← Category.assoc, sq₂.w, Category.assoc, sq.w]
      exact congrArg _ (spMap_comp _ _))) sq₂.w
  have : IsProper C.hom := MorphismProperty.of_isPullback (P := @IsProper) sqC hA.proper
  exact isProjBy_of_fieldExtension L.toSubfield.subtype sq₂ hL₁ hH hw hamp

end GlobalTheory.ProjFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedPolarisedFibreAtFieldPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem GlobalTheory.OneBasis.exists_rigPull_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (K : Type) [Field K] (x : Sp K ⟶ Z), PolAt t x → ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ t.G.left) (w : LB.Iso A.L (t.PP.L.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))), RigPull A.A t.G x φ w ρ t.PP.rig := by
  intro _ _ E _ _ _ H Z t K _ x ⟨hp, hA, hK⟩
  have hsemi : IsSemiAbelian ((Over.pullback x).obj t.G) := by
    refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
    · have := t.semi.comm
      infer_instance
    · have := t.semi.smooth
      change Smooth (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.separated
      change IsSeparated (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.quasiCompact
      change QuasiCompact (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.geomConnected
      change GeometricallyConnected (pullback.snd t.G.hom x)
      infer_instance
    · intro Ω _ _ q
      obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ x)
      exact ⟨torusExtOfIso (pullCompIso q x t.G) A⟩
  have hpull : ∃ (PP' : RigLB ((Over.pullback x).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
      (m : SABMap ⟨(Over.pullback x).obj t.G, hsemi,
        Geo.Tor.OAct.pullback x t.G t.act, PP', cub, sym, adj, prim⟩ t x),
      m.φ = pullback.fst t.G.hom x := by
    have h := isGrpPullback_pullback t.G x
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := CubePf.cubePull _ _ t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((Geo.Tor.OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x =
        pullback.fst t.G.hom x ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over _} (y : T ⟶ (Over.pullback x).obj t.G) a,
        pushPt h.1.w (y ≫ (Geo.Tor.OAct.pullback x t.G t.act).act a) = pushPt h.1.w y ≫ t.act.act a := fun y a =>
      Over.OverMorphism.ext (by
        show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback x).obj t.G) ((Over.pullback x).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback x).obj t.G) ((Over.pullback x).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback x).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := hpull
  let t' : SAB H (Spec (CommRingCat.of K)) :=
    ⟨(Over.pullback x).obj t.G, hsemi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t x := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom x := hm₁
  obtain ⟨w, hw, hr, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom x)) := hm₀ ▸ ⟨w, hw⟩
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  have hL' : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull (𝟙 t'.G.left)) :=
    LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) hL
  obtain ⟨v, hv⟩ := hL'
  have : IsMonHom (Iso.refl t'.G).hom := inferInstanceAs (IsMonHom (𝟙 t'.G))
  have hid : IsGrpPullback t'.G t'.G (𝟙 _) (𝟙 t'.G.left) := isGrpPullback_of_iso (Iso.refl t'.G)
  have hA' : RelAmple t'.G t'.PP.L :=
    relAmple_pull hid.1 hM t'.PP.isLB ((isGen_iff v).1 hv) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
  have hK' : KTriv t'.G t'.PP.L := kTriv_pull hid hM t'.PP.isLB ((isGen_iff v).1 hv) hK
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  have hP : PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m₀.cm.e :=
    (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m₀.cm.e _
      (rigPull_le m₀.cm.F m₀.cm.e m₀.cm.e_comm t.PP.L) (fun _ => rfl)).1 hr
  rw [m₀.base] at hP
  exact ⟨GlobalTheory.GenericPol.toPolAV t' g hg hp hA' hK', m₀.cm.F, w, t'.PP.rig, m₀.cart, hw, t'.PP.rigGen, hP⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymPmaps
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibSym
open GlobalTheory.FrameValue GlobalTheory.TorusExt GlobalTheory.DegPull

theorem vF_down {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ} {u : HolUnif A L' g} (hL' : L'.IsLB)
    {X Y Y' : Scheme.{0}} {L : LB X} {Φ : A.left ⟶ X} {K : Type} [Fintype K] {w : LB.Iso L' (L.pull Φ)}
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {y : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' y z) :
    vF t (y ≫ h) J = genVal u hL' a y z * ∏ k, (fr (z k) : ℂ) ^ ε k := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : ∀ q : Sp ℂ, Good L q J := fun q ψ => hJ ψ trivial
  have gJ' : ∀ q : Sp ℂ, Good L' q (chartAt hL') := fun q ψ => le_chartAt hL' ψ trivial
  have key : ∀ {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)ˣ), ⊤ ≤ x ⁻¹ᵁ U →
      (gm x p U f).val = stalkConst p (valAt' x U f.val) := fun x U f hU =>
    (gs_unit x p U (hU trivial) f).symm.trans (gs_eq_stalkConst x p hU _)
  have e := congrArg Units.val (pmaps_val hψ H y p (gJ p) (gJ' p))
  have e₁ : (val t (y ≫ h) p J).val = stalkConst p (vF t (y ≫ h) J) :=
    key _ _ _ (fun q _ => (gJ q).mem φ (y ≫ h))
  have e₂ : (val a y p (chartAt hL')).val = stalkConst p (genVal u hL' a y z *
      frameProd u ε z fun k => chartAt hL' (y ≫ φ' k)) :=
    (key _ _ _ (le_wchart_chartAt hL' φ' y)).trans (congrArg _ (valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' y)))
  have hm : ∀ x : Sp ℂ ⟶ A.left, ⊤ ≤ x ⁻¹ᵁ ((L.pull Φ).U (fun _ => J (x ≫ Φ)) ⊓ L'.U (chartAt hL' x)) :=
    fun x q _ => ⟨mem_pull.2 (gJ q (x ≫ Φ)), gJ' q x⟩
  have e₃ : ∀ x : Sp ℂ ⟶ A.left, Geo.Tor.gw w x p (J (x ≫ Φ)) (chartAt hL' x) = stalkUnits p
      (Units.mk0 (valAt' x _ (w.s (fun _ => J (x ≫ Φ), chartAt hL' x)).val)
        (CubeValues.val_unit_ne_zero x SymmetricSemicharacter.valueRules (hm x) _)) := fun x =>
    Units.ext (key x _ _ (hm x))
  rw [Units.val_mul, e₁, e₂] at e
  simp only [e₃, ← map_zpow, ← map_prod] at e
  rw [stalkUnits_val, ← map_mul] at e
  rw [(stalkConst p).injective e, mul_left_comm, frameProd, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, hfr (z k) _ (le_chartAt hL' _)]
  rfl

theorem exists_sym_pmaps {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L)) :
    ∃ s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]), s'.IsGen ∧
      LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s' (eSec G')) (LB.oneGen L') ∧
      (∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k) ∧ PMaps w _ _ _ s' s F := by
  have hι : (ι[G']).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine Eq.trans e ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  have hψ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', H⟩ := exists_pmaps hw hL hL' F hψ s hs
  refine ⟨s', hs', corr_of_val hL' fun y J' hJ' => ?_, hψ, H⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e := pmaps_val hψ H (eSec G') y hJ hJ'
  have e₀ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left]; simp
  have he : eSec G' ≫ F = f ≫ eSec G := (cubeMapOf gp).e_comm
  rw [Fin.prod_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id, zpow_one, zpow_neg,
    mul_inv_cancel, _root_.one_mul] at e
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp, ← e, he]
  exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hr f).trans (val_one _))

theorem fibSymSt : Laws → FibSymSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hF
  obtain ⟨hJ, P', φ, w, u, rfl, gp, hw, hAH, -, -, -, hex, hfr⟩ := hF
  obtain ⟨s, hs, hr, hψ, H⟩ := exists_sym_pmaps gp D.P.isLB P'.isLB ((isGen_iff w).1 hw) D.sym D.sym_gen D.sym_rig
  obtain ⟨h₁, h₂⟩ := genVal_sym P'.isLB hAH s hs hr
  refine ⟨fun x => ?_, h₂⟩
  have e := vF_down P'.isLB hψ hs H hJ (fr := fr) (fun z i hi => hex z ▸ hfr z i hi) (isLift_sym u x)
  rw [h₁, Fin.prod_univ_two] at e
  rw [hex x]
  refine (congrArg (· * (fr x : ℂ)) e).trans ?_
  simp

end GlobalTheory.Ex.Arch.FibSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfRetract
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem isSemiAbelian_of_retract : ∀ (S : Scheme.{0}) (G G₁ : Over S) [GrpObj G] [GrpObj G₁], IsSemiAbelian G → SmConn G₁ → ∀ (i : G₁ ⟶ G) (r : G ⟶ G₁), IsMonHom r → i ≫ r = 𝟙 G₁ → IsSemiAbelian G₁ := by
  intro S G G₁ _ _ hG h₁ i r hr hir
  obtain ⟨hc, hs, hsep, hq, hg⟩ := h₁
  refine ⟨hc, hs, hsep, hq, hg, fun Ω _ _ p => ?_⟩
  have h₂ : SmConn ((Over.pullback p).obj G₁) := by
    refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
    · show Smooth (pullback.snd G₁.hom p); infer_instance
    · show IsSeparated (pullback.snd G₁.hom p); infer_instance
    · show QuasiCompact (pullback.snd G₁.hom p); infer_instance
    · show GeometricallyConnected (pullback.snd G₁.hom p); infer_instance
  refine _root_.GlobalTheory.SS.nonempty_torusExtension_of_surjective_points Ω ((Over.pullback p).obj G) ((Over.pullback p).obj G₁) h₂ (hG.fibres Ω p)
    ((Over.pullback p).map r) inferInstance fun y => ⟨y ≫ (Over.pullback p).map i, ?_⟩
  rw [Category.assoc, ← Functor.map_comp, hir, CategoryTheory.Functor.map_id, Category.comp_id]

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionIsometryValuesIsTorsionLabelSystem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData

theorem labels_of_tateIsoQ : BrGtSt → BrWpSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F) (N : NumD F) (ν : NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ n a, ν.QPt (I.ev n a) (q n a)) → Labels N D.EF I.ζ q ∧ ∀ k, 0 < k → ∀ (x : 𝓞 E) (a : D.La), ∃ z, ν.eX (q k (x • a)).1.1.toAdd = x • ν.eX (q k a).1.1.toAdd + k • z := by
  intro hG hW E _ _ _ H D R _ _ D₀ _ oa he hB F _ _ _ I N ν q hq
  obtain ⟨h1, -, h2, -, hQ⟩ := hG R D₀ he hB F N ν
  obtain ⟨hadd, htow⟩ := GlobalTheory.NestQVal.qval_add_tower E H D R D₀ oa he hB F I N ν q h1 h2
    (fun k => ⟨(hQ k).1, (hQ k).2.2⟩) hq
  refine ⟨⟨hadd, fun n hn a b => ?_, fun n hn p => ?_, htow, fun n hn a b => ?_⟩, fun n hn x a => ?_⟩
  · rw [← (hQ n).2.2 _ _ _ _ (hq n a) (hq n b)]
    exact I.ker n hn a b
  · obtain ⟨p₀, hp₀⟩ := (hQ n).2.1 p
    obtain ⟨a, ha⟩ := I.onto n hn p₀
    exact ⟨a, ((hQ n).2.2 _ _ _ _ (hq n a) hp₀).1 ha⟩
  · exact Units.ext ((hW R D₀ he hB F N ν n hn _ _ _ _ _ (hq n a) (hq n b)).1 (I.isom n hn a b)).symm
  · obtain ⟨q₀, hy, -, heq⟩ := I.lin n hn x a
    obtain ⟨c, hc, -⟩ := (hQ n).1 q₀
    obtain ⟨z, hz, -⟩ := ((hQ n).2.2 _ _ _ _ hc (hq n (x • a))).1 heq
    exact ⟨ν.eX z, by rw [hz, map_add (f := _), map_nsmul, hc.1, hy, (hq n a).1]⟩

end GlobalTheory.ModelData
end

