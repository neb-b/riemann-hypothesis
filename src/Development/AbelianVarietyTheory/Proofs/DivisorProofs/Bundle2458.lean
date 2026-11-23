module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ProjOverBase

theorem isProjOver_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (κ : C.o →+* X.o₁), X.uΩ ≫ C.i ≫ C.z = spMap ((algebraMap X.o₁ X.Ω₁).comp κ) → IsProjOver X.M.s := by
  intro E _ _ _ H Dw l Xo cf C X κ h
  have hs : X.M.s ≫ spMap κ = X.π ≫ C.z := by
    refine ext_of_isDominant X.M.pt ?_
    rw [← Category.assoc, X.M.pt_s, ← Category.assoc, X.comp]
    simp only [USetup.uΩ, UCompact.i, Category.assoc] at h ⊢
    rw [h]
    exact (Spec.map_comp (CommRingCat.ofHom κ) (CommRingCat.ofHom (algebraMap X.o₁ X.Ω₁))).symm
  haveI := C.ded
  exact GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over C.o X.o₁ κ X.M.Z C.Z C.z X.π X.M.s C.proj X.fin inferInstance hs

end GlobalTheory.UPoinc.ProjOverBase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegSquareFourthSide
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullSquare

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_of_eq {θ θ' : R →+* R'} (e : θ = θ') {D : DegPre R} {D' : DegPre R'} (r : IsPullDeg θ D D') :
    ∃ r' : IsPullDeg θ' D D', (∀ x, r'.xe x = r.xe x) ∧
      ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g : GtPtF D F)
        (g' : GtPtF D' F), IsPullGtF θ r F g g' → IsPullGtF θ' r' F g g' := by
  subst e
  exact ⟨r, fun _ => rfl, fun _ _ _ _ _ _ h => h⟩

end GlobalTheory.PullSquare

theorem GlobalTheory.Mum.isPullDeg_square : ∀ (R R₁ W W₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [CommRing W₁] [IsDomain W₁] (I : Ideal R) (I₁ : Ideal R₁) (J : Ideal W) (J₁ : Ideal W₁), AdmBase R I → AdmBase R₁ I₁ → AdmBase W J → AdmBase W₁ J₁ → ∀ (ρ : R →+* R₁) (φ : R →+* W) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁), φ₁.comp ρ = iw.comp φ → Function.Injective φ₁ → Function.Injective ρ → Function.Injective φ → Function.Injective iw → ∀ (D : DegData R I) (D₁ : DegData R₁ I₁) (D' : DegData W J) (D'₁ : DegData W₁ J₁) (hρ : IsPullDeg ρ D.toPre D₁.toPre) (hD : IsPullDeg φ D.toPre D'.toPre) (hX : IsPullDeg iw D'.toPre D'₁.toPre), ∃ h : IsPullDeg φ₁ D₁.toPre D'₁.toPre, (∀ x, hρ.xe (h.xe x) = hD.xe (hX.xe x)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R₁) F] [Algebra (FractionRing W) F] [Algebra (FractionRing W₁) F], GlobalTheory.ArcPull.Compat ρ F → GlobalTheory.ArcPull.Compat φ F → GlobalTheory.ArcPull.Compat iw F → GlobalTheory.ArcPull.Compat φ₁ F → ∀ (g : GtPtF D.toPre F) (g₁ : GtPtF D₁.toPre F) (g' : GtPtF D'.toPre F) (g'₁ : GtPtF D'₁.toPre F), IsPullGtF ρ hρ F g g₁ → IsPullGtF φ hD F g g' → IsPullGtF iw hX F g' g'₁ → IsPullGtF φ₁ h F g₁ g'₁ := by
  intro R R₁ W W₁ _ _ _ _ _ _ _ _ I I₁ J J₁ _ _ _ _ ρ φ iw φ₁ hsq hφ₁ hρi hφi hiw D D₁ D' D'₁ hρ hD hX
  obtain ⟨r, Tr⟩ := GlobalTheory.LabTrans.exists_comp hφi hiw hD hX
  obtain ⟨r', hx', hg'⟩ := GlobalTheory.PullSquare.exists_of_eq hsq.symm r
  obtain ⟨h, Th⟩ := GlobalTheory.LabTrans.exists_cancel hρi hφ₁ hρ r'
  refine ⟨h, fun x => ?_, ?_⟩
  · rw [Th.xe_eq, hx', ← Tr.xe_eq]
  · intro F _ _ _ _ _ cρ cφ ci c₁ g g₁ g' g'₁ Hρ HD HX
    have cθ : GlobalTheory.ArcPull.Compat (iw.comp φ) F := fun a => (cφ a).trans (ci (φ a))
    have cθ' : GlobalTheory.ArcPull.Compat (φ₁.comp ρ) F := fun a => (cρ a).trans (c₁ (ρ a))
    have H : IsPullGtF (φ₁.comp ρ) r' F g g'₁ := hg' F g g'₁ (Tr.isPullGtF cθ HD HX)
    obtain ⟨g'', H''⟩ := GlobalTheory.ArcPull.exists_pullGt h GlobalTheory.ExpansionTotal.globalFns c₁ g₁
    have H2 := Th.isPullGtF cθ' Hρ H''
    rwa [GlobalTheory.ArcPull.pullGt_unique r' cθ' H2 H] at H''
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackDescentSquarePairToOpenSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

abbrev prU (N : Near π G) : (Desc.UT N).left ⟶ N.U.left := pullback.fst _ _

def liftU (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : Y ⟶ (Desc.UT N).left :=
  pullback.lift x t h

theorem liftU_prU (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : liftU N x t h ≫ prU N = x :=
  pullback.lift_fst _ _ _

theorem liftU_hom (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : liftU N x t h ≫ (Desc.UT N).hom = t :=
  pullback.lift_snd _ _ _

theorem UT_ext (N : Near π G) {Y : Scheme.{0}} (f g : Y ⟶ (Desc.UT N).left) (h1 : f ≫ prU N = g ≫ prU N)
    (h2 : f ≫ (Desc.UT N).hom = g ≫ (Desc.UT N).hom) : f = g :=
  pullback.hom_ext h1 h2

theorem pairU_fst (N : Near π G) :
    pairU N ≫ (fst N.U N.U).left = (fst (Desc.UT N) (Desc.UT N)).left ≫ prU N :=
  congrArg Over.Hom.left (lift_fst (fstU N) (sndU N))

theorem pairU_snd (N : Near π G) :
    pairU N ≫ (snd N.U N.U).left = (snd (Desc.UT N) (Desc.UT N)).left ≫ prU N :=
  congrArg Over.Hom.left (lift_snd (fstU N) (sndU N))

theorem pairU_isPullback (N : Near π G) :
    IsPullback (pairU N) (Desc.UT N ⊗ Desc.UT N).hom (N.U ⊗ N.U).hom (pullback.fst π π ≫ π) := by
  have hUU : (N.U ⊗ N.U).hom = (fst N.U N.U).left ≫ N.U.hom := rfl
  have cUU : (fst N.U N.U).left ≫ N.U.hom = (snd N.U N.U).left ≫ N.U.hom := pullback.condition
  have hTT : (Desc.UT N ⊗ Desc.UT N).hom = (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom := rfl
  have cTT : (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom := pullback.condition
  have extUU : ∀ {Y : Scheme.{0}} (f g : Y ⟶ (N.U ⊗ N.U).left), f ≫ (fst N.U N.U).left = g ≫ (fst N.U N.U).left →
      f ≫ (snd N.U N.U).left = g ≫ (snd N.U N.U).left → f = g := fun f g h1 h2 => pullback.hom_ext h1 h2
  have extTT : ∀ {Y : Scheme.{0}} (f g : Y ⟶ (Desc.UT N ⊗ Desc.UT N).left),
      f ≫ (fst (Desc.UT N) (Desc.UT N)).left = g ≫ (fst (Desc.UT N) (Desc.UT N)).left →
      f ≫ (snd (Desc.UT N) (Desc.UT N)).left = g ≫ (snd (Desc.UT N) (Desc.UT N)).left → f = g :=
    fun f g h1 h2 => pullback.hom_ext h1 h2
  have liftTT : ∀ {Y : Scheme.{0}} (a b : Y ⟶ (Desc.UT N).left), a ≫ (Desc.UT N).hom = b ≫ (Desc.UT N).hom →
      ∃ f : Y ⟶ (Desc.UT N ⊗ Desc.UT N).left,
        f ≫ (fst (Desc.UT N) (Desc.UT N)).left = a ∧ f ≫ (snd (Desc.UT N) (Desc.UT N)).left = b :=
    fun a b h => ⟨pullback.lift a b h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have ha : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      (s.fst ≫ (fst N.U N.U).left) ≫ N.U.hom = s.snd ≫ pullback.fst π π ≫ π := fun s => by
    rw [Category.assoc, ← hUU]; exact s.condition
  have hb : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      (s.fst ≫ (snd N.U N.U).left) ≫ N.U.hom = s.snd ≫ pullback.fst π π ≫ π := fun s => by
    rw [Category.assoc, ← cUU, ← hUU]; exact s.condition
  have hab : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      liftU N _ _ (ha s) ≫ (Desc.UT N).hom = liftU N _ _ (hb s) ≫ (Desc.UT N).hom := fun s => by
    rw [liftU_hom, liftU_hom]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (pairU_over N)) ?_
  refine PullbackCone.IsLimit.mk (pairU_over N) (fun s => (liftTT _ _ (hab s)).choose) ?_ ?_ ?_
  · intro s
    obtain ⟨h1, h2⟩ := (liftTT _ _ (hab s)).choose_spec
    apply extUU
    · rw [Category.assoc, pairU_fst, ← Category.assoc, h1, liftU_prU]
    · rw [Category.assoc, pairU_snd, ← Category.assoc, h2, liftU_prU]
  · intro s
    obtain ⟨h1, _⟩ := (liftTT _ _ (hab s)).choose_spec
    show _ ≫ (Desc.UT N ⊗ Desc.UT N).hom = _
    rw [hTT, ← Category.assoc, h1, liftU_hom]
  · intro s m m1 m2
    obtain ⟨h1, h2⟩ := (liftTT _ _ (hab s)).choose_spec
    have m2' : m ≫ (Desc.UT N ⊗ Desc.UT N).hom = s.snd := m2
    rw [hTT] at m2'
    apply extTT
    · rw [h1]
      apply UT_ext
      · rw [liftU_prU, Category.assoc, ← pairU_fst, ← Category.assoc, m1]
      · rw [liftU_hom, Category.assoc, m2']
    · rw [h2]
      apply UT_ext
      · rw [liftU_prU, Category.assoc, ← pairU_snd, ← Category.assoc, m1]
      · rw [liftU_hom, Category.assoc, ← cTT, m2']

end GlobalTheory.Mum.DescKP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackUniformisationCompIdPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullUnifId

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW' {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := hψ x y J J' hJ hJ'
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem exists_isPullDeg_comp {R'' : Type} [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    (hj : Function.Injective j) {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D')
    (q : IsPullDeg j D' D'') :
    ∃ (r : IsPullDeg (j.comp i) D D'') (w : LB.Iso D''.P.L (D.P.L.pull (proj q ≫ proj p))),
      proj r = proj q ≫ proj p ∧ r.xe = q.xe.trans p.xe ∧ HEq r.w w ∧ Tri p.w q.w w := by
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
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, r₁, r₂, r₃⟩ := exists_isPullDeg_of_valW' D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, w, r₁, r₂, r₃, T⟩

end GlobalTheory.PullUnifId

namespace GlobalTheory.PullUnifId

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def pullIdIso (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) :
    (Over.pullback (specOf (RingHom.id R'))).obj ((Over.pullback (specOf φ)).obj G) ≅ (Over.pullback (specOf φ)).obj G :=
  Over.isoMk (pullbackLeftPullbackSndIso G.hom (specOf φ) (specOf (RingHom.id R')) ≪≫
    pullback.congrHom rfl (by rw [specOf_id, Category.id_comp])) (by
      show _ ≫ pullback.snd _ _ = pullback.snd _ _
      simp only [Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map]
      erw [pullback.lift_snd]
      simp)

theorem pullIdIso_fst (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) :
    (pullIdIso φ G).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst _ (specOf (RingHom.id R')) ≫ pullback.fst G.hom (specOf φ) := by
  simp only [pullIdIso, Over.isoMk_hom_left, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map]
  simp

end GlobalTheory.PullUnifId

namespace GlobalTheory.PullUnifId

open GlobalTheory.PsiEvenPull (proj)

theorem isPullUnif_comp_id : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R')
    (D : DegData R I) (D' D'' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
    (hid : IsPullDeg (RingHom.id R') D'.toPre D''.toPre)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' A'' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (G' G'' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (bc' : G'' ≅ (Over.pullback (specOf (RingHom.id R'))).obj G')
    (U : Unif I D A G) (U' : Unif I' D' A' G') (U'' : Unif I' D'' A'' G''),
    IsPullUnif φ hD bc U U' → IsPullUnif (RingHom.id R') hid bc' U' U'' →
    ∃ (h : IsPullDeg φ D.toPre D''.toPre) (bc'' : G'' ≅ (Over.pullback (specOf φ)).obj G),
      IsPullUnif φ h bc'' U U'' ∧ (∀ x, h.xe x = hD.xe (hid.xe x)) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) =
        hid.e.hom.left ≫ pullback.fst D'.toPre.P.A.hom (specOf (RingHom.id R')) ≫
          hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) ∧
      bc''.hom.left ≫ pullback.fst G.hom (specOf φ) =
        bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      (IsMonHom bc.hom → IsMonHom bc'.hom → IsMonHom bc''.hom) := by
  intro R R' _ _ _ _ I I' φ D D' D'' hD hid A A' A'' G _ _ G' G'' _ _ _ _ bc bc' U U' U'' H₁ H₂
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := exists_isPullDeg_comp (j := RingHom.id R') (fun _ _ h => h) hD hid
  let bc'' : G'' ≅ (Over.pullback (specOf φ)).obj G :=
    bc' ≪≫ (Over.pullback (specOf (RingHom.id R'))).mapIso bc ≪≫ pullIdIso φ G
  have hb : bc''.hom.left ≫ pullback.fst G.hom (specOf φ) =
      bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    have := pullIdIso_fst φ G
    simp only [bc'', Iso.trans_hom, Over.comp_left, Category.assoc, this, Functor.mapIso_hom]
    congr 1
    simp only [Over.pullback, Over.homMk_left]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc]
  refine ⟨r, bc'', GalMul.isPullUnif_comp (i := φ) (j := RingHom.id R') r₁ r₂ r₃ T
      (hb.trans (Category.assoc _ _ _).symm) H₁ H₂, fun x => congrArg (fun e => e x) r₂,
      r₁.trans (Category.assoc _ _ _), hb, fun m₁ m₂ => ?_⟩
  have p₁ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have p₂ : IsGrpPullback G'' G' (specOf (RingHom.id R')) (bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R'))) :=
    ((isGrpPullback_of_iso bc').comp (isGrpPullback_pullback G' (specOf (RingHom.id R')))).congr (Category.id_comp _) rfl
  have p : IsGrpPullback G'' G (specOf φ) (bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    (p₂.comp p₁).congr (by rw [specOf_id, Category.id_comp]) (Category.assoc _ _ _)
  obtain ⟨e, he, hf⟩ := grpPullback_iso p (isGrpPullback_pullback G (specOf φ))
  have : bc''.hom = e.hom := by
    ext1
    apply pullback.hom_ext
    · exact hb.trans hf.symm
    · exact (Over.w bc''.hom).trans (Over.w e.hom).symm
  rw [this]
  exact he

end GlobalTheory.PullUnifId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackUniformisationOfLineBundleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section
namespace GlobalTheory.Mum

theorem isPullUnif_of_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (D₁ : DegData R (maximalIdeal R)) (U₁ : Unif (maximalIdeal R) D₁ A G), LBIso U'.LG.L (U₁.LG.L.pull β) → ∃ (h : IsPullDeg ρ D₁.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf ρ)).obj G), bc.hom.left ≫ pullback.fst G.hom (specOf ρ) = β ∧ IsPullUnif ρ h bc U₁ U' := by
  intro R _ _ _ hRb R' _ _ _ ρ hfin D' A' G' _ _ hsa' U' G _ _ β hsa hgp A D₁ U₁ hL
  obtain ⟨hR', hinj, hfinite⟩ := hfin
  have hR := hRb.1
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hgp (isGrpPullback_pullback G (spMap ρ))
  subst hbc
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' :=
    GlobalTheory.ResidueGalois.map_maximalIdeal_le ρ hfinite.to_isIntegral
  have hP := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
  have sq : spMap (fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hinj).symm.trans (Category.id_comp _)
  obtain ⟨A'', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hinj)) A
  have gpA : IsGrpPullback A''.A A.A (spMap (fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U₁.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj G') G (spMap (fracMap hinj) ≫ jK R)
      (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback G' (jK R')).comp hgp).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₁.gen.inv.left ≫ U₁.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A''.L.pull eA.hom.left) (U₁.LG.L.pull (pullback.fst G'.hom (jK R') ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf ρ))) := by
    refine LBIso.trans (pull_isLB A''.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U₁.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A''.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₁.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U₁.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₁.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U₁.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ρ) = specOf ρ ≫ eSec G :=
    (cubeMapOf hgp).e_comm
  obtain ⟨w₀, hw₀⟩ := hL
  have hσ : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  obtain ⟨wL, gL, pL⟩ := GlobalTheory.UnifPreCompare.exists_rigidified U₁.LG.isLB U'.LG.isLB G'.hom (eSec G') hσ w₀ hw₀
    U'.LG.rig U'.LG.rigGen U₁.LG.rig U₁.LG.rigGen (specOf ρ) he
  have mL : LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig
      (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf ρ)) (specOf ρ) he U₁.LG.L U₁.LG.rig) :=
    (maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U₁.LG.rig (specOf ρ) _
      (rigPull_le (G' := G') (G := G) _ (specOf ρ) he U₁.LG.L) (fun _ => rfl)).2 pL
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists R (maximalIdeal R) hR D₁
  have hgen : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective ρ hinj)
    rw [this]; exact hWo
  obtain ⟨D'', hD₁, U'', hLG, -, H₁⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds R R' (maximalIdeal R) (maximalIdeal R')
    hR hR' ρ hI D₁ A G hsa U₁ Wo hψ hgen G' bc mbc A'' dA eA mE wA U'.LG wL he gL mL
  obtain ⟨wL₀, g₀, m₀⟩ := exists_iso_of_eq hLG.symm
  have h6 := GlobalTheory.unifUniq GlobalTheory.abelianSchemeLaws_all.1.globalFns GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.ample
  obtain ⟨hD₂, hlev, -⟩ := h6 R' (maximalIdeal R') hR' D'' D' A'' A' G' hsa' U'' U' wL₀ g₀ m₀
  have hs := specOf_id R'
  haveI mR : IsMonHom (Iso.refl G').hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨bc₀, -, hbc₀⟩ := grpPullback_iso ((isGrpPullback_of_iso (Iso.refl G')).congr hs.symm rfl)
    (isGrpPullback_pullback G' (Out.specOf (RingHom.id R')))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst G'.hom (Out.specOf (RingHom.id R')) = 𝟙 _ := hbc₀
  have H₂ := isPullUnif_of_uniq U'' U' hD₂ wL₀ g₀ m₀ hlev bc₀ hbc₀'
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := GalMul.exists_isPullDeg_comp hinj (fun _ _ h => h) hD₁ hD₂
  have hb : bc.hom.left ≫ pullback.fst G.hom (specOf ((RingHom.id R').comp ρ)) =
      (bc₀.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R'))) ≫
        (bc.hom.left ≫ pullback.fst G.hom (specOf ρ)) := by
    rw [hbc₀', Category.id_comp]
  exact ⟨r, bc, rfl, GalMul.isPullUnif_comp r₁ r₂ r₃ T hb H₁ H₂⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

theorem triv_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), GlobalTheory.TensBal.Triv T 0 := by
  intro R _ _ D D' r W T
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB
    (φ' := fun v : (0 : Vec r →₀ ℤ).support => (vecHom T v.1).left) (ε' := fun v => (0 : Vec r →₀ ℤ) v.1)
    (fun U _ h => by simp) (LB.oneGen D.P.L (Y := (D'.P.A ⊗ D'.P.A).left)) (LB.isGen_oneGen _)
  refine ⟨t, ht, fun z J hJ => (hv _ _ z J hJ).trans (val_one _), fun z J hJ y y' => ?_⟩
  rw [hv _ _ z J hJ, val_one]
  simp

end GlobalTheory.TensBal
end

