module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.HomConst

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegPre R} {e : ℕ}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

def Acts (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left) (f : D₂.X → D₁.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J₁ : (Z ⟶ D₁.P.A.left) → D₁.P.L.ι)
    (J₂ : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D₁.P.L z J₁ → Good D₂.P.L z J₂ →
    r ≫ g₁.pG.left = r ≫ (fstG I e G₁).left ≫ G₁.hom ≫ eSec D₁.P.A →
    ∀ x, val (g₂.t x) (r ≫ a) z J₂ = val (g₁.t (f x)) r z J₁

theorem acts_of_torusHomOf (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) {f : D₂.X → D₁.X}
    {t : splitTorus _ D₁.X ⟶ splitTorus _ D₂.X} (ht : TorusHomOf f t)
    (hi : g₁.i ≫ a = t ≫ g₂.i) : Acts g₁ g₂ a.left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ h x
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G₁).hom)
  let b : FinalForm ⟶ thickObj R I e G₁ := Over.homMk r rfl
  let τ := g₁.isKernel.lift b (toUnit _) ((CharAgree.comp_q_eq_one_iff g₁ b).2 h)
  have hτ : τ ≫ g₁.i = b := g₁.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ t) ≫ g₂.i = b ≫ a := by rw [Category.assoc, ← hi, ← Category.assoc, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D₂ e G₂ g₂ FinalForm (τ ≫ t) 1 z J₂ hJ₂ x).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ FinalForm τ 1 z J₁ hJ₁ (f x)).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ t _).trans
    (congrArg τ.left.appTop.hom ((torusHomOf_iff_appTop _ _).1 ht x))

theorem acts_unique [IsAdicComplete I R] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    {a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left} {f f' : D₂.X → D₁.X}
    (h : Acts g₁ g₂ a f) (h' : Acts g₁ g₂ a f') : f = f' := by
  funext x
  have := EndTorus.connectedSpace_thickening I e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J₁ hJ₁ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (ψ z)
  choose J₂ hJ₂ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₂.P.A.left => exists_chart D₂.P.isLB (ψ z)
  have c := (CharAgree.comp_q_eq_one_iff g₁ g₁.i).1 g₁.isKernel.w
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ _ (𝟙 _) 1 z J₁ hJ₁ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J₁ J₂ hJ₁ hJ₂ c x).symm.trans (h' _ _ z J₁ J₂ hJ₁ hJ₂ c x)).trans (k _))


omit [IsDomain R] [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] in
theorem thickMap_comm (aG : G₁ ⟶ G₂) (e : ℕ) :
    thickMap R I e G₁ ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      ((Over.pullback (thick R I e)).map aG).left ≫ thickMap R I e G₂ := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem acts_down {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
    (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (aG : G₁ ⟶ G₂)
    {f : D₂.toPre.X → D₁.toPre.X}
    (h : Acts (U₁.gt (e + 1)) (U₂.gt (e + 1)) ((Over.pullback (thick R I (e + 1))).map aG).left f) :
    Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map aG).left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ c x
  have t : thickMap R I e G₁ ≫ (fstG I (e + 1) G₁).left = (fstG I e G₁).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : (r ≫ thickMap R I e G₁) ≫ (U₁.gt (e + 1)).pG.left =
      (r ≫ thickMap R I e G₁) ≫ (fstG I (e + 1) G₁).left ≫ G₁.hom ≫ eSec D₁.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U₁.gt_q e)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G₁.hom ≫ eSec D₁.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G₁) z J₁ J₂ hJ₁ hJ₂ up x
  have sq : (r ≫ thickMap R I e G₁) ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      (r ≫ ((Over.pullback (thick R I e)).map aG).left) ≫ thickMap R I e G₂ := by
    rw [Category.assoc, Category.assoc, thickMap_comm]
  rw [sq] at k
  exact (val_corr hJ₂ (U₂.gt_t e x) _).symm.trans ((val_pull hJ₂ _ _ _).trans (k.trans
    ((val_pull hJ₁ _ _ _).symm.trans (val_corr hJ₁ (U₁.gt_t e (f x)) r))))

theorem exists_torus_hom (hR : AdmBase R I) (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ h : D₂.X →+ D₁.X, ∃ t, TorusHomOf h t ∧ g₁.i ≫ a = t ≫ g₂.i := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := EndTorus.connectedSpace_thickening I e
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₂.i_hom
  have hk := g₂.isKernel
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  have : Mono g₂.i := by
    have : Mono (η[thickObj R I e D₂.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  let t := hk.lift (g₁.i ≫ a) (toUnit _) (by rw [Category.assoc, h1])
  have ht : t ≫ g₂.i = g₁.i ≫ a := hk.lift_fst _ _ _
  have : IsMonHom (t ≫ g₂.i) := ht ▸ inferInstance
  have : IsMonHom t := EndTorus.isMonHom_of_mono t g₂.i
  obtain ⟨h, hh⟩ := SplitTorusHom.exists_addMonoidHom t
  exact ⟨h, t, (torusHomOf_iff_appTop _ _).2 hh, ht.symm⟩

end GlobalTheory.Mum.Two.HomConst


open GlobalTheory.Mum.Two.HomConst in
theorem GlobalTheory.Mum.Two.unifPre_hom_character_const : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ h : D₂.toPre.X →+ D₁.toPre.X, OnTorus U₁ U₂ a h := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have ex := fun e => exists_torus_hom hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  choose h t ht hi using ex
  obtain ⟨-, -, -, hC⟩ := hR
  have down : ∀ (e : ℕ) (f : D₂.toPre.X → D₁.toPre.X),
      Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a).left f →
      Acts (U₁.gt 0) (U₂.gt 0) ((Over.pullback (thick R I 0)).map a).left f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun k => ih (acts_down U₁ U₂ a k)
  refine ⟨h 0, fun e => ⟨t e, ?_, hi e⟩⟩
  rw [← acts_unique _ _ (down e _ (acts_of_torusHomOf _ _ _ (ht e) (hi e)))
    (acts_of_torusHomOf _ _ _ (ht 0) (hi 0))]
  exact ht e
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem over₀_onTorus_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), (∀ b b' : D₁.toPre.P.A ⟶ D₂.toPre.P.A, Over₀ U₁ U₂ a b → Over₀ U₁ U₂ a b' → b = b') ∧ ∀ h h' : D₂.toPre.X → D₁.toPre.X, OnTorus U₁ U₂ a h → OnTorus U₁ U₂ a h' → h = h' := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a
  refine ⟨fun b b' hb hb' => ?_, fun h h' hh hh' => ?_⟩
  · obtain ⟨_, -, -, _⟩ := hR
    have := D₁.toPre.P.isAb.smooth
    have := D₁.toPre.P.isAb.geomConnected
    have := D₁.toPre.P.isAb.proper
    have := D₂.toPre.P.isAb.proper
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I) D₁.toPre.P.A).2 _ b b'
      fun e => ?_
    have := (U₁.gt e).q_flat
    have := (U₁.gt e).q_surj
    have := (U₁.gt e).q_affine
    have := FlatQuotient.epi_of_flat_surjective (U₁.gt e).q
    have k := congrArg (fun q => q.left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
      ((cancel_epi _).1 ((hb e).symm.trans (hb' e)))
    exact (pullback.lift_fst _ _ _).symm.trans (k.trans (pullback.lift_fst _ _ _))
  · have := hR.2.2.2
    have := EndTorus.connectedSpace_thickening I 0
    have : Mono (U₂.gt 0).i := by
      have : Mono (η[thickObj R I 0 D₂.toPre.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
      exact (MorphismProperty.monomorphisms _).of_isPullback (U₂.gt 0).isKernel.flip (.infer_property _)
    obtain ⟨t, ht, e⟩ := hh 0
    obtain ⟨t', ht', e'⟩ := hh' 0
    obtain rfl : t = t' := (cancel_mono _).1 (e.symm.trans e')
    funext χ
    exact SplitTorusHom.charUnit_injective (S := Sp (R ⧸ I ^ (0 + 1)))
      (congrArg Units.val ((ht χ).symm.trans (ht' χ)))

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomPullbackMaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.PullLin

open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

theorem act_proj₂ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} {A' B' : Over S'}
    (e : A' ⟶ (Over.pullback f).obj A) (e₂ : B' ⟶ (Over.pullback f).obj B) {u : A ⟶ B} {u' : A' ⟶ B'}
    (h : u' ≫ e₂ = e ≫ (Over.pullback f).map u) :
    u'.left ≫ e₂.left ≫ pullback.fst B.hom f = (e.left ≫ pullback.fst A.hom f) ≫ u.left := by
  have h1 : u'.left ≫ e₂.left = e.left ≫ ((Over.pullback f).map u).left := congrArg (·.left) h
  rw [← Category.assoc, h1, Category.assoc, map_left_fst, Category.assoc]

theorem torusHomOf_iff' {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') :
    TorusHomOf h t ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X'),
      gm (r ≫ t.left) z ⊤ (charUnit S X' χ) = gm r z ⊤ (charUnit S X (h χ)) := by
  constructor
  · intro H Z r z χ
    rw [← H χ]
    exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm
  · intro H χ
    refine unit_ext fun z _ => ?_
    rw [← H]
    exact (gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)


set_option maxHeartbeats 800000 in
theorem linPull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (D₁' D₂' : DegData R' I') (A₁' A₂' : PolAV (Sp (FractionRing R'))) (hD₁ : IsPullDeg φ D₁.toPre D₁'.toPre) (hD₂ : IsPullDeg φ D₂.toPre D₂'.toPre) (U₁' : Unif I' D₁' A₁' ((Over.pullback (specOf φ)).obj G₁)) (U₂' : Unif I' D₂' A₂' ((Over.pullback (specOf φ)).obj G₂)), IsPullUnif φ hD₁ (Iso.refl _) U₁ U₁' → IsPullUnif φ hD₂ (Iso.refl _) U₂ U₂' → ∀ (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁.toUnifPre U₂.toUnifPre a b h → ∃ (b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A) (h' : D₂'.toPre.X →+ D₁'.toPre.X), Lin U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) b' h' ∧ b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ∧ ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) := by
  intro R R' _ _ _ _ I I' φ D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ D₁' D₂' A₁' A₂' hD₁ hD₂ U₁' U₂' hU₁ hU₂ a b h hL
  obtain ⟨homA, homB, hq0, hi0⟩ := hL
  obtain ⟨_wL₁, -, _he₁, -, H₁⟩ := (isPullUnif_iff_stalks R R' I I' φ D₁ D₁' hD₁ A₁ A₁' G₁ _ (Iso.refl _) U₁ U₁').1 hU₁
  obtain ⟨_wL₂, -, _he₂, -, H₂⟩ := (isPullUnif_iff_stalks R R' I I' φ D₂ D₂' hD₂ A₂ A₂' G₂ _ (Iso.refl _) U₂ U₂').1 hU₂
  choose h₁ hf₁ hpt₁ _hw₁ using H₁
  choose h₂ hf₂ hpt₂ _hw₂ using H₂
  have := hD₁.e_hom
  have := hD₂.e_hom
  obtain ⟨b', homB', hB⟩ : ∃ b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A, IsMonHom b' ∧
      b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b :=
    ⟨hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ≫ hD₂.e.inv, inferInstance, by simp⟩
  obtain ⟨h', hx⟩ : ∃ h' : D₂'.toPre.X →+ D₁'.toPre.X, ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) :=
    ⟨hD₁.xe.symm.toAddMonoidHom.comp (h.comp hD₂.xe.toAddMonoidHom), fun χ => hD₁.xe.apply_symm_apply _⟩
  have hG : (Over.pullback (specOf φ)).map a ≫ (Iso.refl ((Over.pullback (specOf φ)).obj G₂)).hom =
      (Iso.refl ((Over.pullback (specOf φ)).obj G₁)).hom ≫ (Over.pullback (specOf φ)).map a := by simp
  have hact : ∀ e : ℕ, ((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left ≫ h₂ e =
      h₁ e ≫ ((Over.pullback (thick R I e)).map a).left := by
    intro e
    have hf' : h₂ e ≫ pullback.fst G₂.hom (thick R I e) =
        pullback.fst ((Over.pullback (specOf φ)).obj G₂).hom (thick R' I' e) ≫
          (Iso.refl ((Over.pullback (specOf φ)).obj G₂)).hom.left ≫ pullback.fst G₂.hom (specOf φ) := hf₂ e
    have hf₁' : h₁ e ≫ pullback.fst G₁.hom (thick R I e) =
        pullback.fst ((Over.pullback (specOf φ)).obj G₁).hom (thick R' I' e) ≫
          (Iso.refl ((Over.pullback (specOf φ)).obj G₁)).hom.left ≫ pullback.fst G₁.hom (specOf φ) := hf₁ e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G₂.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G₂.hom (thick R I e)), Category.assoc, hf', Category.assoc, map_left_fst,
      ← Category.assoc (h₁ e), hf₁',
      ← Category.assoc (((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left), map_left_fst,
      Category.assoc, act_proj₂ _ (Iso.refl _).hom (Iso.refl _).hom hG]
    simp only [Category.assoc]
  have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S} {e : ℕ}
      {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
      {B : Over (Spec (CommRingCat.of S))} (u : E.P.A ⟶ B), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
        pullback.fst B.hom (thick S J e) = g.pG.left ≫ u.left := by
    intro S _ _ J E e K _ _ g B u
    rw [Over.comp_left, Category.assoc, map_left_fst, pG_left, Category.assoc]
  have hB' := act_proj₂ (specOf φ) hD₁.e.hom hD₂.e.hom hB
  have k₂ : ∀ e, (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)) ≫
      (U₂'.gt e).pG = (U₁'.gt e).pG ≫ b' := by
    intro e
    have k₁ : ((Over.pullback (thick R I e)).map a).left ≫ (U₂.gt e).pG.left =
        (U₁.gt e).pG.left ≫ b.left := by
      rw [← k, ← hq0 e]
      exact (Category.assoc _ _ _).symm
    refine ext_of_iso_pullback _ hD₂.e ?_
    change (((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left ≫ (U₂'.gt e).pG.left) ≫ _ =
      ((U₁'.gt e).pG.left ≫ b'.left) ≫ _
    rw [Category.assoc, Category.assoc, hB', (hpt₂ e).1,
      ← Category.assoc (U₁'.gt e).pG.left, (hpt₁ e).1, ← Category.assoc, hact, Category.assoc,
      Category.assoc, k₁]
  have hq : ∀ e : ℕ, (Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a) ≫ (U₂'.gt e).q =
      (U₁'.gt e).q ≫ (Over.pullback (thick R' I' e)).map b' := by
    intro e
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) (k₂ e)
  refine ⟨b', h', ⟨inferInstance, homB', hq, fun e => ?_⟩, hB, hx⟩
  obtain ⟨t, ht, hi⟩ := hi0 e
  have hk : ((U₁'.gt e).i ≫ (Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)) ≫ (U₂'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D₂'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U₁'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U₂'.gt e).isKernel.lift_fst _ _ hk
  generalize (U₂'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U₁.gt e) (U₁'.gt e) (hpt₁ e).1 ((hpt₁ e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U₂.gt e).i).left = (t' ≫ (U₂'.gt e).i).left ≫ h₂ e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U₂.gt e) (U₂'.gt e) hD₂.w ((hpt₂ e).2 χ).1 ((hpt₂ e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U₁.gt e) (U₁'.gt e) hD₁.w ((hpt₁ e).2 (h' χ)).1 ((hpt₁ e).2 (h' χ)).2 (𝟙 _) τ hτ z
  have e₃ := (torusHomOf_iff' _ t).1 ht _ τ.left z (hD₂.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.Mum.Two.PullLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitMovesToFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UniEnlarge

open GlobalTheory.Mum.ClosureDescent GlobalTheory.ThetaDescent

theorem uniTrait_of_finExt : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂), FinExt i₁₂ → IsLocalHom i₁₂ → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → UniTrait D₂.toPre A₂ := by
  intro R₁ _ _ _ _ D₁ A hU R₂ _ _ _ i₁₂ hi₁₂ hl₁₂ D₂ ⟨hD₂⟩ A₂ a₂ hA₂
  classical
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD', a, hW, hφ, hφl, hG', ga, hga, g₁, l₁⟩ := hU
  obtain ⟨ga₂, hga₂, g₂, l₂⟩ := hA₂
  have hfin : i₁₂.Finite := hi₁₂.2.2
  let β : FractionRing W →+* AlgebraicClosure (FractionRing W) := algebraMap _ _
  have hβ : β.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := FractionRing W) x
  obtain ⟨j₁, hj₁⟩ := exists_extend hfin (algebraMap R₁ (FractionRing R₁)) ga₂ (RingHom.ext fun r => hga₂ r)
    (β.comp ga)
  have hjρ : ∀ r, j₁ (algebraMap R₂ _ (i₁₂ r)) = β (((algebraMap W (FractionRing W)).comp φ) r) := fun r => by
    rw [← hga₂, ← RingHom.comp_apply j₁ ga₂, hj₁, RingHom.comp_apply, hga, RingHom.comp_apply]
  obtain ⟨s₀, hs₀⟩ := exists_range_le_gen hfin β ((algebraMap W _).comp φ) j₁ hjρ
  let i := β.codRestrict _ (mem_gen β s₀)
  let k := j₁.codRestrict _ hs₀
  have hi : i.Finite := finite_gen β hβ s₀
  have := hW.1
  have hWb : Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩, hW.2.2⟩
  obtain ⟨W₁, _, _, _, io, σ, hio, hiol, hσ⟩ := GlobalTheory.CommonCover.exists_cover_field W hWb _ i hi
  obtain ⟨D₃, hD₃, A₃, U₃, a₃, hA₃⟩ := exists_unif_fib hWb.1 hio.1 io hio.2.1 (map_maximalIdeal_le io) hG' U'
    (σ.comp i) ((RingHom.comp_assoc _ _ _).trans hσ)
  have f₁ : Fib A₃ A ((σ.comp i).comp ga) (a₃ ≫ a) := hA₃.comp ⟨g₁, l₁⟩ rfl
  have e : (σ.comp k).comp ga₂ = (σ.comp i).comp ga := RingHom.ext fun x =>
    congrArg σ (Subtype.ext (DFunLike.congr_fun hj₁ x))
  obtain ⟨d, -, hd⟩ := Fib.cancel (σ.comp k) (⟨g₂, l₂⟩ : Fib A₂ A ga₂ a₂) f₁ e
  haveI := hio.1.2.2.1
  obtain ⟨φ₂, hφ₂, hcomp, hinj, hl⟩ := exists_restrict hfin (io.comp φ) (σ.comp k) fun r => by
    have e₁ : k (algebraMap R₂ _ (i₁₂ r)) = i (algebraMap W _ (φ r)) := Subtype.ext (hjρ r)
    exact (congrArg σ e₁).trans (DFunLike.congr_fun hσ (φ r))
  obtain ⟨q⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ hio.2.1 hD' hD₃
  rw [← hcomp] at q
  obtain ⟨q₁⟩ := GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel hi₁₂.2.1 hinj hD₂ q
  exact ⟨W₁, _, _, _, φ₂, _, inferInstance, inferInstance, D₃, A₃, U₃, q₁, d, cDvr_of_finExt hW hio, hinj, hl,
    IsSemiAbelian.pullback _ G' hG', σ.comp k, hφ₂, hd.1, hd.2⟩

end GlobalTheory.Mum.UniEnlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingClassicalTraitSameGeometricFibr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.USpread.noeth (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (z : M.Z) : IsNoetherianRing (M.O z) := by
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  exact isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem GlobalTheory.UPoinc.USpread.same_of_uSame {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω']
    [Algebra o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam}
    {φ : Ω →+* Ω'} (h : USame ρ ρ' lab φ) :
    Same ρ (fun _ => 𝟙 _) ρ' (fun _ => 𝟙 _) lab φ := by
  obtain ⟨P₀, a, a', ha, ha', hL, hL', ht⟩ := h
  exact ⟨P₀, a, a', fun _ => 𝟙 _, ha, ha', hL, hL', fun _ => ⟨by simp, by simp⟩, ht⟩

theorem GlobalTheory.UPoinc.USpread.endo_id {R O : Type} [CommRing R] [CommRing O] [IsDomain O] (f : R →+* O)
    (hf : ∀ o : O, ∃ a b : R, f b ≠ 0 ∧ f b * o = f a) (σ : Sp O ⟶ Sp O) (h : σ ≫ spMap f = spMap f) : σ = 𝟙 _ := by
  obtain ⟨s, rfl⟩ := Spec.map_surjective σ
  rw [← Spec.map_comp] at h
  have h' := Spec.map_injective h
  have hs : ∀ r, s.hom (f r) = f r := fun r => congrArg (fun g => g.hom r) h'
  have : s = 𝟙 _ := by
    ext o
    obtain ⟨a, b, hb, e⟩ := hf o
    have e2 := congrArg s.hom e
    rw [map_mul, hs, hs, ← e] at e2
    exact mul_left_cancel₀ hb e2
  rw [this, Spec.map_id]

theorem GlobalTheory.UPoinc.USpread.sec {R₁ R₂ O M Γ : Type} [CommRing R₁] [CommRing R₂] [CommRing O] [IsDomain O] {P₁ : PolAV (Sp R₁)} {P₂ : PolAV (Sp R₂)} {f₁ : R₁ →+* O} {f₂ : R₂ →+* O} {e₁ : M → (P₁.A ⟶ P₁.A)} {e₂ : M → (P₂.A ⟶ P₂.A)} {t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)} {t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)}
    (hf : ∀ o : O, ∃ a b : R₁, f₁ b ≠ 0 ∧ f₁ b * o = f₁ a) (h : SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂) :
    ∃ (P : PolAV (Sp O)) (b₁ : P.A.left ⟶ P₁.A.left) (b₂ : P.A.left ⟶ P₂.A.left), IsGrpPullback P.A P₁.A (spMap f₁) b₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) b₂ ∧ LBIso P.L (P₁.L.pull b₁) ∧ LBIso P.L (P₂.L.pull b₂) ∧ (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ b₁ = b₁ ≫ (e₁ E).left ∧ e.left ≫ b₂ = b₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp O ⟶ P.A.left, w ≫ P.A.hom = 𝟙 _ ∧ w ≫ b₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ b₂ = spMap f₂ ≫ (t₂ x).left := by
  obtain ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, ht⟩ := h
  refine ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, fun x => ?_⟩
  obtain ⟨w, w₁, w₂⟩ := ht x
  refine ⟨w, GlobalTheory.UPoinc.USpread.endo_id f₁ hf _ ?_, w₁, w₂⟩
  have := Over.w (t₁ x)
  rw [Category.assoc, ← h₁.1.w, ← Category.assoc, w₁, Category.assoc, this]
  exact Category.comp_id _

theorem GlobalTheory.UPoinc.USpread.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real), USame X.ρ ρ' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real), USame X.ρ ρ'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ ∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left := by
  intro E _ _ _ H Dw l Xo cf C X p _ z ct c₀ hc R' fg frac hth hev ρ' hS' hR' y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' hS'' hR'' y₁ hy₁ u u'
  set z' := (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) with hz'
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z') := GlobalTheory.UPoinc.USpread.noeth X.o₁ X.Ω₁ X.M z'
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z') := X.normal.isIntegrallyClosed_stalk z'
  haveI : IsIntegrallyClosed (X.M.O z') := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z')
  let ι' : R' →+* X.M.O z' := (Subalgebra.inclusion hR').toRingHom
  let ι'' : R'' →+* X.M.O z' := (Subalgebra.inclusion hR'').toRingHom
  have h0 := _root_.GlobalTheory.Poinc.SameComb.combine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (GlobalTheory.UPoinc.USpread.same_of_uSame hS') (GlobalTheory.UPoinc.USpread.same_of_uSame hS'')
  have h1 := _root_.GlobalTheory.Poinc.sameAt_of_generic (X.M.O z') X.Ω₁ _ _ _ _ _ _ ι' ι'' _ _ _ _ h0
  let v : X.M.O z' →+* PadicAlgCl p := RatModel.valHom (gPt p ≫ ct.y) z' (RatModel.range_eq_singleton _ _)
  have e₀ : v.comp ι' = y₀ := RingHom.ext fun a => (hy₀ a).symm
  have e₁ : v.comp ι'' = y₁ := RingHom.ext fun a => (hy₁ a).symm
  have hfr : ∀ o : X.M.O z', ∃ a b : R', ι' b ≠ 0 ∧ ι' b * o = ι' a := by
    intro o
    obtain ⟨a, ha, b, hb, e⟩ := frac (o : X.Ω₁)
    by_cases hb0 : b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : o = 0 := Subtype.ext (by simpa [hb0] using e)
      simp [this]
    · refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hb0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      change b * (o : X.Ω₁) = a
      rw [e]; field_simp
  obtain ⟨P₀, a, a', ha, ha', hL, hL', ht, -⟩ := GlobalTheory.Poinc.Special.main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.UPoinc.USpread.sec hfr h1) v u.yK u'.yK
    (u.fac.trans e₀.symm) (u'.fac.trans e₁.symm) u.A u'.A u.φ u'.φ u.cart u'.cart u.lb u'.lb
  refine ⟨P₀, a, a', ha, ha', hL, hL', fun b => ?_⟩
  obtain ⟨w, hw, h₁, h₂⟩ := ht b
  have q₁ : (w ≫ a) ≫ u.A.A.hom = jFK (R := u.V) (PadicAlgCl p) := by
    rw [Category.assoc, ha.1.w, ← Category.assoc, hw, Category.id_comp]
  have q₂ : (w ≫ a') ≫ u'.A.A.hom = jFK (R := u'.V) (PadicAlgCl p) := by
    rw [Category.assoc, ha'.1.w, ← Category.assoc, hw, Category.id_comp]
  refine ⟨w, Over.homMk (w ≫ a) q₁, Over.homMk (w ≫ a') q₂, hw, rfl, rfl, ?_, ?_⟩
  · simpa [e₀] using h₁
  · simpa [e₁] using h₂
end

