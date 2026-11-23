module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameExpansionFramedPointGenerator
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GeneratorFrame

section Bundles
variable {X Y Z : Scheme.{0}}

theorem gs_linComb_one (L : LB X) (x : X) (j j' : Fin 1 → L.ι)
    (hj : (𝟙 X : X ⟶ X) x ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j)
    (hj' : (𝟙 X : X ⟶ X) x ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j') :
    gs (𝟙 X) x _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))).g j j').val =
      gs (𝟙 X) x _ (L.g (j 0) (j' 0)).val := by
  have h₁ : (𝟙 X : X ⟶ X) x ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨Set.mem_iInter.1 hj 0, Set.mem_iInter.1 hj' 0⟩
  refine (gs_unit (𝟙 X) x _ (show _ ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ⊓ _ from ⟨hj, hj'⟩) _).trans
    (Eq.trans ?_ (gs_unit (𝟙 X) x _ h₁ _).symm)
  refine congrArg Units.val ((gm_linComb L _ _ (𝟙 X) x j j' hj hj').trans ?_)
  simp only [Fin.prod_univ_one, Nat.cast_one, zpow_one, Category.comp_id]

theorem le_wchart (L : LB X) (i : L.ι) : L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem wchart_le' (L : LB X) (j : Fin 1 → L.ι) : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) :=
  fun _ hy => Set.mem_iInter.1 hy 0

def toPow {L : LB X} (θ : LB.Sec L) : H0 L 1 where
  f := fun j => (X.presheaf.map (homOfLE (wchart_le' L j)).op).hom (θ.f (j 0))
  compat := fun j j' => fn_ext fun y hy => by
    have h₁ : (𝟙 X : X ⟶ X) y ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨wchart_le' L j hy.1, wchart_le' L j' hy.2⟩
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.1 _)).trans (Eq.trans ?_
      ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_linComb_one L y j j' hy.1 hy.2)
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.2 _)))).symm)
    exact (gs_res (𝟙 X) y _ h₁ _).symm.trans ((congrArg (gs (𝟙 X) y _) (θ.compat (j 0) (j' 0))).trans
      ((gs_mul (𝟙 X) y _ h₁ _ _).trans (congrArg₂ (· * ·) rfl (gs_res (𝟙 X) y _ h₁ _))))

def ofPow {L : LB X} (s : H0 L 1) : LB.Sec L where
  f := fun i => (X.presheaf.map (homOfLE (le_wchart L i)).op).hom (s.f (fun _ => i))
  compat := fun i i' => fn_ext fun y hy => by
    have h₁ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ⊓
      LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i') := ⟨le_wchart L i hy.1, le_wchart L i' hy.2⟩
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.1 _)).trans (Eq.trans ?_
      ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_linComb_one L y _ _ h₁.1 h₁.2).symm
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.2 _)))).symm)
    exact (gs_res (𝟙 X) y _ h₁ _).symm.trans ((congrArg (gs (𝟙 X) y _) (s.compat (fun _ => i) (fun _ => i'))).trans
      ((gs_mul (𝟙 X) y _ h₁ _ _).trans (congrArg₂ (· * ·) rfl (gs_res (𝟙 X) y _ h₁ _))))

theorem spans_toPow {R : Type} [CommRing R] (p : X ⟶ Sp R) {L : LB X} (θ : LB.Sec L)
    (h : ∀ σ : LB.Sec L, ∃ a : R, ∀ i, σ.f i = resG X le_top (p.appTop.hom (toΓ R a)) * θ.f i) (s : H0 L 1) :
    ∃ b : R, SecIsMul p b s (toPow θ) := by
  obtain ⟨a, ha⟩ := h (ofPow s)
  refine ⟨a, fun (j : Fin 1 → L.ι) => fn_ext fun y hy => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
  have h₁ : (𝟙 X : X ⟶ X) y ∈ L.U i := wchart_le' L _ hy
  refine (gs_res (𝟙 X) y (le_wchart L i) h₁ _).symm.trans ((congrArg (gs (𝟙 X) y _) (ha i)).trans
    ((gs_mul (𝟙 X) y _ h₁ _ _).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy _ _).symm)))
  exact congrArg₂ (· * ·) ((gs_res (𝟙 X) y le_top h₁ _).trans (gs_res (𝟙 X) y le_top hy _).symm)
    (gs_res (𝟙 X) y _ hy _).symm

theorem gs_isoMaps {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s') (r : Z ⟶ X)
    (z : Z) (i : M.ι) (k : L.ι) (hi : r z ∈ M.U i) (hk : r z ∈ L.U k) :
    gs r z (M.U i) (s'.f i) = (gv w r z i k).val * gs r z (L.U k) (s.f k) := by
  have hm : r z ∈ M.U i ⊓ L.U k := ⟨hi, hk⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (h i k)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem gs_appLE' (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens) (h : V ≤ g ⁻¹ᵁ U) (hz : r z ∈ V)
    (a : Γ(X, U)) : gs r z V ((g.appLE U V h).hom a) = gs (r ≫ g) z U a :=
  (gs_res r z h hz ((g.app U).hom a)).trans (gs_pull r g z U (h hz) a)

theorem exists_spanning {R : Type} [CommRing R] (p : X ⟶ Sp R) {L L' : LB X} (e : L = L') (θ : LB.Sec L)
    (h : ∀ σ : LB.Sec L, ∃ a : R, ∀ i, σ.f i = resG X le_top (p.appTop.hom (toΓ R a)) * θ.f i)
    {M : LB Y} (f : Y ⟶ X) (w : LB.Iso M (L.pull f)) (σ : LB.Sec M) (θ₂ : LB.Sec (L.pull f))
    (hm : IsoMaps w σ θ₂) (hp : PullSec f θ θ₂) :
    ∃ ϑ : H0 L' 1, (∀ s : H0 L' 1, ∃ b : R, SecIsMul p b s ϑ) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L'.ι) (j' : M.ι), Good L' z J → r z ∈ M.U j' →
        sval ϑ (r ≫ f) z J = (gv (isoCast e f w) r z (fun _ => J (r ≫ f)) j').val * gs r z (M.U j') (σ.f j') := by
  subst e
  refine ⟨toPow θ, spans_toPow p θ h, fun Z r z J j' hJ hj' => ?_⟩
  have h₁ : r z ∈ (L.pull f).U (fun _ => J (r ≫ f)) := mem_pull.2 (hJ (r ≫ f))
  have le : (L.pull f).U (fun _ => J (r ≫ f)) ≤ f ⁻¹ᵁ L.U (J (r ≫ f)) := fun _ hy => mem_pull.1 hy
  refine Eq.trans ?_ (gs_isoMaps hm r z _ j' h₁ hj')
  rw [sval_of _ (r ≫ f) z J (fun _ => J (r ≫ f)) (fun _ => by rw [Category.comp_id]), hp _ le, gs_appLE' r f z _ _ le h₁]
  exact gs_res (r ≫ f) z _ (le_wchart L _ (hJ (r ≫ f))) _

end Bundles

theorem secLin_of_secScal {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    {R : Type} [CommRing R] (π : Y' ⟶ Spec (CommRingCat.of R))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ (fun _ : Fin 1 => s₂) h (fun _ => Out.scal π (1 : R)) := by
  intro j₁ j₂ hc
  have e : Out.scal π (1 : R) = 1 := by simp [Out.scal]
  have := H j₁ j₂ hc
  rw [Fin.sum_univ_one, e, this]
  simp only [map_one, _root_.one_mul]

theorem thFrame_of_spanning (hL : Laws) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (ϑ : H0 U.LG.L 1) (hsp : ∀ s : H0 U.LG.L 1, ∃ b : V, SecIsMul G.hom b s ϑ)
    (F : Type) [Field F] [Algebra (FractionRing V) F] (σ : U.toUnifPre.SecGF F 1)
    (hσ : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => UnifPre.gFK (R := V) (G := G) F) (fun _ => ((1 : ℕ) : ℤ)) σ
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) ϑ (UnifPre.gFK (R := V) (G := G) F) 1)
    (θ : Fam D.toPre F 1) (hθ : U.toUnifPre.ExpandsG F 1 σ θ) : ThFrame D ϖ F θ := by
  obtain ⟨ϑ₀, h₀, -⟩ := ThetaSectionTest.exists_isTheta_of_dvr hL V D A G U
  have hϑ : IsTheta U ϑ := ThetaLocalDomain.main hL V _ le_rfl D A G U ϑ
    ((ThetaSectionTest.spans_iff_nonzero hL.globalFns hL.secBaseChange le_rfl U h₀ ϑ).1 hsp)
  obtain ⟨sK, hsK⟩ := IndivisibleSection.exists_pull_val U.LG.isLB ϑ (pullback.fst G.hom (jK V))
    (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK V)) (ε' := fun _ => ((1 : ℕ) : ℤ))
    (fun U _ h => by simp only [Category.comp_id])
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 sK
  obtain ⟨g, hgE, hg⟩ := _root_.GlobalTheory.ExpInt.main V ϖ hϖ D A G U.toUnifPre 1 ϑ sK
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => (hsK _ _ y J hJ).symm) E hE
  obtain ⟨θ', hθ'⟩ := FamBaseChange.main hL.globalFns V (maximalIdeal V) D 1 E g hg F
  have hx : U.toUnifPre.ExpandsG F 1 σ θ' := ⟨1, fun _ => 1, fun _ => ϑ, fun _ => g, fun _ e => hgE e,
    secLin_of_secScal _ hσ, fun α => secLin_of_secScal _ (hθ' α)⟩
  obtain rfl : θ = θ' :=
    ((FieldBaseChange.expandsG_bijective U.toUnifPre F hL.globalFns le_rfl (U.expand 1 le_rfl)).1 σ).unique hθ hx
  refine ⟨g 0, θ.s 0, hθ' 0, fun _ => rfl, ?_⟩
  rintro ⟨g', hg''⟩
  have hg' : SecIsMul D.toPre.P.A.hom ϖ (g 0) g' := hg''
  obtain ⟨f, hfE, hf⟩ := hϑ 0
  have hd := GlobalTheory.expandsAt_sub V _ D A G U.toUnifPre 0 1 ϑ ϑ SecOps.secZero f g
    (fun α => SecOps.secAdd (f α) (SecOps.secNeg (g α))) (fun j => (sub_self _).symm)
    (fun α j => (sub_eq_add_neg _ _).symm) hfE (hgE 0)
  obtain ⟨h, hh⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U.toUnifPre 0 1 0 _).1
    (WeightPf.weightIndep V _ D A G U.toUnifPre 0 1 _ _ (fun j => map_zero _) hd 0)
  rw [zero_add, pow_one] at hh
  refine hϖ.not_isUnit (ThetaNu.isUnit_of_generates (t := SecOps.secAdd h g') hf fun j => ?_)
  have e₁ : (f 0).f j + - (g 0).f j = _ := hh j
  have e₂ := hg' j
  show _ = _ * (h.f j + g'.f j)
  rw [mul_add, ← e₁, ← e₂, neg_add_cancel_right]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (ϖ : T.V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y yF → ∀ (σ : P.U.toUnifPre.SecGF F 1) (θ : Fam P.D.toPre F 1), SecTieF I P F yF.x 1 σ yF.s → P.U.toUnifPre.ExpandsG F 1 σ θ → ThFrame P.D ϖ F θ := by
  intro E _ _ _ H Dw l Xo c T io y I P ϖ hϖ F _ _ φ hφ yF hy σ θ ht hθ
  let _ := io.toAlgebra
  let _ : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  obtain ⟨hx, -, pm, hp₁, hp₂, hpm⟩ := hy
  rw [hφ] at hx hp₂
  obtain ⟨ϑ, hsp, hϑ⟩ := exists_spanning I.G.G.hom (congrArg RigLB.L P.bundle).symm I.θ
    (fun s => (I.θgen s).exists) I.m2.φ I.w2 I.σ I.θ2 I.maps2 I.pull
  refine thFrame_of_spanning GlobalTheory.firstFiveLaws.1 hϖ P.U ϑ hsp F σ
    (SectionScalarValuation.secScal_of_sval P.U.LG.isLB fun z J₂ hJ₂ => ?_) θ hθ
  let a : (UnifPre.GF (R := T.V) (G := I.G.G) F).left ⟶ Sp F :=
    (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left
  have w : UnifPre.gFK (R := T.V) (G := I.G.G) F ≫ I.G.G.hom =
      (a ≫ spMap (algebraMap T.Fr F)) ≫ spMap (algebraMap T.V T.Fr) := by
    have e₁ : (snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left ≫ pullback.snd I.G.G.hom (jK T.V) =
        a ≫ spMap (algebraMap T.Fr F) :=
      (Over.w (snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G))).trans
        (Over.w (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G))).symm
    rw [← e₁]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : (UnifPre.GF (R := T.V) (G := I.G.G) F).left ⟶ I.t'.G.left,
      r ≫ I.m2.φ = UnifPre.gFK (R := T.V) (G := I.G.G) F ∧ r ≫ I.t'.G.hom = a ≫ spMap (algebraMap T.Fr F) :=
    ⟨I.m2.cart.1.lift _ _ w, I.m2.cart.1.lift_fst _ _ w, I.m2.cart.1.lift_snd _ _ w⟩
  have w₁ : I.m1.φ ≫ Xo.univ.t.G.hom = I.t'.G.hom ≫ y.x := I.m1.cart.1.w
  obtain ⟨g, hg₁, hg₂⟩ : ∃ g : I.t'.G.left ⟶ Gx y.x, g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = I.m1.φ ∧
      g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = I.t'.G.hom :=
    ⟨pullback.lift (f := y.x) (g := Xo.univ.t.G.hom) _ _ w₁.symm, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  have w₂ : a ≫ yF.x = (r ≫ I.m1.φ) ≫ Xo.univ.t.G.hom := by
    rw [Category.assoc, w₁, ← Category.assoc, hr₂, hx, Category.assoc]
  obtain ⟨zU, hz₁, hz₂⟩ : ∃ zU : (UnifPre.GF (R := T.V) (G := I.G.G) F).left ⟶ Gx yF.x,
      zU ≫ (snd (Over.mk yF.x) Xo.univ.t.G).left = r ≫ I.m1.φ ∧ zU ≫ (fst (Over.mk yF.x) Xo.univ.t.G).left = a :=
    ⟨pullback.lift (f := yF.x) (g := Xo.univ.t.G.hom) _ _ w₂, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  have hz₃ : zU ≫ (fst (Over.mk yF.x) Xo.univ.t.G).left ≫ spMap (algebraMap T.Fr F) = r ≫ I.t'.G.hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hz₂).trans hr₂.symm)
  have hc : zU ≫ pm = r ≫ g := by
    refine pullback.hom_ext (f := y.x) (g := Xo.univ.t.G.hom) ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (zU ≫ ·) hp₂).trans (hz₃.trans
        ((congrArg (r ≫ ·) hg₂).symm.trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (zU ≫ ·) hp₁).trans (hz₁.trans
        ((congrArg (r ≫ ·) hg₁).symm.trans (Category.assoc _ _ _).symm)))
  choose J₁ hJ₁ using fun χ : (UnifPre.GF (R := T.V) (G := I.G.G) F).left ⟶ Xo.univ.t.G.left =>
    exists_chart Xo.univ.t.PP.isLB (χ z)
  obtain ⟨j', hj'⟩ := exists_chart I.t'.PP.isLB (r z)
  have key := ht.2 _ r (𝟙 _) zU ((Category.id_comp _).trans hr₁.symm) hz₁ ((Category.id_comp _).trans hz₂.symm) hz₃
    z J₁ J₂ j' hJ₁ hJ₂ hj'
  have h₁ : r z ∈ (Xo.univ.t.PP.L.pull I.m1.φ).U (fun _ => J₁ (r ≫ I.m1.φ)) := mem_pull.2 (hJ₁ (r ≫ I.m1.φ))
  have le₁ : (Xo.univ.t.PP.L.pull I.m1.φ).U (fun _ => J₁ (r ≫ I.m1.φ)) ≤
      g ⁻¹ᵁ (PPx y.x).U (fun _ => J₁ (r ≫ I.m1.φ)) := fun x hx => Set.mem_iInter.2 fun _ => by
    have := mem_pull.1 hx
    rw [← hg₁] at this ⊢
    exact this
  have le₂ : (PPx yF.x).U (fun _ => J₁ (r ≫ I.m1.φ)) ≤ pm ⁻¹ᵁ (PPx y.x).U (fun _ => J₁ (r ≫ I.m1.φ)) :=
    fun x hx => Set.mem_iInter.2 fun _ => by
      have : (snd (Over.mk yF.x) Xo.univ.t.G).left x ∈ Xo.univ.t.PP.L.U (J₁ (r ≫ I.m1.φ)) := Set.mem_iInter.1 hx 0
      rw [← hp₁] at this
      exact this
  have h₂ : zU z ∈ (PPx yF.x).U (fun _ => J₁ (r ≫ I.m1.φ)) := Set.mem_iInter.2 fun _ => by
    have := hJ₁ (r ≫ I.m1.φ)
    generalize J₁ (r ≫ I.m1.φ) = i at this ⊢
    rw [← hz₁] at this
    exact this
  have v₁ : sval yF.s zU z J₁ = (gv I.w1 r z (fun _ => J₁ (r ≫ I.m1.φ)) j').val * gs r z _ (I.σ.f j') := by
    refine Eq.trans ?_ (gs_isoMaps I.maps1 r z _ j' h₁ hj')
    refine (sval_of yF.s zU z J₁ (fun _ => J₁ (r ≫ I.m1.φ)) (fun _ => congrArg J₁ hz₁)).trans ?_
    refine (congrArg (gs zU z _) (hpm _ le₂).symm).trans ((gs_appLE' zU pm z _ _ le₂ h₂ _).trans ?_)
    rw [hc]
    exact ((congrArg (gs r z _) (I.gen1 g hg₁ hg₂ _ le₁)).trans (gs_appLE' r g z _ _ le₁ h₁ _)).symm
  refine ((congrArg (fun q => sval ϑ q z J₂) ((Category.id_comp _).trans hr₁.symm)).trans
    (hϑ _ r z J₂ j' hJ₂ hj')).trans ?_
  rw [pow_one, pow_one] at key
  refine (Units.mul_left_inj (gv I.w1 r z (fun _ => J₁ (r ≫ I.m1.φ)) j')).1 (Eq.trans ?_ key.symm)
  refine Eq.trans ?_ (congrArg (· * _) v₁.symm)
  ring

end GlobalTheory.GeneratorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameFamiliesDifferByValuationZeroUnit
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ThetaFrameLine

section
variable {V : Type} [CommRing V] [IsDomain V]

theorem cst_prB (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (y : (DegPre.BF D F).left) (a : V) :
    Geo.Tor.cst ((𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom) y a =
      gs (𝟙 _) y ⊤ (gF D F (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a))) := by
  have hw : (DegPre.prB D F).left ≫ D.P.A.hom = (fst (TF (R := V) F) D.P.A).left ≫ jFK (R := V) F ≫ jK V :=
    (Over.w (DegPre.prB D F)).trans (Over.w (fst (TF (R := V) F) D.P.A)).symm
  have e : (jFK (R := V) F ≫ jK V).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a)) := by
    have h := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))))
    have h' := congrArg (fun f => f.hom a) h
    rw [jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact h'.symm
  rw [Category.assoc, hw, Geo.Tor.cst]
  refine (gs_pull (𝟙 _) _ y ⊤ trivial _).symm.trans (congrArg (gs (𝟙 _) y ⊤) ?_)
  exact congrArg (fst (TF (R := V) F) D.P.A).left.appTop.hom e

end

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ θ θ' : Fam D.toPre F 1, ThFrame D ϖ F θ → ThFrame D ϖ F θ' → ∃ u : F, v u = 0 ∧ Fam.IsSmul D.toPre F u θ θ' := by
  intro V _ _ _ _ ϖ hϖ D F _ _ v hv θ θ' h h'
  obtain ⟨σ, σF, hs, he, hn⟩ := h
  obtain ⟨τ, τF, ht, hf, hm⟩ := h'
  have hL := D.toPre.P.isLB
  have gσ := GlobalTheory.IndivisibleSection.secBGenerates_of_not_dvd GlobalTheory.firstFiveLaws.1.secBaseChange V ϖ hϖ D σ hn
  obtain ⟨a, ha, -⟩ := gσ τ
  have hu : IsUnit a := by
    by_contra hna
    have hmem : a ∈ maximalIdeal V := hna
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hmem
    obtain ⟨b, rfl⟩ := hmem
    refine hm ⟨SecOps.secScale (Out.scal D.toPre.P.A.hom b) σ, ?_⟩
    show SecIsMul D.toPre.P.A.hom ϖ τ (SecOps.secScale (Out.scal D.toPre.P.A.hom b) σ)
    intro j
    refine (ha j).trans ?_
    simp only [SecOps.secScale, Out.scal, resTop, map_mul, _root_.mul_assoc]
  refine ⟨algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a), ?_, ?_⟩
  · have := hv (algebraMap V (FractionRing V) a) 0 ⟨hu.unit, by simp⟩
    simpa using this
  · set u := algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a) with hudef
    have eθ : θ.s 0 = σF := SecOps.sec_ext he
    have eθ' : θ'.s 0 = τF := SecOps.sec_ext hf
    have h0 : ∀ j, (θ'.s 0).f j = ((u • θ).s 0).f j := by
      refine sec_ext_val hL fun y J hJ => ?_
      have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hs (𝟙 _) y hJ
      have e₂ := GlobalTheory.PullIntegral.sval_of_secScal ht (𝟙 _) y hJ
      have e₃ := GlobalTheory.IndivisibleSection.sval_of_secIsMul ha (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y hJ
      have o : gs (𝟙 (DegPre.BF D.toPre F).left) y ⊤ 1 = 1 := by
        rw [gs_eq _ y ⊤ trivial, map_one, map_one]
      rw [o, _root_.one_mul] at e₁ e₂
      rw [e₁, e₂, cst_prB, ← eθ, ← eθ'] at e₃
      refine e₃.trans ?_
      have hmem := hJ.mem (DegPre.famφ D.toPre F 0) (𝟙 _)
      exact ((gs_mul (𝟙 _) y _ hmem _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) y le_top hmem _) rfl)).symm
    refine (isSmul_iff u θ θ').2 (sub_eq_zero.1 (fam_ext fun α j => TG.fam_eq_zero hϖ (θ' - u • θ) (fun j => ?_) α j))
    exact (congrArg (· + -((u • θ).s 0).f j) (h0 j)).trans (add_neg_cancel _)

end GlobalTheory.ThetaFrameLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaValueNaturalField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) (hm : FrMap ψ y z) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    (hF : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x (x b)) (F b)) :
    ∃ F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo z.x)),
      (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) z.s (levPt Xo z.x (x b)) (F' b)) ∧
      ψ (thExpr Xo c nab y P F) = thExpr Xo c nab z P F' := by
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  choose F' hF' using fun b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2)
    (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b)
  refine ⟨F', fun b => ?_, ?_⟩
  · have e : h ≫ levPt Xo y.x (x b) = levPt Xo z.x (x b) := by
      unfold levPt
      rw [← Category.assoc, comp_toUnit]
    rw [← e]
    exact (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo l.M (l.Mb ^ 2) _ _ h y.s z.s
      (GlobalTheory.FramedBaseChange.isPullSec ψ hm h rfl) (F b) (F' b) (hF' b)).1 _ (hF b)
  · unfold thExpr
    rw [map_mul, AlgHom.commutes,
      _root_.GlobalTheory.harmonicValue_baseChange_field E H Dw l Xo c nab hnab S T ψ y z hm h rfl a n P hP.1 l.M F F' hF']

theorem exists_algHom_field (F U : Type) [Field F] [CommRing U] [Algebra F U] [Nontrivial U] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K), Nonempty (U →ₐ[F] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal U
  exact ⟨U ⧸ m, Ideal.Quotient.field m, inferInstance, ⟨Ideal.Quotient.mkₐ F m⟩⟩

theorem thetaValue_natural_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S T : Type) [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S T _ _ _ _ φ y0 y hφ a n x P hP v0 w hv hw
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨S₁, i₁, j₁, φ₁, y₁, F₁, hff₁, hm₁, hV₁, he₁⟩ := hv
  obtain ⟨T₁, i₂, j₂, κ, y₂, F₂, hff₂, hm₂, hV₂, he₂⟩ := hw
  obtain ⟨U, iU, jU, ψ₁, ψ₂, hcomm, -, hinj⟩ :=
    exists_faithfullyFlat_pushout c.F S T₁ S₁ (κ.comp φ) φ₁ hff₁
  have hκ : Function.Injective κ := hff₂.injective
  haveI : Nontrivial U := (hinj.comp hκ).nontrivial
  obtain ⟨K, iK, jK, ⟨π⟩⟩ := exists_algHom_field c.F U
  have hψ : (π.comp ψ₁).comp (κ.comp φ) = (π.comp ψ₂).comp φ₁ := by
    rw [AlgHom.comp_assoc, hcomm, AlgHom.comp_assoc]
  obtain ⟨z, hz1⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c T₁ K (π.comp ψ₁) y₂
  have hz : FrMap ((π.comp ψ₂).comp φ₁) y0 z :=
    hψ ▸ GlobalTheory.FramedBaseChange.trans (κ.comp φ) (π.comp ψ₁) (FramedBaseChange.trans φ κ hφ hm₂) hz1
  have hz2 : FrMap (π.comp ψ₂) y₁ z := GlobalTheory.FramedBaseChange.cancel φ₁ (π.comp ψ₂) hm₁ hz
  obtain ⟨G1, w1, e1⟩ := exists_pull nab hnab (π.comp ψ₁) y₂ z hz1 a n x P hP F₂ hV₂
  obtain ⟨G2, w2, e2⟩ := exists_pull nab hnab (π.comp ψ₂) y₁ z hz2 a n x P hP F₁ hV₁
  have hG : G1 = G2 := funext fun b => vtUniq_obj hL.globalFns Xo.univ (w1 b) (w2 b)
  apply ((π.comp ψ₁).comp κ).toRingHom.injective
  change (π.comp ψ₁) (κ (φ v0)) = (π.comp ψ₁) (κ w)
  rw [he₂, e1, hG, ← e2, ← he₁]
  exact AlgHom.congr_fun hψ v0

end GlobalTheory.ThetaField
end
end

