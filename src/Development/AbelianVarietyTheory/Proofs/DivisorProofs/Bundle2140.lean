module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationClassPullbackEqConstantAddEps
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham

theorem exists_const_add_eps_const {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    (z : TensorProduct K (DualNumber K) (primDR A)) :
    ∃ a b : primDR A, liftSemi (constMor A).pull z =
      (constMor A).pull a + (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  induction z with
  | add x y hx hy =>
    obtain ⟨a, b, e⟩ := hx
    obtain ⟨a', b', e'⟩ := hy
    refine ⟨a + a', b + b', ?_⟩
    rw [map_add (f := _), e, e', map_add (f := _), map_add (f := _), smul_add]
    abel
  | tmul r c =>
    refine ⟨r.fst • c, r.snd • c, ?_⟩
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, smul_smul]
    have e1 : (TrivSqZeroExt.inl r.fst : DualNumber K) = algebraMap K (DualNumber K) r.fst := rfl
    have e2 : (TrivSqZeroExt.inr r.snd : DualNumber K) = DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [DualNumber.inr_eq_smul_eps, Algebra.smul_def, mul_comm]
    have er : r = algebraMap K (DualNumber K) r.fst + DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [← e1, ← e2, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
    conv_lhs => rw [er]
    exact add_smul _ _ _

theorem liftMor_pull_eq_const_add_eps : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → ∀ x : primDR A', ∃ b : primDR A,
      (liftMor (epsDP K) h).pull x = (constMor A).pull ((fibMor h).pull x) +
        (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  intro P K _ A _ A' _ i h g hA hg x
  have a₀ : IsAbelianScheme A := by
    haveI := hA.comm
    haveI : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  obtain ⟨z, hz⟩ := constMor_surjective P a₀ g₀ ((liftMor (epsDP K) h).pull x)
  obtain ⟨a, b, e⟩ := exists_const_add_eps_const z
  rw [hz] at e
  have red : (redMor A).pull ((liftMor (epsDP K) h).pull x) = (fibMor h).pull x :=
    GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (fibMor h) (fun _ => rfl) (by simp) x
  have ra : (fibMor h).pull x = a := by
    rw [← red, e, map_add (f := _), LinearMap.map_smulₛₗ, redMor_constMor, redMor_constMor]
    have : (TrivSqZeroExt.fstHom K K K).toRingHom (DualNumber.eps : DualNumber K) = 0 := rfl
    rw [this, zero_smul, add_zero]
  exact ⟨b, by rw [ra]; exact e⟩

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPreDataLawsOfGeneratorValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

namespace GenTr

theorem stalkMap_gm_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (q : Z ⟶ Y) (hq : r ≫ g = q) (z : Z)
    (J : (Z ⟶ X) → L.ι) :
    val t q z J = Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) := by
  subst hq
  rw [val_of t g (r z) _ (fun k => J ((r ≫ g) ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact (stalkMap_gm_comp r g z _ _).symm

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R := by
  have := Over.w (toUnit (TK R))
  simpa using this

theorem val_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

end GenTr

open GenTr

theorem rlaws_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ (w0 : O) (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
    GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ →
    ∃ h : ∀ y, (LB.pullGen D₀.P.L _ _ (ψ y) (jK R)).IsGen,
      letI : Module O ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).X :=
        ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).OAct O,
        oa.onB = onB ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) y
          Set.univ := by
  intro R _ _ D₀ O _ _ _ onB hc w0 uw huw hnw ψ hR
  obtain ⟨hgen, h1, h2, h3, h4⟩ := hR
  have hL := D₀.P.isLB
  have htu := toUnit_TK_left R
  let Dn : DegPre R := { D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _ }
  have Fψ : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ y,
      val (Dn.psi y) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val (ψ y) (𝟙 _) ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ y => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp) _ _)
  have Frig : ∀ (z : (TK R).left) J, Good D₀.P.L z J →
      val Dn.rigK (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (rigV D₀ ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp [htu]) _ _)
  have Ftau : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a b : D₀.X,
      val (Dn.tau a b) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (tauV D₀ ψ ((jK R) z) (fun f => J (jK R ≫ f)) a b) := by
    intro z J hJ a b
    rw [val_tau Dn hJ, Fψ z J hJ, Fψ z J hJ, Fψ z J hJ, Frig z J hJ, tauV, map_mul, map_mul, map_mul, map_inv, map_inv,
      map_inv]
    rfl
  have Fx : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K] (φ : K → (D₀.P.A.left ⟶ D₀.P.A.left))
      (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.xK y)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val t (D₀.c y).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp]
    show _ = (toUnit (TK R) ≫ D₀.c y).left
    rw [Over.comp_left, htu]
  have F2 : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K]
      (φ : K → ((D₀.P.A ⊗ D₀.P.A).left ⟶ D₀.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y y' : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.pt2 y y')) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val t (lift (D₀.c y) (D₀.c y')).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y y'
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt2, ← htu, ← Over.comp_left, comp_lift]
  have Fcub : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a a' b : D₀.X,
      val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val D₀.cub.t (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ a a' b
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt3, ← htu, ← Over.comp_left, comp_lift, comp_lift]
  refine ⟨fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _, ⟨onB, hc, ?_⟩, rfl, ?_, ?_, ⟨uw, huw, hnw, ?_⟩, ?_⟩
  · intro a u hu hun y y'
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Ftau z J hJ, F2 z J hJ, Ftau z J hJ, ← map_mul]
    exact congrArg _ (h3 a u hu hun y y' _ _ fun f => hJ _)
  · intro χ
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Fψ z J hJ, Fx z J hJ, Fψ z J hJ, ← map_mul]
    exact congrArg _ (h2 χ _ _ fun f => hJ _)
  · intro a a' b
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau (a + a') b) (𝟙 _) z J *
        val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
          val (Dn.tau a b) (𝟙 _) z J * val (Dn.tau a' b) (𝟙 _) z J := by
      rw [Ftau z J hJ, Fcub z J hJ, Ftau z J hJ, Ftau z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h1 a a' b _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau y (w0 • y)) (𝟙 _) z J * val (LB.pullGen D₀.P.L _ _ uw (Dn.xK y)) (𝟙 _) z J =
        val (Dn.psi y) (𝟙 _) z J * val Dn.rigK (𝟙 _) z J := by
      rw [Ftau z J hJ, Fx z J hJ, Fψ z J hJ, Frig z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h4 y _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y j V _ _ hV h
    have hle : V ≤ LB.wchart D₀.P.L (fun _ : PUnit => (D₀.c y).left) j :=
      fun x hx => Set.mem_iInter.2 fun _ => hV hx
    refine ⟨(res hle ((ψ y).s j)).val, Units.isUnit _, ?_⟩
    have e := congrArg (fun q => q.hom ((ψ y).s j).val) ((jK R).naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    refine e.trans ?_
    show _ = ((TK R).left.presheaf.map (homOfLE h).op).hom (((TK R).left.presheaf.map (homOfLE _).op).hom
      (((jK R).app _).hom ((ψ y).s j).val))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

end GlobalTheory.UTau0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationContractionLieDerivativeDeRhamRules
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B)

theorem indLeft {P : DR R B → Prop} (h : ∀ b : B, P (algebraMap B _ b)) (ha : ∀ x y, P x → P y → P (x + y))
    (hm : ∀ (ω : Ω[B⁄R]) x, P x → P (ι1 ω * x)) (x : DR R B) : P x :=
  CliffordAlgebra.left_induction (P := P) 0 h ha (fun x m hx ↦ hm m x hx) x

theorem ctr_algebraMap (b : B) : ctr v (algebraMap B (DR R B) b) = 0 := by
  simp [ctr]

theorem ctr_ι (ω : Ω[B⁄R]) : ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω) := by
  simp [ctr]

theorem ctr_ι_mul (ω : Ω[B⁄R]) (x : DR R B) :
    ctr v (ι1 ω * x) = v.liftKaehlerDifferential ω • x - ι1 ω * ctr v x :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

theorem ctr_mul (x y : DR R B) : ctr v (x * y) = ctr v x * y + sgn x * ctr v y := by
  induction x using indLeft with
  | h b =>
    rw [← Algebra.smul_def, map_smul, ctr_algebraMap, zero_mul, zero_add, AlgHom.commutes, Algebra.smul_def]
  | ha x x' hx hx' => rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), map_add (f := _), add_mul, add_mul]; abel
  | hm ω x ih =>
    rw [mul_assoc, ctr_ι_mul, ih, ctr_ι_mul, map_mul, sgn_ι]
    simp only [mul_add, sub_mul, smul_mul_assoc, mul_assoc, neg_mul]
    abel

theorem ctr_ctr (x : DR R B) : ctr v (ctr v x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

theorem ctr_sgn (x : DR R B) : ctr v (sgn x) = -sgn (ctr v x) := by
  induction x using indLeft with
  | h b => rw [AlgHom.commutes, ctr_algebraMap, map_zero, neg_zero]
  | ha x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _), neg_add]
  | hm ω x ih =>
    rw [map_mul, sgn_ι, neg_mul, map_neg, ctr_ι_mul, ih, ctr_ι_mul, map_sub, map_smul, map_mul, sgn_ι, mul_neg, neg_mul]

theorem ctr_mem_pred {n : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^n Ω[B⁄R]) : ctr v x ∈ ⋀[B]^(n - 1) Ω[B⁄R] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap b => rw [ctr_algebraMap]; exact zero_mem _
  | add x y i _ _ hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    change ctr v (ι1 ω * x) ∈ _
    rw [ctr_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    cases i with
    | zero =>
      change x ∈ LinearMap.range _ ^ 0 at hx
      rw [pow_zero] at hx
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 hx
      rw [ctr_algebraMap, mul_zero]; exact zero_mem _
    | succ k =>
      have := mul_mem (ι_mem ω) ih
      rwa [Nat.add_sub_cancel, add_comm] at this

theorem ctr_mem {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^(j + 1) Ω[B⁄R]) : ctr v x ∈ ⋀[B]^j Ω[B⁄R] := by
  simpa using ctr_mem_pred v hx

theorem lie_apply (x : DR R B) : lie v x = dDR R B (ctr v x) + ctr v (dDR R B x) := rfl

theorem lie_mul (x y : DR R B) : lie v (x * y) = lie v x * y + x * lie v y := by
  simp only [lie_apply, ctr_mul, dDR_mul, map_add (f := _), ctr_sgn, dDR_sgn, sgn_sgn, neg_mul, add_mul, mul_add]
  abel

theorem lie_algebraMap (b : B) : lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b) := by
  rw [lie_apply, ctr_algebraMap, map_zero, zero_add, dDR_algebraMap, ctr_ι,
    Derivation.liftKaehlerDifferential_comp_D]

theorem lie_D (b : B) : lie v (ι1 (D R B b)) = ι1 (D R B (v b)) := by
  rw [lie_apply, ctr_ι, Derivation.liftKaehlerDifferential_comp_D, dDR_algebraMap, dDR_D, map_zero, add_zero]

theorem lie_dDR (x : DR R B) : lie v (dDR R B x) = dDR R B (lie v x) := by
  rw [lie_apply, lie_apply, dDR_dDR, map_zero, add_zero, map_add (f := _), dDR_dDR, zero_add]

theorem lie_ctr (x : DR R B) : lie v (ctr v x) = ctr v (lie v x) := by
  rw [lie_apply, lie_apply, ctr_ctr, map_zero, zero_add, map_add (f := _), ctr_ctr, add_zero]

theorem lie_mem {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^j Ω[B⁄R]) : lie v x ∈ ⋀[B]^j Ω[B⁄R] := by
  cases j with
  | zero =>
    have hx' := hx
    change x ∈ LinearMap.range _ ^ 0 at hx'
    rw [pow_zero] at hx'
    obtain ⟨b, rfl⟩ := Submodule.mem_one.1 hx'
    rw [lie_algebraMap]
    change _ ∈ LinearMap.range _ ^ 0
    rw [pow_zero]; exact Submodule.algebraMap_mem _
  | succ k =>
    rw [lie_apply]
    exact add_mem (dDR_mem (ctr_mem v hx)) (ctr_mem v (dDR_mem hx))

theorem ctr_lie_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ b, ctr v (algebraMap B (DR R B) b) = 0) ∧ (∀ ω, ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω)) ∧ (∀ x y, ctr v (x * y) = ctr v x * y + sgn x * ctr v y) ∧ (∀ x, ctr v (ctr v x) = 0) ∧ (∀ x, ctr v (sgn x) = -sgn (ctr v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], ctr v x ∈ ⋀[B]^j Ω[B⁄R]) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ x y, lie v (x * y) = lie v x * y + x * lie v y) ∧ (∀ b, lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b)) ∧ (∀ b, lie v (ι1 (D R B b)) = ι1 (D R B (v b))) ∧ (∀ x, lie v (dDR R B x) = dDR R B (lie v x)) ∧ (∀ x, lie v (ctr v x) = ctr v (lie v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^j Ω[B⁄R], lie v x ∈ ⋀[B]^j Ω[B⁄R] :=
  ⟨fun _ _ _ _ _ v ↦ ⟨ctr_algebraMap v, ctr_ι v, ctr_mul v, ctr_ctr v, ctr_sgn v, fun _ _ hx ↦ ctr_mem v hx⟩,
    fun _ _ _ _ _ v ↦ ⟨lie_mul v, lie_algebraMap v, lie_D v, lie_dDR v, lie_ctr v, fun _ _ hx ↦ lie_mem v hx⟩⟩

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectNormalisedEqOne
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm

theorem tripleFibreProductProjOneThree_comp_fst {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.fst f f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

theorem tripleFibreProductProjOneThree_comp_snd {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.snd f f = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

theorem defect_eq_one_of_coboundary {X Y Z : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (hL : L.IsLB)
    (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (z : X ⟶ X)
    (ρ : pullback f f ⟶ pullback f f) (σ : Triple f ⟶ Triple f)
    (h₁ : ρ ≫ pullback.fst f f = pullback.fst f f ≫ z) (h₂ : ρ ≫ pullback.snd f f = pullback.snd f f ≫ z)
    (k₁ : σ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (k₂ : σ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (g : X ⟶ Z) (U : L.ι → Z.Opens) (s : ∀ i, Γ(Z, U i)ˣ)
    (hN : ∀ (T : Scheme.{0}) (r : T ⟶ pullback f f) (t : T) (i j : L.ι),
      pullback.fst f f (ρ (r t)) ∈ L.U i → pullback.snd f f (ρ (r t)) ∈ L.U j →
      gm (r ≫ ρ) t _ (φ i j) =
        (gm (r ≫ pullback.fst f f ≫ g) t _ (s i))⁻¹ * gm (r ≫ pullback.snd f f ≫ g) t _ (s j))
    (hD : Defect f L φ D) (w : Triple f) : gm σ w ⊤ D = 1 := by
  have c : pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f := pullback.condition
  have k₃ : σ ≫ pr13 f = pr13 f ≫ ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_fst, h₁, ← Category.assoc, k₁, Category.assoc, h₁,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_fst]
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_snd, h₂, ← Category.assoc, k₂, Category.assoc, h₂,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_snd]
  obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)))
  have e := hD _ σ w i j k hi hj hk
  have p₁ : ρ (pullback.fst (pullback.snd f f) (pullback.fst f f) w) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₁.symm
  have p₂ : ρ (pullback.snd (pullback.snd f f) (pullback.fst f f) w) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₂.symm
  have p₃ : ρ (pr13 f w) = pr13 f (σ w) := congrArg (fun m => m w) k₃.symm
  have pc : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) =
      pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) c.symm
  have q₁ : pullback.fst f f (pr13 f (σ w)) =
      pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_fst f)
  have q₂ : pullback.snd f f (pr13 f (σ w)) =
      pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_snd f)
  have a := hN _ (pullback.fst (pullback.snd f f) (pullback.fst f f)) w i j (by rw [p₁]; exact hi)
    (by rw [p₁]; exact hj)
  have b := hN _ (pullback.snd (pullback.snd f f) (pullback.fst f f)) w j k (by rw [p₂, pc]; exact hj)
    (by rw [p₂]; exact hk)
  have d := hN _ (pr13 f) w i k (by rw [p₃, q₁]; exact hi) (by rw [p₃, q₂]; exact hk)
  simp only [← Category.assoc] at a b d
  rw [tripleFibreProductProjOneThree_comp_fst, tripleFibreProductProjOneThree_comp_snd] at d
  rw [← c] at b
  rw [k₁, k₂, k₃, a, b, d, _root_.mul_assoc, mul_inv_cancel_left] at e
  exact mul_eq_right.1 e

theorem defect_normalised : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → ∀ (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) (D : Γ(Triple (q ▷ B).left, ⊤)ˣ), NormAlong q P τ φ → Defect (q ▷ B).left P φ D → ∀ w : Triple (q ▷ B).left, gm (rhoW q) w ⊤ D = 1 := by
  intro K _ A A' B _ _ q P τ hP φ D hN hD w
  exact defect_eq_one_of_coboundary (q ▷ B).left P hP φ D (zb A B).left (rhoZ q) (rhoW q) (rhoZ_fst q) (rhoZ_snd q)
    (rhoW_fst q) (rhoW_snd q) (fst A B).left _ (fun i => τ.s fun _ => i) hN hD w

end GlobalTheory.DescNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepFixesIntegralUnipotentInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.NabFix

theorem nab_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv n hn
  change GlobalTheory.InertDbl.UD σ G.W →* _ at omd
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) with hΦdef
  obtain ⟨c, hc⟩ := GlobalTheory.T.doubledWeil_inert_place_vacuum_eigenfunction F E σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv n hn.1
  change omd n Φ = c • Φ at hc
  obtain ⟨s, hs, hsn⟩ := GlobalTheory.T.integralUnipotentRadical_conj_to_square_inertPlace F E σ B hTr.base (a + a') G.W v w hin n hn
  have hs1 : omd s Φ = Φ := GlobalTheory.T.doubledWeilRep_fixes_vacuum_tensor_siegelParabolic_inert F E σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv s hs
  have hs2 : omd s⁻¹ Φ = Φ := by
    conv_lhs => rw [← hs1]
    change (omd _ * omd _) Φ = Φ
    rw [← omd.map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  have e1 : omd (s * n * s⁻¹) Φ = c • Φ := by
    simp only [omd.map_mul, mul_apply_eq_comp, hs2, hc, map_smul, hs1]
  have e2 : omd (n * n) Φ = (c * c) • Φ := by
    simp only [omd.map_mul, mul_apply_eq_comp, hc, map_smul, smul_smul]
  rw [hsn, e2] at e1
  by_cases hΦ : Φ = 0
  · rw [hΦ, map_zero]
  have hcc : c * c = c := smul_left_injective ℂ hΦ e1
  have h01 : c = 0 ∨ c = 1 := by
    rcases mul_eq_zero.1 (show c * (c - 1) = 0 by linear_combination hcc) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases h01 with h0 | h1
  · exfalso
    apply hΦ
    have : omd n⁻¹ (omd n Φ) = Φ := by
      change (omd n⁻¹ * omd n) Φ = Φ
      rw [← omd.map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
    rw [← this, hc, h0, zero_smul, map_zero]
  · change omd n Φ = Φ
    rw [hc, h1, one_smul]

end GlobalTheory.NabFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_symmetric_lineBundle_grpScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (M₀ : LB G.left), IsAmpleLB M₀ → ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  first | exact @GlobalTheory.SymAmple.exists_isAmpleLB_symm | exact GlobalTheory.SymAmple.exists_isAmpleLB_symm | (intros; apply GlobalTheory.SymAmple.exists_isAmpleLB_symm <;> assumption)
end

