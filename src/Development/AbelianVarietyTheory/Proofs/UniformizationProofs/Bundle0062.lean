module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.RigidPullbackIdentification
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullDegCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent ptK_comp)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)ˣ) :
    res h₂ (res h₁ s) = res (h₂.trans h₁) s := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)ˣ) : res h s = s := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have : (homOfLE h).op = 𝟙 _ := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem res_eq_iff {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (h' : U ≤ V) (s t : Γ(X, U)ˣ) :
    res h s = res h t ↔ s = t :=
  ⟨fun e => by
    have := congrArg (res h') e
    rwa [res_res, res_res, res_self, res_self] at this, fun e => e ▸ rfl⟩

section Bundle

variable {X X' Y : Scheme.{0}} (L : LB X) (L' : LB X') (F : X' ⟶ X)

theorem corr_iff_eq (p : Y ⟶ X) (n : ℤ)
    (b c : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    LB.Gen.Corr L _ _ _ _ b c ↔ b = c := by
  constructor
  · intro h
    obtain ⟨b⟩ := b
    obtain ⟨c⟩ := c
    congr 1
    funext j
    have := h j j (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    exact (res_eq_iff _ (le_inf le_rfl le_rfl) _ _).1 this
  · rintro rfl j j' _ _ h
    obtain rfl : j = j' := funext fun k => h k k rfl
    rfl

theorem exists_mapsAt_iff (w : LB.Iso L' (L.pull F)) (p' : Y ⟶ X') (p : Y ⟶ X) (hp : p' ≫ F = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n)))
    (c : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    (∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p' ≫ F) (fun _ => n)),
      GeneratorPullback.MapsAt L L' (J := PUnit) (fun _ => F) w p' n a b ∧ LB.Gen.Corr L _ _ _ _ b c) ↔
    CarriesAt L L' F w p' p hp n a c := by
  subst hp
  constructor
  · rintro ⟨b, hb, hc⟩ j j'
    obtain rfl := (corr_iff_eq L _ n b c).1 hc
    exact hb (fun _ => j) j'
  · intro h
    exact ⟨c, fun jN jL => h (jN PUnit.unit) jL, (corr_iff_eq L _ n c c).2 rfl⟩

end Bundle

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']

theorem rig_iff [IsCommMonObj G] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (f : S' ⟶ S)
    (he : eSec G' ≫ F = f ≫ eSec G) (L : LB G.left) (L' : LB G'.left) (w : LB.Iso L' (L.pull F))
    (r : LB.Gen (L.pull (eSec G))) (r' : LB.Gen (L'.pull (eSec G'))) :
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) r' (rigPullOf F f he L r) ↔
    CarriesAt L L' F w (eSec G') (f ≫ eSec G) he 1 r' (LB.pullGen L _ _ r f) := by
  have key : ∀ (j : L.ι) (j' : L'.ι),
      (res (inf_le_left : _ ⊓ (L'.pull (eSec G')).U (fun _ => j') ≤ _) ((rigPullOf F f he L r).s (fun _ _ => j)) =
        @id (Γ((𝟙_ (Over S')).left, ((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => j'))ˣ)
          ((LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)).s (fun _ _ => j, fun _ => j')) *
          res inf_le_right (r'.s (fun _ => j'))) ↔
      res (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.chart_le_target L L' F (eSec G') (f ≫ eSec G) he j j')
          ((LB.pullGen L _ _ r f).s (fun _ => j)) =
        (pullU (eSec G') _ (w.s (fun _ => j, j'))) ^ (1 : ℤ) *
          res (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.chart_le_source L L' F (eSec G') j j') (r'.s (fun _ => j')) := by
    intro j j'
    have h₁ : ((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => j') ≤
        eSec G' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') :=
      fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩
    have h₂ : eSec G' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') ≤
        ((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => j') :=
      fun y hy => ⟨Set.mem_iInter.2 fun _ => hy.1, Set.mem_iInter.2 fun _ => hy.2⟩
    rw [← res_eq_iff h₁ h₂, map_mul, map_zpow]
    refine Eq.congr ?_ (congrArg₂ (· * ·) (Fintype.prod_unique fun _ : PUnit =>
      res h₁ (pullU (eSec G') _ (w.s (fun _ => j, j'))) ^ (1 : ℤ)) ?_)
    · exact (res_res _ _ _).trans ((res_res _ _ _).trans (res_res _ _ _)).symm
    · exact (res_res _ _ _).symm
  exact ⟨fun h j j' => (key j j').1 (h (fun _ _ => j, fun _ => j')),
    fun h p => (key (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit)).2 (h _ _)⟩

theorem isGrpPullback_iff {f : S' ⟶ S} {F : G'.left ⟶ G.left} (cart : IsPullback F G'.hom G.hom f) :
    IsGrpPullback G' G f F ↔ (μ[G']).left ≫ F =
      pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ (μ[G]).left := by
  have m : ∀ (T : Over S') (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G),
      x₀.left = x.left ≫ F → y₀.left = y.left ≫ F → (lift x₀ y₀).left = (lift x y).left ≫
        pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm := by
    intro T x y x₀ y₀ hx hy
    apply pullback.hom_ext
    · have e₁ : (lift x₀ y₀).left ≫ pullback.fst G.hom G.hom = x₀.left := congrArg (·.left) (lift_fst x₀ y₀)
      have e₂ : (lift x y).left ≫ pullback.fst G'.hom G'.hom = x.left := congrArg (·.left) (lift_fst x y)
      refine e₁.trans (hx.trans ?_)
      rw [← e₂, Category.assoc, Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _).symm
    · have e₁ : (lift x₀ y₀).left ≫ pullback.snd G.hom G.hom = y₀.left := congrArg (·.left) (lift_snd x₀ y₀)
      have e₂ : (lift x y).left ≫ pullback.snd G'.hom G'.hom = y.left := congrArg (·.left) (lift_snd x y)
      refine e₁.trans (hy.trans ?_)
      rw [← e₂, Category.assoc, Category.assoc]
      exact congrArg _ (pullback.lift_snd _ _ _).symm
  constructor
  · intro h
    have e := h.2 _ (fst G' G') (snd G' G') (pushPt cart.w _) (pushPt cart.w _) rfl rfl
    have e' := m _ (fst G' G') (snd G' G') (pushPt cart.w _) (pushPt cart.w _) rfl rfl
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left, e', lift_fst_snd, Over.id_left] at e
    exact e.symm.trans (congrArg (· ≫ _) (Category.id_comp _))
  · intro h
    refine ⟨cart, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, m T x y x₀ y₀ hx hy, Category.assoc]
    exact (Category.assoc _ _ _).trans (congrArg _ h.symm)

end Grp

section Main

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

abbrev OpenChoice (φ : R →+* R') (D : DegPre R) : Type :=
  Σ W : (Spec (CommRingCat.of R)).Opens,
    PsiOn D W × {g : (TK R').left ⟶ (TW W).left // g ≫ W.ι = jK R' ≫ specOf φ}

def PsiCarried (p : PullIdent φ D D') (o : OpenChoice φ D) : Prop :=
  ∀ χ : D'.X, CarriesAt D.P.L D'.P.L p.F p.w (D'.xK χ) (o.2.2.1 ≫ (toUnit (TW o.1) ≫ D.c (p.xe χ)).left)
    (ptK_comp φ p.F (D.c (p.xe χ)) (D'.c χ) (p.c_eq χ) o.1 o.2.2.1 o.2.2.2) (-1) (D'.psi χ)
    (LB.pullGen D.P.L _ _ (o.2.1.psi (p.xe χ)) o.2.2.1)

def toOpenChoice (h : IsPullDeg φ D D') : OpenChoice φ D := ⟨h.W, h.psiW, h.g, h.g_comm⟩

theorem psi_pr_carries (h : IsPullDeg φ D D') (χ : D'.X) :
    CarriesAt D.P.L D'.P.L (h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h.w (D'.xK χ)
      (h.g ≫ (toUnit (TW h.W) ≫ D.c (h.xe χ)).left)
      (ptK_comp φ _ (D.c (h.xe χ)) (D'.c χ) (h.c_pr χ) h.W h.g h.g_comm) (-1) (D'.psi χ)
      (LB.pullGen D.P.L _ _ (h.psiW.psi (h.xe χ)) h.g) :=
  (exists_mapsAt_iff D.P.L D'.P.L _ h.w _ _ _ (-1) _ _).1 (h.psi_pr χ)

def toIdent (h : IsPullDeg φ D D') : PullIdent φ D D' where
  F := h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  cart := (pull_grp h).1
  F_one := h.he
  F_mul := (isGrpPullback_iff (pull_grp h).1).1 (pull_grp h)
  w := h.w
  w_gen := h.w_gen
  w_rig := (rig_iff _ _ h.he _ _ h.w D.rig D'.rig).1 h.w_rig
  xe := h.xe
  c_eq := h.c_pr
  w_psi := ⟨h.W, h.psiW, h.g, h.g_comm, psi_pr_carries h⟩

theorem exists_toIdent_eq (p : PullIdent φ D D') (o : OpenChoice φ D) (H : PsiCarried p o) :
    ∃ h : IsPullDeg φ D D', toIdent h = p ∧ toOpenChoice h = o := by
  obtain ⟨e, me, he⟩ := grpPullback_iso ((isGrpPullback_iff p.cart).2 p.F_mul)
    (isGrpPullback_pullback D.P.A (specOf φ))
  obtain ⟨F, cart, F₁, Fm, w, wg, wr, xe, ce, wp⟩ := p
  dsimp only at he
  subst he
  exact ⟨⟨e, me, w, wg, F₁, (rig_iff _ _ F₁ _ _ w D.rig D'.rig).2 wr, xe, ce, o.1, o.2.1, o.2.2.1, o.2.2.2,
    fun χ => (exists_mapsAt_iff D.P.L D'.P.L _ w _ _ _ (-1) _ _).2 (H χ)⟩, rfl, rfl⟩

theorem toIdent_surjective : Function.Surjective (toIdent : IsPullDeg φ D D' → PullIdent φ D D') := fun p => by
  obtain ⟨W, ψW, g, hg, H⟩ := p.w_psi
  obtain ⟨h, e, -⟩ := exists_toIdent_eq p ⟨W, ψW, g, hg⟩ H
  exact ⟨h, e⟩

theorem nonempty_iff : Nonempty (IsPullDeg φ D D') ↔ Nonempty (PullIdent φ D D') :=
  ⟨fun ⟨h⟩ => ⟨toIdent h⟩, fun ⟨p⟩ => let ⟨h, _⟩ := toIdent_surjective p; ⟨h⟩⟩

end Main

end GlobalTheory.PullDegCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineZeroConst
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem line_zero_const {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F (DegPre.zeroF D F)) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      (val w r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TF (R := R) F).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TF (R := R) F).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 w hw
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show h (DegPre.zeroF D F).left ^ (k : ℤ) * h (DegPre.zeroF D F).left ^ (-(k : ℤ)) = 1
      rw [zpow_neg, mul_inv_cancel])
  obtain ⟨c, rfl⟩ : ∃ c : F, (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = a :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have hc : c ≠ 0 := by
    rintro rfl
    let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e := ha _ (𝟙 _) z I hI
    rw [gs_eq _ z ⊤ trivial, map_zero] at e
    exact (val w (𝟙 _) z I).ne_zero (e.trans ((congrArg _ (map_zero _)).trans (map_zero _)))
  refine ⟨Units.mk0 c hc, fun Z r z J hJ => ?_⟩
  have e := ha Z r z J hJ
  rw [Category.comp_id] at e
  exact e

theorem trPt_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] : DegPre.trPt D F (DegPre.zeroF D F) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [DVR.tr_fst, Category.id_comp]
  · refine (DVR.tr_pr D F _).trans ?_
    have : fst (TF (R := R) F) D.P.A ≫ DegPre.zeroF D F = 1 := MonObj.comp_one (M := D.P.A) _
    rw [this, _root_.mul_one, Category.id_comp]

theorem phiRaw_torus : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))), g.b = DegPre.zeroF D F → w.IsGen → ∃ c : Fˣ, ∀ s s' : Raw D F k, PhiRaw D F k 0 g w s s' → (∀ α, (∃ j, (s α).f j ≠ 0) → ∀ z J, Good D.P.L z J → val (g.s α) (𝟙 _) z J = 1) → ∀ α j, (s' α).f j = DegPre.constBF D F c.val _ * (s α).f j := by
  intro R _ _ D F _ _ k g w hb hw
  obtain ⟨b, gs', hg, h0, hm⟩ := g
  dsimp only at hb w
  subst hb
  obtain ⟨c, hc⟩ := line_zero_const D F k w hw
  refine ⟨c, fun s s' H hs α j => ?_⟩
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.phiφ D F 0 α (DegPre.zeroF D F)) (ε' := DegPre.deltaε k)
    (fun U _ h => by
      have e₁ : padd D.P.A (DegPre.cF D F α) (DegPre.zeroF D F) = DegPre.cF D F α :=
        _root_.mul_one (DegPre.cF D F α)
      rw [DegPre.phiφ, trPt_zero, add_zero]
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := U) _ (c := 1) (c' := 1) ?_ ?_)
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) rfl
          (DVR.prod_neg _ _ (c := ∏ i, h (DegPre.famφ D F α i) ^ DegPre.famε k i) ?_)).symm)
      · simp [Fin.prod_univ_four, DegPre.gtφ, DegPre.gtε, e₁]
      · simp [Fin.prod_univ_two, DegPre.lineφ, DegPre.lineε]
      · simp
      · simp)
    (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (gs' α) w) (fst (TF (R := R) F) D.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (hg α) hw) _)
  have z₁ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) (toUnit _ ≫ η[D.P.A]))
  have rel := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H α u hu (corr_of_val D.P.isLB fun y J hJ => by
    rw [val_pull hJ, vu _ _ y J hJ, val_pull hJ, Category.id_comp, z₁]))
  have key : ∀ y J, Good D.P.L y J → sval (s' α) (𝟙 _) y J = sval (s α) (𝟙 _) y J *
      ((val (gs' α) (fst (TF (R := R) F) D.P.A).left y J).val *
        gs (fst (TF (R := R) F) D.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val)) := by
    intro y J hJ
    have e := rel _ (𝟙 _) y J hJ
    rw [vu _ _ y J hJ, val_pull hJ, val_mul hJ, Category.id_comp, Category.id_comp, Units.val_mul, hc _ _ y J hJ] at e
    dsimp only at e
    rw [trPt_zero, add_zero] at e
    exact e
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hI' : Good D.P.L y I := hI
  have e₁ := sec_trans (s' α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₂ := sec_trans (s α) (𝟙 _) y hy (hI'.mem _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (DegPre.constBF D F c.val _ * (s α).f j) =
      gs (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c.val) *
        gs (𝟙 _) y (LB.wchart D.P.L (DegPre.famφ D F α) j) ((s α).f j) :=
    (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) y le_top hy _).trans
      (gs_pull (𝟙 _) (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _)) rfl)
  rw [Category.id_comp] at e₃
  have e₄ : sval (s α) (𝟙 _) y I * (val (gs' α) (fst (TF (R := R) F) D.P.A).left y I).val = sval (s α) (𝟙 _) y I := by
    by_cases hz : ∃ j, (s α).f j ≠ 0
    · have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (gs' α) (LB.oneGen D.P.L) :=
        corr_of_val D.P.isLB fun z J hJ => (hs α hz z J hJ).trans (val_one _).symm
      rw [val_corr hI' hcorr, val_one, Units.val_one, _root_.mul_one]
    · push_neg at hz
      have : sval (s α) (𝟙 _) y I = 0 :=
        (congrArg (gs (𝟙 _) y _) (hz _)).trans ((gs_eq _ y _ (hI'.mem _ (𝟙 _)) _).trans
          ((congrArg _ (map_zero _)).trans (map_zero _)))
      rw [this, MulZeroClass.zero_mul]
  have e₅ := key y I hI'
  rw [← _root_.mul_assoc, e₄] at e₅
  refine e₁.trans (Eq.trans ?_ (e₃.trans (congrArg _ e₂)).symm)
  refine (congrArg _ e₅).trans ?_
  rw [sval]; ring

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MatchingSectionsExist
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UnitSec

section Gen
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y)
    (hφ : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  exact ⟨_, fun Z r z J hJ => DVR.SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

theorem exists_push {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (g : Y ⟶ Y')
    (h₁ : g ≫ h = 𝟙 Y) (h₂ : h ≫ g = 𝟙 Y')
    (hφ : ∀ k, φ' k = h ≫ φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_pull (φ' := φ) g
    (fun k => by rw [hφ k, ← Category.assoc, h₁, Category.id_comp]) s'
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, Category.assoc, h₂, Category.comp_id]

end Gen

theorem unit_inv_snd {S : Scheme.{0}} (G : Over S) :
    (λ_ G).inv.left ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 G.left := by
  rw [← Over.comp_left, leftUnitor_inv_snd, Over.id_left]

theorem snd_unit_inv {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ (Over S)) G).left ≫ (λ_ G).inv.left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]

theorem famφT_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : Fin 4) : famφT D T α k = (snd T D.P.A).left ≫ D.famφB α k := by
  fin_cases k
  · change (snd T D.P.A).left = (snd T D.P.A).left ≫ 𝟙 _
    rw [Category.comp_id]
  · change (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (snd T D.P.A).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left]; congr 1
    simp only [padd]
    rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ D.c α).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]

theorem same_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (G : Over (Spec (CommRingCat.of R))) (L : LB G.left), L.IsLB → ∀ k : ℕ, (∀ σ : H0 L k, ∃ σ', SameG σ σ') ∧ (∀ σ', ∃ σ : H0 L k, SameG σ σ') ∧ (∀ f : ∀ α, D.SecB k α, ∃ f', SameB f f') ∧ ∀ f', ∃ f : ∀ α, D.SecB k α, SameB f f' := by
  intro R _ _ D G L _ k
  refine ⟨fun σ => ?_, fun σ' => ?_, fun f => ?_, fun f' => ?_⟩
  · exact exists_pull (snd _ G).left (fun _ => (Category.comp_id _).symm) σ
  · exact exists_push (φ := fun _ : Fin 1 => 𝟙 G.left) (snd _ G).left (λ_ G).inv.left (unit_inv_snd G)
      (snd_unit_inv G) (fun _ => (Category.comp_id _).symm) σ'
  · choose f' hf' using fun α => exists_pull (snd _ D.P.A).left (famφT_eq D (𝟙_ _) α) (f α)
    exact ⟨f', hf'⟩
  · choose f hf using fun α => exists_push (snd _ D.P.A).left (λ_ D.P.A).inv.left (unit_inv_snd _)
      (snd_unit_inv _) (famφT_eq D (𝟙_ _) α) (f' α)
    exact ⟨f, hf⟩

end GlobalTheory.UnitSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullBValues
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem pullB_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T₀ : Over (Spec (CommRingCat.of R))) (φ : TF (R := R) F ⟶ T₀) (k : ℕ) (f : ∀ α, SecBT D T₀ k α) (s : Raw D F k), PullB D F φ k f s → ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TF (R := R) F) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (s α) (lift ρ x).left z J = sval (f α) (lift (ρ ≫ φ) x).left z J := by
  intro R _ _ D F _ _ T₀ φ k f s h α T ρ x z J hJ
  have e : (lift ρ x).left ≫ (φ ▷ D.P.A).left = (lift (ρ ≫ φ) x).left := by
    rw [← Over.comp_left, lift_whiskerRight]
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) (lift ρ x).left z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left (lift ρ x).left z J hJ).2.1 (f α)
  have hJ' : Good D.P.L ((lift ρ x).left z) (fun ψ => J ((lift ρ x).left ≫ ψ)) := fun ψ => hJ _
  rw [e] at b
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)

end GlobalTheory
end

