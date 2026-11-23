module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFOfIntegral
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange

theorem gs_pullOver {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) (s : SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y') (z : Z) (j : K → L.ι)
    (hj : ∀ k, φ' k (r z) ∈ L.U (j k)) :
    gs r z (LB.wchart L φ' j) (LB.Sec.f (pullOver L ε hp hφ s) j) = gs (r ≫ p) z (LB.wchart L φ j) (LB.Sec.f s j) :=
  gs_pullFn hp _ _ r z (mem_wchart.2 hj)

section Act

variable {S₀ : Scheme.{0}} {A : Over S₀} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S₀}
  {S : Type} [CommRing S]

theorem lpow_ext (hL : L.IsLB) {s s' : LB.Sec (LPow A L k T)}
    (h : ∀ y J, Good L y J → secVal s (𝟙 _) y J = secVal s' (𝟙 _) y J) : s = s' :=
  sec_ext' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL h

theorem secVal_add' (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (s t : SecOver π (LPow A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal (s + t : SecOver π _) r z J = secVal s r z J + secVal t r z J :=
  sval_add' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (π := π) hJ r s t

theorem secVal_smul' (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (c : S) (s : SecOver π (LPow A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal (c • s : SecOver π _) r z J = constVal (r ≫ π) z c * secVal s r z J :=
  sval_smul' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (π := π) hJ r c s

theorem exists_actMap (hL : L.IsLB) (θ : ThetaGrp A L k T) (q : T.left ⟶ Spec (CommRingCat.of S))
    (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (hπ : π = (fst T A).left ≫ q) :
    ∃ a : SecOver π (LPow A L k T) →ₗ[S] SecOver π (LPow A L k T), Function.Injective a ∧
      ∀ s s', IsActOf A L k θ s s' ↔ a s = s' := by
  choose a ha using fun s : SecOver π (LPow A L k T) => exists_actVal hL θ s
  have e : (𝟙 _ ≫ (translT A θ.pt).left) ≫ π = 𝟙 _ ≫ π := by
    rw [hπ, Category.assoc, ← Category.assoc (translT A θ.pt).left, ← Over.comp_left, translT, lift_fst]
  refine ⟨{ toFun := a
            map_add' := fun s t => lpow_ext hL fun y J hJ => ?_
            map_smul' := fun c s => lpow_ext hL fun y J hJ => ?_ }, fun s t h => lpow_ext hL fun y J hJ => ?_,
    fun s s' => ⟨fun H => lpow_ext hL fun y J hJ => (ha s _ _ y J hJ).trans (actVal_of_isActOf H _ _ y J hJ).symm,
      fun H => H ▸ (ha s).isActOf hL⟩⟩
  · refine (ha _ _ _ y J hJ).trans (Eq.trans ?_ (secVal_add' π _ _ _ y hJ).symm)
    rw [secVal_add' π _ _ _ y hJ, mul_add]
    exact (congrArg₂ (· + ·) (ha s _ _ y J hJ) (ha t _ _ y J hJ)).symm
  · refine (ha _ _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul' π _ _ _ y hJ).symm)
    rw [secVal_smul' π _ _ _ y hJ, mul_left_comm, e]
    exact (congrArg _ (ha s _ _ y J hJ)).symm
  · have h : a s = a t := h
    have r : (translT A θ.pt⁻¹).left ≫ (translT A θ.pt).left = 𝟙 _ := by
      rw [← Over.comp_left, translT_mul, mul_inv_cancel, translT_one, Over.id_left]
    have e₁ := ha s _ (translT A θ.pt⁻¹).left y J hJ
    have e₂ := ha t _ (translT A θ.pt⁻¹).left y J hJ
    rw [r] at e₁ e₂
    rw [h] at e₁
    exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)

theorem exists_act_ratio (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {F : Type} [Field F]
    {t : Spec (CommRingCat.of F) ⟶ S₀} (θ θ' : ThetaGrp A L k (Over.mk t)) (h : θ.pt = θ'.pt)
    (π : (Over.mk t ⊗ A).left ⟶ Spec (CommRingCat.of F)) (hπ : π = (fst (Over.mk t) A).left) :
    ∃ c : F, c ≠ 0 ∧ ∀ s s₁ s₂ : SecOver π (LPow A L k (Over.mk t)), IsActOf A L k θ s s₁ →
      IsActOf A L k θ' s s₂ → s₂ = c • s₁ := by
  obtain ⟨u, hu⟩ := ThetaAct.exists_ratio hG hA hL θ θ' h
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 u.val
  refine ⟨c, ?_, fun s s₁ s₂ h₁ h₂ => lpow_ext hL fun y J hJ => ?_⟩
  · rintro rfl
    have : Nontrivial Γ((Over.mk t).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    exact u.ne_zero (hc.symm.trans (map_zero _))
  · refine (actVal_of_isActOf h₂ _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul' π _ _ _ y hJ).symm)
    rw [actVal_of_isActOf h₁ _ _ y J hJ, ← _root_.mul_assoc, h]
    refine congrArg (· * _) ((hu _ _ y J hJ).trans (congrArg (· * _) ?_))
    rw [hπ, ← hc]; rfl

end Act

section Side

variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S₁} {T₀ : Over S₀} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}


include hp hτ in
theorem exists_psi : ∃ ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left, IsPullback ψ (fst T A).left (fst T₀ G).left τ ∧
    ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ ∧ ψ = (psiO hp τ hτ).left := by
  refine ⟨(psiO hp τ hτ).left, ?_, psi_snd hp τ hτ, rfl⟩
  have h₀ : IsPullback (snd T₀ G).left (fst T₀ G).left G.hom T₀.hom := (IsPullback.of_hasPullback _ _).flip
  have h₁ : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (psi_fst hp τ hτ) h₀
  rw [psi_snd, hτ]
  exact h₁.paste_horiz hp.1

theorem exists_theta_side (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ)
    {ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (hψ : ψ = (psiO hp τ hτ).left) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧ ∀ (s₀ s₀' : LB.Sec (LPow G L₀ k T₀)) (s s' : LB.Sec (LPow A L₁ k T)),
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s s₀ →
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s' s₀' →
      IsActOf G L₀ k θ₀ s₀ s₀' → IsActOf A L₁ k θ s s' := by
  obtain ⟨θ, rfl, hm⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx
  have hm : PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
      θ.φ θ₀.φ ψ := hψ ▸ hm
  have c₁ : (snd T A).left ≫ φ = ψ ≫ (snd T₀ G).left := hψ ▸ (psi_snd hp τ hτ).symm
  have c₂ : (translPt A θ.pt).left ≫ φ = ψ ≫ (translPt G θ₀.pt).left := hψ ▸ (psi_tr hp τ hτ _ _ hx).symm
  have c₃ : (translT A θ.pt).left ≫ ψ = ψ ≫ (translT G θ₀.pt).left := hψ ▸ psi_transl hp τ hτ _ _ hx
  refine ⟨θ, rfl, fun s₀ s₀' s s' m m' H => (ThetaAct.isActOf_iff hL₁ θ s s').2 fun y J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hJ₀ : Good L₀ y J₀ := hJ₀
  have c : ∀ _ : Fin 1, (snd T A).left ≫ φ = ψ ≫ (snd T₀ G).left := fun _ => c₁
  have a := actVal_of_isActOf H _ (𝟙 _ ≫ ψ) y J₀ hJ₀
  have b := ExpTrans.gen_val w _ _ _ _ (fun i => by
    fin_cases i
    · exact c₁
    · exact c₂) _ _ hm y hJ₀ hJ
  have d := ExpTrans.sec_val w _ _ _ _ c _ _ (𝟙 _) y (m' _ (𝟙 _) y) hJ₀ hJ
  have e := ExpTrans.sec_val w _ _ _ _ c _ _ (𝟙 _ ≫ (translT A θ.pt).left) y (m _ _ y) hJ₀ hJ
  have g : (𝟙 _ ≫ ψ) ≫ (translT G θ₀.pt).left =
      (𝟙 _ ≫ (translT A θ.pt).left) ≫ ψ := by
    rw [Category.assoc, Category.assoc, c₃]
  rw [g] at a
  rw [Fin.prod_univ_one] at d e
  rw [Fin.prod_univ_two] at b
  rw [Category.assoc _ _ (snd T A).left, translT_snd_left, Category.id_comp (translPt A θ.pt).left] at e
  rw [Category.id_comp (snd T A).left] at d
  have b' : thetaVal θ₀ (𝟙 _ ≫ ψ) y J₀ = ExpTrans.om w y J₀ J (snd T A).left ^ k *
      ExpTrans.om w y J₀ J (translPt A θ.pt).left ^ (-k) * thetaVal θ (𝟙 _) y J := by
    rw [Category.id_comp]; exact b
  have z := d.symm.trans (a.trans (congrArg₂ (· * ·) (congrArg Units.val b') e))
  refine (ExpTrans.om w y J₀ J (snd T A).left ^ k).mul_right_inj.1 (z.trans ?_)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, zpow_neg, mul_right_comm _ _⁻¹,
    inv_mul_cancel_right]
  rfl

end Side

section Phi

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem eq_zero_of_phiVal {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (s : Fam D F k)
    (h : PhiVal p w s.s (0 : Fam D F k).s) : s = 0 := by
  have := D.P.isAb.comm
  have r : DegPre.trPt D F p.g.b⁻¹ ≫ DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_)
      rw [MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel,
        MonObj.comp_one, _root_.mul_one, Category.id_comp]
  refine fam_ext fun α j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  have e := h α _ rfl _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [r] at e
  have z : ∀ β (r : (DegPre.BF D F).left ⟶ (DegPre.BF D F).left), sval ((0 : Fam D F k).s β) r y J = 0 := fun β r =>
    sval_zero' (π := famBase D F) hJ r
  rw [z] at e ⊢
  exact (Units.mul_left_eq_zero _).1 e.symm

end Phi

section Expand

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem expandsF_of_integral {k : ℕ}
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}
    {u : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))}
    (hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ A.A.left) (z : Z) (j : U.LG.L.ι) (i : A.L.ι),
      (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) (f z) ∈ U.LG.L.U j → f z ∈ A.L.U i →
      gw u f z j i = isoVal w (f ≫ U.gen.inv.left) z j i)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : ∀ α y J, Good D.toPre.P.L y J →
      sval (s.s α) (𝟙 _) y J = sval (f α) (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y J)
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) t σ) :
    U.ExpandsF F k w t s := by
  have h₂ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)
  have n₃ : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  have h₃ : ((𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
      𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [Category.id_comp, Category.id_comp, h₂, Category.assoc, n₃, Category.comp_id]
  have h₄ : (𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) := by
    rw [← h₃]; simp only [Category.assoc]
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  refine ⟨extendSec U F k (genericSec U k σ), (isoRelM_iff w _ k _ h₂ _ (Category.id_comp _) _ _).2
    fun y i₂ i₁ a₂ a₁ => ?_, 1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE,
    (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  · have b₂ := (congrArg (fun q : _ ⟶ G.left => q y ∈ U.LG.L.U i₂) h₄).mpr a₂
    have b₁ := (congrArg (fun q : _ ⟶ A.A.left => q y ∈ A.L.U i₁) h₂).mpr a₁
    have e := ht _ (𝟙 _ ≫ (U.genF F).left) y (fun _ => i₂) (fun _ => i₁) (fun _ => b₂) (fun _ => b₁)
    rw [Fin.prod_univ_one, hu _ ((𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) y i₂ i₁ b₂ b₁, h₃, h₄] at e
    refine Eq.trans ?_ e
    rw [Category.id_comp (𝟙 _)]
    exact (gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k σ) (𝟙 _) y (fun _ => i₂)
      (fun _ => a₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition
        (fun _ => (Category.comp_id _).symm) σ _ y (fun _ => i₂) (fun _ => a₂))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact hs α y J hJ

end Expand

end GlobalTheory.ThetaSpecialise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfLaws
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem finrank_fam_of_laws : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.P.g + D.rank) :=
  fun h₁ h₂ _ _ _ D hB F _ _ k hk => by
    rw [Nat.add_comm]
    exact GlobalTheory.FamDimension.finrank_fam (D := D) (F := F) h₁.globalFns h₂.secTwist hB hk

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FiniteCover

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']

theorem rankAtStalk_bot {A C : Type} [CommRing A] [IsDomain A] [AddCommGroup C] [Module A C] :
    Module.rankAtStalk (R := A) C ⊥ = Module.finrank A C := by
  have h : (⊥ : PrimeSpectrum A).asIdeal.primeCompl ≤ nonZeroDivisors A := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hx (h0 ▸ Ideal.zero_mem _)
  rw [Module.rankAtStalk, IsLocalization.finrank_eq _ _ h]
  exact IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ C) h

theorem generic_mem_preimage (φ : X' ⟶ X) [Surjective φ] {U : X.Opens} (h : genericPoint X ∈ U) :
    genericPoint X' ∈ φ ⁻¹ᵁ U := by
  obtain ⟨y, hy⟩ := φ.surjective (genericPoint X)
  exact generic_mem (x := y) (show φ y ∈ U from hy ▸ h)

theorem chart_data (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ]
    [Algebra X.functionField X'.functionField]
    (hF : ∀ x, algebraMap X.functionField X'.functionField x = functionFieldMap φ x)
    {D : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D) :
    (∃ x, Module.finrank X.functionField X'.functionField = φ.finrank x) ∧
    ∀ {d : ℕ} (e : Module.Basis (Fin d) X.functionField X'.functionField),
      ∃ c ∈ (toField h).range, c ≠ 0 ∧
        (∀ j, ∀ y ∈ (toField (generic_mem_preimage φ h)).range, c * e.repr y j ∈ (toField h).range) ∧
        ∀ j, c • e j ∈ (toField (generic_mem_preimage φ h)).range := by
  have h' := generic_mem_preimage φ h
  haveI : Nonempty D := ⟨⟨_, h⟩⟩
  haveI : Nonempty (φ ⁻¹ᵁ D) := ⟨⟨_, h'⟩⟩
  letI := (φ.app D).hom.toAlgebra
  haveI : Module.Finite Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := φ.finite_app D hD
  haveI : Module.Flat Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := by
    have := φ.flat_appLE hD (hD.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  haveI := functionField_isFractionRing_of_isAffineOpen X D hD
  haveI := functionField_isFractionRing_of_isAffineOpen X' _ (hD.preimage φ)
  letI : Algebra Γ(X, D) X'.functionField :=
    ((algebraMap X.functionField X'.functionField).comp (algebraMap Γ(X, D) X.functionField)).toAlgebra
  haveI : IsScalarTower Γ(X, D) X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower Γ(X, D) Γ(X', φ ⁻¹ᵁ D) X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      have e := toField_appLE φ le_rfl h h' a
      rw [Scheme.Hom.appLE_eq_app] at e
      exact (hF _).trans e.symm
  refine ⟨⟨hD.fromSpec (⊥ : PrimeSpectrum Γ(X, D)), ?_⟩, fun e => ?_⟩
  · have hp : IsPullback (hD.preimage φ).fromSpec (Spec.map (φ.app D)) φ hD.fromSpec :=
      (IsOpenImmersion.isPullback _ _ _ _ (by
        rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hD (hD.preimage φ)])
        (by simp)).flip
    rw [IsFractionRing.finrank_eq Γ(X, D) X.functionField Γ(X', φ ⁻¹ᵁ D) X'.functionField,
      ← rankAtStalk_bot]
    refine Eq.trans ?_ (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp _)
    exact (Scheme.Hom.finrank_SpecMap_algebraMap Γ(X, D) Γ(X', φ ⁻¹ᵁ D) _).symm
  · obtain ⟨c, hc, h₁, h₂⟩ := exists_denominator (A := Γ(X, D)) (C := Γ(X', φ ⁻¹ᵁ D)) e
    refine ⟨toField h c, ⟨c, rfl⟩, fun h0 => hc (toField_injective h (h0.trans (map_zero _).symm)),
      ?_, h₂⟩
    rintro j _ ⟨y, rfl⟩
    exact h₁ j y

theorem exists_mul_pow_mem {D D' : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D)
    (h' : genericPoint X ∈ D') (r : Γ(X, D)) (hr : toField h r ≠ 0) (hle : X.basicOpen r ≤ D')
    (c : Γ(X, D')) : ∃ m : ℕ, toField h' c * toField h r ^ m ∈ (toField h).range := by
  have hb : genericPoint X ∈ X.basicOpen r :=
    (Scheme.mem_basicOpen X r _ h).2 (isUnit_iff_ne_zero.2 hr)
  have := hD.isLocalization_basicOpen r
  obtain ⟨m, b, e⟩ := IsLocalization.Away.surj r (rs X hle c)
  have e' : toField hb (rs X hle c * rs X (X.basicOpen_le r) r ^ m) =
      toField hb (rs X (X.basicOpen_le r) b) := congrArg (toField hb) e
  rw [map_mul, map_pow, toField_rs, toField_rs, toField_rs] at e'
  exact ⟨m, b, e'.symm⟩


omit [IsIntegral X] in
theorem basicOpen_le_nonzeroLocus {H : LB X} (s s' : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s'.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) :
    X.basicOpen r ≤ nonzeroLocus s' := by
  intro x hx
  have hs : x ∈ nonzeroLocus s := X.basicOpen_le r hx
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  have e := congrArg X.basicOpen (h l)
  rw [Scheme.basicOpen_mul] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ nonzeroLocus s ⊓ H.U l := ⟨hs, X.basicOpen_le _ hl⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, (e.ge ⟨⟨hx', hx⟩, hx', hl⟩).2⟩

def powSec {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (t : ℕ) : LB.Sec (pw H t) where
  f k := (s.f k : Γ(X, H.U k)) ^ t
  compat i j := by
    have e := congrArg (· ^ t) (s.compat i j)
    simp only [mul_pow, ← map_pow] at e
    refine e.trans ?_
    congr 1

end GlobalTheory.FiniteCover

namespace GlobalTheory

open FiniteCover

theorem finrank_sec_pull_sandwich : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Etale φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  haveI : Surjective φ := φ.one_le_finrank_iff_surjective.1 fun x => (hd x).symm ▸ hd1
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
end
end

