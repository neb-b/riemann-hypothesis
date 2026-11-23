module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedOfTwoIdempotentFactors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.TwoFac
variable {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ D' : DegPre R}

theorem inc_pr_inc (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    F₂.inc ≫ F₁.pr ≫ F₁.inc = F₂.inc := by
  rw [F₁.pr_inc, he, ← F₂.pr_inc, ← Category.assoc, F₂.inc_pr, Category.id_comp]

theorem comp_inv (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    (F₂.inc ≫ F₁.pr) ≫ (F₁.inc ≫ F₂.pr) = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← Category.assoc F₁.pr, ← Category.assoc F₂.inc, inc_pr_inc F₁ F₂ he, F₂.inc_pr]

theorem inv_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    (F₁.inc ≫ F₂.pr) ≫ (F₂.inc ≫ F₁.pr) = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← Category.assoc F₂.pr, F₂.pr_inc, ← he, ← F₁.pr_inc, Category.assoc F₁.pr, ← Category.assoc F₁.inc, F₁.inc_pr,
    Category.id_comp]

theorem xi_xp_xi (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) (a : D₂.X) :
    F₁.xi (F₁.xp (F₂.xi a)) = F₂.xi a := by
  rw [F₁.xi_xp, hXe, ← F₂.xi_xp, F₂.xp_xi]

theorem c_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) (a : D₂.X) :
    D₂.c a ≫ F₂.inc ≫ F₁.pr = D₁.c (F₁.xp (F₂.xi a)) := by
  have h := F₁.c_xi (F₁.xp (F₂.xi a))
  rw [xi_xp_xi F₁ F₂ hXe] at h
  rw [← Category.assoc, ← F₂.c_xi, h, Category.assoc, F₁.inc_pr, Category.comp_id]

def xEquiv (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) : D₂.X ≃+ D₁.X where
  toFun a := F₁.xp (F₂.xi a)
  invFun a := F₂.xp (F₁.xi a)
  left_inv a := by
    show F₂.xp (F₁.xi (F₁.xp (F₂.xi a))) = a
    rw [xi_xp_xi F₁ F₂ hXe, F₂.xp_xi]
  right_inv a := by
    show F₁.xp (F₂.xi (F₂.xp (F₁.xi a))) = a
    rw [F₂.xi_xp, ← hXe, ← F₁.xi_xp, F₁.xp_xi, F₁.xp_xi]
  map_add' a b := by simp

theorem lift_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e)
    (hf : F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f) :
    (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) : G2 D₂.P.A ⟶ G2 D₁.P.A).left ≫
      (lift (fst D₁.P.A D₁.P.A ≫ F₁.inc) (snd D₁.P.A D₁.P.A ≫ F₁.inc ≫ F₁.o.onB.act F₁.f) : G2 D₁.P.A ⟶ G2 D'.P.A).left =
    (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₂.o.onB.act F₂.f) : G2 D₂.P.A ⟶ G2 D'.P.A).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% (inc_pr_inc F₁ F₂ he), inc_pr_inc F₁ F₂ he, hf]

theorem formEq_cancel {X Y Y' : Scheme.{0}} {K : Type} [Fintype K] (ε : K → ℤ) (A B : K → (Y ⟶ X)) (A₁ B₁ : K → (Y' ⟶ X))
    (h : Y ⟶ Y') (hA : ∀ k, h ≫ A₁ k = A k) :
    FormEq (Sum.elim (Sum.elim A B) (fun k => h ≫ Sum.elim A₁ B₁ k))
      (Sum.elim (Sum.elim ε (fun k => - ε k)) (fun k => - Sum.elim ε (fun k => - ε k) k))
      (Sum.elim (fun k => h ≫ B₁ k) B) (Sum.elim ε (fun k => - ε k)) := by
  intro U _ g
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hA, neg_neg, zpow_neg, Finset.prod_inv_distrib]
  generalize ∏ a₁, g (A a₁) ^ ε a₁ = a
  generalize ∏ x, g (B x) ^ ε x = b
  generalize ∏ x, g (h ≫ B₁ x) ^ ε x = c
  rw [mul_inv, inv_inv, _root_.mul_comm a, _root_.mul_assoc, mul_inv_cancel_left, _root_.mul_comm]

theorem samePol_of_two_factors : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ D' : DegPre R), D₁.TauBimult → ∀ (F₁ : Factor D₁ D') (F₂ : Factor D₂ D'), F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e → F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f → (∀ z : D'.X, F₁.e • z = F₂.e • z) → (∀ z : D'.X, F₁.f • z = F₂.f • z) → SamePol D₁ D₂ := by
  intro R _ _ D₁ D₂ D' hB F₁ F₂ he hf hXe hXf
  haveI := F₂.inc_hom
  haveI := F₁.pr_hom
  let eI : D₂.P.A ≅ D₁.P.A := ⟨F₂.inc ≫ F₁.pr, F₁.inc ≫ F₂.pr, comp_inv F₁ F₂ he, inv_comp F₁ F₂ he⟩
  haveI : IsMonHom eI.hom := inferInstanceAs (IsMonHom (F₂.inc ≫ F₁.pr))
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  refine ⟨GlobalTheory.PolDeg.Wit.ofDeg D₁ hB, AddEquiv.refl _, xEquiv F₁ F₂ hXe, GlobalTheory.PolDeg.Wit.refines_ofDeg D₁ hB, ?_⟩
  let β₂ := (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) : G2 D₂.P.A ⟶ G2 D₁.P.A).left
  have hsq : IsSquare (F₂.inc ≫ F₁.pr).left β₂ := by
    constructor
    · rw [← Over.comp_left, lift_fst, Over.comp_left]
    · rw [← Over.comp_left, lift_snd, Over.comp_left]

  haveI : Nonempty (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0}) :=
    ⟨(coprod.inl : D₁.P.A.left ⟶ _) (Classical.arbitrary _)⟩
  have hL₁ := D₁.P.isLB
  have hL₂ := D₂.P.isLB
  have hL' := D'.P.isLB
  have h₁₂ := join_isLB hL₁ hL₂
  have hN := join_isLB h₁₂ hL'
  have P₁ : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D₁.P.L (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) :=
    (isPart_inl _ _).trans (isPart_inl _ _)
  have P₂ : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D₂.P.L (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) :=
    (isPart_inl _ _).trans (isPart_inr _ _)
  have P' : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D'.P.L coprod.inr Prod.snd := isPart_inr _ _
  have sπ₁ : Function.Surjective (Prod.fst ∘ Prod.fst : (join (join D₁.P.L D₂.P.L) D'.P.L).ι → D₁.P.L.ι) :=
    (fst_surjective hL₂).comp (fst_surjective hL')
  have sπ₂ : Function.Surjective (Prod.snd ∘ Prod.fst : (join (join D₁.P.L D₂.P.L) D'.P.L).ι → D₂.P.L.ι) :=
    (snd_surjective hL₁).comp (fst_surjective hL')
  obtain ⟨t₂, ht₂, vt₂⟩ := exists_gen_of_iso P' P₂ F₂.w F₂.w_gen
  obtain ⟨t₁, ht₁, vt₁⟩ := exists_gen_of_iso P' P₁ F₁.w F₁.w_gen
  have hℓ := lift_comp F₁ F₂ he hf
  let t := LB.mulGen _ _ _ _ _ t₂ (LB.invGen _ _ _ (LB.pullGen _ _ _ t₁ β₂))
  have ht : t.IsGen := LB.isGen_mulGen _ _ _ _ _ _ _ ht₂ (LB.isGen_invGen _ _ _ _ (LB.isGen_pullGen _ _ _ _ ht₁ _))
  obtain ⟨t', ht', vt'⟩ := exists_gen hN (formEq_cancel _ _ _ _ _ β₂ (fun k => by rw [← Category.assoc, hℓ])) t ht
  obtain ⟨w, hw, vw⟩ := exists_iso_of_gen P₁ P₂ hL₁ hL₂ sπ₁ sπ₂ t' ht'
  refine ⟨(F₂.inc ≫ F₁.pr).left, β₂, w, (isGrpPullback_of_iso eI).congr hs.symm rfl, hsq, hw, fun a => ?_, ?_⟩
  · show (D₂.c a).left ≫ (F₂.inc ≫ F₁.pr).left = spMap (RingHom.id R) ≫ (D₁.c (F₁.xp (F₂.xi a))).left
    rw [hs, Category.id_comp, ← Over.comp_left, c_comp F₁ F₂ hXe]
  intro κ hκ a b z J J' hJ hJ'
  obtain rfl : κ = 𝟙 _ := by
    rw [hs, Category.comp_id] at hκ
    have : Mono (jK R) := GlobalTheory.PolDeg.Wit.mono_jK
    exact (cancel_mono (jK R)).1 (hκ.trans (Category.id_comp _).symm)
  obtain ⟨J₁₂, hJ₁₂, e₁, e₂⟩ := exists_good_join hL₁ hL₂ hJ hJ'
  choose I hI using fun χ : (TK R).left ⟶ D'.P.A.left => exists_chart hL' (χ z)
  obtain ⟨JN, hJN, e₃, e₄⟩ := exists_good_join h₁₂ hL' hJ₁₂ (J₂ := I) hI
  have r₁ : GlobalTheory.Mum.Two.rs (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) JN = J := by
    rw [← e₁, ← e₃]; funext ψ; simp only [GlobalTheory.Mum.Two.rs, GlobalTheory.Mum.Two.rl, GlobalTheory.Mum.Two.rr, Function.comp, Category.assoc]
  have r₂ : GlobalTheory.Mum.Two.rs (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) JN = J' := by
    rw [← e₂, ← e₃]; funext ψ; simp only [GlobalTheory.Mum.Two.rs, GlobalTheory.Mum.Two.rl, GlobalTheory.Mum.Two.rr, Function.comp, Category.assoc]
  have r₃ : GlobalTheory.Mum.Two.rs coprod.inr Prod.snd JN = I := e₄
  have hp : (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left ≫ β₂ =
      (lift (toUnit (TK R) ≫ D₁.c (F₁.xp (F₂.xi a))) (toUnit (TK R) ≫ D₁.c (F₁.xp (F₂.xi b)))).left := by
    simp only [β₂]
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc,
      c_comp F₁ F₂ hXe, c_comp F₁ F₂ hXe]
  have v := vw _ (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN hJN
  rw [vt' _ _ z JN hJN] at v
  have hv : val t (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN =
      val t₂ (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN *
        (val t₁ ((lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left ≫ β₂) z JN)⁻¹ := by
    rw [val_mul hJN, val_inv, val_pull hJN]
  rw [hv, vt₂ _ _ z JN hJN, vt₁ _ _ z JN hJN, r₁, r₂, r₃, hp] at v
  have hF₂ := F₂.tau a b z I J' hI hJ'
  have hF₁ := F₁.tau (F₁.xp (F₂.xi a)) (F₁.xp (F₂.xi b)) z I J hI hJ
  rw [xi_xp_xi F₁ F₂ hXe, xi_xp_xi F₁ F₂ hXe, hXf] at hF₁
  have hQ := (GlobalTheory.PolDeg.Wit.exists_tau D₁ (F₁.xp (F₂.xi a)) (F₁.xp (F₂.xi b))).choose_spec.2 _ (𝟙 _) z J hJ
  change GlobalTheory.PolDeg.lamVal w _ z J J' = GlobalTheory.PolDeg.lamVal F₂.w _ z I J' * (GlobalTheory.PolDeg.lamVal F₁.w _ z I J)⁻¹ at v
  rw [hF₂]
  refine Eq.trans ?_ (congrArg₂ (· * ·) v.symm hQ.symm)
  rw [hF₁, _root_.mul_assoc, inv_mul_cancel_left]

end GlobalTheory.Mum.TwoFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqZeroWeightIndependenceLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory

namespace WeightValPart

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem coeff_eq_zero_over {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {X : Scheme.{0}} {N : LB X}
    (hN : N.IsLB) {ι₀ : D.P.A.left ⟶ X} {π : N.ι → D.P.L.ι} (hP : IsPart N D.P.L ι₀ π) {K : Type} [Fintype K]
    {φ : D.X → K → (Y.left ⟶ X)} {ε : K → ℤ} (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X)
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left →
      ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0)
    (α : D.X) (hα : α ∈ s) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Z ⟶ thickObj R I e G)
    (r : Z.left ⟶ Y.left) (hr : r ≫ p.left = x.left ≫ g.pG.left) (z : Z.left) (J) (hJ : Good N z J) :
    sval (d α) r z J = 0 := by
  classical
  let jf : D.X → K → N.ι := fun β a => J (r ≫ φ β a)
  let jt : D.X → Fin 4 → D.P.L.ι := fun β a => rs ι₀ π J (x.left ≫ D.Oφ g.pG β a)
  let V : Z.left.Opens := s.inf (fun β => r ⁻¹ᵁ LB.wchart N (φ β) (jf β) ⊓
      x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β))
  have hz : z ∈ V := DVR.mem_finf s _ _ fun β _ => ⟨hJ.mem (φ β) r, (hP.good hJ).mem (D.Oφ g.pG β) x.left⟩
  have hVf : ∀ β ∈ s, V ≤ r ⁻¹ᵁ LB.wchart N (φ β) (jf β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_left
  have hVt : ∀ β ∈ s, V ≤ x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_right
  have ex : ∀ β ∈ s, ∃ c : Γ(Z.left, V), ∀ (W : Scheme.{0}) (ρ : W ⟶ Z.left) (w : W),
      ρ w ∈ V → gs ρ w V c = gs (ρ ≫ r) w (LB.wchart N (φ β) (jf β)) ((d β).f (jf β)) *
        (gm (ρ ≫ x.left) w (LB.wchart D.P.L (D.Oφ g.pG β) (jt β)) ((g.t β).s (jt β))).val := fun β hβ =>
    ⟨(r.appLE _ V (hVf β hβ)).hom ((d β).f (jf β)) * (x.left.appLE _ V (hVt β hβ)).hom ((g.t β).s (jt β)).val,
      fun W ρ w hw => (gs_mul ρ w V hw _ _).trans (congrArg₂ (· * ·) (gs_appLE _ _ V _ ρ w hw _)
        ((gs_appLE _ _ V _ ρ w hw _).trans (gs_unit (ρ ≫ x.left) w _ (hVt β hβ hw) _)))⟩
  choose! c hc using ex
  have hsn : (WeightPf.Te D I e ◁ x).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left =
      (snd (WeightPf.Te D I e) Z).left ≫ x.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  let σ : Z ⟶ WeightPf.Te D I e ⊗ Z := lift (toUnit _ ≫ η[WeightPf.Te D I e]) (𝟙 _)
  have hσ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have H0 := WeightVal.eq_zero_of_stalk_sum D.X Z s c (fun w hw => by
    choose j hj using fun ψ : (WeightPf.Te D I e ⊗ Z).left ⟶ X => exists_chart hN (ψ w)
    let J₂ : ((WeightPf.Te D I e ⊗ Z).left ⟶ X) → N.ι := fun ψ =>
      if ψ w ∈ N.U (J (σ.left ≫ ψ)) then J (σ.left ≫ ψ) else j ψ
    have hJ₂ : Good N w J₂ := fun ψ => by
      by_cases h : ψ w ∈ N.U (J (σ.left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hj ψ
    have eJ : ∀ ψ : Z.left ⟶ X, ψ ((snd (WeightPf.Te D I e) Z).left w) ∈ N.U (J ψ) →
        J₂ ((snd (WeightPf.Te D I e) Z).left ≫ ψ) = J ψ := fun ψ h => by
      have e₁ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left ≫ ψ = ψ := by
        rw [← Category.assoc, hσ, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    have E := H _ ((WeightPf.Te D I e ◁ x).left ≫ (WeightPf.act g).left) ((snd (WeightPf.Te D I e) Z).left ≫ r)
      (by rw [Category.assoc, Category.assoc, hr, WeightPf.act_left_pG, ← Category.assoc, ← Category.assoc, hsn])
      w J₂ hJ₂
    refine Eq.trans (Finset.sum_congr rfl fun β hβ => ?_) E
    rw [hc β hβ _ _ w hw, WeightVal.val_act g β _ w (hP.good hJ₂), mul_left_comm, hsn, WeightVal.gs_chiP_whisker,
      sval_of (d β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (g.t β) _ w (rs ι₀ π J₂) (jt β) (fun a => by
        have m : ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀) ((snd (WeightPf.Te D I e) Z).left w) ∈
            N.U (J ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀)) := (hP.mem _ _).2 (Set.mem_iInter.1 (hVt β hβ hw) a)
        show π (J₂ ((((snd (WeightPf.Te D I e) Z).left ≫ x.left) ≫ D.Oφ g.pG β a) ≫ ι₀)) =
          π (J ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀))
        rw [show (((snd (WeightPf.Te D I e) Z).left ≫ x.left) ≫ D.Oφ g.pG β a) ≫ ι₀ =
          (snd (WeightPf.Te D I e) Z).left ≫ ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀) by simp only [Category.assoc], eJ _ m])]) α hα
  have E := hc α hα _ (𝟙 _) z hz
  rw [H0, gs_eq _ z V hz, map_zero, map_zero, Category.id_comp, Category.id_comp] at E
  exact (Units.mul_left_eq_zero _).1 E.symm

end WeightValPart

theorem sval_eq_zero_of_sum_mul_coord_part : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (ι₀ : D.P.A.left ⟶ X) (π : N.ι → D.P.L.ι), IsPart N D.P.L ι₀ π → ∀ (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ X)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → sval (d α) r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p X N hN ι₀ π hP K _ φ ε d s H α hα Z x r hr z J hJ
  exact WeightValPart.coeff_eq_zero_over g p hN hP d s H α hα (Over.mk (x ≫ (thickObj R I e G).hom))
    (Over.homMk x rfl) r hr z J hJ

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValuesIdentityDescendsToFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ValDescent

theorem spMap_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem eq_of_comp_jK {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} {f g : X ⟶ Sp (FractionRing R)}
    (h : f ≫ jK R = g ≫ jK R) : f = g := by
  haveI : Mono (jK R) := Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap R (FractionRing R))).op
  exact (cancel_mono (jK R)).1 h

theorem desc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s w H Z p p' hpp z J hJ
  have := C.semi.smooth
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  haveI : Flat C.gp := Modif.flat_gp R C.toModif
  haveI : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip inferInstance
  haveI : Flat (pullback.fst T.β C.α) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.β C.α).flip inferInstance
  set q₁ : pullback T.β C.α ⟶ T.G.left := pullback.fst T.β C.α with hq₁
  set q₂ : pullback T.β C.α ⟶ C.A.A.left := pullback.snd T.β C.α with hq₂
  have hq : q₁ ≫ T.β = q₂ ≫ C.α := pullback.condition
  set ρ : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hρ
  have hρi : Function.Injective ρ := (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  set d : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ pullback T.β C.α := pullback.fst _ _ with hd
  set t : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ Sp F := pullback.snd _ _ with ht
  have hdt : d ≫ q₁ ≫ T.G.hom = t ≫ spMap ρ := pullback.condition
  have hinj : ∀ V, Function.Injective (d.app V) := by
    intro V
    have : IsDominant (spMap ρ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 hρi).le.trans bot_le)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant (spMap ρ)
    have : IsSchemeTheoreticallyDominant d :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip
    have : QuasiCompact d := MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip inferInstance
    exact d.app_injective V

  have hover : t ≫ jFK (R := R) F = d ≫ q₂ ≫ C.A.A.hom := by
    apply ValDescent.eq_of_comp_jK
    have e₁ : jFK (R := R) F ≫ jK R = spMap ρ ≫ spMap T.φ := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext hF
    have e₂ : T.G.hom ≫ spMap T.φ = T.β ≫ C.G.hom ≫ C.π := by
      rw [← T.ξ_π, ← Category.assoc, ← T.cart.1.w, Category.assoc]
    have e₃ : C.α ≫ C.G.hom ≫ C.π = C.A.A.hom ≫ jK R := by
      rw [← Category.assoc, C.α_cart.1.w, Category.assoc, C.gp_π]
    rw [Category.assoc, e₁, ← Category.assoc, ← hdt, Category.assoc, Category.assoc, e₂, ← Category.assoc q₁,
      hq, Category.assoc, e₃]
    simp only [Category.assoc]
  let P' : Over (Sp (FractionRing R)) := Over.mk (d ≫ q₂ ≫ C.A.A.hom)
  let ℓ : P' ⟶ TFK (R := R) F ⊗ C.A.A := lift (Over.homMk t hover) (Over.homMk (d ≫ q₂) (Category.assoc _ _ _))
  have hfst : ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left = t := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left = d ≫ q₂ := by
    rw [← Over.comp_left, lift_snd]; rfl

  have hL : C.P.L.L.IsLB := C.P.L.isLB
  set i := J (p ≫ T.β) with hi
  set Vβ := LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => i) with hVβ
  set Vα := LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i) with hVα
  set V : (pullback T.β C.α).Opens := q₁ ⁻¹ᵁ Vβ ⊓ q₂ ⁻¹ᵁ Vα with hV
  have l₀ : V ≤ q₁ ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let a : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_left : V ≤ q₁ ⁻¹ᵁ Vβ)).op).hom ((q₁.app Vβ).hom (σ.f fun _ => i))
  let b : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE l₀).op).hom ((q₁.app ⊤).hom (scal T.G.hom w)) *
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_right : V ≤ q₂ ⁻¹ᵁ Vα)).op).hom ((q₂.app Vα).hom (s.f fun _ => i))
  have ka : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₁) ≫ T.β) = i → gs r z₀ V a = sval σ (r ≫ q₁) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of σ (r ≫ q₁) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ Vβ hr.1 _)
  have kb : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₂) ≫ C.α) = i → gs r z₀ V b = gs (r ≫ q₁) z₀ ⊤ (scal T.G.hom w) * sval s (r ≫ q₂) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of s (r ≫ q₂) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_mul r z₀ V hr _ _).trans (congrArg₂ (· * ·) ((gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ ⊤ trivial _))
      ((gs_res r z₀ _ hr _).trans (gs_pull r q₂ z₀ Vα hr.2 _)))
  have hab : a = b := by
    apply hinj V
    refine fn_ext fun x hx => ?_
    rw [gs_pull (𝟙 _) d x V hx, gs_pull (𝟙 _) d x V hx, Category.id_comp]
    have hmem : ((d ≫ q₁) ≫ T.β) x ∈ C.P.L.L.U i := Set.mem_iInter.1 hx.1 0
    obtain ⟨J', hJ', eJ'⟩ := exists_good C.P.L.L hL x (fun _ : Fin 1 => (d ≫ q₁) ≫ T.β) (fun _ => i) (fun _ _ _ => rfl)
      (fun _ => hmem)
    have e₁ : J' ((d ≫ q₁) ≫ T.β) = i := eJ' 0
    have e₂ : J' ((d ≫ q₂) ≫ C.α) = i := by rw [Category.assoc, ← hq, ← Category.assoc]; exact e₁
    rw [ka _ d x J' hx e₁, kb _ d x J' hx e₂]
    have h₁ : (d ≫ q₁) ≫ T.β = ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
      rw [← Category.assoc, hsnd, Category.assoc, Category.assoc, hq]
    have h₂ : (d ≫ q₁) ≫ T.G.hom = ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ρ := by
      rw [← Category.assoc, hfst, Category.assoc, hdt]
    have := H _ (d ≫ q₁) ℓ.left h₁ h₂ x J' hJ'
    rw [hsnd] at this
    exact this

  set u : Z ⟶ pullback T.β C.α := pullback.lift p p' hpp with hu
  have hu₁ : u ≫ q₁ = p := pullback.lift_fst _ _ _
  have hu₂ : u ≫ q₂ = p' := pullback.lift_snd _ _ _
  have hz : u z ∈ V := by
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [← hu₁] at h
      exact h
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [hpp, ← hu₂] at h
      exact h
  have A := ka Z u z J hz (by rw [hu₁])
  have B := kb Z u z J hz (by rw [hu₂, ← hpp])
  rw [hu₁] at A B
  rw [hu₂] at B
  rw [hab] at A
  exact A.symm.trans B

end GlobalTheory.Mum.ValDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianOverOpenPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory.ZH

theorem abLocus_of_over₀ : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  intro o Ω _ _ _ S ρ M U₀ EE FinalForm hO z hz
  rw [FinalForm.ab]
  show S.TT M z = ⊥
  have hle : M.ringOn U₀ ≤ M.O z := RatModel.ringOn_le_O hz
  have hsub : {x | S.th x ≠ 0} ⊆ S.supI M z := by
    intro x hx
    refine ⟨hx, fun y => ?_⟩
    rw [div_eq_mul_inv]
    exact mul_mem (hle (hO.le (S.th_mem y))) (hle (hO.th_unit x hx))
  have hHH : S.HH M z = ⊤ := by
    rw [eq_top_iff, ← S.supp]
    exact AddSubgroup.closure_mono hsub
  rw [ThetaSys.TT, hHH, eq_bot_iff]
  intro a ha
  rw [AddSubgroup.mem_bot]
  have h := fun b => ha b (AddSubgroup.mem_top b)
  funext j
  rcases j with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianThickeningHomEqOfEqOnOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumAgree

theorem subsingleton_thick (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    Subsingleton (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) := by
  have key : ∀ P : PrimeSpectrum (R ⧸ maximalIdeal R ^ (e + 1)),
      P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) = maximalIdeal R := by
    intro P
    have hp : (P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))).IsPrime :=
      Ideal.comap_isPrime _ _
    have hle : maximalIdeal R ^ (e + 1) ≤ P.asIdeal.comap (Ideal.Quotient.mk _) := by
      intro r hr
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]
      exact P.asIdeal.zero_mem
    have hm : maximalIdeal R ≤ _ := hp.le_of_pow_le hle
    exact ((maximalIdeal.isMaximal R).eq_of_le hp.ne_top hm).symm
  constructor
  intro P Q
  change PrimeSpectrum _ at P Q
  exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    ((key P).trans (key Q).symm))

theorem eq_of_eq_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e : ℕ) (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), IsMonHom x → IsMonHom x' → ∀ (W : (thickObj R (maximalIdeal R) e G).left.Opens) (y : (thickObj R (maximalIdeal R) e G).left), y ∈ W → W.ι ≫ x.left = W.ι ≫ x'.left → x = x' := by
  intro R _ _ _ _ D A G _ _ hG U e x x' hx hx' W y hy hW
  have hH : IsSemiAbelian (thickObj R (maximalIdeal R) e G) :=
    IsSemiAbelian.pullback (thick R (maximalIdeal R) e) G hG
  have := hH.smooth
  have hflat : Flat (thickObj R (maximalIdeal R) e G).hom := inferInstance
  let V : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :=
    Over.mk (W.ι ≫ (thickObj R (maximalIdeal R) e G).hom)
  let j : V ⟶ thickObj R (maximalIdeal R) e G := Over.homMk W.ι rfl
  have hsub := subsingleton_thick R e
  have hVs : Surjective V.hom := ⟨fun s => ⟨⟨y, hy⟩, Subsingleton.elim _ _⟩⟩
  have hj : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hF := GlobalTheory.Mum.FlatMul.main _ _ V j hj hflat
  have hS := GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres _ _ V j hj hVs
    (fun K _ t => GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ _ hH K t)
  have : Epi ((fst V V ≫ j) * (snd V V ≫ j)).left := Flat.epi_of_flat_of_surjective _
  have : Epi ((fst V V ≫ j) * (snd V V ≫ j)) := Over.epi_of_epi_left _
  have hjx : j ≫ x = j ≫ x' := Over.OverMorphism.ext hW
  rw [← cancel_epi ((fst V V ≫ j) * (snd V V ≫ j)), MonObj.mul_comp, MonObj.mul_comp,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, hjx]

end GlobalTheory.MumAgree
end

