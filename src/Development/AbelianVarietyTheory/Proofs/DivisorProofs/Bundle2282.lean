module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericEighthPowerUniformisedIsPolarised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SharpGen
open GlobalTheory.PowE8

theorem exists_gen {S T : Scheme.{0}} (f : T ⟶ S) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] {B C : Over T}
    [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a)
    (u : (Over.pullback f).obj G₀ ≅ C) [IsMonHom u.hom] :
    ∃ gen : (Over.pullback f).obj (powObj G₀ 8) ≅ B, IsMonHom gen.hom ∧
      ∀ a, gen.hom ≫ pr a = (Over.pullback f).map (powPr G₀ a) ≫ u.hom := by
  let hl := isLimitOfPreserves (Over.pullback f) (powIsLimit G₀ 8)
  let ρ : Fin 8 → ((Over.pullback f).obj (powObj G₀ 8) ⟶ (Over.pullback f).obj G₀) :=
    fun a => (Over.pullback f).map (powPr G₀ a)
  choose x hx hxu using fun (T' : Over T) (y : Fin 8 → (T' ⟶ C)) => huniq T' y
  let inv : B ⟶ (Over.pullback f).obj (powObj G₀ 8) :=
    hl.lift ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩
  have hinv : ∀ a, inv ≫ ρ a = pr a ≫ u.inv := fun a => hl.fac ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩ ⟨a⟩
  let hom := x _ (fun a => ρ a ≫ u.hom)
  have hhom : ∀ a, hom ≫ pr a = ρ a ≫ u.hom := hx _ _
  refine ⟨⟨hom, inv, ?_, ?_⟩, ?_, hhom⟩
  · refine hl.hom_ext fun ⟨a⟩ => ?_
    show (hom ≫ inv) ≫ ρ a = 𝟙 _ ≫ ρ a
    rw [Category.assoc, hinv, ← Category.assoc, hhom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  · have h1 := hxu B (fun a => pr a) (inv ≫ hom) (fun a => by
      rw [Category.assoc, hhom, ← Category.assoc, hinv, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have h2 := hxu B (fun a => pr a) (𝟙 B) (fun a => Category.id_comp _)
    exact h1.trans h2.symm
  · have hm : ∀ a, IsMonHom (hom ≫ pr a) := fun a => by rw [hhom]; infer_instance
    constructor
    · have h1 := hxu _ (fun a => η[C]) (η ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.one_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => η[C]) η (fun a => by haveI := hpr a; exact IsMonHom.one_hom (pr a))
      exact h1.trans h2.symm
    · have h1 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) (μ ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.mul_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) ((hom ⊗ₘ hom) ≫ μ) (fun a => by
        haveI := hpr a; rw [Category.assoc, IsMonHom.mul_hom (pr a), ← Category.assoc, tensorHom_comp_tensorHom])
      exact h1.trans h2.symm

theorem lift_lamφ {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (x y : T ⟶ B)
    (I : ULift.{0} (Finset (Fin 2))) :
    (lift x y).left ≫ GlobalTheory.PrimCocycle.lamφ B I = (psum B ![x, y] I.down).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I.down).trans
    (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))

theorem psum_comp_hom {S : Scheme.{0}} {B C T : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
    (u : B ⟶ C) [IsMonHom u] (x y : T ⟶ B) (I : Finset (Fin 2)) :
    psum C ![x ≫ u, y ≫ u] I = psum B ![x, y] I ≫ u :=
  ((congrArg (fun q => psum C q I) (funext fun i => by fin_cases i <;> rfl)).trans
    (psum_hom (MonoidHom.mk' (fun z : T ⟶ B => z ≫ u) fun a b => MonObj.mul_comp a b u) ![x, y] I).symm)

theorem zpow_lam {U : Type} [CommGroup U] (a b c d : U) (w : ℤ) :
    (a * b⁻¹ * c⁻¹ * d) ^ w = a ^ (-(w * negε 0)) * b ^ (-(w * negε 1)) * c ^ (-(w * negε 2)) * d ^ (-(w * negε 3)) := by
  simp only [negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, mul_zpow, inv_zpow', mul_neg, mul_one, neg_neg]
  norm_num

theorem gen_eighthPower : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ P.A, IsMonHom gen.hom ∧ LBIso (P.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  set_option maxSynthPendingDepth 10 in
    classical
    let trivialSums (X : Scheme.{0}) (L : LB X) (Y : Scheme.{0}) : Subgroup (Group.Abelianization (FreeGroup (Y ⟶ X))) := {
      carrier := {s | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), GlobalTheory.MulPull.HasGen L φ ε ∧
        ∏ k, Group.Abelianization.of (FreeGroup.of (φ k)) ^ ε k = s}
      one_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ⟨LB.oneGen L, fun _ _ => (map_one _).trans
        ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm⟩,
        Fintype.prod_empty _⟩
      mul_mem' := by
        rintro _ _ ⟨K, _, φ, ε, h, rfl⟩ ⟨K', _, φ', ε', h', rfl⟩
        exact ⟨K ⊕ K', inferInstance, _, _, h.mul h', Fintype.prod_sum_type _⟩
      inv_mem' := by
        rintro _ ⟨K, _, φ, ε, h, rfl⟩
        exact ⟨K, inferInstance, _, _, h.inv, by simp only [zpow_neg, Finset.prod_inv_distrib]⟩ }

    let cls {X Y : Scheme.{0}} (L : LB X) (ψ : Y ⟶ X) : Group.Abelianization (FreeGroup (Y ⟶ X)) ⧸ trivialSums X L Y := QuotientGroup.mk' _ (Group.Abelianization.of (FreeGroup.of ψ))

    have hasGen_iff {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
        GlobalTheory.MulPull.HasGen L φ ε ↔ ∏ k, cls L (φ k) ^ ε k = 1 := by
      have e : ∏ k, cls L (φ k) ^ ε k =
          QuotientGroup.mk' (trivialSums X L Y) (∏ k, Group.Abelianization.of (FreeGroup.of (φ k)) ^ ε k) := by
        simp only [map_prod, map_zpow, cls]
      rw [e, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      refine ⟨fun h => ⟨K, inferInstance, φ, ε, h, rfl⟩, ?_⟩
      rintro ⟨K', _, φ', ε', h, e⟩
      refine h.of_formEq hL fun U _ f => ?_
      simpa only [map_prod, map_zpow, Group.Abelianization.lift_apply_of, FreeGroup.lift_apply_of] using
        congrArg (Group.Abelianization.lift (FreeGroup.lift f)) e

    have lbIso_iff {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
        LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔ ∏ k, cls L (φ k) ^ ε k = ∏ k, cls L (φ' k) ^ ε' k := by
      have e : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔ GlobalTheory.MulPull.HasGen L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k) :=
        ⟨fun ⟨w, hw⟩ => gen_chartPull (GlobalTheory.PrimNorm.chartDivIn L φ ε φ' ε') w hw,
          fun ⟨w, hw⟩ => gen_chartPull (GlobalTheory.PrimNorm.chartDivOut L φ ε φ' ε') w hw⟩
      rw [e, hasGen_iff hL]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_eq_one]
      exact eq_comm

    have prod_flat {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ) :
        ∏ p : K' × K, cls L (ψ p.1 ≫ φ p.2) ^ (ε p.2 * δ p.1) = ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k := by
      simp only [Fintype.prod_prod_type, ← Finset.prod_zpow, zpow_mul]

    have lbIso_nested {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ)
        {K₃ : Type} [Fintype K₃] (χ : K₃ → (Z ⟶ X)) (κ : K₃ → ℤ)
        (h : ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k = ∏ k, cls L (χ k) ^ κ k) :
        LBIso (LB.LinComb (LB.LinComb L φ ε) ψ δ) (LB.LinComb L χ κ) :=
      ((lbIso_iff hL _ _ χ κ).2 ((prod_flat φ ε ψ δ).trans h)).chartPull (GlobalTheory.PrimNorm.chartFlat L φ ε ψ δ) (chartPullId _)

    intro g n o _ ζ F W V₁ _ _ _ D₀ G₀ _ _ A₀ U₀ y α α₂ hcart hsq hlb P hP
    obtain ⟨c, ⟨φ, φ₂, hφ, hφsq, hφlb, -⟩, pr, prh, prl, hPL⟩ := hP
    obtain ⟨e, he, heα⟩ := grpPullback_iso hcart hφ
    haveI := he
    haveI := U₀.gen_hom
    haveI : IsMonHom (U₀.gen ≪≫ e).hom := by rw [Iso.trans_hom]; infer_instance
    obtain ⟨gen, hgen, hcoord⟩ := exists_gen (jK V₁) G₀ pr prh prl (U₀.gen ≪≫ e)
    refine ⟨gen, hgen, ?_⟩
    have hA0 := A₀.isLB
    have hc := c.isLB
    have hLG := U₀.LG.isLB
    have hPl := P.isLB
    have hU := F.univ.isLB
    let ρ : Fin 8 → ((Over.pullback (jK V₁)).obj (powObj G₀ 8) ⟶ (Over.pullback (jK V₁)).obj G₀) :=
      fun a => (Over.pullback (jK V₁)).map (powPr G₀ a)
    let e₂ : (G2 A₀.A).left ⟶ (G2 c.A).left := (lift (fst _ _ ≫ e.hom) (snd _ _ ≫ e.hom)).left
    let mAB : Fin 8 × Fin 8 → (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ (G2 A₀.A).left) :=
      fun ab => (lift (ρ ab.1 ≫ U₀.gen.hom) (ρ ab.2 ≫ U₀.gen.hom)).left
    have hm : ∀ ab : Fin 8 × Fin 8, mAB ab ≫ e₂ = gen.hom.left ≫ (lift (pr ab.1) (pr ab.2)).left := fun ab => by
      simp only [mAB, e₂, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, hcoord, Iso.trans_hom,
        Category.assoc]
      rfl
    have he₂ : e₂ ≫ φ₂ = α₂ := by
      apply pullback.hom_ext
      · have h1 : (fst F.univ.A F.univ.A).left = pullback.fst _ _ := rfl
        rw [← h1, Category.assoc, hφsq.1, hsq.1, ← heα]
        simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_fst]
      · have h1 : (snd F.univ.A F.univ.A).left = pullback.snd _ _ := rfl
        rw [← h1, Category.assoc, hφsq.2, hsq.2, ← heα]
        simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_snd]
    have Q1 : LBIso (c.P.pull e₂) (abelian₂ A₀.A A₀.L) := by
      refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
        (GlobalTheory.PowPrimitive.lbIso_linComb hφlb (fun _ : PUnit => e₂) (fun _ => 1)) ?_
      refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
        (lbIso_nested hU (fun _ : PUnit => φ₂) (fun _ => 1) (fun _ : PUnit => e₂) (fun _ => 1)
          (fun _ : PUnit => α₂) (fun _ => 1) (by simp [he₂])) ?_
      exact hlb.symm
    let q := pullback.fst (powObj G₀ 8).hom (jK V₁)
    let q0 := pullback.fst G₀.hom (jK V₁)
    let n : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) →
        (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ ((Over.pullback (jK V₁)).obj G₀).left) :=
      fun p => (psum _ ![ρ p.1.1, ρ p.1.2] p.2.down).left
    let κ : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) → ℤ := fun p => GlobalTheory.PrimCocycle.lamε p.2 * W p.1.1 p.1.2
    have hn : ∀ ab I, mAB ab ≫ GlobalTheory.PrimCocycle.lamφ A₀.A I = n (ab, I) ≫ U₀.gen.hom.left := fun ab I => by
      rw [lift_lamφ, psum_comp_hom]; rfl
    let Uq : Over.mk (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).hom ≫ jK V₁) ⟶ powObj G₀ 8 :=
      Over.homMk q pullback.condition
    have hq : ∀ ab I, n (ab, I) ≫ q0 = q ≫ (lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I :=
      fun ab I => by
        rw [lift_lamφ]
        refine psum_push (isGrpPullback_pullback G₀ (jK V₁)) _ _ Uq (fun i => ?_) I.down
        apply Over.OverMorphism.ext
        fin_cases i
        · exact pullback.lift_fst _ _ _
        · exact pullback.lift_fst _ _ _
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hPL (fun _ : PUnit => gen.hom.left) (fun _ => 1)) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hc _ _ (fun _ : PUnit => gen.hom.left) (fun _ => 1) (fun ab => mAB ab ≫ e₂)
        (fun ab => W ab.1 ab.2) (by simp [hm])) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hc (fun _ : PUnit => e₂) (fun _ => 1) mAB (fun ab => W ab.1 ab.2)
        (fun ab => mAB ab ≫ e₂) (fun ab => W ab.1 ab.2) (by simp)).symm ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb Q1 mAB (fun ab => W ab.1 ab.2)) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hA0 (GlobalTheory.PrimCocycle.lamφ A₀.A) GlobalTheory.PrimCocycle.lamε mAB (fun ab => W ab.1 ab.2)
        (fun p => n p ≫ U₀.gen.hom.left) κ ?_) ?_
    · refine Eq.trans ?_ (Fintype.prod_prod_type _).symm
      refine Fintype.prod_congr _ _ fun ab => ?_
      rw [← Finset.prod_zpow]
      refine Fintype.prod_congr _ _ fun I => ?_
      rw [← zpow_mul, hn]
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hA0 (fun _ : PUnit => U₀.gen.hom.left) (fun _ => 1) n κ
        (fun p => n p ≫ U₀.gen.hom.left) κ (by simp)).symm ?_
    obtain ⟨w, hw⟩ := U₀.ext
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (GlobalTheory.PowPrimitive.lbIso_linComb ⟨w, hw⟩ n κ) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hLG (fun _ : PUnit => q0) (fun _ => 1) n κ (fun p => n p ≫ q0) κ (by simp)) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      ((lbIso_iff hLG (fun p => n p ≫ q0) κ
        (fun k : (Fin 8 × Fin 8) × Fin 4 => q ≫ lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
        (fun k => -(W k.1.1 k.1.2 * negε k.2))).2 ?_) ?_
    · refine ((Fintype.prod_prod_type _).trans ?_).trans (Fintype.prod_prod_type _).symm
      refine Fintype.prod_congr _ _ fun ab => ?_
      have e1 : ∏ I, cls U₀.LG.L (n (ab, I) ≫ q0) ^ κ (ab, I) =
          (∏ I, (fun m => cls U₀.LG.L (q ≫ m))
            ((lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I) ^ GlobalTheory.PrimCocycle.lamε I) ^
            W ab.1 ab.2 := by
        rw [← Finset.prod_zpow]
        refine Fintype.prod_congr _ _ fun I => ?_
        rw [← zpow_mul, hq]
        simp only [κ, Category.assoc]
      rw [e1]
      refine (congrArg (· ^ W ab.1 ab.2) (GlobalTheory.PrimCocycle.prod_lam (powPr G₀ ab.1) (powPr G₀ ab.2)
        (fun m => cls U₀.LG.L (q ≫ m)))).trans ?_
      rw [Fin.prod_univ_four]
      exact zpow_lam _ _ _ _ _
    exact (lbIso_nested hLG
      (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
      (fun k => -(W k.1.1 k.1.2 * negε k.2)) (fun _ : PUnit => q) (fun _ => 1) _ _ (by simp)).symm

end GlobalTheory.SharpGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsDimPullbackLeGenericallyFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GlobalSectionsPullback

theorem globalSectionsDim_pullback_le_generically_finite : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    (p : W ⟶ Sp F) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → Surjective f →
    f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (A : LB W), IsAmpleLB A ∧
      ∀ B : LB W, B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤
        r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  intro F _ M W _ _ p f hp hfp _ hdeg
  obtain ⟨r, co, hco, hinj⟩ := _root_.GlobalTheory.functionField_coords M W f hdeg
  obtain ⟨hpp, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨hfpp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (f ≫ p)).1 hfp
  haveI := hpp
  haveI := hfpp
  haveI : IsProper f := IsProper.of_comp f p
  haveI : IsNoetherian W := isNoetherian_of_isProjOver hp
  obtain ⟨n, hn, t, ht, htP⟩ := _root_.GlobalTheory.exists_sec_forall_local_condition W H hH
    (fun y c => ∀ (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V')
      (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (c * co j (fnOf (f ⁻¹ᵁ V') h z)))
    (fun y c c' hc hc' V' hy h z j => by rw [mul_assoc]; exact hc'.mul (hc V' hy h z j))
    (fun y => by
      obtain ⟨V, hy, d, hd, hd'⟩ := _root_.GlobalTheory.ProperDenom.exists_local_denom M W f L hL co hco y
      exact ⟨V, hy, d, hd, fun y' hy' V' hV' h z j => hd' y' hy' V' hV' h z j⟩)
  exact ⟨r, lbPow H n, (isAmpleLB_pow_iff hH.isLB hn).2 hH, fun B hB =>
    GlobalTheory.T.finrank_sections_pullback_le_mul_twist_of_dominant F M W p f hp co hco hinj (lbPow H n) (isLB_lbPow hH.isLB n) t ht
      (fun y i hi V' hV' h z j => htP y i hi V' hV' h z j) B hB⟩

end GlobalTheory.GlobalSectionsPullback
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalDescentsNearClosedFibreGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GlueNear

theorem isSeparated_of_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  let m : pullback (j ≫ f) (j ≫ f) ⟶ pullback f f :=
    pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have e : j ≫ pullback.diagonal f = pullback.diagonal (j ≫ f) ≫ m := by
    apply pullback.hom_ext <;> simp [m, pullback.map, pullback.lift_fst, pullback.lift_snd]
  have : UniversallyClosed (j ≫ pullback.diagonal f) := by rw [e]; infer_instance
  have : UniversallyClosed (pullback.diagonal f) := UniversallyClosed.of_comp_surjective j _
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range⟩

theorem isPullback_iSup {Y X S S' : Scheme.{0}} (π : Y ⟶ X) (q : X ⟶ S) (t : Y ⟶ S') (f : S' ⟶ S)
    {I : Type} (V : I → X.Opens)
    (h : ∀ i, IsPullback (π ∣_ V i) ((π ⁻¹ᵁ V i).ι ≫ t) ((V i).ι ≫ q) f) :
    IsPullback (π ∣_ (⨆ i, V i)) ((π ⁻¹ᵁ (⨆ i, V i)).ι ≫ t) ((⨆ i, V i).ι ≫ q) f := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Opens.iSupOpenCover V) fun (i : I) => ?_
  have e : V i ≤ ⨆ i, V i := le_iSup V i
  have sq : IsPullback (Y.homOfLE (π.preimage_mono e)) (π ∣_ V i) (π ∣_ (⨆ i, V i)) (X.homOfLE e) := by
    refine IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ (⨆ i, V i)).ι) (h₂₂ := (⨆ i, V i).ι) (v₁₃ := π) ?_ ?_
      (isPullback_morphismRestrict π _).flip
    · simpa using (isPullback_morphismRestrict π (V i)).flip
    · rw [← cancel_mono (⨆ i, V i).ι]; simp
  refine (h i).of_iso sq.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans sq.isoPullback_hom_snd.symm
  · refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    erw [sq.isoPullback_hom_fst]
    simp
  · change _ = 𝟙 _ ≫ X.homOfLE e ≫ _
    simp
  · simp

theorem smooth_iSup {X S : Scheme.{0}} (q : X ⟶ S) {I : Type} (V : I → X.Opens)
    (h : ∀ i, Smooth ((V i).ι ≫ q)) : Smooth ((⨆ i, V i).ι ≫ q) := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Scheme.Opens.iSupOpenCover V) fun (i : I) => ?_
  change Smooth (X.homOfLE (le_iSup V i) ≫ _)
  simpa using h i

theorem exists_near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (f : S ⟶ Sp R) [IsFinite f] [Surjective f]
    (G : Over S) [IsSeparated G.hom] (H : G.left.Opens)
    (hcl : ∀ g : G.left, f (G.hom g) = closedPoint R → g ∈ H) (hc : IsCompact (H : Set G.left))
    (X : Over (Sp R)) (π : H.toScheme ⟶ X.left)
    (hloc : ∀ x : H.toScheme, f (G.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧
      Smooth (V.ι ≫ X.hom) ∧ IsPullback (π ∣_ V) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G.hom) (V.ι ≫ X.hom) f) :
    ∃ N : Near f G, ∀ (α : G.left ⟶ G.left) (β : S ⟶ S) (hα : H ≤ α ⁻¹ᵁ H), α ≫ G.hom = G.hom ≫ β →
      α.resLE H H hα ≫ π = π →
      ∀ (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left), N.Pt s u x → N.Pt (s ≫ β) u (x ≫ α) := by
  classical
  have : CompactSpace H.toScheme := isCompact_iff_compactSpace.mp hc
  let Z : Set H.toScheme := {x | f (G.hom (H.ι x)) = closedPoint R}
  have hZ : IsCompact Z := by
    refine IsClosed.isCompact ?_
    exact (isClosed_singleton_closedPoint R).preimage
      (f.continuous.comp (G.hom.continuous.comp H.ι.continuous))
  choose V hV hVa hVs hVp using fun x : Z => hloc x.1 x.2
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun x : Z => ((π ⁻¹ᵁ V x : H.toScheme.Opens) : Set H.toScheme))
    (fun x => (π ⁻¹ᵁ V x).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hV ⟨x, hx⟩⟩)
  let W : t → X.left.Opens := fun i => V i.1
  have P := isPullback_iSup π X.hom (H.ι ≫ G.hom) f W fun i => hVp i.1
  have hS := smooth_iSup X.hom W fun i => hVs i.1
  have hC : IsCompact ((⨆ i, W i : X.left.Opens) : Set X.left) := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun i => (hVa i.1).isCompact
  have hA : ∀ x ∈ Z, π x ∈ ⨆ i, W i := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi⟩, hx⟩
  generalize (⨆ i, W i) = U at P hS hC hA
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hC
  have hq : QuasiCompact (U.ι ≫ X.hom) := (quasiCompact_iff_compactSpace _).2 inferInstance
  have hsep : IsSeparated (U.ι ≫ X.hom) := by
    have h₁ : IsFinite (π ∣_ U) := MorphismProperty.of_isPullback (P := @IsFinite) P.flip inferInstance
    have h₂ : Surjective (π ∣_ U) := MorphismProperty.of_isPullback (P := @Surjective) P.flip inferInstance
    have h₃ : IsSeparated (π ∣_ U ≫ U.ι ≫ X.hom) := by rw [P.w]; infer_instance
    exact isSeparated_of_surjective (π ∣_ U) _
  let N : Near f G :=
    { U := Over.mk (U.ι ≫ X.hom)
      smooth := hS
      separated := hsep
      quasiCompact := hq
      u := P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι
      isOpen := inferInstanceAs (IsOpenImmersion (P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι))
      u_over := (Category.assoc _ _ _).trans
        ((congrArg (P.isoPullback.inv ≫ ·) (Category.assoc _ _ _)).trans P.isoPullback_inv_snd)
      all := by
        intro g hg
        refine ⟨P.isoPullback.hom ⟨⟨g, hcl g hg⟩, hA ⟨g, hcl g hg⟩ hg⟩, ?_⟩
        change (P.isoPullback.hom ≫ P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι) _ = g
        rw [Iso.hom_inv_id_assoc]
        rfl }
  have pt : ∀ {T : Scheme.{0}} (s : T ⟶ S) (u : T ⟶ U.toScheme) (x : T ⟶ G.left), N.Pt s u x ↔
      ∃ y : T ⟶ (π ⁻¹ᵁ U).toScheme, y ≫ π ∣_ U = u ∧ y ≫ (π ⁻¹ᵁ U).ι ≫ H.ι ≫ G.hom = s ∧
        y ≫ (π ⁻¹ᵁ U).ι ≫ H.ι = x := by
    intro T s u x
    constructor
    · rintro ⟨x₀, h₁, h₂, h₃⟩
      refine ⟨x₀ ≫ P.isoPullback.inv, ?_, ?_, ?_⟩
      · exact (Category.assoc _ _ _).trans ((congrArg (x₀ ≫ ·) P.isoPullback_inv_fst).trans h₁)
      · exact (Category.assoc _ _ _).trans ((congrArg (x₀ ≫ ·) P.isoPullback_inv_snd).trans h₂)
      · exact (Category.assoc _ _ _).trans h₃
    · rintro ⟨y, h₁, h₂, h₃⟩
      refine ⟨y ≫ P.isoPullback.hom, ?_, ?_, ?_⟩
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) P.isoPullback_hom_fst).trans h₁)
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) P.isoPullback_hom_snd).trans h₂)
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (P.isoPullback.hom_inv_id_assoc _)).trans h₃)
  refine ⟨N, fun α β hα hαβ hπ T s u x hx => ?_⟩
  obtain ⟨y, rfl, rfl, rfl⟩ := (pt s u x).1 hx
  have Q := isPullback_morphismRestrict π U
  let δ : (π ⁻¹ᵁ U).toScheme ⟶ (π ⁻¹ᵁ U).toScheme :=
    Q.lift (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ α.resLE H H hα) (by rw [Category.assoc, hπ, Q.w])
  have hδ : δ ≫ (π ⁻¹ᵁ U).ι ≫ H.ι = (π ⁻¹ᵁ U).ι ≫ H.ι ≫ α := by
    rw [Q.lift_snd_assoc, Category.assoc, Scheme.Hom.resLE_comp_ι]
  refine (pt _ _ _).2 ⟨y ≫ δ, ?_, ?_, ?_⟩
  · rw [Category.assoc, Q.lift_fst]
  · simp only [Category.assoc]
    rw [reassoc_of% hδ, hαβ]
  · simp only [Category.assoc]
    rw [hδ]

theorem glue_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) → IsCompact (H : Set G'.left) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ))) → ∃ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ _ D D' hD A' G' _ _ hG U' a H hH hcl hc X π hX _ _ hπ _ _ hloc
  have := hG.separated
  have : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hρ.2.2
  have : Surjective (spMap ρ) := ⟨RingHom.IsIntegral.comap_surjective hρ.2.2.to_isIntegral hρ.2.1⟩
  obtain ⟨N, hN⟩ := exists_near (spMap ρ) G' H hcl hc X π fun x hx => by
    obtain ⟨V, h₁, h₂, h₃, h₄⟩ := hloc x hx
    refine ⟨V, h₁, h₂, h₃, ?_⟩
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    refine IsPullback.of_iso_pullback ⟨?_⟩ (@asIso _ _ _ _ _ h₄) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    rw [Scheme.Hom.resLE_comp_ι_assoc, hX]
    simp only [Category.assoc]
  exact ⟨N, fun σ => hN (a.act σ) _ (hH σ).ge (a.cart σ).1.w (hπ σ)⟩

end GlobalTheory.Mum.GlueNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackDivisionPointsPushEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivPush

theorem push_div_pts : ∀ {S S₀ : Scheme.{0}} (f : S ⟶ S₀) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (β : G.left ⟶ G₀.left), IsGrpPullback G G₀ f β → ∀ (n r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ G)) (c : (Fin r → ℤ) → (𝟙_ (Over S₀) ⟶ G₀)), (∀ a a', c (a + a') = c a * c a') → (∀ i, (d i ^ n).left ≫ β = f ≫ (c (Pi.single i 1)).left) → ∀ a, (∏ i, d i ^ ((n : ℤ) * a i)).left ≫ β = f ≫ (c a).left := by
  intro S S₀ f G _ _ G₀ _ _ β hp n r d c hc hd a
  let T : Over S := 𝟙_ (Over S)
  let U : Over.mk (T.hom ≫ f) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = f := by
    simp [U, T, Over.toUnit_left]
  let cH : (Fin r → ℤ) →+ Additive (𝟙_ (Over S₀) ⟶ G₀) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (c a)) (fun a a' => by simp [hc])
  have hca : c a = ∏ i, c (Pi.single i 1) ^ a i := by
    have e : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin r → ℤ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have := congrArg cH e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_zsmul] at this
    exact congrArg Additive.toMul this
  have hdi : ∀ i, pushHom hp T (d i ^ n) = preHom U (c (Pi.single i 1)) := by
    intro i
    apply Over.OverMorphism.ext
    show (d i ^ n).left ≫ β = U.left ≫ (c (Pi.single i 1)).left
    rw [hU]; exact hd i
  have key : pushHom hp T (∏ i, d i ^ ((n : ℤ) * a i)) = preHom U (c a) := by
    rw [hca, map_prod, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_zpow, map_zpow, zpow_mul, zpow_natCast, ← map_pow, hdi]
  have := congrArg (fun z => z.left) key
  rw [← hU]
  exact this

end GlobalTheory.DivPush
end

