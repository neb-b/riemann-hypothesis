module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegeneration
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem trF_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X → D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (mu : D.X) :
    (DegPre.trF D F mu).left ≫ (TF (R := R) F ◁ p).left =
      (TF (R := R) F ◁ p).left ≫ (DegPre.trF D₁ F (q mu)).left := by
  refine congrArg (fun m => m.left) (?_ : DegPre.trF D F mu ≫ (TF (R := R) F ◁ p) =
    (TF (R := R) F ◁ p) ≫ DegPre.trF D₁ F (q mu))
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerLeft_snd, DegPre.trF, DegPre.trF, lift_snd, lift_snd_assoc]
    have b : DegPre.prB D F ≫ p = (TF (R := R) F ◁ p) ≫ DegPre.prB D₁ F := (whiskerLeft_snd _ _).symm
    have e : (DegPre.prB D F * cP D _ mu) ≫ p = (TF (R := R) F ◁ p) ≫ (DegPre.prB D₁ F * cP D₁ _ (q mu)) := by
      rw [MonObj.mul_comp, MonObj.comp_mul, b, GlobalTheory.ProdUnif.cPoint_pr hc, comp_cP]
    exact e

theorem zF_pr {D D₁ : DegPre R} (p : D.P.A ⟶ D₁.P.A) [IsMonHom p] :
    (DegPre.zF D F).left ≫ (TF (R := R) F ◁ p).left = (DegPre.zF D₁ F).left := by
  refine congrArg (fun m => m.left) (?_ : DegPre.zF D F ≫ (TF (R := R) F ◁ p) = DegPre.zF D₁ F)
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem deltaφ_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X →+ D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (k : ℕ) (α mu : D.X) (a : Fin 4 ⊕ Fin 4) :
    DegPre.deltaφ D F k α mu a ≫ p.left = (TF (R := R) F ◁ p).left ≫ DegPre.deltaφ D₁ F k (q α) (q mu) a := by
  rcases a with a | a
  · refine (GlobalTheory.ProdUnif.famφ_pr hc F (α + k • mu) a).trans ?_
    rw [map_add (f := _), map_nsmul]; rfl
  · show ((DegPre.trF D F mu).left ≫ DegPre.famφ D F α a) ≫ _ =
      _ ≫ (DegPre.trF D₁ F (q mu)).left ≫ DegPre.famφ D₁ F (q α) a
    rw [Category.assoc, GlobalTheory.ProdUnif.famφ_pr hc, ← Category.assoc, trF_pr F hc, Category.assoc]

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

section Values

variable {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X)
  {w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)}

theorem famMult_box₂ (hrig : IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig)
    (hpsi : ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x)))
    (k : ℕ) (α mu : D.X) (y : (TF (R := R) F).left) {J₁ J₂ J}
    (hJ₁ : Good D₁.P.L y J₁) (hJ₂ : Good D₂.P.L y J₂) (hJ : Good D.P.L y J) :
    (∏ a, om w y J₁ J₂ J ((DegPre.zF D F).left ≫ DegPre.deltaφ D F k α mu a) ^ DegPre.deltaε k a) *
      val (Z := (TF (R := R) F).left) (DegPre.famMult D F k mu α) (𝟙 _) y J =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)) (𝟙 _) y J₁ *
        val (Z := (TF (R := R) F).left) (DegPre.famMult D₂ F k (q₂ mu) (q₂ α)) (𝟙 _) y J₂ := by
  have a₁ : ∀ χ, (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ =>
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have a₂ : (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left ≫ eSec D.P.A =
      (1 : TF (R := R) F ⟶ D.P.A).left :=
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have b₁ := fun χ => hpsi χ _ (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ J₂ J hJ₁ hJ₂ hJ
  have b₂ := hrig _ ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₁ J₂ J hJ₁ hJ₂ hJ
  simp only [Fintype.prod_unique, Category.comp_id] at b₁ b₂
  have r₀ : val D.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      val D.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J := val_pull hJ _ _ _
  have r₁ : val D₁.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ =
      val D₁.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₁ := val_pull hJ₁ _ _ _
  have r₂ : val D₂.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂ =
      val D₂.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₂ := val_pull hJ₂ _ _ _
  have c₁ : ∀ χ, val (D.psi χ) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      om w y J₁ J₂ J (cP D (TF (R := R) F) χ).left *
        (val (D₁.psi (q₁ χ)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ *
          val (D₂.psi (q₂ χ)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂) := fun χ => by
    have h := b₁ χ
    rw [zpow_neg_one, show (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ ptK (D.c χ) =
      (cP D (TF (R := R) F) χ).left from a₁ χ] at h
    exact inv_mul_eq_iff_eq_mul.1 h
  have c₂ : val D.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      (om w y J₁ J₂ J (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ *
        (val D₁.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ *
          val D₂.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂) := by
    rw [r₀, r₁, r₂]
    rw [zpow_one, Category.assoc, a₂] at b₂
    exact eq_inv_mul_of_mul_eq b₂
  have c₃ := c₁ (mu + α)
  rw [map_add (f := _), map_add (f := _)] at c₃
  rw [GlobalTheory.BoxFamily.prod_delta_zero F D k α mu (om w y J₁ J₂ J), GlobalTheory.BoxFamily.famMult_val F hJ,
    GlobalTheory.BoxFamily.famMult_val F hJ₁, GlobalTheory.BoxFamily.famMult_val F hJ₂, c₃, c₁ mu, c₁ α, c₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
  module

end Values

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem fe_along {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X →+ D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) {k : ℕ} (E₁ : Fam D₁ F k) (mu α : D.X)
    (u₁ : LB.Gen (LB.LinComb D₁.P.L (DegPre.deltaφ D₁ F k (q α) (q mu)) (DegPre.deltaε k))) (hu₁ : u₁.IsGen)
    (hc₁ : LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ u₁ (DegPre.zF D₁ F).left)
      (DegPre.famMult D₁ F k (q mu) (q α)))
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J₁} (hJ₁ : Good D₁.P.L z J₁) :
    sval (E₁.s (q (α + k • mu))) (r ≫ (TF (R := R) F ◁ p).left) z J₁ =
      sval (E₁.s (q α)) ((r ≫ (DegPre.trF D F mu).left) ≫ (TF (R := R) F ◁ p).left) z J₁ *
        (val u₁ (r ≫ (TF (R := R) F ◁ p).left) z J₁).val := by
  have h := (secRel_iff D₁.P.isLB _ _ _ _ _ _ _ _ _ u₁).1 (E₁.fe _ _ u₁ hu₁ hc₁) _
    (r ≫ (TF (R := R) F ◁ p).left) z J₁ hJ₁
  rw [map_add (f := _), map_nsmul, h, Category.assoc, Category.assoc, trF_pr F hc]

variable {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} {q₁ : D.X →+ D₁.X} {q₂ : D.X →+ D₂.X}
  {w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)}

theorem gen_box₂ (hS : IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂) (hw : w.IsGen)
    (hrig : IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig)
    (hpsi : ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) (hG : GlobalFnsSt)
    (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α))
    (u₁ : LB.Gen (LB.LinComb D₁.P.L (DegPre.deltaφ D₁ F k (q₁ α) (q₁ mu)) (DegPre.deltaε k))) (hu₁ : u₁.IsGen)
    (hc₁ : LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ u₁ (DegPre.zF D₁ F).left)
      (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)))
    (u₂ : LB.Gen (LB.LinComb D₂.P.L (DegPre.deltaφ D₂ F k (q₂ α) (q₂ mu)) (DegPre.deltaε k))) (hu₂ : u₂.IsGen)
    (hc₂ : LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ u₂ (DegPre.zF D₂ F).left)
      (DegPre.famMult D₂ F k (q₂ mu) (q₂ α))) :
    IsBoxGen w (TF (R := R) F ◁ p₁).left (TF (R := R) F ◁ p₂).left u u₁ u₂ := by
  haveI := hS.hom₁
  haveI := hS.hom₂
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (deltaφ_pr F hS.c_pr₁ k α mu)
    (deltaφ_pr F hS.c_pr₂ k α mu) hu hu₁ hu₂ (fst (TF (R := R) F) D.P.A).left (DegPre.zF D F).left
    (congrArg (fun q => q.left) z₁) (surj_appTop D F hG) ?_
  intro y J₁ J₂ J hJ₁ hJ₂ hJ
  have e := famMult_box₂ F q₁ q₂ hrig hpsi k α mu y hJ₁ hJ₂ hJ
  have v : val u (DegPre.zF D F).left y J =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D F k mu α) (𝟙 _) y J := by
    have h := val_corr hJ hc (𝟙 _)
    rwa [val_pull hJ, Category.id_comp] at h
  have v₁ : val u₁ ((DegPre.zF D F).left ≫ (TF (R := R) F ◁ p₁).left) y J₁ =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)) (𝟙 _) y J₁ := by
    have h := val_corr hJ₁ hc₁ (𝟙 _)
    rw [val_pull hJ₁, Category.id_comp] at h
    rw [zF_pr]; exact h
  have v₂ : val u₂ ((DegPre.zF D F).left ≫ (TF (R := R) F ◁ p₂).left) y J₂ =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₂ F k (q₂ mu) (q₂ α)) (𝟙 _) y J₂ := by
    have h := val_corr hJ₂ hc₂ (𝟙 _)
    rw [val_pull hJ₂, Category.id_comp] at h
    rw [zF_pr]; exact h
  rw [v, v₁, v₂]
  exact e

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

theorem exists_isBoxFam₂ : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), w.IsGen → IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig → (∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (E₁ : Fam D₁ F k) (E₂ : Fam D₂ F k), ∃ E : Fam D F k, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k E E₁ E₂ := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w hw hrig hpsi F _ _ k E₁ E₂
  haveI := hS.hom₁
  haveI := hS.hom₂
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  choose s hs using fun α : D.X => exists_boxSec w hw D₁.P.isLB D₂.P.isLB D.P.isLB
    (GlobalTheory.ProdUnif.famφ_pr hS.c_pr₁ F α) (GlobalTheory.ProdUnif.famφ_pr hS.c_pr₂ F α) (E₁.s (q₁ α)) (E₂.s (q₂ α))
  refine ⟨⟨s, ?_⟩, hs⟩
  intro mu α u hu hc
  obtain ⟨u₁, hu₁, hc₁⟩ := (gen_fe (D := D₁) (F := F) hG k (q₁ mu) (q₁ α)).1
  obtain ⟨u₂, hu₂, hc₂⟩ := (gen_fe (D := D₂) (F := F) hG k (q₂ mu) (q₂ α)).1
  have hb := gen_box₂ F hS hw hrig hpsi hG k α mu u hu hc u₁ hu₁ hc₁ u₂ hu₂ hc₂
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.P.isLB y
  have e₁ := hs (α + k • mu) _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have e₂ := hs α _ (𝟙 _ ≫ (DegPre.trF D F mu).left) y J₁ J₂ J hJ₁ hJ₂ hJ
  have e₃ := hb _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have f₁ := fe_along F hS.c_pr₁ E₁ mu α u₁ hu₁ hc₁ (𝟙 _) y hJ₁
  have f₂ := fe_along F hS.c_pr₂ E₂ mu α u₂ hu₂ hc₂ (𝟙 _) y hJ₂
  have e₅ : (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.deltaφ D F k α mu a) ^ DegPre.deltaε k a) =
      (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.famφ D F (α + k • mu) a) ^ DegPre.famε k a) *
      (∏ a, om w y J₁ J₂ J ((𝟙 _ ≫ (DegPre.trF D F mu).left) ≫ DegPre.famφ D F α a) ^ DegPre.famε k a)⁻¹ := by
    simp only [Category.assoc]
    exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
  refine (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.famφ D F (α + k • mu) a) ^ DegPre.famε k a).mul_right_inj.1 ?_
  refine e₁.trans ?_
  rw [f₁, f₂]
  refine Eq.trans ?_ ((congrArg₂ (· * ·) e₂ (congrArg Units.val e₃)).symm.trans ?_)
  · rw [Units.val_mul]; ring
  · rw [e₅]; exact GlobalTheory.BoxFamily.unit_shuffle _ _ _ _

end GlobalTheory.BoxFamSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.ExtDiv

open TopologicalSpace CartierDiv

theorem unitAt_map {Y V X : Scheme.{0}} [IsIntegral Y] [IsIntegral X] (i : V ⟶ Y) [IsOpenImmersion i]
    (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField) (h : PFF i φ θ) (v : V)
    {u : X.functionField} (hu : UnitAt (φ v) u) : UnitAt (i v) (θ u) := by
  obtain ⟨l, h₁, h₂⟩ := h
  obtain ⟨a, ha, rfl⟩ := hu
  let sY := Y.presheaf.stalkSpecializes (genericPoint_specializes (i v))
  let sX := X.presheaf.stalkSpecializes (genericPoint_specializes (φ v))
  have e₁ : Spec.map (inv (i.stalkMap v) ≫ sY) ≫ V.fromSpecStalk v = l := by
    rw [← cancel_mono i, h₁, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let t : X.presheaf.stalk (genericPoint X) ⟶ Y.presheaf.stalk (genericPoint Y) := CommRingCat.ofHom θ
  have e₂ : φ.stalkMap v ≫ inv (i.stalkMap v) ≫ sY = sX ≫ t := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (φ v)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, e₁, h₂, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  refine ⟨(φ.stalkMap v ≫ inv (i.stalkMap v)).hom a, ha.map _, ?_⟩
  exact congrArg (fun f => CommRingCat.Hom.hom f a) e₂

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

theorem finite_mult (D : CartierDiv Y) (U : Set Y) [NoetherianSpace U] :
    {z | z ∈ U ∧ D.mult z ≠ 0}.Finite := by
  classical
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    (D.supp.isClosed.preimage (continuous_subtype_val (p := (· ∈ U))))
  refine (hS.image fun T => if h : IsIrreducible ((Subtype.val : U → Y) '' T) then h.genericPoint
    else genericPoint Y).subset fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le
    (show (⟨z, hz.1⟩ : U) ∈ Subtype.val ⁻¹' (D.supp : Set Y) from mem_supp_of_mult_ne_zero hz.2))
  have hi' : IsIrreducible ((Subtype.val : U → Y) '' T) :=
    (hi T hT).image _ continuous_subtype_val.continuousOn
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos hi']
  have hg := hi'.isGenericPoint_genericPoint_closure
  have h₁ : z ≤ hi'.genericPoint := hg.specializes (subset_closure ⟨_, hzT, rfl⟩)
  have hsub : closure ((Subtype.val : U → Y) '' T) ⊆ D.supp :=
    closure_minimal (by rintro _ ⟨t, ht, rfl⟩; exact hU.ge (Set.mem_sUnion.2 ⟨T, hT, ht⟩))
      D.supp.isClosed
  have h₂ : hi'.genericPoint < genericPoint Y := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hsub hg.mem)
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [coheight_eq_one_of_mult_ne_zero hz.2] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

theorem locally_finite (O : Set Y) (c : Y → ℤ) (h0 : ∀ z, z ∉ O → c z = 0)
    (hc : ∀ z ∈ O, ∃ N : Set Y, IsOpen N ∧ z ∈ N ∧ ∃ E : CartierDiv Y, ∀ w ∈ N, c w = E.mult w)
    (y : Y) : ∃ W : Y.Opens, y ∈ W ∧ {z | z ∈ W ∧ c z ≠ 0}.Finite := by
  obtain ⟨_, ⟨U : Y.Opens, hU, rfl⟩, hy, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.1 (IsAffineOpen.isCompact hU)
  have : IsNoetherian U.toScheme := {}
  have : NoetherianSpace (U : Set Y) := inferInstanceAs (NoetherianSpace U.toScheme)
  choose! N hN hzN E hE using hc
  have hK : IsCompact ((Subtype.val : ↥(U : Set Y) → Y) '' ((Subtype.val : ↥(U : Set Y) → Y) ⁻¹' O)) :=
    (NoetherianSpace.isCompact _).image continuous_subtype_val
  have hKO : ∀ z ∈ ((Subtype.val : ↥(U : Set Y) → Y) '' ((Subtype.val : ↥(U : Set Y) → Y) ⁻¹' O)), z ∈ O := by
    rintro _ ⟨t, ht, rfl⟩; exact ht
  obtain ⟨t, ht, hcov⟩ := hK.elim_nhds_subcover N fun z hz =>
    (hN z (hKO z hz)).mem_nhds (hzN z (hKO z hz))
  refine ⟨U, hy, (t.finite_toSet.biUnion fun z _ => finite_mult (E z) (U : Set Y)).subset fun w hw => ?_⟩
  have hwO : w ∈ O := by_contra fun h => hw.2 (h0 w h)
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.1 (hcov ⟨⟨w, hw.1⟩, hwO, rfl⟩)
  exact Set.mem_iUnion₂.2 ⟨z, hz, hw.1, hE z (hKO z (ht z hz)) w hwz ▸ hw.2⟩

theorem exists_mult_eq (hY : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) (c : Y → ℤ)
    (h1 : ∀ z, c z ≠ 0 → Order.coheight z = 1)
    (hf : ∀ y, ∃ W : Y.Opens, y ∈ W ∧ {z | z ∈ W ∧ c z ≠ 0}.Finite) :
    ∃ D : CartierDiv Y, ∀ z, D.mult z = c z := by
  classical
  have : GlobalTheory.IsNormalScheme Y := ⟨fun x => inferInstance, fun x => by have := hY x; infer_instance⟩
  choose W hW hfin using hf
  have hE : ∀ y, ∃ E : CartierDiv Y, ∀ z ∈ W y, E.mult z = c z := fun y => by
    obtain ⟨E, hE⟩ := exists_mult_eq_of_locallyFactorial Y hY (fun z => if z ∈ W y then c z else 0)
      ((hfin y).subset fun z hz => by
        by_cases h : z ∈ W y
        · exact ⟨h, by simpa [h] using hz⟩
        · simp [h] at hz)
      fun z hz => h1 z fun h => hz (by simp [h])
    exact ⟨E, fun z hz => by rw [hE z, if_pos hz]⟩
  choose E hE using hE
  let D : CartierDiv Y := show cartierGroup Y from ⟨fun y => (E y).germ y, fun y => by
    obtain ⟨U, hU, g, hg⟩ := (E y).exists_isEqn_nhds y
    refine ⟨U ⊓ W y, ⟨hU, hW y⟩, g, fun z hz =>
      (MultEff.eff_supp_eq_of_mult Y (E z)).2.2.2 z g fun w hw => ?_⟩
    rw [hE z w (hw.mem_open (W z).isOpen (hW z)), ← hE y w (hw.mem_open (W y).isOpen hz.2),
      (hg w (hw.mem_open U.isOpen hz.1)).mult_eq]⟩
  refine ⟨D, fun z => ?_⟩
  obtain ⟨g, hg⟩ := (E z).exists_isEqn z
  rw [(show D.IsEqn z g from hg).mult_eq, ← hg.mult_eq, hE z z (hW z)]

end GlobalTheory.Desc.ExtDiv


open GlobalTheory.Desc.ExtDiv CartierDiv in
theorem GlobalTheory.Desc.exists_cartierDiv_closure : ∀ (Y V X : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian Y], (∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) → ∀ (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), Flat φ → PFF i φ θ → ∀ D : CartierDiv X, ∃ D₁ : CartierDiv Y, PPull i φ θ D D₁ ∧ ∀ y : Y, y ∉ Set.range i → ringKrullDim (Y.presheaf.stalk y) = 1 → D₁.IsEqn y 1 := by
  intro Y V X _ _ _ hY i _ φ θ _ hθ D
  classical
  have : GlobalTheory.IsNormalScheme Y := ⟨fun x => inferInstance, fun x => by have := hY x; infer_instance⟩
  choose e he using fun v : V => D.exists_isEqn (φ v)
  let c : Y → ℤ := fun z => if h : z ∈ Set.range i then Scheme.ord (θ (e h.choose)) z else 0
  have h0 : ∀ z, z ∉ Set.range i → c z = 0 := fun z hz => dif_neg hz
  have h1 : ∀ z, c z ≠ 0 → Order.coheight z = 1 := fun z hz => by
    by_contra h
    apply hz
    simp only [c]
    split_ifs
    · exact Scheme.ord_eq_zero_of_coheight_neq_one h _
    · rfl
  have hc : ∀ v (g : X.functionFieldˣ), D.IsEqn (φ v) g → c (i v) = Scheme.ord (θ g) (i v) := by
    intro v g hg
    have hv : i v ∈ Set.range i := ⟨v, rfl⟩
    have e₀ : hv.choose = v := i.isOpenEmbedding.injective hv.choose_spec
    have hu := (unitAt_map i φ θ hθ v (hg.iff_unitAt.1 (he v))).ord_eq_zero
    simp only [c, dif_pos hv, e₀]
    rw [← div_mul_cancel₀ (e v : X.functionField) g.ne_zero, map_mul,
      Scheme.ord_mul ((map_ne_zero θ).2 (div_ne_zero (e v).ne_zero g.ne_zero))
        ((map_ne_zero θ).2 g.ne_zero), hu, zero_add]
  obtain ⟨D₁, hD₁⟩ := exists_mult_eq hY c h1 (locally_finite (Set.range i) c h0 (by
    rintro _ ⟨v, rfl⟩
    obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (φ v)
    refine ⟨i '' (φ ⁻¹ᵁ U), i.isOpenEmbedding.isOpenMap _ (φ ⁻¹ᵁ U).isOpen, ⟨v, hU, rfl⟩,
      principal (Units.map θ.toMonoidHom g), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [hc w g (hg _ hw), (isEqn_principal _ _).mult_eq]
    rfl))
  refine ⟨D₁, fun v g hg => (MultEff.eff_supp_eq_of_mult Y D₁).2.2.2 _ _ fun w hw => ?_,
    fun y hy hd => (MultEff.eff_supp_eq_of_mult Y D₁).2.2.2 _ _ fun w hw => ?_⟩
  · obtain ⟨w, rfl⟩ : w ∈ Set.range i := hw.mem_open i.isOpenEmbedding.isOpen_range ⟨v, rfl⟩
    obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
    have hwv := (i.isOpenEmbedding.isInducing.specializes_iff.1 hw).map φ.continuous
    rw [hD₁, hc w g (hgU _ (hwv.mem_open U.isOpen hU))]
    rfl
  · rw [hD₁, Units.val_one, MultEff.ord_one]
    by_contra hne
    have hw1 := h1 w (Ne.symm hne)
    have hy1 : Order.coheight y = 1 := by
      rw [ringKrullDim_stalk_eq_coheight] at hd
      exact_mod_cast hd
    have hlt : y < w := lt_of_le_not_ge hw fun e =>
      hne ((Specializes.antisymm hw e).eq ▸ (h0 y hy).symm)
    have h₃ := Order.coheight_add_one_le hlt
    rw [hw1, hy1] at h₃
    exact absurd h₃ (by decide)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernTopPowerVolumeDensityRatio
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ENNReal

namespace GlobalTheory.HSAmp

theorem exists_isRatio_chernInt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ (L : HermLB p), L.SemiPos D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D),
    ∃ ρ : CxPts p σ → ℝ, ω.IsRatio (L.φ σ) ρ ∧ (∀ y, 0 ≤ ρ y) ∧ ∀ f : CxPts p σ → ℝ, Continuous f →
      (L.φ σ).chernInt D Set.univ f = ∫ y, f y * ρ y ∂ω.meas := by
  intro k _ X _ p D hX hG L hL σ ω
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hG σ
  have hcov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source := fun y =>
    have ⟨i, hi⟩ := R.cover y
    ⟨R.chart i, hi⟩
  choose c₀ hc₀ using hcov
  let ρ : CxPts p σ → ℝ := fun y => (c₀ y).chernDens (L.φ σ) y / ω.dens (c₀ y) y
  have key : ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, c.chernDens (L.φ σ) y = ρ y * ω.dens c y := by
    intro c y hy
    have hpos := ω.pos (c₀ y) y (hc₀ y)
    rw [c.chernDens_trans (c₀ y) (L.cInf σ) hy (hc₀ y), ω.trans c (c₀ y) y hy (hc₀ y)]
    simp only [ρ]
    field_simp
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y =>
    div_nonneg ((c₀ y).chernDens_nonneg (L.cInf σ) (hL σ) (hc₀ y)) (ω.pos _ _ (hc₀ y)).le

  have hρc : Continuous ρ := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    set c := c₀ y
    set i := pick (L.φ σ).isLB y
    have hyi : y ∈ ptsIn p σ (L.B.U i) := mem_pick _ y
    set O : Set (CxPts p σ) := c.e.source ∩ ptsIn p σ (L.B.U i) with hO
    have hOo : IsOpen O := c.e.open_source.inter (isOpen_ptsIn _)
    have hyO : y ∈ O := ⟨hc₀ y, hyi⟩
    set U' : Set (V D) := c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (L.B.U i)
    have hU' : IsOpen U' := isOpen_over c.e (isOpen_ptsIn _)
    have h2 : ContDiffOn ℝ 2 (fun v => (L.φ σ).φ i (c.e.symm v)) U' :=
      (contDiffOn_chart ((L.cInf σ) i) c).of_le (by norm_cast)
    have hmap : Set.MapsTo c.e O U' := fun z hz => mem_over c.e hz.1 hz.2
    have hent : ∀ a b, ContinuousOn (fun z => c.hess (L.φ σ) i z a b) O := fun a b =>
      (continuousOn_cHess_of_contDiffOn_two D U' _ hU' h2 a b).comp (c.e.continuousOn.mono fun z hz => hz.1) hmap
    have hdet : ContinuousOn (fun z => c.chernDens (L.φ σ) z) O := by
      have hm : ContinuousOn (fun z => c.hess (L.φ σ) i z) O :=
        continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => hent a b
      have hc : Continuous fun M : Matrix (Fin D) (Fin D) ℂ => (D.factorial / Real.pi ^ D : ℝ) * M.det.re :=
        continuous_const.mul (Complex.continuous_re.comp continuous_id.matrix_det)
      refine (hc.comp_continuousOn hm).congr fun z hz => ?_
      exact c.chernDens_eq (L.cInf σ) hz.1 hz.2
    have hq : ContinuousOn (fun z => c.chernDens (L.φ σ) z / ω.dens c z) O :=
      hdet.div ((ω.cont c).mono fun z hz => hz.1) fun z hz => (ω.pos c z hz.1).ne'
    refine (hq.congr fun z hz => ?_).continuousAt (hOo.mem_nhds hyO)
    rw [key c z hz.1, mul_div_cancel_right₀ _ (ω.pos c z hz.1).ne']
  have hm : Measurable fun y => ENNReal.ofReal (ρ y) := hρc.measurable.ennreal_ofReal
  have hneg : (L.φ σ).chernPart D (-1) = 0 := Weight.chernPart_neg_eq_zero (L.cInf σ) (hL σ)
  have hmeas : (L.φ σ).chernPart D 1 = ω.meas.withDensity fun y => ENNReal.ofReal (ρ y) := by
    refine ext_of_cover (fun c : AlgChart p σ D => c.e.source) (fun c => c.e.open_source)
      (fun y => ⟨c₀ y, hc₀ y⟩) fun c A hA hAc => ?_
    have hr : ω.meas.restrict A = (chartMeas c.e fun y => ENNReal.ofReal (ω.dens c y)).restrict A := by
      ext T hT
      rw [Measure.restrict_apply hT, Measure.restrict_apply hT, VolDens.meas,
        glueMeas_apply _ _ (fun a a' => a.holo_trans a') (fun a a' z hz hz' => by
          rw [ω.trans a a' z hz hz', ENNReal.ofReal_mul (sq_nonneg _)]) c (hT.inter hA)
          (Set.inter_subset_right.trans hAc)]
    have hsy : AEMeasurable c.e.symm (volume.restrict c.e.target) :=
      c.e.continuousOn_symm.aemeasurable c.e.open_target.measurableSet
    have hdm : AEMeasurable ((fun y => ENNReal.ofReal (ω.dens c y)) ∘ c.e.symm) (volume.restrict c.e.target) :=
      (ENNReal.continuous_ofReal.comp_continuousOn ((ω.cont c).comp c.e.continuousOn_symm
        fun v hv => c.e.map_target hv)).aemeasurable c.e.open_target.measurableSet
    have hI := measurableSet_image c.e hA hAc
    have hIt : c.e '' A ⊆ c.e.target := by rintro _ ⟨z, hz, rfl⟩; exact c.e.map_source (hAc hz)
    rw [Weight.chernPart_apply (L.cInf σ) 1 c hA hAc, withDensity_apply _ hA, hr, ← lintegral_indicator hA, chartMeas,
      lintegral_map' (hm.indicator hA).aemeasurable (hsy.mono_ac (withDensity_absolutelyContinuous _ _)),
      lintegral_withDensity_eq_lintegral_mul₀ hdm (g := fun v => A.indicator (fun y => ENNReal.ofReal (ρ y)) (c.e.symm v))
        ((hm.indicator hA).comp_aemeasurable hsy),
      ← Set.inter_eq_left.2 hIt, ← Measure.restrict_restrict hI, ← lintegral_indicator hI]
    refine setLIntegral_congr_fun c.e.open_target.measurableSet fun v hv => ?_
    by_cases hvA : c.e.symm v ∈ A
    · have hvI : v ∈ c.e '' A := ⟨_, hvA, c.e.right_inv hv⟩
      simp only [Set.indicator_of_mem hvI, Pi.mul_apply, Set.indicator_of_mem hvA, Function.comp_apply,
        Units.val_one, Int.cast_one, one_mul]
      rw [key c _ (hAc hvA), ENNReal.ofReal_mul (hρ0 _), mul_comm]
    · have hvI : v ∉ c.e '' A := by
        rintro ⟨z, hz, rfl⟩
        exact hvA (by rwa [c.e.left_inv (hAc hz)])
      simp only [Set.indicator_of_notMem hvI, Pi.mul_apply, Set.indicator_of_notMem hvA, mul_zero]
  refine ⟨ρ, ⟨hρc, key⟩, hρ0, fun f _ => ?_⟩
  have hn : Measurable fun y => (ρ y).toNNReal := hρc.measurable.real_toNNReal
  rw [Weight.chernInt, hneg, Measure.restrict_univ, Measure.restrict_univ, integral_zero_measure, sub_zero, hmeas]
  change ∫ y, f y ∂ω.meas.withDensity (fun y => ((ρ y).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hn]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hρ0 y), smul_eq_mul]
  exact mul_comm _ _

end GlobalTheory.HSAmp
end
end

