module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixUnitsExtendNormalNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EighthPowerUnits

section Rel

variable {S' S : Scheme.{0}} {j : S' ⟶ S} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
  {φ : G'.left ⟶ G.left}

theorem one_left_comp (hφ : IsGrpPullback G' G j φ) :
    (1 : G' ⟶ G').left ≫ φ = φ ≫ (1 : G ⟶ G).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hφ.1.w
  let z : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ)
    (by rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w]; rfl)
  have h := hφ.2 G' 1 1 z z rfl rfl
  rw [_root_.mul_one] at h
  have hz : z = 1 := mul_eq_left.1 (Over.OverMorphism.ext h)
  have h1 : φ₀ ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  have h2 : z.left = (φ₀ ≫ (1 : G ⟶ G)).left := congrArg (fun w => w.left) (hz.trans h1.symm)
  rw [Over.comp_left] at h2
  exact h2

theorem mul_left_comp (hφ : IsGrpPullback G' G j φ) {e₁ e₂ : G' ⟶ G'} {F₁ F₂ : G ⟶ G}
    (h₁ : e₁.left ≫ φ = φ ≫ F₁.left) (h₂ : e₂.left ≫ φ = φ ≫ F₂.left) :
    (e₁ * e₂).left ≫ φ = φ ≫ (F₁ * F₂).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hφ.1.w
  have h := hφ.2 G' e₁ e₂ (φ₀ ≫ F₁) (φ₀ ≫ F₂) h₁.symm h₂.symm
  rw [← MonObj.comp_mul] at h
  exact h.symm

theorem comp_left_comp {e₁ e₂ : G' ⟶ G'} {F₁ F₂ : G ⟶ G}
    (h₁ : e₁.left ≫ φ = φ ≫ F₁.left) (h₂ : e₂.left ≫ φ = φ ≫ F₂.left) :
    (e₁ ≫ e₂).left ≫ φ = φ ≫ (F₁ ≫ F₂).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

end Rel

theorem exists_matrixUnits_extend : ∀ {S B : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (U₀ : S.Opens) (hU : Dense (U₀ : Set S)) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (G' : Over U₀.toScheme) [GrpObj G'] (P : Over B) [GrpObj P] [IsCommMonObj P] (f : U₀.toScheme ⟶ B) (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G U₀.ι φ) (hψ : IsGrpPullback G' P f ψ) (E' : Fin 8 → Fin 8 → (P ⟶ P)) (hE' : ∀ a b, IsMonHom (E' a b)) (hrel : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1) (hsum : ∏ a, E' a a = 𝟙 P), ∃ E : Fin 8 → Fin 8 → (G ⟶ G), (∀ a b, IsMonHom (E a b)) ∧ (∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) ∧ ∏ a, E a a = 𝟙 G ∧ ∀ a b, ∃ e : G' ⟶ G', IsMonHom e ∧ e.left ≫ φ = φ ≫ (E a b).left ∧ e.left ≫ ψ = ψ ≫ (E' a b).left := by
  intro S B _ hS U₀ hU G _ _ hG G' _ P _ _ f φ ψ hφ hψ E' hE' hrel hsum
  have : IsDominant U₀.ι := AlgebraicGeometry.Opens.isDominant_ι hU
  obtain ⟨_, _⟩ := GlobalTheory.Published.SemiAbelianHomExtension.quasiCompact_and_dominant hS U₀.ι
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  let e : Fin 8 → Fin 8 → (G' ⟶ G') := fun a b =>
    Over.homMk (hψ.1.lift (ψ ≫ (E' a b).left) G'.hom (by rw [Category.assoc, Over.w, hψ.1.w]))
      (hψ.1.lift_snd _ _ _)
  have he : ∀ a b, (e a b).left ≫ ψ = ψ ≫ (E' a b).left := fun a b => hψ.1.lift_fst _ _ _
  have heM : ∀ a b, IsMonHom (e a b) := fun a b => by
    haveI := hE' a b
    exact ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback hψ hψ (E' a b) (e a b) (he a b)
  have uq : ∀ {x y : G' ⟶ G'} {F : P ⟶ P}, x.left ≫ ψ = ψ ≫ F.left → y.left ≫ ψ = ψ ≫ F.left → x = y :=
    fun hx hy => Over.OverMorphism.ext (hψ.1.hom_ext (hx.trans hy.symm) ((Over.w _).trans (Over.w _).symm))
  have uG : ∀ {F₁ F₂ : G ⟶ G}, φ ≫ F₁.left = φ ≫ F₂.left → F₁ = F₂ :=
    fun h => GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 h
  have ext : ∀ a b, ∃ F : G ⟶ G, IsMonHom F ∧ (e a b).left ≫ φ = φ ≫ F.left := fun a b => by
    haveI := heM a b
    exact (GlobalTheory.Published.SemiAbelianHomExtension.of_isGrpPullback GlobalTheory.semiAbelianHomExtension_holds hS hG hG hφ hφ
      (e a b)).exists
  choose E hE using ext
  refine ⟨E, fun a b => (hE a b).1, ?_, ?_, fun a b => ⟨e a b, heM a b, (hE a b).2, he a b⟩⟩
  · intro a b c d
    apply uG
    by_cases hbc : b = c
    · subst hbc
      rw [if_pos rfl]
      have h1 := comp_left_comp (he a b) (he b d)
      rw [hrel, if_pos rfl] at h1
      have h2 : e a b ≫ e b d = e a d := uq h1 (he a d)
      rw [← comp_left_comp (hE a b).2 (hE b d).2, h2, (hE a d).2]
    · rw [if_neg hbc]
      have h1 := comp_left_comp (he a b) (he c d)
      rw [hrel, if_neg hbc] at h1
      have h2 : e a b ≫ e c d = 1 := uq h1 (one_left_comp hψ)
      rw [← comp_left_comp (hE a b).2 (hE c d).2, h2, one_left_comp hφ]
  · have key : ∀ s : Finset (Fin 8), ∃ x : G' ⟶ G', x.left ≫ φ = φ ≫ (∏ a ∈ s, E a a).left ∧
        x.left ≫ ψ = ψ ≫ (∏ a ∈ s, E' a a).left := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · refine ⟨1, ?_, ?_⟩
        · rw [Finset.prod_empty]; exact one_left_comp hφ
        · rw [Finset.prod_empty]; exact one_left_comp hψ
      · intro a s ha ih
        obtain ⟨x, h1, h2⟩ := ih
        refine ⟨e a a * x, ?_, ?_⟩
        · rw [Finset.prod_insert ha]; exact mul_left_comp hφ (hE a a).2 h1
        · rw [Finset.prod_insert ha]; exact mul_left_comp hψ (he a a) h2
    obtain ⟨x, h1, h2⟩ := key Finset.univ
    rw [hsum] at h2
    have hx : x = 𝟙 G' := uq h2 (by simp)
    apply uG
    rw [← h1, hx]
    simp

end GlobalTheory.EighthPowerUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedBundleFrameFromPartFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section

namespace GlobalTheory.Mum.Two.Mix

theorem exists_frame_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X) (j j' : ℕ) (g : GtPtF D₁ F) (b' : TF (R := R) F ⟶ D₂.P.A), b' = g.b ≫ b → ∀ (w : Frm D₂ F j b') (w' : Frm D₁ F j' g.b), w.IsGen → w'.IsGen → ∃ τ : LB.Gen (LB.LinComb (JN D₁ D₂) (fun i => g.b.left ≫ mixφ D₁ D₂ b α i) (MixedConv.mixε j j')), τ.IsGen ∧ ∀ z J, Good (JN D₁ D₂) z J → val τ (𝟙 _) z J = rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s α) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹ := by
  intro R _ _ D₁ D₂ F _ _ b α j j' g b' hb w w' hw hw'
  subst hb
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  let ρ₁ : LB.Gen (LB.LinComb D₁.P.L (fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₁.P.A) (fun _ => 1)) :=
    LB.pullGen D₁.P.L (fun _ : PUnit.{1} => eSec D₁.P.A) (fun _ => 1) D₁.rig (TF (R := R) F).hom
  have hρ₁ : ρ₁.IsGen := DVR.pullGen_isGen _ _ _ _ D₁.rig_gen _
  let ρ₂ : LB.Gen (LB.LinComb D₂.P.L (fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₂.P.A) (fun _ => 1)) :=
    LB.pullGen D₂.P.L (fun _ : PUnit.{1} => eSec D₂.P.A) (fun _ => 1) D₂.rig (TF (R := R) F).hom
  have hρ₂ : ρ₂.IsGen := DVR.pullGen_isGen _ _ _ _ D₂.rig_gen _
  let t := LB.mulGen (JN D₁ D₂) _ _ _ _
    (LB.mulGen (JN D₁ D₂) _ _ _ _ (p₂.gen (GeneratorPullback.powGen D₂.P.L _ _ ρ₂ j)) (p₁.gen (GeneratorPullback.powGen D₁.P.L _ _ ρ₁ j')))
    (LB.invGen (JN D₁ D₂) _ _ (LB.mulGen (JN D₁ D₂) _ _ _ _ (p₁.gen (g.s α))
      (LB.mulGen (JN D₁ D₂) _ _ _ _ (p₂.gen w) (p₁.gen w'))))
  have ht : t.IsGen :=
    DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₂.gen_isGen (DVR.powGen_isGen _ _ _ _ hρ₂ _))
        (p₁.gen_isGen (DVR.powGen_isGen _ _ _ _ hρ₁ _)))
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₁.gen_isGen (g.isGen α))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₂.gen_isGen hw) (p₁.gen_isGen hw'))))
  obtain ⟨τ, hτ, hv⟩ := exists_gen (jn_isLB D₁ D₂) (φ' := fun i => g.b.left ≫ mixφ D₁ D₂ b α i)
    (ε' := MixedConv.mixε j j') (fun U _ h => by
      have q₁ : ∏ i : PUnit.{1}, h ((fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₂.P.A) i ≫ coprod.inr) ^
          ((j : ℤ) * (fun _ => (1 : ℤ)) i) = h ((1 : TF (R := R) F ⟶ D₂.P.A).left ≫ coprod.inr) ^ (j : ℤ) := by
        rw [Fintype.prod_unique, _root_.mul_one]; rfl
      have q₂ : ∏ i : PUnit.{1}, h ((fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₁.P.A) i ≫ coprod.inl) ^
          ((j' : ℤ) * (fun _ => (1 : ℤ)) i) = h ((1 : TF (R := R) F ⟶ D₁.P.A).left ≫ coprod.inl) ^ (j' : ℤ) := by
        rw [Fintype.prod_unique, _root_.mul_one]; rfl
      have q₃ := prod_gt g.b α (fun f => h (f ≫ coprod.inl))
      have q₄ := CoefBasic.prod_line j (g.b ≫ b) (fun f => h (f ≫ coprod.inr))
      have q₅ := CoefBasic.prod_line j' g.b (fun f => h (f ≫ coprod.inl))
      have q₆ := prod_neg (fun i => h (Sum.elim (fun k => DegPre.gtφ D₁ F g.b α k ≫ coprod.inl)
        (Sum.elim (fun k => DegPre.lineφ D₂ F (g.b ≫ b) k ≫ coprod.inr) (fun k => DegPre.lineφ D₁ F g.b k ≫ coprod.inl)) i))
        (Sum.elim DegPre.gtε (Sum.elim (DegPre.lineε j) (DegPre.lineε j')))
        (DVR.prod_sum₂ (U := U) _ q₃ (DVR.prod_sum₂ (U := U) _ q₄ q₅))
      have q₇a : ∏ i : PUnit.{1}, h (g.b.left ≫ mixφ D₁ D₂ b α (.inl i)) ^ MixedConv.mixε j j' (.inl i) =
          h ((g.b ≫ b).left ≫ coprod.inr) ^ (j : ℤ) := by
        rw [Fintype.prod_unique]
        show h (g.b.left ≫ b.left ≫ coprod.inr) ^ (j : ℤ) = _
        rw [Over.comp_left, Category.assoc]
      have q₇b : ∏ i : Fin 4, h (g.b.left ≫ mixφ D₁ D₂ b α (.inr i)) ^ MixedConv.mixε j j' (.inr i) =
          ∏ i, (fun f => h (f ≫ coprod.inl)) (g.b.left ≫ D₁.famφB α i) ^ DegPre.famε j' i :=
        Finset.prod_congr rfl fun i _ => by
          show h (g.b.left ≫ D₁.famφB α i ≫ coprod.inl) ^ DegPre.famε j' i = _
          rw [← Category.assoc]
      have q₇c := MixedConv.prod_comp D₁ g.b α j' (fun f => h (f ≫ coprod.inl))
      refine Eq.trans (DVR.prod_sum₂ (U := U) _ (DVR.prod_sum₂ (U := U) _ q₁ q₂) q₆)
        (Eq.trans ?_ (DVR.prod_sum₂ (U := U) _ q₇a (q₇b.trans q₇c)).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      push_cast
      module) t ht
  refine ⟨τ, hτ, fun z J hJ => (hv _ _ z J hJ).trans ?_⟩
  have g₁ := p₁.good hJ
  have g₂ := p₂.good hJ
  have e₂ : val (GeneratorPullback.powGen D₂.P.L _ _ ρ₂ j) (𝟙 _) z (rr J) = rigV D₂ (TF (R := R) F).hom z (rr J) ^ j :=
    (map_pow _ _ _).trans (congrArg (· ^ j) ((val_pull g₂ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  have e₁ : val (GeneratorPullback.powGen D₁.P.L _ _ ρ₁ j') (𝟙 _) z (rl J) = rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' :=
    (map_pow _ _ _).trans (congrArg (· ^ j') ((val_pull g₁ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  rw [val_mul hJ, val_mul hJ, val_inv, val_mul hJ, val_mul hJ, p₂.val_gen _ _ _ hJ, p₁.val_gen _ _ _ hJ,
    p₁.val_gen _ _ _ hJ, p₂.val_gen _ _ _ hJ, p₁.val_gen _ _ _ hJ]
  rw [← e₁, ← e₂]

end GlobalTheory.Mum.Two.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSectionJoinBundles
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

theorem prod_mix_hom {R : Type} [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X)
    (j j' : ℕ) {U : Type} [CommGroup U] (h : (D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) → U) :
    ∏ i, h (mixφ D₁ D₂ b α i) ^ MixedConv.mixε j j' i = h (b.left ≫ coprod.inr) ^ (j : ℤ) *
      (h (Over.Hom.left (𝟙 D₁.P.A) ≫ coprod.inl) ^ ((j' : ℤ) - 1) * h ((cP D₁ D₁.P.A α * 𝟙 D₁.P.A).left ≫ coprod.inl) *
        (h ((cP D₁ D₁.P.A α).left ≫ coprod.inl))⁻¹ * h ((1 : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl)) :=
  DVR.prod_sum₂ (K := PUnit.{1}) (K' := Fin 4) (U := U) _ (Fintype.prod_unique _)
    (MixedConv.prod_comp D₁ (𝟙 _) α j' (fun q => h (q ≫ coprod.inl)))

theorem exists_mix_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (j j' : ℕ) (χ : D₂.X) (χ' β α : D₁.X), χ' + β = α → ∀ (u : LB.Gen (CmpLB D₁ D₂ b χ' χ)), u.IsGen → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' β), ∃ n : LB.Sec (LB.LinComb (JN D₁ D₂) (mixφ D₁ D₂ b α) (MixedConv.mixε j j')), ∀ (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) (J), Good (JN D₁ D₂) z J → sval n r z J = sval f (r ≫ b.left) z (rr J) * sval f' r z (rl J) * (val u r z J * val (MixedConv.cubB D₁ χ' β) r z (rl J)).val := by
  intro R _ _ D₁ D₂ b j j' χ χ' β α hα u hu f f'
  subst hα
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  obtain ⟨t, ht⟩ := exists_sec (jn_isLB D₁ D₂) (φ' := mixφ D₁ D₂ b (χ' + β)) (ε' := MixedConv.mixε j j')
    (fun U _ h => by
      have q₁ := prod_cub (cP D₁ D₁.P.A χ') (cP D₁ D₁.P.A β) (𝟙 D₁.P.A) (fun q => h (q ≫ coprod.inl))
      have q₂ := MixedConv.prod_comp D₂ b χ j (fun q => h (q ≫ coprod.inr))
      have q₃ := MixedConv.prod_comp D₁ (𝟙 _) β j' (fun q => h (q ≫ coprod.inl))
      have q₄ := prod_mix_hom D₁ D₂ b (χ' + β) j j' h
      have q₅ := MixedConv.prod_coord D₁ (𝟙 _) χ' (fun q => h (q ≫ coprod.inl))
      have q₆ := MixedConv.prod_coord_inv D₂ b χ (fun q => h (q ≫ coprod.inr))
      rw [DVR.cPoint_add] at q₄
      simp only [Over.id_left, Category.id_comp] at q₃ q₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := (Fin 4 ⊕ Fin 4) ⊕ thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ q₂ q₃)
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ q₅ q₆) q₁)) (Eq.trans ?_ q₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.id_left, Category.id_comp]
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec (p₂.sec (H1.SectionArithmetic.pullSec f b.left)) (p₁.sec f'))
      (Geo.Tor.genSec (LB.mulGen (JN D₁ D₂) _ _ _ _ u (p₁.gen (MixedConv.cubB D₁ χ' β)))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (p₁.gen_isGen (MixedConv.cubB_isGen D₁ χ' β)))))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  exact (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
      ((p₂.sval_sec _ _ z hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z (p₂.good hJ))) (p₁.sval_sec _ _ z hJ)))
    ((sval_genSec _ _ _ z hJ).trans (congrArg Units.val ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (p₁.val_gen _ _ z hJ)))))))

end GlobalTheory.Mum.Two.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevelImports
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.EndRosati

namespace GlobalTheory.HomMum

variable {S : Scheme.{0}}

theorem mφ_comp {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂)
    {T : Over S} (x y : T ⟶ H₁) (k : MK) :
    (lift x y).left ≫ mφ H₁ H₂ a b k =
      Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr)
        (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₁ ![x, y] I.down).left ≫ coprod.inl) k := by
  rcases k with I | I
  · have e : lift x y ≫ lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b) ≫ psum H₂ (x2 H₂) I.down =
        psum H₂ ![x ≫ a, y ≫ b] I.down := by
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr =
      (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr
    rw [← e]
    simp only [Over.comp_left, Category.assoc]
  · have e : lift x y ≫ psum H₁ (x2 H₁) I.down = psum H₁ ![x, y] I.down := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl = (psum H₁ ![x, y] I.down).left ≫ coprod.inl
    rw [← e]
    simp only [Over.comp_left, Category.assoc]

theorem mφ_push {S' : Scheme.{0}} {j : S' ⟶ S} {E₁ E₂ : Over S'} [GrpObj E₁] [IsCommMonObj E₁] [GrpObj E₂]
    [IsCommMonObj E₂] {A₁ A₂ : Over S} [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂]
    (p₁ : (Over.map j).obj E₁ ⟶ A₁) (p₂ : (Over.map j).obj E₂ ⟶ A₂)
    (hm₁ : ∀ {T : Over S'} (x y : T ⟶ E₁), push p₁ (x * y) = push p₁ x * push p₁ y)
    (hm₂ : ∀ {T : Over S'} (x y : T ⟶ E₂), push p₂ (x * y) = push p₂ x * push p₂ y)
    {a' b' : E₁ ⟶ E₂} {a b : A₁ ⟶ A₂} (ha : push p₂ a' = p₁ ≫ a) (hb : push p₂ b' = p₁ ≫ b)
    {T : Over S'} (x y : T ⟶ E₁) (k : MK) :
    (lift (push p₁ x) (push p₁ y)).left ≫ mφ A₁ A₂ a b k =
      (lift x y).left ≫ mφ E₁ E₂ a' b' k ≫ coprod.map p₁.left p₂.left := by
  let ρ₁ : (T ⟶ E₁) →* ((Over.map j).obj T ⟶ A₁) :=
    MonoidHom.mk' (push p₁) fun x y => hm₁ x y
  let ρ₂ : (T ⟶ E₂) →* ((Over.map j).obj T ⟶ A₂) :=
    MonoidHom.mk' (push p₂) fun x y => hm₂ x y
  have pa : ∀ (z : T ⟶ E₁) {c' : E₁ ⟶ E₂} {c : A₁ ⟶ A₂}, push p₂ c' = p₁ ≫ c → push p₂ (z ≫ c') = push p₁ z ≫ c :=
    fun z c' c h => by
      simp only [push, Functor.map_comp, Category.assoc] at h ⊢
      rw [h]
  rw [← Category.assoc, mφ_comp, mφ_comp]
  rcases k with I | I
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₂ ![x ≫ a', y ≫ b'] I.down
    have e' : (fun i => ρ₂ ((![x ≫ a', y ≫ b'] : Fin 2 → (T ⟶ E₂)) i)) = ![push p₁ x ≫ a, push p₁ y ≫ b] := by
      funext i
      fin_cases i
      · exact pa x ha
      · exact pa y hb
    rw [e'] at e
    show (psum A₂ ![push p₁ x ≫ a, push p₁ y ≫ b] I.down).left ≫ coprod.inr =
      ((psum E₂ ![x ≫ a', y ≫ b'] I.down).left ≫ coprod.inr) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inr_map, ← Category.assoc]
    rfl
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₁ ![x, y] I.down
    have e' : (fun i => ρ₁ ((![x, y] : Fin 2 → (T ⟶ E₁)) i)) = ![push p₁ x, push p₁ y] := by
      funext i
      fin_cases i <;> rfl
    rw [e'] at e
    show (psum A₁ ![push p₁ x, push p₁ y] I.down).left ≫ coprod.inl =
      ((psum E₁ ![x, y] I.down).left ≫ coprod.inl) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inl_map, ← Category.assoc]
    rfl

end GlobalTheory.HomMum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierExponentNonzeroSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.MumMult

theorem exists_closedFibre_pt (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) :
    ∃ x : D.toPre.P.A.left, D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) := by
  let y : (𝟙_ (Over (Sp R))).left := (IsLocalRing.closedPoint R : PrimeSpectrum R)
  refine ⟨(η[D.toPre.P.A]).left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Over.w (η[D.toPre.P.A])]
  rfl

theorem exists_N_sec : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ GlobalTheory.MumMult.PosN D a h h' N ∧ ∃ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧ GlobalTheory.MumMult.NonzeroAt D a N σ₀ x := by
  intro R _ _ _ hR D a a' h h' hE
  have := D.toPre.P.isAb.proper
  have hP := D.toPre.P.isLB
  obtain ⟨N₀, hN₀, -, hκ⟩ := GlobalTheory.Mum.PosMult.exists_pos_mult R hR.1 D a a' h h' hE
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.Mum.PosMult.eventually_relAmple R D.toPre.P a
  have hA : IsAmpleLB D.toPre.P.L := isAmpleLB_of_relAmple_of_isAffine D.toPre.P.A hP D.toPre.P.ample
  have hNb := LB.isLB_linComb hP (K := Fin 1) ![a.left] ![1]
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (GlobalTheory.AmpleDominates.eventually_isGenerated D.toPre.P.A.hom hA hNb)
  set N := max N₀ (max N₁ N₂) with hNdef
  have hN0 : N₀ ≤ N := le_max_left _ _
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hL' := LB.isLB_linComb hP (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]
  have hG := hN₂ N hN2
  have hD := LB.isLB_div (isLB_lbPow hP N) hNb
  have hGen : IsGenerated (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) := by
    refine hG.of_lbIso hL' ((cls_eq_iff hL' hD).1 ?_)
    rw [cls_linComb hP, cls_div (isLB_lbPow hP N) hNb, cls_lbPow hP, cls_linComb hP]
    simp [Fin.sum_univ_two, GlobalTheory.CechPic.pull_id]
    abel
  refine ⟨N, le_trans hN₀ hN0, ⟨hN₁ N hN1, ?_⟩, ?_⟩
  · intro κ hs h0 hc hint hb y
    obtain ⟨r, hr⟩ := hκ κ hs h0 hc hint hb y
    obtain ⟨r', hr'⟩ := hint y
    refine ⟨r' ^ (N - N₀) * r, ?_⟩
    have hsplit : (κ y : FractionRing R) ^ N = (κ y : FractionRing R) ^ (N - N₀) * (κ y : FractionRing R) ^ N₀ := by
      rw [← pow_add, Nat.sub_add_cancel hN0]
    have hr0 : ((κ y ^ N₀ : (FractionRing R)ˣ) : FractionRing R) = (κ y : FractionRing R) ^ N₀ := Units.val_pow_eq_pow_val _ _
    rw [Units.val_pow_eq_pow_val, hsplit, ← hr0, hr, map_mul, map_pow, ← hr']
    ring
  · obtain ⟨x, hx⟩ := exists_closedFibre_pt R D
    obtain ⟨σ₀, hσ⟩ := hGen.exists_mem x
    refine ⟨σ₀, x, hx, fun j hj => ?_⟩
    exact (mem_nonzeroLocus_iff_basicOpen σ₀ hj).1 hσ

end GlobalTheory.MumMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedIotaGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam

theorem exists_iota_of_rosati {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a a' : D.P.A ⟶ D.P.A)
    [IsMonHom a] [IsMonHom a'] (hr : RosatiAdj D.P.A D.P.L a a') (α δ : D.X) (hc : D.c δ = D.c α ≫ a') :
    ∃ u : LB.Gen (IotaLB D a α δ), IsIota u := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  have cf : ∀ T, DVR.cP D T δ = DVR.cP D T α ≫ a' := fun T => by
    rw [DVR.cP, hc, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) δ) (D.Oφ a α)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (DVR.prod_neg _ _ (prod_ros a a' (𝟙 D.P.A) (DVR.cP D _ α) h)).trans (Eq.symm ?_)
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) δ h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D a α h)).trans ?_
      rw [cf, Category.id_comp, _root_.mul_comm (DVR.cP D _ α) a, _root_.mul_comm (DVR.cP D _ α ≫ a') (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _))
  refine ⟨v, hv, fun Z r z J hJ => ?_⟩
  let T : Over (Spec (CommRingCat.of R)) := Over.mk r
  have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb a a' u hu u₀ (T := T) hJ 1 1 (DVR.cP D _ α)).1
  rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := T) z J 1 (DVR.cP D _ α) = 1 := mul_eq_left.1 e.symm
  have o : (1 : T ⟶ D.P.A).left = r ≫ eSec D.P.A := rfl
  have k : (r ≫ eSec D.P.A) ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = (lift (1 : T ⟶ D.P.A) (DVR.cP D T α)).left := by
    rw [← o, ← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]
  rw [vv Z _ z J hJ, val_inv, val_pull hJ, k]
  exact inv_eq_one.2 e'

theorem exists_iota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ α : D.toPre.X, ∃ u : LB.Gen (IotaLB D.toPre a α (h' α)), IsIota u := by
  intro R _ _ _ _ D a a' h h' hE α
  obtain ⟨h₁, h₂, hr, -, hc, -⟩ := hE
  exact exists_iota_of_rosati D.toPre a a' hr α (h' α) (hc α)

end GlobalTheory.TwFam
end
end

