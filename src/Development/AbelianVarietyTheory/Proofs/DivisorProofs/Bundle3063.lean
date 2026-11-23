module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotTwistSumZeroFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourierClassSumsMemIntegralClosureGalois
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupTowerBaseChangeMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem exists_ringHom_val_of_regAt : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₂ : Setup F W i) (z : X₂.M.Z) {V : Type} [CommRing V] [IsDomain V] (ev : X₂.M.Z.presheaf.stalk z →+* V), RegAt X₂ z ev → ∃ yK : X₂.S.R →+* FractionRing V, ∀ a : X₂.S.R, yK a = X₂.M.val (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) a := by
  intro g n F W Z i X₂ z V _ _ ev hr
  have hR : X₂.S.R ≤ X₂.M.O ((jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))) :=
    fun a ha => hr a ha
  exact ⟨(RatModel.valHomOf (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) _
    (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₂.M) (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))))).comp
      (Subalgebra.inclusion hR).toRingHom, fun a => rfl⟩

theorem Tower.comp_act₂_of_comp_act : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) (y₂ : 𝔗.X₂.S.R →+* K) (φ₂ : A'.left ⟶ 𝔗.X₂.ρ.P.A.left), φ₂ ≫ 𝔗.X₂.ρ.P.A.hom = A'.hom ≫ spMap y₂ → ∀ (e : A' ⟶ A') (a : Matrix (Fin 8) (Fin 8) ℤ), e.left ≫ φ₂ ≫ 𝔗.φ = φ₂ ≫ 𝔗.φ ≫ (act a).left → e.left ≫ φ₂ = φ₂ ≫ (𝔗.act₂ a).left := by
  intro g n F W Z i X₁ act 𝔗 K _ A' y₂ φ₂ hφ e a h
  refine 𝔗.cart.1.hom_ext ?_ ?_
  · simp only [Category.assoc, 𝔗.act_eq a]
    simpa only [Category.assoc] using h
  · simp only [Category.assoc, Over.w (𝔗.act₂ a), hφ]
    rw [← Category.assoc, Over.w e]

theorem Tower.pt_iff_pt_gl : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) [GrpObj A'] (ya yb : 𝔗.X₂.S.R →+* K) (φa φb : A'.left ⟶ 𝔗.X₂.ρ.P.A.left) (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap ya) φa → IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap yb) φb → φa ≫ 𝔗.φ = φb ≫ 𝔗.φ → ya = yb.comp (𝔗.sR σ) → ∀ {L : Type} [Field L] (j : K →+* L) (x : Sp L ⟶ A'.left), x ≫ A'.hom = spMap j → ∀ a, (x ≫ φa = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ↔ x ≫ φb = spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) := by
  intro g n F W Z i X₁ act 𝔗 K _ A' _ ya yb φa φb σ ha hb hab hy L _ j x hx a
  have hc := 𝔗.cart.1
  have hsec : ∀ b, (𝔗.X₂.ρ.pt b).left ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ := fun b => Over.w (𝔗.X₂.ρ.pt b)
  have hsp : ∀ y : 𝔗.X₂.S.R →+* K, spMap j ≫ spMap y = spMap (j.comp y) := fun y => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hxa : (x ≫ φa) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, ha.1.w, ← Category.assoc, hx, hsp]
  have hxb : (x ≫ φb) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hb.1.w, ← Category.assoc, hx, hsp]
  have hra : (spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hrb : (spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hg : spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left ≫ 𝔗.φ = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ≫ 𝔗.φ := by
    rw [𝔗.gl_pt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc, ← hy]
  constructor
  · intro h1
    refine hc.hom_ext ?_ (hxb.trans hrb.symm)
    rw [Category.assoc, ← hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]
  · intro h1
    refine hc.hom_ext ?_ (hxa.trans hra.symm)
    rw [Category.assoc, hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]

end GlobalTheory.Poinc.Sep

namespace GlobalTheory

theorem exists_baseChange_member_of_tower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V'), IsCN V' → Function.Injective io → io.Finite → ∃ 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ, (∀ ev₂ h (zt : 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → (𝔪₂ ev₂ h).Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c))) ∧ ∀ ev₂ h ev₂' h' (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → ∀ a mu, (𝔪₂ ev₂' h').YY a mu ↔ (𝔪₂ ev₂ h).YY (𝔗.gl σ a) mu := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hE8 hth X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv
  obtain ⟨eps, heps⟩ := _root_.GlobalTheory.Poinc.Sep.BaseTerms.terms_baseChange X₁ act 𝔗 z₁ z₂ hz₂ x₀ hdiv
  refine ⟨eps, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab T hT V' _ _ _ io hcn hinj hfin
  have hle : nonZeroDivisors V ≤ (nonZeroDivisors V').comap io :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hinj
  let f : FractionRing V →+* FractionRing V' := IsLocalization.map (FractionRing V') io hle
  have hf : ∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v) :=
    fun v => IsLocalization.map_eq hle v
  obtain ⟨D', e₈', G', _, _, A', U', ψ, hD, bc, hsemi, hψ, hw, hbc, hPU, hxe, hgen, hE, hpsi⟩ :=
    _root_.GlobalTheory.Poinc.Sep.UMem.exists_baseChange X₁ z₁ act V ev X m t δ 𝔪 V' io f hf hcn hinj hfin
  have hreg : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → RegAt 𝔗.X₂ z₂ ev₂ :=
    fun ev₂ h => _root_.GlobalTheory.Poinc.Sep.Tower.regAt 𝔗 hz₂ ev io ev₂ hinj h 𝔪.reg
  choose yK hyK using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    exists_ringHom_val_of_regAt 𝔗.X₂ z₂ ev₂ (hreg ev₂ h)
  have hyKc : ∀ ev₂ h, (yK ev₂ h).comp 𝔗.om = f.comp 𝔪.yK := by
    intro ev₂ h
    ext a
    simp only [RingHom.comp_apply]
    rw [hyK, 𝔪.yK_eq]
    exact _root_.GlobalTheory.Poinc.Sep.Tower.val_om_ext 𝔗 hz₂ ev io ev₂ f hf hinj h 𝔪.reg a
  have hsq : ∀ ev₂ h, spMap (yK ev₂ h) ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK := by
    intro ev₂ h
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hyKc ev₂ h]
  choose φ₂ hφ₂ using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    _root_.GlobalTheory.isGrpPullback_paste X₁.ρ.P.A 𝔗.X₂.ρ.P.A 𝔪.A.A A'.A (spMap 𝔗.om) (spMap 𝔪.yK) (spMap f) (spMap (yK ev₂ h)) 𝔗.φ 𝔪.φ ψ
      𝔗.cart 𝔪.cart hψ (hsq ev₂ h)
  choose wl hwl using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    _root_.GlobalTheory.Poinc.SquareIso.iso_pull_of_square A'.L 𝔪.A.L X₁.ρ.P.L 𝔗.X₂.ρ.P.L ψ 𝔪.φ (φ₂ ev₂ h) 𝔗.φ A'.isLB 𝔪.A.isLB X₁.ρ.P.isLB 𝔗.X₂.ρ.P.isLB
      (hφ₂ ev₂ h).2.symm hw ⟨𝔪.wl, 𝔪.wl_gen⟩ 𝔗.lb
  let 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ →
      UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ := fun ev₂ h =>
    { cn := hcn
      loc := h.1
      reg := hreg ev₂ h
      yK := yK ev₂ h
      yK_eq := hyK ev₂ h
      D := D'
      e₈ := e₈'
      G := G'
      semi := hsemi
      A := A'
      U := U'
      φ := φ₂ ev₂ h
      cart := (hφ₂ ev₂ h).1
      wl := wl ev₂ h
      wl_gen := hwl ev₂ h
      equiv := fun a a' hc => by
        obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a a' hc
        obtain ⟨E', hE'1, hE'2⟩ := hE E
        refine ⟨E', ?_, fun mu => hD.xe.injective ?_⟩
        · have e2 := (hφ₂ ev₂ h).2
          refine Tower.comp_act₂_of_comp_act 𝔗 A'.A (yK ev₂ h) (φ₂ ev₂ h) (hφ₂ ev₂ h).1.1.w E'.aA a ?_
          calc E'.aA.left ≫ φ₂ ev₂ h ≫ 𝔗.φ = E'.aA.left ≫ ψ ≫ 𝔪.φ := by rw [e2]
            _ = ψ ≫ E.aA.left ≫ 𝔪.φ := by rw [← Category.assoc, hE'1, Category.assoc]
            _ = ψ ≫ 𝔪.φ ≫ (act a).left := by rw [hE1]
            _ = φ₂ ev₂ h ≫ 𝔗.φ ≫ (act a).left := by rw [← Category.assoc, ← e2, Category.assoc]
        · rw [hE'2, hxe, hE2, hxe]
      psi := hpsi }
  refine ⟨𝔪₂, ?_, ?_⟩
  · intro ev₂ h zt hzt
    exact heps V ev X m t δ 𝔪 C lab T hT V' io f hf hinj hfin ev₂ (𝔪₂ ev₂ h) ψ hD bc h (hyKc ev₂ h) hψ hw
      (hφ₂ ev₂ h).2 hbc hPU hxe hgen zt hzt
  · intro ev₂ h ev₂' h' σ h1 h2 a mu
    have hy : yK ev₂' h' = (yK ev₂ h).comp (𝔗.sR σ) := by
      ext b
      simp only [RingHom.comp_apply]
      rw [hyK, hyK]
      exact _root_.GlobalTheory.Poinc.Sep.val_galois_conj 𝔗 ev₂ ev₂' σ h1 h2 (hreg ev₂ h) (hreg ev₂' h') b
    unfold UMem.YY
    refine exists_congr fun p => exists_congr fun x => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact Tower.pt_iff_pt_gl 𝔗 A'.A (yK ev₂' h') (yK ev₂ h) (φ₂ ev₂' h') (φ₂ ev₂ h) σ (hφ₂ ev₂' h').1 (hφ₂ ev₂ h).1
      ((hφ₂ ev₂' h').2.trans (hφ₂ ev₂ h).2.symm) hy
      (algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))) x.left (Over.w x) a

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTowerThetaMemberTermsBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep.BaseTerms

theorem terms_baseChange : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite → ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ) (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre) (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK → IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → (∃ w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ), w.IsGen) → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U → (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) → 𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) → ∀ zt : 𝔗.X₂.M.Z.presheaf.stalk z₂, 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → 𝔪₂.Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c)) := by
  intro I X₁ act 𝔗 z₁ z₂ hp x₀ hdiv
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_tower_frames_pullback_constant_root X₁ act 𝔗
  set M := (𝔗.X₂.S.r * 𝔗.X₂.S.N) ^ 2 with hM
  refine ⟨fun b => k x₀ + (M - 1) * k b, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab T hT V' _ _ _ io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart hw hφ hmon hU he₈ hgen zt hzt
  obtain ⟨x, fr, th, w₀, s, g', w, h1, h2, h3, h4, h5, h6, h7⟩ := hT
  obtain ⟨wψ, hwψ⟩ := hw
  obtain ⟨x₂, fr₂, h1', h2'⟩ := GlobalTheory.T.exists_torsionPoints_transported_frames 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ 𝔪₂
  obtain ⟨c₀, hc₀⟩ := hk z₁ z₂ hp V ev X t δ 𝔪 V' io f hf ev₂ X (fun k => io (t k)) δ 𝔪₂ ψ wψ hwψ hExt hyK hcart hφ
    x fr h1 h2 x₂ fr₂ h1' h2'
  set ζ' : FractionRing V' := 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ with hζ'
  have hζM : ζ' ^ M = 1 := by
    rw [hζ', ← map_pow]
    have : (⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ : 𝔗.X₂.S.R) ^ M = 1 := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hM, 𝔗.X₂.S.prim.pow_eq_one, map_one]
    rw [this, map_one]
  have hMpos : M ≠ 0 := by
    rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := 𝔗.X₂.S.r_pos; omega) (by have := 𝔗.X₂.S.N_ge; omega))
  have hζ0 : ζ' ≠ 0 := by
    intro h0
    rw [h0, zero_pow hMpos] at hζM
    exact zero_ne_one hζM
  let ρ : X₁.S.Gam → (FractionRing V')ˣ := fun b => c₀ * (Units.mk0 ζ' hζ0) ^ k b
  have hρ : ∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b) := by
    intro b
    simpa [ρ] using hc₀ b
  obtain ⟨th₂, w₀₂, s₂, g'₂, w₂, K, h3', h4', h5', h6', hcoef, hval⟩ := GlobalTheory.T.termsWitnesses_baseChange_along_tower X₁ act 𝔗 z₁ z₂ hp x₀ hdiv V ev X t δ 𝔪 C lab
    x fr th w₀ s g' w h1 h2 h3 h4 h5 h6 V' io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart wψ hwψ hφ hmon hU he₈ hgen
    x₂ fr₂ h1' h2' ρ hρ
  refine ⟨x₂, fr₂, th₂, w₀₂, s₂, g'₂, w₂, h1', h2', h3', h4', h5', h6', ?_⟩
  intro mu c
  have hz : algebraMap V' (FractionRing V') (ev₂ zt) = ζ' := by
    haveI : IsLocalHom ev₂ := 𝔪₂.loc
    rw [← GlobalTheory.GSep.TwistModel.val_stalkHom (X₁ := 𝔗.X₂) (z₁ := z₂) (V := V') (ev := ev₂) zt, hzt, hζ', 𝔪₂.yK_eq]
  have hF0 : f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) ≠ 0 :=
    (map_ne_zero_iff f f.injective).2 (GlobalTheory.GSep.TwistModel.yK_th_ne_zero 𝔪 hdiv)
  have hρc : (ρ (lab c) : FractionRing V') ≠ 0 := (ρ (lab c)).ne_zero
  have e1 := hcoef mu c
  have e2 := hval x₀
  have e3 := h7 mu c
  have eρ : (ρ x₀ : FractionRing V') = ρ (lab c) * ζ' ^ (k x₀ + (M - 1) * k (lab c)) := by
    simp only [ρ, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [_root_.mul_assoc, ← pow_add]
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 hMpos
    have hsum : (M - 1) * k (lab c) + k (lab c) = M * k (lab c) := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hM1]
    rw [show k (lab c) + (k x₀ + (M - 1) * k (lab c)) = k x₀ + ((M - 1) * k (lab c) + k (lab c)) by ring, hsum,
      pow_add, pow_mul, hζM, one_pow, _root_.mul_one]
  have e3' : f (coef s (g' c) (w c) (𝔪.e₈ mu)) =
      algebraMap V' (FractionRing V') (io (T mu c)) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) := by
    rw [← e3, map_mul, hf]
  show algebraMap V' (FractionRing V') (ev₂ zt ^ (k x₀ + (M - 1) * k (lab c)) * io (T mu c)) *
    𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam x₀), 𝔗.X₂.S.th_mem _⟩ = coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu)
  rw [map_mul, map_pow, hz]
  apply mul_right_cancel₀ (mul_ne_zero hρc hF0)
  linear_combination (-(algebraMap V' (FractionRing V') (io (T mu c))) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) *
      𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam x₀), 𝔗.X₂.S.th_mem _⟩) * eρ +
    (algebraMap V' (FractionRing V') (io (T mu c)) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) * e2 -
    f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) * e1 - K * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) * e3'

end GlobalTheory.GSep.BaseTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorDefectPolynomialMonomialPeriods
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatDefect

theorem shiftEq_add {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {mu α : Q.X}
    {σ σ' σ'' : Q.SecB k α} {σ₁ σ₁' : Q.SecB k (α + k • mu)} {c₁ c₂ : R}
    (h0 : ShiftEq Q k mu α σ σ₁ 0 σ₁) (h1 : ShiftEq Q k mu α σ'' σ₁' c₁ σ₁)
    (h2 : ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J →
      sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom c₂) * sval σ x.left z J) :
    ShiftEq Q k mu α σ' σ₁' (c₁ + c₂) σ₁ := by
  intro u hu hc z J hJ
  have a := h1 u hu hc z J hJ
  have b := h0 u hu hc z J hJ
  have e := h2 _ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)) z J hJ
  have hz : (𝟙 (DegPre.BF Q (FractionRing R)).left) z ∈ (⊤ : (DegPre.BF Q (FractionRing R)).left.Opens) := trivial
  have g0 : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (0 : R)) = 0 := by
    rw [gs_eq _ z ⊤ hz]; simp only [Out.scal, map_zero]
  have gadd : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (c₁ + c₂)) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₁) +
        gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₂) := by
    rw [← gs_add _ z ⊤ hz]; simp only [Out.scal, map_add (f := _)]
  rw [g0, zero_mul, add_zero] at b
  rw [a, e, gadd]
  linear_combination (-(gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₂))) * b

end GlobalTheory.HeatDefect

theorem GlobalTheory.HeatDefect.defect_polynomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hm ht D hD h hb
  have hA := fun mu => _root_.GlobalTheory.HeatDefect.exists_conj_shift R Dd O oa Y n v dd hv m t gam hm ht D hD h hb mu
  choose h' w₁ π₁ π₁' hb' hΘ hu hrel using hA
  have hU := fun mu => _root_.GlobalTheory.HeatUniq.exists_affine_scalar R Dd.toPre O oa Y n v dd hv D h (h' mu) hb (hb' mu) (hΘ mu).symm (hu mu).symm
  choose ℓ π₂ π₂' hU using hU
  refine ⟨fun mu => w₁ mu + ℓ mu, fun mu => π₁ mu + π₂ mu, fun mu => π₁' mu + π₂' mu, ?_⟩
  intro k mu α σ σ' σ₁ σ₁' hk hs ht₀ ht₁
  obtain ⟨σ'', hσ'', hsh⟩ := hrel mu k α σ σ₁ σ₁' hk hs ht₁
  have key := GlobalTheory.HeatDefect.shiftEq_add hs hsh (hU mu k α σ σ' σ'' ht₀ hσ'')
  refine (congrArg (fun c => ShiftEq Dd.toPre k mu α σ' σ₁' c σ₁) ?_).mpr key
  simp only [AddMonoidHom.add_apply]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingLinearMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem weilIs_heckeSub_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) 1 := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_commutatorPairing_value_heckePoints p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂
  have hQ : (lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hA2 : IsAbelianScheme (G2 o.A) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have h1 : u = 1 := by
    refine _root_.GlobalTheory.rootOfUnity_eq_one_of_geom R S s k u (b.unit k hk)
      (_root_.GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_pow_eq_one p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ u hu) ?_
    intro K _ _ x β hx
    have hp := GlobalTheory.CommPairing.weilIs_pull (A := G2 o.A) GlobalTheory.globalFns_holds hA2 hQ (toUnit (Over.mk x)) hu
    exact GlobalTheory.T.weilPairing_heckePoints_geometric_eq_one p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ K x β hx _ hp
  subst h1
  exact hu

end GlobalTheory.UPel.HT.Hecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingPowerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSections_isotropic_commutatorPairing_power : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 g₂) 1 := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_one) | (exact GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_one) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeApprox

variable {p : ℕ} [Fact p.Prime]

abbrev fAf (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) := (D.EF.baseChange ℚ).baseChange (AfP p)

theorem isInt_one : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _
theorem isInt_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)
theorem isInt_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)
theorem isInt_sub {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a - b) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)
theorem isInt_intCast (k : ℤ) : IsIntAf (k : AfP p) := fun v => by rw [map_intCast]; exact intCast_mem _ k
theorem isInt_natCast (k : ℕ) : IsIntAf (k : AfP p) := fun v => by rw [map_natCast]; exact natCast_mem _ k

def inAfH (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D := AddMonoidHom.mk' (inAf D) (fun x y => by
  simp only [inAf, TensorProduct.tmul_add])

theorem inAf_sub (D : Datum p) (x y : D.La) : inAf D (x - y) = inAf D x - inAf D y := map_sub (inAfH D) x y
theorem inAf_add (D : Datum p) (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := map_add (inAfH D) x y
theorem inAf_nsmul (D : Datum p) (n : ℕ) (x : D.La) : inAf D (n • x) = n • inAf D x := map_nsmul (inAfH D) n x
theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isInt_one, rfl⟩

theorem form_inAf (D : Datum p) (x y : D.La) : fAf D (inAf D x) (inAf D y) = (D.EF x y : AfP p) := by
  simp [fAf, inAf, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

end GlobalTheory.HeckeApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyFiniteKillingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_cohomology_finite_killing : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ (n i : ℤ), 2 ≤ n → ∀ x : Ht q (sp (LaurentPolynomial A)) n i,
  ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Module.Finite A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
    pull _ (spMap (laurentMap (algebraMap A A'))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.GmKill.main) | (exact GlobalTheory.EtC.GmKill.main) | (intros; apply GlobalTheory.EtC.GmKill.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantsEqScalarMulRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem GlobalTheory.USep.thetaConst_eq_lam_root_mul : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro n hn hodd
  refine ⟨1, fun j hj V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth => ?_⟩
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, rfl⟩
    omega
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  obtain ⟨M, lam, hM, H⟩ := GlobalTheory.T.thetaGenerator_torsionFrame_value_eq_scalar_mul_root (n ^ j) (hodd.pow) hm3 V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hth
  refine ⟨M, lam, hM, fun y c hc => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant (Sp V₁) D.P ρ₀ hρ₀ (n ^ j) (hodd.pow) _ th y _ hc
  exact H (y ^ n ^ j) τ c (GlobalTheory.T.isTorsionFrame_sq_of_torsion _ D.P ρ₀ (n ^ j) _ (y ^ n ^ j) τ hτ) hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourierClassSumsMemIntegralClosureGaloisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFourier_classSums_mem_integralClosure_galois : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 8 → Φ.X y) → Q → PadicAlgCl p) (f : (Fin 8 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod ℤ N (k y)) ∧ Φ.IsTerms W t ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧ (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin 8 → Φ.X y), ∀ S : Finset (Fin 8 → Φ.X y), (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) → ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.Poinc.ClassCore.classSums_integralClosure | exact GlobalTheory.Poinc.ClassCore.classSums_integralClosure | (intros; apply GlobalTheory.Poinc.ClassCore.classSums_integralClosure <;> assumption)
end

