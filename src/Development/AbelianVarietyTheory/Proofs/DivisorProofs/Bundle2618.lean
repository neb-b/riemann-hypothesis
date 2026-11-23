module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiTwistedEqPsiMulCharacterOfPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwPsi

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point

variable {R : Type} [CommRing R] [IsDomain R]

theorem toUnit_left_eq {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem cancel {A : Type} [CommRing A] [IsDomain A] {S S₂ : A} {ψ rig G N W Wc W1 ψ₂ rig₂ : Aˣ} (hs : S₂ ≠ 0)
    (e : S * (ψ * rig).val * (G * N).val = (W * Wc⁻¹ * W1).val * (S₂ * (ψ₂ * rig₂).val))
    (e4 : S * N.val = W.val * S₂) : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂) := by
  refine Units.ext (mul_left_cancel₀ (mul_ne_zero W.ne_zero hs) ?_)
  simp only [Units.val_mul] at e ⊢
  linear_combination e - ((ψ : A) * G * rig) * e4

theorem core {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ))
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β g.b) twε))
    (f : ∀ α : D.X, D.SecB 1 α) (f₂ : ∀ α : D₂.X, D₂.SecB 1 α)
    (ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]))
    (h : LevelOneEq D f) (h₂ : LevelOneEq D₂ f₂)
    (hf : ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
      (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' →
      sval (f (xe χ)) (r ≫ twφ D₂ D β g.b 0) z J *
        (val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * sval (f₂ χ) r z J')
    [IsIntegral (DegPre.BF D₂ (FractionRing R)).left]
    (χ : D₂.X) (z : (DegPre.BF D₂ (FractionRing R)).left) (J : _ → D.P.L.ι) (J' : _ → D₂.P.L.ι)
    (hJ : Good D.P.L z J) (hJ' : Good D₂.P.L z J')
    (ne : sval (f₂ 0) (DegPre.prB D₂ (FractionRing R)).left z J' ≠ 0) :
    val (D.psi (xe χ)) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J *
        val (g.s (xe χ)) (toUnit (DegPre.BF D₂ (FractionRing R))).left z J *
        val D.rig (DegPre.BF D₂ (FractionRing R)).hom z J =
      (wv w (cP D₂ (DegPre.BF D₂ (FractionRing R)) χ).left z J J')⁻¹ *
        wv w (1 : DegPre.BF D₂ (FractionRing R) ⟶ D₂.P.A).left z J J' *
        (val (D₂.psi χ) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J' *
          val D₂.rig (DegPre.BF D₂ (FractionRing R)).hom z J') := by
  let T := DegPre.BF D₂ (FractionRing R)
  let κ : T ⟶ TF (R := R) (FractionRing R) := fst _ _
  let Φ : D₂.P.A ⟶ D.P.A := padd D.P.A β (toUnit D₂.P.A ≫ g.b)
  have hΦ : ∀ u : T ⟶ D₂.P.A, u ≫ Φ = (u ≫ β) * (toUnit T ≫ g.b) := fun u => by
    show u ≫ (β * (toUnit D₂.P.A ≫ g.b)) = _
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  have hU : ∀ u : T ⟶ D₂.P.A, u.left ≫ (toUnit D₂.P.A).left = (toUnit T).left := fun u => by
    rw [← Over.comp_left, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  obtain ⟨y, hy⟩ : ∃ y : T ⟶ D₂.P.A, y * cP D₂ T χ = DegPre.prB D₂ (FractionRing R) :=
    ⟨_, inv_mul_cancel_right _ _⟩
  have hyΦ : (y ≫ Φ) * cP D T (xe χ) = DegPre.prB D₂ (FractionRing R) ≫ Φ := by
    rw [hΦ, hΦ, ← hy, MonObj.mul_comp, cP_comp β (hc χ), mul_right_comm]
  have e₁ := h (xe χ) 0 rfl T κ (y ≫ Φ) z J hJ
  have e₂ := h₂ χ 0 rfl T κ y z J' hJ'
  have e₃ := hf χ _ y.left z J J' hJ hJ'
  have e₄ := hf 0 _ (DegPre.prB D₂ (FractionRing R)).left z J J' hJ hJ'
  have p₃ := prod_famB D₂ y χ (fun q => wv w q z J J')
  have p₄ := prod_famB D₂ (DegPre.prB D₂ (FractionRing R)) 0 (fun q => wv w q z J J')
  rw [hy] at p₃ e₂
  rw [cPoint_zero, _root_.mul_one, inv_mul_cancel_right] at p₄
  rw [hyΦ] at e₁
  change _ = (∏ κ, wv w (y.left ≫ D₂.famφB χ κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₃
  change _ = (∏ κ, wv w ((DegPre.prB D₂ (FractionRing R)).left ≫ D₂.famφB 0 κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₄
  rw [p₃, hU, show y.left ≫ twφ D₂ D β g.b 0 = (y ≫ Φ).left from rfl, e₁, e₂] at e₃
  rw [p₄, hU, map_zero xe, val_corr hJ g.s_zero, val_one, _root_.one_mul,
    show (DegPre.prB D₂ (FractionRing R)).left ≫ twφ D₂ D β g.b 0 = (DegPre.prB D₂ (FractionRing R) ≫ Φ).left from rfl] at e₄
  exact cancel ne e₃ e₄

theorem grp {U : Type} [CommGroup U] {ψ0 ψ₂0 rig rig₂ W1 ψ G Wc ψ₂ : U} (h0 : ψ0 = W1⁻¹ * ψ₂0)
    (c0 : ψ0 * rig = ψ₂0 * rig₂) (c : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂)) : ψ * G = Wc⁻¹ * ψ₂ := by
  subst h0
  apply Additive.ofMul.injective
  have e0 := congrArg Additive.ofMul c0
  have e := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_inv] at e0 e ⊢
  linear_combination (norm := abel) e - e0

theorem formEq {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ)) (χ : D₂.X) :
    FormEq (Sum.elim (fun _ : PUnit => ptK (D.c (xe χ)))
        (fun k => (toUnit (TK R)).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) k))
      (Sum.elim (fun _ => -1) DegPre.gtε) (fun i => D₂.xK χ ≫ twφ D₂ D β g.b i) (fun i => -1 * twε i) := by
  let u := toUnit (TK R)
  have k : ∀ a : TK R ⟶ 𝟙_ (Over (Sp R)), a = u := fun a => toUnit_unique _ _
  have m0 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 0 = D₂.xK χ ≫ twφ D₂ D β g.b 0 := by
    show u.left ≫ ((toUnit _ ≫ D.c (xe χ)) * g.b).left = (u ≫ D₂.c χ).left ≫ (β * (toUnit _ ≫ g.b)).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [MonObj.comp_mul, ← Category.assoc]
    rw [k (u ≫ toUnit _), k ((u ≫ D₂.c χ) ≫ toUnit _), Category.assoc, hc]
  have m1 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 1 = ptK (D.c (xe χ)) := by
    show u.left ≫ (toUnit _ ≫ D.c (xe χ)).left = (u ≫ D.c (xe χ)).left
    rw [← Over.comp_left, ← Category.assoc, k (u ≫ toUnit _)]
  have m2 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 2 = D₂.xK χ ≫ twφ D₂ D β g.b 1 := by
    show u.left ≫ g.b.left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ g.b).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, k ((u ≫ D₂.c χ) ≫ toUnit _)]
  have m3 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 3 = D₂.xK χ ≫ twφ D₂ D β g.b 2 := by
    show u.left ≫ (toUnit _ ≫ η[D.P.A]).left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, ← Category.assoc, k (u ≫ toUnit _),
      k ((u ≫ D₂.c χ) ≫ toUnit _)]
  intro U _ h
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, Fintype.prod_unique, Sum.elim_inl,
    Sum.elim_inr]
  rw [m0, m1, m2, m3]
  simp only [DegPre.gtε, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_succ]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

end GlobalTheory.MumCmp.TwPsi

namespace GlobalTheory.MumCmp


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point GlobalTheory.MumCmp.TwPsi in
theorem psi_maps_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₂ : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen → GlobalTheory.PsiCompare.LevelOneEq D.toPre f → GlobalTheory.PsiCompare.LevelOneEq D₂.toPre f₂ → (¬ ∀ mu j, (f₂ mu).f j = 0) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  intro R _ _ _ _ D D₂ g β hβ xe hc w hw ⟨t₀, m₀, c₀⟩ f f₂ ν _ h h₂ hne hf χ
  have hL := D.toPre.P.isLB
  have hL' := D₂.toPre.P.isLB
  have := D₂.toPre.P.isAb.smooth
  have := D₂.toPre.P.isAb.geomConnected
  have : IsIntegral (DegPre.BF D₂.toPre (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D₂.toPre.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D₂.toPre.P.A.hom).flip
  let T := DegPre.BF D₂.toPre (FractionRing R)
  let π : T.left ⟶ (TK R).left :=
    (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)
  have hπ : π ≫ jK R = T.hom := by
    rw [Category.assoc]; exact Over.w (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A)
  have hT0 : π ≫ D₂.toPre.xK 0 = (1 : T ⟶ D₂.toPre.P.A).left := by
    rw [Uniq.xK_zero, ← Category.assoc, hπ]; rfl
  have hTχ : π ≫ D₂.toPre.xK χ = (cP D₂.toPre T χ).left := by
    let k : T ⟶ TK R := Over.homMk π hπ
    exact congrArg (fun q => q.left) (comp_cP D₂.toPre k χ)
  have hTU : π ≫ (toUnit (TK R)).left = (toUnit T).left := by
    rw [toUnit_left_eq, toUnit_left_eq]; exact hπ
  have key : ∀ (z : T.left) J J', Good D.toPre.P.L z J → Good D₂.toPre.P.L z J' →
      val (D.toPre.psi (xe χ)) π z J * val (g.s (xe χ)) (π ≫ (toUnit (TK R)).left) z J =
        (wv w (π ≫ D₂.toPre.xK χ) z J J')⁻¹ * val (D₂.toPre.psi χ) π z J' := by
    intro z J J' hJ hJ'
    have ne : sval (f₂ 0) (DegPre.prB D₂.toPre (FractionRing R)).left z J' ≠ 0 := fun e => hne (h₂.eq_zero z hJ' e)
    have cχ := core g β.hom xe hc w f f₂ ν h h₂ hf χ z J J' hJ hJ' ne
    have c0 := core g β.hom xe hc w f f₂ ν h h₂ hf 0 z J J' hJ hJ' ne
    rw [map_zero xe, val_corr hJ g.s_zero, val_one, _root_.mul_one, cPoint_zero, inv_mul_cancel, _root_.one_mul] at c0
    have h0 : val (D.toPre.psi 0) π z J = (wv w (π ≫ D₂.toPre.xK 0) z J J')⁻¹ * val (D₂.toPre.psi 0) π z J' := by
      have e := Uniq.gm_mapsAtExp m₀ π z (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
        (J' (π ≫ D₂.toPre.xK 0)) (Set.mem_iInter.2 fun k => hJ _) (hJ' _)
      rw [← val_of t₀ π z J (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
          (fun k => congrArg J (Category.assoc π _ _).symm), val_corr hJ c₀, val_mul hJ, val_pull hJ,
        val_corr hJ g.s_zero, val_one, _root_.mul_one] at e
      rw [e, zpow_neg_one]; rfl
    rw [hT0] at h0
    rw [hTχ, hTU]
    exact grp h0 c0 cχ
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_gen hL (formEq g β.hom xe hc χ)
    (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))
    (mulGen_isGen _ _ _ _ _ _ _ (D.toPre.psi_gen _) (pullGen_isGen _ _ _ _ (g.isGen _) _))
  have R₁ := reg_val (L' := D₂.toPre.P.L) ht₁ π
  have R₂ := reg_wv (L := D.toPre.P.L) (L' := D₂.toPre.P.L) hw (π ≫ D₂.toPre.xK χ)
  have R₃ := (reg_val' (L := D.toPre.P.L) (D₂.toPre.psi_gen χ) π).inv
  obtain ⟨a, ha⟩ := ((R₁.mul R₂).mul R₃).glue hL hL' (fun U _ h h' => by
    simp only [Category.assoc, Fintype.prod_unique, zpow_neg_one, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv, ofMul_prod, ofMul_one]
    simp only [neg_mul, _root_.one_mul, neg_zsmul, Finset.sum_neg_distrib]
    abel)
  have ha1 : a = 1 := unit_ext fun x _ => by
    obtain ⟨J, hJ⟩ := good_exists hL x
    obtain ⟨J', hJ'⟩ := good_exists hL' x
    rw [← ha _ (𝟙 _) x J J' hJ hJ', map_one]
    show val t₁ (𝟙 _ ≫ π) x J * wv w (𝟙 _ ≫ π ≫ D₂.toPre.xK χ) x J J' * (val (D₂.toPre.psi χ) (𝟙 _ ≫ π) x J')⁻¹ = 1
    rw [Category.id_comp, Category.id_comp, hv₁ _ _ x J hJ, val_mul hJ, val_pull hJ, key x J J' hJ hJ']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have H : ∀ (y : (TK R).left) J J', Good D.toPre.P.L y J → Good D₂.toPre.P.L y J' →
      val t₁ (𝟙 _) y J = wv w (D₂.toPre.xK χ) y J J' ^ (-1 : ℤ) * val (D₂.toPre.psi χ) (𝟙 _) y J' := by
    intro y J J' hJ hJ'
    have e := ha _ (DegPre.zF D₂.toPre (FractionRing R)).left y J J' hJ hJ'
    rw [ha1, map_one] at e
    have hz : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π = 𝟙 _ := PsiCompare.zF_fst D₂.toPre
    change val t₁ ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J *
      wv w ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ) y J J' *
      (val (D₂.toPre.psi χ) ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J')⁻¹ = 1 at e
    have hz' : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ = D₂.toPre.xK χ := by
      rw [← Category.assoc (DegPre.zF D₂.toPre (FractionRing R)).left π, hz, Category.id_comp]
    rw [hz', hz] at e
    rw [zpow_neg_one, ← mul_inv_eq_one, mul_inv, inv_inv, ← _root_.mul_assoc]
    exact e
  exact ⟨t₁, mapsAtExp_of_val hL hL' hw (D₂.toPre.psi_gen χ) ht₁ H, corr_of_val hL fun y J hJ => hv₁ _ _ y J hJ⟩

end GlobalTheory.MumCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIsoBaseChangeOverReducedClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_residue_apply_eq_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (w : Sp (ResidueField R)) :
    spMap (residue R) w = closedPoint R :=
  IsLocalRing.PrimeSpectrum.comap_residue _ _

theorem pullbackLeftPullbackSnd_congr_fst {X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (g'' : W ⟶ Z)
    (hg : g' ≫ g = g'') :
    (pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hg).hom ≫ pullback.fst f g'' =
      pullback.fst _ _ ≫ pullback.fst f g := by
  subst hg
  simp [pullback.map]

theorem pullbackLeftPullbackSnd_congr_snd {X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (g'' : W ⟶ Z)
    (hg : g' ≫ g = g'') :
    (pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hg).hom ≫ pullback.snd f g'' = pullback.snd _ _ := by
  subst hg
  simp [pullback.map]

theorem Emb.pullback_iso_of_closed (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    (G' : Over S) [GrpObj G'] (hG : Smooth G'.hom) (E : Emb π G') (T : Scheme.{0}) (t : T ⟶ S)
    (k : T ⟶ Sp (ResidueField R)) (_hT : IsLocallyNoetherian T) (hTr : IsReduced T)
    (htk : t ≫ π = k ≫ spMap (residue R)) :
    ∃ (e : pullback G'.hom t ≅ pullback E.Y.hom k) (l : pullback G'.hom t ⟶ E.H.toScheme),
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ l ≫ E.H.ι = pullback.fst _ _ ∧
      l ≫ E.f = e.hom ≫ pullback.fst _ _ ≫ E.j := by
  haveI := hG
  haveI : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
  haveI : IsImmersion E.j := E.imm
  haveI : Smooth E.Y.hom := E.smooth
  have hclosed : ∀ w : (pullback G'.hom t : Scheme.{0}), π (G'.hom (pullback.fst G'.hom t w)) = closedPoint R := by
    intro w
    have h1 : π (G'.hom (pullback.fst G'.hom t w)) = (pullback.fst G'.hom t ≫ G'.hom ≫ π) w := by simp
    rw [h1, pullback.condition_assoc, htk]
    simp only [Scheme.Hom.comp_apply]
    exact spMap_residue_apply_eq_closedPoint R _
  have hrng : Set.range (pullback.fst G'.hom t) ⊆ Set.range E.H.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact E.H_all _ (hclosed w)
  let l : pullback G'.hom t ⟶ E.H.toScheme := IsOpenImmersion.lift E.H.ι (pullback.fst G'.hom t) hrng
  have hl : l ≫ E.H.ι = pullback.fst G'.hom t := IsOpenImmersion.lift_fac _ _ _
  haveI : IsReduced (pullback G'.hom t) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd G'.hom t)
  have hrj : Set.range (l ≫ E.f) ⊆ Set.range E.j := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := (_root_.GlobalTheory.Mum.Emb.range_closed R S π G' E).1 (l w) (by
      have e1 : E.H.ι (l w) = pullback.fst G'.hom t w := by rw [← Scheme.Hom.comp_apply, hl]
      rw [e1]; exact hclosed w)
    exact ⟨y, by rw [Scheme.Hom.comp_apply, hy]⟩
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.Mum.lift_immersion_of_reduced _ _ _ (l ≫ E.f) E.j inferInstance E.imm hrj
  have hgY : g ≫ E.Y.hom = pullback.snd G'.hom t ≫ k := by
    rw [← cancel_mono (spMap (residue R)), Category.assoc, ← E.j_over, reassoc_of% hg, E.f_over,
      reassoc_of% hl, pullback.condition_assoc, htk, Category.assoc]
  let h : pullback G'.hom t ⟶ pullback E.Y.hom k := pullback.lift g (pullback.snd G'.hom t) hgY
  have hh : h ≫ pullback.snd E.Y.hom k = pullback.snd G'.hom t := pullback.lift_snd _ _ _
  have hhf : h ≫ pullback.fst E.Y.hom k = g := pullback.lift_fst _ _ _
  haveI : IsIso h := by
    refine _root_.GlobalTheory.Mum.isIso_of_isIso_fibres T _ _ (pullback.snd G'.hom t) (pullback.snd E.Y.hom k) h hh inferInstance inferInstance ?_
    intro s
    let Ω := T.residueField s
    let x0 : Sp Ω ⟶ T := T.fromSpecResidueField s
    have hx : ∀ w, (x0 ≫ t ≫ π) w = closedPoint R := by
      intro w
      rw [htk]
      simp only [Scheme.Hom.comp_apply]
      exact spMap_residue_apply_eq_closedPoint R _
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x0 ≫ t ≫ π) hx
    have hκk : x0 ≫ k = spMap κ := by
      rw [← cancel_mono (spMap (residue R)), Category.assoc, ← htk, hκ]
      simp only [spMap, ← Spec.map_comp]
      rfl
    obtain ⟨Ω', _, io, e', l', -, hl1, hl2⟩ := E.fib Ω (x0 ≫ t) κ (by rw [Category.assoc]; exact hκ)
    let x : Sp Ω' ⟶ T := spMap io ≫ x0
    refine ⟨Ω', inferInstance, x, ?_, ?_⟩
    · let w : Sp Ω' := closedPoint Ω'
      refine ⟨w, ?_⟩
      show (spMap io ≫ T.fromSpecResidueField s) w = s
      rw [Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    · have hxk : x ≫ k = spMap (io.comp κ) := by
        simp only [x, Category.assoc, hκk, spMap, ← Spec.map_comp]
        rfl
      let α : pullback (pullback.snd G'.hom t) x ≅ pullback G'.hom (spMap io ≫ x0 ≫ t) :=
        pullbackLeftPullbackSndIso G'.hom t x ≪≫ pullback.congrHom rfl (Category.assoc _ _ _)
      let β : pullback (pullback.snd E.Y.hom k) x ≅ pullback E.Y.hom (spMap (io.comp κ)) :=
        pullbackLeftPullbackSndIso E.Y.hom k x ≪≫ pullback.congrHom rfl hxk
      have hα : α.hom ≫ pullback.fst G'.hom (spMap io ≫ x0 ≫ t) =
          pullback.fst (pullback.snd G'.hom t) x ≫ pullback.fst G'.hom t :=
        pullbackLeftPullbackSnd_congr_fst _ _ _ _ _
      have hαs : α.hom ≫ pullback.snd G'.hom (spMap io ≫ x0 ≫ t) = pullback.snd (pullback.snd G'.hom t) x :=
        pullbackLeftPullbackSnd_congr_snd _ _ _ _ _
      have hβ : β.hom ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) =
          pullback.fst (pullback.snd E.Y.hom k) x ≫ pullback.fst E.Y.hom k :=
        pullbackLeftPullbackSnd_congr_fst _ _ _ _ _
      have hβs : β.hom ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd (pullback.snd E.Y.hom k) x :=
        pullbackLeftPullbackSnd_congr_snd _ _ _ _ _
      have hll : pullback.fst (pullback.snd G'.hom t) x ≫ l = α.hom ≫ l' := by
        rw [← cancel_mono E.H.ι, Category.assoc, Category.assoc, hl, hl1, hα]
      have he's : e'.hom.left ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd G'.hom (spMap io ≫ x0 ≫ t) :=
        Over.w e'.hom
      let eb := α ≪≫ (Over.forget _).mapIso e' ≪≫ β.symm
      have key0 : ∀ φ : pullback (pullback.snd G'.hom t) x ⟶ pullback (pullback.snd E.Y.hom k) x,
          φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ h → φ ≫ pullback.snd _ _ = pullback.snd _ _ → φ = eb.hom := by
        intro φ hφ hφs
        have heb : eb.hom = α.hom ≫ e'.hom.left ≫ β.inv := rfl
        rw [heb, ← Category.assoc, Iso.eq_comp_inv]
        apply pullback.hom_ext
        · rw [← cancel_mono E.j, Category.assoc, Category.assoc, reassoc_of% hβ, Category.assoc, Category.assoc,
            ← hl2, ← reassoc_of% hll, reassoc_of% hφ, reassoc_of% hhf, hg]
        · rw [Category.assoc, Category.assoc, hβs, he's, hαs, hφs]
      rw [key0 (pullback.map _ x _ x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _))]
      infer_instance
  exact ⟨asIso h, l, hh, hl, by rw [asIso_hom, reassoc_of% hhf, hg]⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegBaseChange

open GlobalTheory.CechPic

theorem spMap_subtype_comp_inclusion {R : Type} [CommRing R] {R₁ R₂ : Subring R} (h : R₁ ≤ R₂) :
    spMap R₂.subtype ≫ spMap (Subring.inclusion h) = spMap R₁.subtype := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem pullbackTriple_of_le : ∀ (R : Type) [CommRing R] (R₁ R₂ : Subring R) (h : R₁ ≤ R₂) (g M : ℕ) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std g M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), IsAbelianScheme A₁ → SmoothOfRelativeDimension g A₁.hom → P.IsLB → P₁.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → ∃ (A₂ : Over (Sp R₂)) (_ : GrpObj A₂) (lv₂ : Std g M → (𝟙_ (Over (Sp R₂)) ⟶ A₂)) (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₂ ∧ SmoothOfRelativeDimension g A₂.hom ∧ IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π ∧ Geo.Tor.IsSquare π π₂ ∧ IsPullbackTriple A P lv A₂ (P₁.pull π₂) lv₂ (spMap R₂.subtype) := by
  intro R _ R₁ R₂ h g M A _ P lv A₁ _ P₁ lv₁ hab hsm hP hP₁ H
  haveI := hab.comm
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := H
  have e := spMap_subtype_comp_inclusion h
  have pb₂ := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) A₁
  have sq₂ := Pdiv.PullbackComparison.isSquare (spMap (Subring.inclusion h)) A₁
  have hw : φ ≫ A₁.hom = (A.hom ≫ spMap R₂.subtype) ≫ spMap (Subring.inclusion h) := by
    rw [hφ.1.w, Category.assoc, e]
  let ψ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).left := pb₂.1.lift φ _ hw
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) A₁ = φ := pb₂.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).hom = A.hom ≫ spMap R₂.subtype :=
    pb₂.1.lift_snd _ _ _
  have hψ : IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₁) (spMap R₂.subtype) ψ :=
    pb₂.cancel (by rw [hψ₁, e]; exact hφ) hψ₂
  obtain ⟨ψ₂, sqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  have hc : ψ₂ ≫ Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁ = φ₂ :=
    GlobalTheory.SiegDesc.isSquare_comp hψ₁ sqψ sq₂ ⟨s₁, s₂⟩
  refine ⟨(Over.pullback (spMap (Subring.inclusion h))).obj A₁, inferInstance,
    fun a => GlobalTheory.SiegelPull.secPull pb₂ (lv₁ a), Pdiv.PullbackComparison.pφ _ A₁, Pdiv.PullbackComparison.pφ₂ _ A₁, ?_, ?_, pb₂, sq₂,
    ψ, ψ₂, hψ, sqψ.1, sqψ.2, ?_, fun a => ?_⟩
  · exact
      { comm := inferInstance
        smooth := by have := hab.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := hab.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := hab.geomConnected
          show GeometricallyConnected (pullback.snd _ _); infer_instance }
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback pb₂.1 hsm
  · have hP₂ := pull_isLB hP₁ (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁)
    refine (cls_eq_iff hP (pull_isLB hP₂ ψ₂)).1 ?_
    rw [(cls_eq_iff hP (pull_isLB hP₁ φ₂)).2 iso, cls_pull hP₂ ψ₂, cls_pull hP₁ _ hP₂, ← pull_comp, hc]
    rfl
  · apply pb₂.1.hom_ext
    · rw [Category.assoc, hψ₁, hl a, Category.assoc, GlobalTheory.SiegelPull.secPull_left, ← Category.assoc, e]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (lv a), Category.assoc, Over.w]
      rfl

end GlobalTheory.SiegBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijective
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Conj.FamBij

open GlobalTheory.FieldBaseChange

variable {R : Type} [CommRing R] [IsDomain R]

def famMapTw (D : DegPre R) (σ : Kb R →ₐ[FractionRing R] Kb R) : DegPre.BF D (Kb R) ⟶ DegPre.BF D (Kb R) :=
  (famMap D (Kb R) (TwF σ) : DegPre.BF D (TwF σ) ⟶ DegPre.BF D (Kb R))

theorem famMapTw_eq (D : DegPre R) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    famMapTw D σ = lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF σ) (snd (TF (R := R) (Kb R)) D.P.A) := rfl

theorem twF_comp_eq_id {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x) :
    twF τ ≫ twF σ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap τ.toRingHom ≫ spMap σ.toRingHom = 𝟙 _
  have e : τ.toRingHom.comp σ.toRingHom = RingHom.id _ := RingHom.ext h
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id]

theorem famMapTw_comp_eq_id (D : DegPre R) {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x) :
    famMapTw D τ ≫ famMapTw D σ = 𝟙 _ := by
  have : lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF τ) (snd (TF (R := R) (Kb R)) D.P.A) ≫
      lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF σ) (snd (TF (R := R) (Kb R)) D.P.A) = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst_assoc, Category.assoc, twF_comp_eq_id h, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  exact this

theorem sval_famTw (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s : Fam D (Kb R) N) (α : D.X)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D (Kb R)).left) {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) :
    sval ((famTw D N σ s).s α) r z J = sval (s.s α) (r ≫ (famMapTw D σ).left) z J :=
  sval_pullOver (isPullback_famMap D (Kb R) (TwF σ)).w (famφ_famMap D (Kb R) (TwF σ) α) (s.s α) r hJ

theorem famTw_famTw_eq (D : DegPre R) (N : ℕ) {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x)
    (s : Fam D (Kb R) N) : famTw D N τ (famTw D N σ s) = s := by
  refine ReciprocityTheory.ChartRestriction.G.DVR.fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) ?_
  refine sec_ext' D.P.isLB fun y J hJ => ?_
  rw [sval_famTw D N τ _ α _ hJ, sval_famTw D N σ _ α _ hJ, Category.assoc, ← Over.comp_left,
    famMapTw_comp_eq_id D h, Over.id_left, Category.comp_id]

theorem famTw_bijective (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) : Function.Bijective (famTw D N σ) := by
  let e : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  refine Function.bijective_iff_has_inverse.2 ⟨famTw D N (e.symm : Kb R →ₐ[FractionRing R] Kb R), ?_, ?_⟩
  · exact famTw_famTw_eq D N fun x => e.symm_apply_apply x
  · exact famTw_famTw_eq D N fun x => e.apply_symm_apply x

end GlobalTheory.Mum.Conj.FamBij
end
end

