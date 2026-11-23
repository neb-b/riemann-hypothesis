module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdTw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A)
  (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)

theorem prod_tw {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (x.left ≫ twφ D₀ D β b i) ^ twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have hu : x ≫ toUnit D₀.P.A = toUnit T := toUnit_unique _ _
  rw [Fin.prod_univ_three]
  show h (x ≫ (β * (toUnit D₀.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₀.P.A ≫ b).left ^ (-1 : ℤ) *
    h (x ≫ toUnit D₀.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
  rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
  rfl

theorem lift_β {T : Over (Sp R)} (p q : T ⟶ D₀.P.A) :
    (lift p q).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left =
      (lift (p ≫ β) (q ≫ β)).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]

variable {D₀ D β b} [IsMonHom β]

theorem wv_mul {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D.P.A D.P.L).pull
      (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left)} (hΛ : wΛ.IsGen)
    {T : Over (Sp R)} (x y : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w (x * y).left z J J' * wv w (1 : T ⟶ D₀.P.A).left z J J' *
        lamVal wΛ (lift (1 : T ⟶ D₀.P.A) (1 : T ⟶ D₀.P.A)).left z J J' =
      wv w x.left z J J' * wv w y.left z J J' * lamVal wΛ (lift x y).left z J J' *
        cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⊗ B₀ ⟶ B₀ := fst B₀ B₀
  let s : B₀ ⊗ B₀ ⟶ B₀ := snd B₀ B₀
  have H := (((((reg_wv hw (f * s).left).mul (reg_wv hw f.left).inv).mul (reg_wv hw s.left).inv).mul
    (reg_wv hw (1 : B₀ ⊗ B₀ ⟶ B₀).left)).mul (reg_lam hΛ (lift f s).left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left).inv
  have ev : ∀ x y : T ⟶ B₀,
      wv w ((lift x y).left ≫ (f * s).left) z J J' * (wv w ((lift x y).left ≫ f.left) z J J')⁻¹ *
        (wv w ((lift x y).left ≫ s.left) z J J')⁻¹ * wv w ((lift x y).left ≫ (1 : B₀ ⊗ B₀ ⟶ B₀).left) z J J' *
        (lamVal wΛ ((lift x y).left ≫ (lift f s).left) z J J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          ((lift x y).left ≫ (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left) z J)⁻¹ =
      wv w (x * y).left z J J' * (wv w x.left z J J')⁻¹ * (wv w y.left z J J')⁻¹ *
        wv w (1 : T ⟶ B₀).left z J J' * (lamVal wΛ (lift x y).left z J J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b))⁻¹ := fun x y => by
    have hu : lift x y ≫ toUnit (B₀ ⊗ B₀) = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [MonObj.comp_mul, MonObj.comp_one, comp_lift, comp_lift, comp_lift, ← Category.assoc (lift x y) (toUnit _), hu,
      lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, prod_tw, prod_tw, lift_β, prod_lam, prod_lam]
      erw [prod_cub (G := D.P.A) (f ≫ β) (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b) h]
      rw [MonObj.mul_comp, MonObj.one_comp,
        _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    ((snd B₀ B₀).left ≫ B₀.hom) (surj_comp (surj_snd hG D₀.P.isAb _) (hG _ _ D₀.P.isAb).2)
    (lift x y).left (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left (by
      rw [Over.w, Over.w, Over.w]) z hJ hJ'
  have E' := (ev x y).symm.trans (E.trans (ev 1 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, _root_.mul_one (1 : T ⟶ B₀)] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

theorem wv_inv (hb : padd D.P.A b b = η[D.P.A]) {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) =
      wv w (x⁻¹).left z J J' * val D₀.sym x.left z J' * cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⟶ B₀ := 𝟙 B₀
  have hbb : (toUnit B₀ ≫ b) * (toUnit B₀ ≫ b) = 1 := by
    rw [← MonObj.comp_mul]; exact congrArg (toUnit B₀ ≫ ·) hb
  have H := (((((reg_wv hw f.left).mul (reg_val (L' := D₀.P.L) D.sym_gen (f ≫ β).left)).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left)).mul (reg_wv hw (f⁻¹).left).inv).mul
      (reg_val' (L := D.P.L) D₀.sym_gen f.left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left).inv
  have ev : ∀ x : T ⟶ B₀,
      wv w (x.left ≫ f.left) z J J' * val D.sym (x.left ≫ (f ≫ β).left) z J *
        val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left) z J *
        (wv w (x.left ≫ (f⁻¹).left) z J J')⁻¹ * (val D₀.sym (x.left ≫ f.left) z J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left) z J)⁻¹ =
      wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) *
        (wv w (x⁻¹).left z J J')⁻¹ * (val D₀.sym x.left z J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b))⁻¹ := fun x => by
    have hu : x ≫ toUnit B₀ = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [comp_lift, comp_lift, comp_lift, comp_lift, ← Category.assoc x (toUnit _), hu, GrpObj.comp_inv, GrpObj.comp_inv,
      ← Category.assoc x f, Category.comp_id]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, GlobalTheory.GaugeValues.prod_sym, GlobalTheory.GaugeValues.prod_sym]
      erw [prod_cub (G := D.P.A) (f ≫ β) (toUnit B₀ ≫ b) (toUnit B₀ ≫ b) h,
        prod_cub (G := D.P.A) (f ≫ β) (f ≫ β)⁻¹ (toUnit B₀ ≫ b) h]
      rw [GrpObj.inv_comp,
        _root_.mul_assoc (f ≫ β), hbb, _root_.mul_one (f ≫ β), mul_inv_cancel (f ≫ β), _root_.one_mul (toUnit B₀ ≫ b)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    B₀.hom (hG _ _ D₀.P.isAb).2 x.left (1 : T ⟶ B₀).left (by rw [Over.w, Over.w]) z hJ hJ'
  have E' := (ev x).symm.trans (E.trans (ev 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, (isCub_cubV D.cub hJ).face, inv_one,
    GlobalTheory.GaugeValues.val_sym_one D hJ, GlobalTheory.GaugeValues.val_sym_one D₀ hJ'] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

end GlobalTheory.MumCmp.Point
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaArithmeticCurveRationalFunction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveProd

theorem product_formula_curve : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ f : Y.functionField, f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal f y‖ := by
  intro k _ Y _ _ q hq f hf
  obtain ⟨hAff, hFin⟩ := _root_.GlobalTheory.ArithCurve.isAffine_and_finite k Y q hq
  have := hAff
  have := hFin
  have : Module.Finite ℤ k := hq.finite
  have hgen : genericPoint Y ∈ (⊤ : Y.Opens) := trivial
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : CharZero Γ(Y, ⊤) := (flat_int_iff_charZero (q ≫ spMap (Int.castRingHom k))).1 hq.flat
  have : IsFractionRing Γ(Y, ⊤) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y ⊤ (isAffineOpen_top Y)

  have finHom : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], Finite (B →+* ℂ) := by
    intro B _ _
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
    have hint : ∀ x : B, IsIntegral ℤ x := fun x => Algebra.IsIntegral.isIntegral x
    choose p hpm hp using hint
    let T : Set (s → ℂ) :=
      Set.pi Set.univ fun x => {z : ℂ | ((p x).map (Int.castRingHom ℂ)).IsRoot z}
    have hT : T.Finite :=
      Set.Finite.pi fun x => Polynomial.finite_setOfPred_isRoot ((hpm x).map _).ne_zero
    have hmem : ∀ φ : B →+* ℂ, (fun x : s => φ x) ∈ T := by
      intro φ x _
      show Polynomial.eval (φ (x : B)) ((p x).map (Int.castRingHom ℂ)) = 0
      rw [Polynomial.eval_map]
      rw [← show φ.comp (algebraMap ℤ B) = Int.castRingHom ℂ from RingHom.ext_int _ _,
        ← Polynomial.hom_eval₂, hp x, map_zero]
    let F : (B →+* ℂ) → T := fun φ => ⟨fun x => φ x, hmem φ⟩
    have hF : Function.Injective F := by
      intro φ ψ h
      have h' : Set.EqOn φ.toAddMonoidHom.toIntLinearMap ψ.toAddMonoidHom.toIntLinearMap (s : Set B) := by
        intro x hx
        have := congrArg (fun t : T => t.1 ⟨x, hx⟩) h
        simpa [F] using this
      have hl := LinearMap.ext_on hs h'
      ext x
      exact LinearMap.congr_fun hl x
    have : Finite T := hT.to_subtype
    exact Finite.of_injective F hF

  have finZero : ∀ c : Γ(Y, ⊤), Finite (Γ(Y, ⊤) ⧸ Ideal.span {c}) →
      {z : Y | z ∉ Y.basicOpen c}.Finite := by
    intro c _
    have hS : (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {c})))).Finite :=
      Set.finite_range _
    refine (hS.preimage fun _ _ _ _ h => Y.toSpecΓ.isOpenEmbedding.injective h).subset ?_
    intro z hz
    have h1 : Y.toSpecΓ z ∉ PrimeSpectrum.basicOpen c := by
      intro h
      apply hz
      rw [← Scheme.toSpecΓ_preimage_basicOpen]
      exact h
    show Y.toSpecΓ z ∈ Set.range _
    apply (Set.ext_iff.1 (range_comap_of_surjective _ (Ideal.Quotient.mk (Ideal.span {c}))
      Ideal.Quotient.mk_surjective) _).2
    have h2 : c ∈ (Y.toSpecΓ z).asIdeal := by
      by_contra h
      exact h1 h
    rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff.2 h2

  have hgb : ∀ c : Γ(Y, ⊤), c ≠ 0 → genericPoint Y ∈ Y.basicOpen c := by
    intro c hc
    by_contra h
    apply hc
    rw [← basicOpen_eq_bot_iff (X := Y) (U := ⊤) c, ← TopologicalSpace.Opens.not_nonempty_iff_eq_bot]
    rintro ⟨x, hx⟩
    exact h (gen_mem hx)

  have hsupp : ∀ c : Γ(Y, ⊤), c ≠ 0 → (Function.support fun z =>
      (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
        Real.log (Nat.card (Y.residueField z))).Finite := by
    intro c hc
    refine (finZero c (_root_.GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm Γ(Y, ⊤) c hc).1).subset ?_
    intro z hz hzc
    apply hz
    have hu : UnitAt z (algebraMap Γ(Y, ⊤) Y.functionField c) :=
      (unitAt_fnOf_iff (U := ⊤) trivial hgen c).2 hzc
    simp only
    rw [hu.ord_eq_zero]
    simp

  have key : ∀ c : Γ(Y, ⊤), c ≠ 0 →
      ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) =
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField c) y‖ := by
    intro c hc
    obtain ⟨hfq, hlog⟩ := _root_.GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm Γ(Y, ⊤) c hc
    have := hfq
    rw [_root_.GlobalTheory.AffineCurveSum.finsum_ord_eq k Y q hq c hc, ← _root_.GlobalTheory.CardLength.log_card_eq_finsum_length Γ(Y, ⊤) (Γ(Y, ⊤) ⧸ Ideal.span {c}), hlog,
      _root_.GlobalTheory.AffCurveSum.main k Y q hq c]

  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective Γ(Y, ⊤) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hf
  have hinj := IsFractionRing.injective Γ(Y, ⊤) Y.functionField
  have ha'0 : algebraMap Γ(Y, ⊤) Y.functionField a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
  have hb'0 : algebraMap Γ(Y, ⊤) Y.functionField b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have hord : ∀ z, Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z =
        Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z -
          Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z := by
    intro z
    have h := Scheme.ord_mul (x := z) (div_ne_zero ha'0 hb'0) hb'0
    rw [div_mul_cancel₀ _ hb'0] at h
    omega

  have hpt : ∀ (σ : k →+* ℂ) (y : CxPts q σ),
      Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
        Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖ -
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    intro σ y
    have hg : under y = genericPoint Y := GlobalTheory.TwistTop.under_eq_genericPoint hq y
    have hua : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen a).2 (hgb a ha0)
    have hub : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen b).2 (hgb b hb0)
    have huq : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [div_eq_mul_inv]
      exact hua.mul hub.inv
    have hm : ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y =
        ratVal (algebraMap Γ(Y, ⊤) Y.functionField a / algebraMap Γ(Y, ⊤) Y.functionField b) y *
          ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y := by
      rw [← ratVal_mul huq.regAt hub.regAt, div_mul_cancel₀ _ hb'0]
    rw [hm, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero huq))
      (norm_ne_zero_iff.2 (ratVal_ne_zero hub))]
    ring
  have hL : ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) =
      (∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z : ℝ) *
          Real.log (Nat.card (Y.residueField z))) -
        ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) := by
    rw [← finsum_sub_distrib (hsupp a ha0) (hsupp b hb0)]
    refine finsum_congr fun z => ?_
    rw [hord z]
    push_cast
    ring
  have hR : ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
      (∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖) -
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    have : Finite (k →+* ℂ) := finHom k
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    refine finsum_congr fun σ => ?_
    have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finsum_congr fun y => hpt σ y
  rw [hL, hR, key a ha0, key b hb0]

end GlobalTheory.CurveProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartCoordinateRatioMemModelRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ChartDiv

theorem chart_ratio_mem_O : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (a : Fin (n + 1)) (z : M.Z), PCrd (M.pt ≫ h) c → z ∈ h ⁻¹ᵁ chart k n a → c a ≠ 0 ∧ ∀ z' ∈ h ⁻¹ᵁ chart k n a, ∀ b, c b / c a ∈ M.O z' := by
  intro k Ω _ _ _ M n c h a z hc hz
  have hx : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ chart k n a := M.top_le_preimage_pt (U := h ⁻¹ᵁ chart k n a) ⟨z, hz⟩
  obtain ⟨ha, hb⟩ := GlobalTheory.UMin.CrdChart.pCrd_chart k Ω n (M.pt ≫ h) c a hc hx
  refine ⟨ha, fun z' hz' b => ?_⟩
  rw [← hb b, Points.valR_comp, ← Points.valF_eq_valR]
  exact RatModel.valF_mem_O hz' _

end GlobalTheory.UMin.ChartDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGramFlagCellFrame
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pullGram_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ z : CxPts Y.str σ, InCell E E' φ f A u (under z) → pullGram E H φ f hf (upM u * A.map φ) z = fun τ => upM (fun j => ratVal (u j) z) τ * H A (ptMap σ f hf z) τ * (upM (fun j => ratVal (u j) z) τ)ᴴ := by
  intro F _ σ X Y ι _ m E E' φ f hf hR _c A u H hH z hz
  obtain ⟨hA, hB⟩ := hz
  funext τ
  rw [(_root_.GlobalTheory.ChernCalc.pullGram_eq_of_frame F σ X Y ι m E E' φ f hf hR H hH z).2 A hA _ hB τ]
  have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := fun τ => by
    change ((A τ).map φ).det ≠ 0
    have := RingHom.map_det (φ : X.Fn →+* Y.Fn) (A τ)
    rw [RingHom.mapMatrix_apply] at this
    change ((A τ).map (φ : X.Fn →+* Y.Fn)).det ≠ 0
    rw [← this]
    exact (map_ne_zero _).2 (Fr.det_ne hA τ)
  have e : upM u * A.map φ * (A.map φ)⁻¹ = upM u := by rw [mul_assoc, Mat.mul_inv hd, mul_one]
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) z
  have h0 : ratVal (0 : Y.Fn) z = 0 := by simpa using hψ 0
  have h1 : ratVal (1 : Y.Fn) z = 1 := by simpa using hψ 1
  have hv : (upM u).map (ratVal · z) τ = upM (fun j => ratVal (u j) z) τ := by
    ext a b
    simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [h0, h1]
  rw [e, hv]

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackAevalEvenComplexForms
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem GlobalTheory.FlagCell2.pull_aeval_even : ∀ (n n' : ℕ) (L : V n →L[ℂ] V n') (κ : Type) (w : κ → Ev n) (w' : κ → Ev n') (P : MvPolynomial κ ℂ), (∀ x, (w x : Alt n) = pull L (w' x : Alt n')) → ((aeval w P : Ev n) : Alt n) = pull L ((aeval w' P : Ev n') : Alt n') := by
  intro n n' L κ w w' P h
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C]
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, AlgHom.commutes]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), Subalgebra.coe_add, Subalgebra.coe_add, map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Subalgebra.coe_mul,
      Subalgebra.coe_mul, map_mul, hp, h i]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompLinear
section
open GlobalTheory GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem pull_comp_linear : ∀ (n n' n'' : ℕ) (L : V n →L[ℂ] V n') (L' : V n' →L[ℂ] V n'') (α : Alt n''),
    pull (L'.comp L) α = pull L (pull L' α) :=
  fun n n' n'' L L' α => GlobalTheory.CxForm.pull_comp n'' n' n L L' α

end GlobalTheory.FlagCell2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistChartAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj

theorem famTw_add_f : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s s' s'' : Fam D (Kb R) N), (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) → ∀ α j, ((famTw D N σ s'').s α).f j = ((famTw D N σ s).s α).f j + ((famTw D N σ s').s α).f j := by
  intro R _ _ D N σ s s' s'' h α j
  have e : s'' = s + s' := ReciprocityTheory.ChartRestriction.G.DVR.fam_ext fun α j => (h α j).trans (ReciprocityTheory.ChartRestriction.G.DVR.add_f s s' α j).symm
  subst e
  show ((GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N (s + s') :
    Fam D (TwF σ) N).s α).f j = _
  rw [map_add (f := _)]
  rfl

end GlobalTheory.Mum.Conj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedGaloisLinearisationCarriesRigidificatiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedGaloisLinearisation_carries_rigidification_cube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PMaps (Classical.choose hP.lg) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) ∧ ∀ hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))), PMaps (Classical.choose hP.lg) (thφ G' (x3 G')) (thφ G' (x3 G')) thε U'.cubG.t U'.cubG.t (cubeMapOf hc).F3 := by
  first | exact @GlobalTheory.Mum.rigidified_galois_lin_carries_rig_and_cube | exact GlobalTheory.Mum.rigidified_galois_lin_carries_rig_and_cube | (intros; apply GlobalTheory.Mum.rigidified_galois_lin_carries_rig_and_cube <;> assumption)
end

