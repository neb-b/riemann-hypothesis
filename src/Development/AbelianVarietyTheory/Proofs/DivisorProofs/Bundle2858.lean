module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceDefiniteFormEqSumConjClasses
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDoublingPairDataIdentityCartan
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

open scoped Matrix ComplexOrder

namespace GlobalTheory.NormRatio

theorem gramAt_eq_one_of_gram {D : D7} (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold Formalism.BasicNotions.TH.gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem sig_snd_eq_zero_of_gram {D : D7} {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  by_contra hq
  let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
  have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
  simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
    Complex.one_re] at hk
  have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
    rw [Matrix.mul_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun l _ => by
      rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
  linarith

theorem exists_ipPair_one : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  intro D cc δ t0 Q P X hX h1 h2
  obtain ⟨hF, hW⟩ := hX
  have gA := gramAt_eq_one_of_gram X.A hF.gramA
  have gB := gramAt_eq_one_of_gram X.B hF.gramB
  have hI : ∀ k : ℕ, IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := fun k =>
    ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hA : X.A.SigOK := hF.defA.1
  have hq := sig_snd_eq_zero_of_gram hF.gramA hA
  obtain ⟨cA, hc⟩ := GlobalTheory.Cusp.exists_isCartanFrame X.A hA
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D X.B.rank X.A.rank
  have hone : ∀ τ, compAt X.θ τ (1 : GL (Fin X.A.rank) (AE D)).1 = 1 := fun τ => by
    exact Matrix.map_one ((X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have rA := X.rkA
  have rB := X.rkB
  refine ⟨cA, 1, ν, 𝓕, ⟨by omega, by omega, by omega, hW.inf, hA, hc, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩,
    (GlobalTheory.Doubling.isMaj_iff hW.inf).2 fun τ => ⟨fun _ => true, ?_⟩, fun τ => ?_, hW.weil, hν⟩
  · rw [gA]; exact hI _
  · rw [gB]; exact hI _
  · have hJ : Formalism.UG.Jpq (X.A.sig (tauE D τ)).1 (X.A.sig (tauE D τ)).2 = 1 := by
      have : IsEmpty (Fin (X.A.sig (tauE D τ)).2) := by rw [hq]; infer_instance
      rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
      congr 1
      exact Subsingleton.elim _ _
    rw [hJ]; simp
  · rw [hone, gA]; simp
  · rw [hone, gA]; simp

end GlobalTheory.NormRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTermsTorusTranslate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep.TermsExt
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

theorem exists_frAt_ratio {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {K : Type} [Field K] [Algebra (FractionRing R) K] {x : TFK (R := R) K ⟶ A.A} {e e' : FrAt x} (he : e.IsGen)
    (he' : e'.IsGen) : ∃ c : K, c ≠ 0 ∧ ∀ z J, Good A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := R) K).left.presheaf.stalk z) (cstH (R := R) z c) * (val e (𝟙 _) z J).val := by
  classical
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := K)
  obtain ⟨J₀, hJ₀⟩ := exists_good' A.isLB (z₀ : (TFK (R := R) K).left)
  set u := val e' (𝟙 _) z₀ J₀ * (val e (𝟙 _) z₀ J₀)⁻¹ with hu
  obtain ⟨c, hc⟩ := cstH_surj (R := R) z₀ u.val
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hc
    have h1 : (1 : (TF (R := R) K).left.presheaf.stalk z₀) = 0 := by
      rw [← u.val_inv, ← hc, zero_mul]
    have := cstH_inj (R := R) z₀ (show cstH (R := R) z₀ 1 = cstH (R := R) z₀ 0 by rw [map_one, map_zero]; exact h1)
    exact one_ne_zero this
  · intro z J hJ
    obtain rfl := pt_eq (R := R) (F := K) z z₀
    have h1 := val_tr he' (𝟙 _) hJ hJ₀
    have h2 := val_tr he (𝟙 _) hJ hJ₀
    have hcomm : ∀ (y : (TFK (R := R) K).left) (P a b : ((TFK (R := R) K).left.presheaf.stalk y)ˣ),
        P * a = a * b⁻¹ * (P * b) := by
      intro y P a b
      rw [_root_.mul_comm P b, ← _root_.mul_assoc, inv_mul_cancel_right, _root_.mul_comm]
    have key : val e' (𝟙 _) z J = u * val e (𝟙 _) z J := by
      rw [h1, h2, hu]
      exact hcomm _ _ _ _
    show _ = cstH (R := R) z c * _
    rw [key, Units.val_mul, hc]

theorem over_scale {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) {w₀ : W0 𝔪.U.toUnifPre} {g' : GtPtF 𝔪.D.toPre (FractionRing V)}
    {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b} (hw : w.IsGen) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {e e' : FrAt x} {c : FractionRing V} (hc : c ≠ 0)
    (he : ∀ z J, Good 𝔪.A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) * (val e (𝟙 _) z J).val)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w' (𝟙 _) z J).val = cst (FractionRing V) z c⁻¹ * (val w (𝟙 _) z J).val)
    (h : 𝔪.Over' w₀ g' w x e) : 𝔪.Over' w₀ g' w' x e' := by
  intro k hk wk' hwk' hgen s s' v hexp hval
  obtain ⟨wk, hwkgen, hwk⟩ := GlobalTheory.UT.TorsionValue.exists_frm_pow w hw k
  have hv' : ValAt s x e (c ^ k * v) := by
    intro z J hJ
    rw [hval z J hJ, GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, zpow_natCast, zpow_natCast,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    simp only [id, cst_eq, map_mul, map_pow]
    ring
  have hsum := h k hk wk hwk hwkgen s s' (c ^ k * v) hexp hv'
  have hscale : ∀ j, coef s' g' wk' j = c⁻¹ ^ k * coef s' g' wk j := by
    intro j
    refine GlobalTheory.UT.TorsionValue.coef_scale hwkgen (fun z J hJ => ?_) s' j
    rw [hwk' z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ]
    simp only [cst_eq, map_pow, mul_pow]
  have := sumF_const_mul (c⁻¹ ^ k) hsum
  have hcv : c⁻¹ ^ k * (c ^ k * v) = v := by
    rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, _root_.one_mul]
  rw [hcv] at this
  have hf : coef s' g' wk' = fun j => c⁻¹ ^ k * coef s' g' wk j := funext hscale
  rw [hf]
  exact this


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_terms_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : (Fin 8 → X) → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  intro g n F W Z i X₁ z₁ act x₀ _ V _ _ _ ev X _ m t δ 𝔪 C lab _ T hT c τ hτ
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hexp, hg', hTc⟩ := hT
  obtain ⟨χ, hχ1, hχ⟩ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  obtain ⟨p₀, hp₀y, hg₀⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor 𝔪.D.3 χ hχ1
  obtain ⟨p, xτ, hpy, hpg, hpq, hxτ⟩ := hχ p₀.g hg₀
  have hxadd := GlobalTheory.T.memberTorsionPoints_additive_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx (lab c) τ xτ hxτ
  obtain ⟨ρA, hρA, hρfr⟩ := GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x fr hx hfr
  obtain ⟨hg'o, hwc, hover⟩ := hg' c
  have hadd : (g' c).IsAdd p₀.g (g' c + p₀.g) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).mpr rfl
  obtain ⟨hb, -⟩ := GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd
  obtain ⟨w₂, hw₂gen, hw₂⟩ : ∃ w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + p₀.g).b, w₂.IsGen ∧
      ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    generalize (g' c + p₀.g).b = b at hb ⊢
    subst hb
    exact ⟨w c, hwc, fun _ _ _ => rfl⟩
  obtain ⟨e₂, he₂t, he₂o⟩ := GlobalTheory.T.torusExtension_translate_liesOver_product_torsionFrame g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c))
    (hρfr _) (g' c) (w c) hg'o hwc hover χ hχ1 p₀.g hg₀ p xτ hpy hpg hpq (g' c + p₀.g) hadd w₂ hw₂ (x (lab c + τ)) hxadd
  obtain ⟨κ, hκ0, hκ⟩ := exists_frAt_ratio he₂t.2.1 (hfr (lab c + τ)).1
  obtain ⟨w', hw'gen, hw'⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale w₂ hw₂gen (inv_ne_zero hκ0)
  have hover' := over_scale 𝔪 hw₂gen hκ0 hκ hw' he₂o
  have hrN : 0 < X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    rw [hj, X₁.ρ.N_eq]
    have := X₁.ρ.n_prime.pos
    positivity
  have hκpow : κ ^ ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) = 1 := by
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' 𝔪.A.isLB (z₀ : (TFK (R := V) (FractionRing V)).left)
    have h := GlobalTheory.Poinc.DivDeep.torsFrame_two_levels 𝔪.A (hρfr (lab c + τ)) he₂t hJ₀
    rw [div_self', one_pow] at h
    have hk := hκ z₀ J₀ hJ₀
    apply cstH_inj (R := V) z₀
    rw [map_pow, map_one]
    have hq : (val (fr (lab c + τ)) (𝟙 _) z₀ J₀ / val e₂ (𝟙 _) z₀ J₀).val = cstH (R := V) z₀ κ := by
      rw [div_eq_mul_inv, Units.val_mul, hk, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      rfl
    rw [← hq, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hint : ∀ mu : Fin 8 → X, ∃ y : V,
      algebraMap V (FractionRing V) y = κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val := by
    intro mu
    have hcl : IsIntegrallyClosed V := 𝔪.cn.2.1
    have h1 : (χ (Multiplicative.ofAdd (𝔪.e₈ mu))) ^ (X₁.S.r * X₁.S.N) = 1 := by
      rw [← MonoidHom.pow_apply, hχ1, MonoidHom.one_apply]
    have hpow : (κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val) ^
        ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N)) = 1 := by
      rw [mul_pow, inv_pow, pow_mul, hκpow, one_pow, inv_one, _root_.one_mul, ← Units.val_pow_eq_pow_val, pow_mul', h1,
        one_pow, Units.val_one]
    have hI : IsIntegral V (κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val) := by
      refine IsIntegral.of_pow (Nat.mul_pos (Nat.mul_pos (pow_pos hrN 2) (pow_pos hrN 2)) hrN) ?_
      rw [hpow]
      exact isIntegral_one
    exact IsIntegrallyClosed.isIntegral_iff.mp hI
  choose y hy using hint
  have hcoef : ∀ mu, coef s (g' c + p₀.g) w' (𝔪.e₈ mu) =
      κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val * coef s (g' c) (w c) (𝔪.e₈ mu) := by
    intro mu
    refine GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd hwc (fun z J hJ => ?_) s (𝔪.e₈ mu)
    rw [hw' z J hJ, hw₂ z J hJ, cst_eq]
  have hg₂o : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c + p₀.g) o ∧ o.IsZero := by
    obtain ⟨o, ho, hoz⟩ := hg'o
    rw [GlobalTheory.TorusExt.isNsmul_iff_eq] at ho
    rw [GlobalTheory.TorusExt.isZero_iff_eq] at hoz
    refine ⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).mpr ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).mpr rfl⟩
    rw [smul_add, ← ho, hoz, zero_add, GlobalTheory.TorusExt.qk_nsmul 𝔪.D.3 p₀, hp₀y, map_zero]
  refine ⟨fun mu _ => y mu * T mu c, x, fr, th, w₀, s, fun _ => g' c + p₀.g, fun _ => w', hx, hfr, hth, hw₀, hexp,
    fun _ => ⟨hg₂o, hw'gen, hover'⟩, fun mu _ => ?_⟩
  rw [map_mul, hy mu, hcoef mu, ← hTc mu c]
  ring

end GlobalTheory.Poinc.Sep.TermsExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartPeriodTauZeroValueOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTauZero

theorem exists_isUnitTau_zero_val_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  intro E _ _ _ H k _ _ m d t P gam mu
  have hF : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim
      (K' := Fin 4) ![(P.D.toPre.c (mu + 0)).left, (P.D.toPre.c mu).left, (P.D.toPre.c 0).left, (P.D.toPre.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [add_zero, Finset.univ_eq_empty, Finset.prod_empty, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    simp [Matrix.vecHead, Matrix.vecTail]
  obtain ⟨τ₀, hτ, hv⟩ := exists_gen P.D.toPre.P.isLB hF (LB.oneGen P.D.toPre.P.L) (LB.isGen_oneGen _)
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨τ₀, ⟨hτ, 1, ?_, fun zz J hJ => ?_⟩, h1⟩
  · simp
  · have hB : P.D.toPre.TauBimult := P.D.tau_bimult
    rw [h1 _ _ zz J hJ, _root_.mul_one]
    have vτ : val (P.D.toPre.tau mu 0) (𝟙 _) zz J =
        val (P.D.toPre.psi (mu + 0)) (𝟙 _) zz J * (val (P.D.toPre.psi mu) (𝟙 _) zz J)⁻¹ *
          (val (P.D.toPre.psi 0) (𝟙 _) zz J)⁻¹ * (val P.D.toPre.rigK (𝟙 _) zz J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have vρ : val P.D.toPre.rigK (𝟙 _) zz J = val P.D.toPre.rig (jK _) zz J := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    have hp : ∀ a : P.D.toPre.X, a = mu → val (P.D.toPre.psi a) (𝟙 _) zz J = val (P.D.toPre.psi mu) (𝟙 _) zz J := by
      rintro a rfl; rfl
    have h0 := GlobalTheory.PsiZero.val_psi_zero hB hJ
    have hu : unitOn (1 : (FractionRing (ChartRing k m d))ˣ) = 1 := map_one _
    rw [vτ, hp _ (add_zero mu), h0, vρ, hu, map_one, mul_inv_cancel, _root_.one_mul, inv_inv, mul_inv_cancel]

end GlobalTheory.UnitTauZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitValueTranslatedBundleSection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitPt

theorem isUnit_gs_of_mem_basicOpen {X Y : Scheme.{0}} (T : X ⟶ Y) (x : X) (U : Y.Opens) (h : T x ∈ U) (a : Γ(Y, U))
    (ha : T x ∈ Y.basicOpen a) : IsUnit (gs T x U a) := by
  rw [gs_eq T x U h]
  have hu := (Y.mem_basicOpen a (T x) h).1 ha
  rw [← Scheme.Hom.germ_stalkMap_apply T U x h a]
  exact hu.map _

theorem exists_unit_sval (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (α ν : Q.X)
    (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k))) (hs : ¬ ∀ j, s.f j = 0) :
    ∃ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι),
      Good Q.P.L z J ∧ IsUnit (sval s (DegPre.trF Q (FractionRing R) ν).left z J) := by
  obtain ⟨j, hj⟩ := not_forall.1 hs
  have hsm := Q.P.isAb.smooth
  let p : (DegPre.BF Q (FractionRing R)).left ⟶ Spec (CommRingCat.of (FractionRing R)) :=
    (fst (TF (R := R) (FractionRing R)) Q.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) (FractionRing R)).hom Q.P.A.hom))
  have : IsReduced (DegPre.BF Q (FractionRing R)).left := isReduced_of_smooth p
  have hne : (DegPre.BF Q (FractionRing R)).left.basicOpen (s.f j) ≠ ⊥ := fun h =>
    hj ((basicOpen_eq_bot_iff _).1 h)
  obtain ⟨w, hw⟩ : ∃ w, w ∈ (DegPre.BF Q (FractionRing R)).left.basicOpen (s.f j) := by
    by_contra h
    push_neg at h
    exact hne (eq_bot_iff.2 fun x hx => (h x hx).elim)
  have hwU := Scheme.basicOpen_le _ _ hw
  set T := (DegPre.trF Q (FractionRing R) ν).left with hT
  let z := (DegPre.trF Q (FractionRing R) (-ν)).left w
  have hz : T z = w := by
    change ((DegPre.trF Q (FractionRing R) (-ν)).left ≫ T) w = w
    rw [hT, ← Over.comp_left, ReciprocityTheory.ChartRestriction.G.DVR.UUA.trF_add, neg_add_cancel, ReciprocityTheory.ChartRestriction.G.DVR.UUA.trF_zero]
    rfl
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.P.L z J := ⟨_, fun ψ => (exists_chart Q.P.isLB (ψ z)).choose_spec⟩
  refine ⟨z, J, hJ, ?_⟩
  have hz' : T z ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) α) j := hz ▸ hwU
  have hzb : T z ∈ (DegPre.BF Q (FractionRing R)).left.basicOpen (s.f j) := hz ▸ hw
  rw [sval, sec_trans s T z (hJ.mem _ T) hz']
  exact (Units.isUnit _).mul (isUnit_gs_of_mem_basicOpen T z _ hz' (s.f j) hzb)

end GlobalTheory.UnitPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivation
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DerFieldExt

theorem cover' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) :
    W ≤ ⨆ i : {f : Γ(X, W₀) // X.basicOpen f ≤ W}, X.basicOpen i.1 := by
  intro y hy
  obtain ⟨f, hf, hx⟩ := hW.exists_basicOpen_le (V := W) ⟨y, hy⟩ (h hy)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩

theorem sep' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) (s t : Γ(X, W))
    (e : ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k s = resG X k t) : s = t :=
  X.sheaf.eq_of_locally_eq' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
    W (fun i => homOfLE i.2) (cover' X hW h) s t (fun i => e i.1 i.2)

theorem exists_field : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ δ : Γ(Z, U) → Γ(Z, U),
    (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = a * δ b + b * δ a) →
    ∃ d : Fld Z, IsField U d ∧ d U = δ := by
  intro X W₀ hW d₀ hadd hmul
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(X, X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG X (X.basicOpen_le f) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    obtain ⟨δ, h1, h2, h3⟩ := GlobalTheory.LocDerExt.der_exists f (RingHom.id _)
      (fun a => resG X (X.basicOpen_le f) (d₀ a)) (fun a b => by simp only [hadd, map_add (f := _)])
      (fun a b => by simp only [hmul, map_add (f := _), map_mul, RingHom.id_apply]; rfl)
    exact ⟨δ, h1, fun a b => by simpa using h2 a b, h3⟩
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG X k (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine GlobalTheory.LocDerExt.der_unique f (resG X k)
      (fun s => resG X k (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add (f := _), map_mul]
    · simp only [δmul, map_mul]
    · change resG X k (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [GlobalTheory.LocDerExt.res_res X, δres, δres, GlobalTheory.LocDerExt.res_res X]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(X, W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
      W (fun i => homOfLE i.2) (cover' X hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : X.basicOpen i.1 ⊓ X.basicOpen j.1 ≤ X.basicOpen (i.1 * j.1) := e.ge
        have e' : resG X ki (δ i.1 (resG X i.2 s)) = resG X kj (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X]
        have e'' := congrArg (resG X k) e'
        rw [GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add (f := _), δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep' X hW (h'.trans h) _ _ (fun f k => ?_)
    refine Eq.trans ?_ (GlobalTheory.LocDerExt.res_res X h' k _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), GlobalTheory.LocDerExt.res_res X]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep' X hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

end GlobalTheory.DerFieldExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceDefiniteFormEqSumConjClassesStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_definiteForm_eq_sum_conjClasses : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ B : GlobalTheory.LKDef.DForm G,
      B.trace ξ L.K.toSubgroup f K' f' =
        ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G B.β),
          LinearMap.trace ℂ V (ξ (Quotient.out c : GlobalTheory.LKCx.grp G B.β).1) *
            centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c) := by
  first | (exact @GlobalTheory.HeckeTrace.dform_trace_eq) | (exact GlobalTheory.HeckeTrace.dform_trace_eq) | (intros; apply GlobalTheory.HeckeTrace.dform_trace_eq <;> assumption)
end

