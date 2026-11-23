module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmField
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum

theorem extendedReal_coe_finset_sum_of_real {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem oscLe_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime] (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H F vd → OscLe Xo c p cx (F * m * (1 + vd / 2) * Mb + Sm) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p hp vd hvd hT
  classical
  intro la
  refine ⟨0, fun T io e ho y => ?_⟩
  have hfall : ∀ f : Lt1 Dw, letI := H.starRing
      (((0 : ℝ) : EReal) ≤ nuFac p y f (cx f) ∧ (y.IsAlg → nuFac p y f (cx f) ≤ ((boundAll p (rk f) (cx f) : ℝ) : EReal))) :=
    fun f => ((_root_.GlobalTheory.RefSum.facBetween_zero_boundAll E H Dw l Xo c p la f (cx f)).1 T io e ho y)
  have hnu : letI := H.starRing; nuP p y cx = ∑ f, nuFac p y f (cx f) := rfl
  refine ⟨?_, fun hy => ?_⟩
  · simp only [Nat.cast_zero, EReal.coe_zero] at hfall ⊢
    rw [hnu]
    exact Finset.sum_nonneg fun f _ => (hfall f).1
  · obtain ⟨len, hlen0, -, hlenS, hlen⟩ :=
      GlobalTheory.T.meanUpperBound_bigFactors_placeAboveTwo E H Dw l Xo c p F vd hT T io y (not_isUnit_of_overLa la ho) hy
    set b : Lt1 Dw → ℝ := fun f => if IsBig k f then (cx f : ℝ) * len f.1 else (rk f : ℝ) * cx f with hb
    have hfb : ∀ f, letI := H.starRing; nuFac p y f (cx f) ≤ ((b f : ℝ) : EReal) := by
      intro f
      by_cases hbig : IsBig k f
      · simp only [hb, if_pos hbig]
        simpa [mul_comm] using hlen f (cx f) hbig.1
      · simp only [hb, if_neg hbig]
        have := (hfall f).2 hy
        have hB : boundAll p (rk f) (cx f) ≤ (rk f : ℝ) * cx f := by
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
          unfold boundAll
          exact div_le_self (by positivity) (by linarith)
        exact this.trans (EReal.coe_le_coe_iff.2 hB)
    have hsum : letI := H.starRing; nuP p y cx ≤ ((∑ f, b f : ℝ) : EReal) := by
      rw [hnu, extendedReal_coe_finset_sum_of_real]
      exact Finset.sum_le_sum fun f _ => hfb f
    refine hsum.trans (EReal.coe_le_coe_iff.2 ?_)
    have hsplit : ∑ f, b f = (∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * len f.1) +
        ∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * cx f := by
      simp only [hb]; rw [Finset.sum_ite]
    have hsmall : (∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * cx f) ≤ Sm := by
      refine le_trans (le_of_eq ?_) hE.2.2.1
      unfold sumSmallSpread
      push_cast
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext f; simp [not_isBig_iff]
    have hbig : (∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * len f.1) ≤ F * m * (1 + vd / 2) * Mb := by
      have hfib := Finset.sum_fiberwise (Finset.univ.filter (IsBig k)) (fun f : Lt1 Dw => f.1)
        (fun f => (cx f : ℝ) * len f.1)
      rw [← hfib]
      have h1 : ∀ τ : E →+* ℂ, (∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
          ≤ len τ * Mb := by
        intro τ
        have hτ := hE.2.1 τ
        have : (∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
            = len τ * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), (cx f : ℝ) := by
          rw [Finset.filter_filter, Finset.mul_sum]
          refine Finset.sum_congr (by ext f; simp) fun f hf => ?_
          rw [(Finset.mem_filter.1 hf).2.2, mul_comm]
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (hlen0 τ)
        rw [Nat.cast_sum] at hτ
        refine le_trans (le_of_eq ?_) hτ
        exact Finset.sum_congr (by ext f; simp) fun _ _ => rfl
      have hq : (Dw.q : ℝ) ≤ m := by exact_mod_cast hS.2.1
      calc _ ≤ ∑ τ : E →+* ℂ, len τ * Mb := Finset.sum_le_sum fun τ _ => h1 τ
        _ = (∑ τ, len τ) * Mb := by rw [Finset.sum_mul]
        _ ≤ (F * Dw.q * (1 + vd / 2)) * Mb := mul_le_mul_of_nonneg_right hlenS hE.1
        _ ≤ F * m * (1 + vd / 2) * Mb := by
          apply mul_le_mul_of_nonneg_right _ hE.1
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    simp only [Nat.cast_zero, zero_add]
    rw [hsplit]
    linarith

end GlobalTheory.RefSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrime
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OscSplit

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumBig sumSmallSpread not_isBig_iff)

theorem ereal_coe_sum {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
theorem card_filter_inPsi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← GlobalTheory.LamF.card_psiSet H, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun τ => by
    rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩)


open Classical in
theorem sumBig_le {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {F k : ℕ} {Mb : ℝ} {cx : Lt1 Dw → ℕ}
    (hF : Module.finrank ℚ E = 2 * F)
    (h : ∀ τ : E →+* ℂ, ((∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f : ℕ) : ℝ) ≤ Mb) :
    (sumBig k cx : ℝ) ≤ F * Mb := by
  have hc : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi, hF]; omega
  have e : sumBig k cx = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ),
      ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f := by
    unfold sumBig
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (IsBig k))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.filter_filter]
  rw [e, Nat.cast_sum]
  refine (Finset.sum_le_sum fun τ _ => h τ).trans ?_
  rw [Finset.sum_const, hc, nsmul_eq_mul]

theorem oscLe_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp h2 hd hs la
  classical
  obtain ⟨-, hqm, -, -, -, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hB
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  let B : Lt1 Dw → ℝ := fun f =>
    if IsBig k f then (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) else boundAll p (rk f) (cx f)
  have hsum : ∑ f, B f ≤ (F * m * Mb + Sm) / ((p : ℝ) - 1) := by
    have e1 : ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) =
        (sumBig k cx : ℝ) * Dw.q / ((p : ℝ) - 1) := by
      rw [← Finset.sum_mul, mul_div_assoc, sumBig, Nat.cast_sum]
    have e2 : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), boundAll p (rk f) (cx f) =
        (sumSmallSpread k cx : ℝ) / ((p : ℝ) - 1) := by
      rw [sumSmallSpread, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr (Finset.filter_congr fun f _ => not_isBig_iff k f) fun f _ => ?_
      rw [boundAll, Nat.cast_mul]
    have h1 := sumBig_le (k := k) (cx := cx) hF hbig
    have h3 : (Dw.q : ℝ) ≤ m := by exact_mod_cast hqm
    have h4 : (sumBig k cx : ℝ) * Dw.q ≤ F * Mb * m :=
      mul_le_mul h1 h3 (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hMb)
    rw [Finset.sum_ite, e1, e2, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hp1.le
  refine ⟨0, fun T io e ho y => ?_⟩
  have hall := fun f => (_root_.GlobalTheory.RefSum.facBetween_zero_boundAll E H Dw l Xo c p la f (cx f)).1 T io e ho y
  constructor
  · rw [Nat.cast_zero, EReal.coe_zero]
    exact Finset.sum_nonneg fun f _ => (hall f).1
  · intro ha
    rw [Nat.cast_zero, zero_add]
    refine le_trans ?_ (EReal.coe_le_coe_iff.2 hsum)
    rw [ereal_coe_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    by_cases hf : IsBig k f
    · simp only [B, if_pos hf]
      exact (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) ha h2 hd f (cx f) hf.1).1 hs
    · simp only [B, if_neg hf]
      exact (hall f).2 ha

end GlobalTheory.OscSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantSectionUnitIntegralFramesDvr
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.DvrUnit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] {β' : O' →+* c.F}
  {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_ext (Z : Model Xo c β) (U : Set (Xo.XF c)) (j : c.F →+* R) (x : Sp K ⟶ Xo.XF c)
    (h1 : x ≫ toF Xo c = spMap ((algebraMap R K).comp j)) (hU : Set.range x ⊆ U) :
    ∃ χ : Sp R ⟶ gen Z, χ ≫ genStr Z = spMap j ∧ x ≫ Z.jQ = spMap (algebraMap R K) ≫ χ ∧
      Set.range χ ⊆ compactOf Z U := by
  haveI := isProper_genStr Z
  obtain ⟨χ, h2, h3⟩ := GlobalTheory.exists_valuativeExtension (genStr Z) (spMap j) (x ≫ Z.jQ) (by
    rw [Category.assoc, Z.jQ_over, ← Geo.Tor.spMap_comp]
    exact h1)
  refine ⟨χ, h3, h2.symm, ?_⟩
  rintro _ ⟨p, rfl⟩
  let g0 : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hg : χ (spMap (algebraMap R K) g0) ∈ Z.jQ '' U := by
    rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]
    exact ⟨_, hU ⟨g0, rfl⟩, rfl⟩
  have hp : p ∈ closure {spMap (algebraMap R K) g0} := by
    apply (PrimeSpectrum.le_iff_mem_closure _ _).1
    show Ideal.comap (algebraMap R K) (⊥ : Ideal K) ≤ (p : PrimeSpectrum R).asIdeal
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
    exact bot_le
  exact map_mem_closure χ.continuous hp (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hg)


omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem exists_ident (Z : Model Xo c β) {χ : Sp R ⟶ gen Z} {x : Sp K ⟶ Xo.XF c}
    (hχ : x ≫ Z.jQ = spMap (algebraMap R K) ≫ χ) {tK : SAB H (Sp K)}
    (mK : SABMap tK Xo.univ.t (x ≫ toX Xo c)) {t : SAB H (Sp R)} (m : SABMap t Z.t (χ ≫ genι Z)) :
    ∃ (a : SABMap tK t (spMap (algebraMap R K))) (mF : SABMap tK Z.oF.t x),
      mF.φ ≫ Z.m0.toSABMap.φ = mK.φ ∧ mF.φ ≫ Z.m.φ = a.φ ≫ m.φ := by
  obtain ⟨mF, h1⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Z.oF.t tK (pullback.fst _ _) x
    Z.m0.toSABMap mK
  obtain ⟨mJ, h2⟩ := sabComp pullCubComp E H _ _ _ Z.t Z.oF.t tK (Z.jQ ≫ pullback.fst _ _) x Z.m mF
  have hj : x ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap R K) ≫ χ ≫ genι Z := by
    rw [← Category.assoc, hχ, Category.assoc]
  obtain ⟨a, h3⟩ := sabCancel pullCubCancel E H _ _ _ Z.t t tK (χ ≫ genι Z) (spMap (algebraMap R K)) m
    (PullbackSections.sabMapCast mJ hj)
  exact ⟨a, mF, h1.symm, by rw [← h2, ← PullbackSections.sabMapCast_φ mJ hj, h3]⟩


omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem exists_lift_vec {Z : Model Xo c β} {Y : Model Xo c β'} {χ : Sp R ⟶ gen Z} {χ' : Sp R ⟶ gen Y}
    {x : Sp K ⟶ Xo.XF c} {tK : SAB H (Sp K)} {mK : SABMap tK Xo.univ.t (x ≫ toX Xo c)} {t t' : SAB H (Sp R)}
    {m : SABMap t Z.t (χ ≫ genι Z)} {m' : SABMap t' Y.t (χ' ≫ genι Y)} {ψ : SABMap t t' (𝟙 (Sp R))}
    {a : SABMap tK t (spMap (algebraMap R K))} {a' : SABMap tK t' (spMap (algebraMap R K))}
    {mF : SABMap tK Z.oF.t x} {mF' : SABMap tK Y.oF.t x}
    (hψ : a.φ ≫ ψ.φ = a'.φ) (hF0 : mF.φ ≫ Z.m0.toSABMap.φ = mK.φ)
    (hFm : mF.φ ≫ Z.m.φ = a.φ ≫ m.φ) (hF0' : mF'.φ ≫ Y.m0.toSABMap.φ = mK.φ) (hFm' : mF'.φ ≫ Y.m.φ = a'.φ ≫ m'.φ)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _)
    (w' : epsAt x ⟶ Y.oF.t.G)
    (hw3 : w'.left ≫ Y.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ (v ≫ ψ.φ) ≫ m'.φ) :
    ∃ w : epsAt x ⟶ Z.oF.t.G, w.left ≫ Z.m0.toSABMap.φ = w'.left ≫ Y.m0.toSABMap.φ ∧
      w.left ≫ Z.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v ≫ m.φ := by
  rw [Category.comp_id] at hv
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Sp (DualNumber K) ⟶ Y.oF.t.G.left, w₀ = w'.left := ⟨_, rfl⟩
  have hw1 : w₀ ≫ Y.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x := hw₀ ▸ Over.w w'
  have hw3' : w₀ ≫ Y.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ (v ≫ ψ.φ) ≫ m'.φ := hw₀ ▸ hw3
  obtain ⟨u, e1, hu1⟩ : ∃ u : Sp (DualNumber K) ⟶ tK.G.left, u ≫ mF'.φ = w₀ ∧
      u ≫ tK.G.hom = spMap (algebraMap K (DualNumber K)) :=
    ⟨mF'.cart.1.lift _ _ hw1, mF'.cart.1.lift_fst _ _ _, mF'.cart.1.lift_snd _ _ _⟩
  have hbase : spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap R K) =
      spMap (Chart.dualMapR (algebraMap R K)) ≫ spMap (algebraMap R (DualNumber R)) := by
    rw [OpenReg.spMap_comp, OpenReg.spMap_comp]
    congr 1
    ext z <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have e2 : u ≫ a.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v := by
    apply ψ.cart.1.hom_ext
    · rw [Category.assoc, hψ]
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, ← hFm', ← Category.assoc, e1, hw3']
        simp only [Category.assoc]
      · rw [Category.assoc, a'.cart.1.w, ← Category.assoc, hu1, hbase]
        simp only [Category.assoc, ψ.cart.1.w, Category.comp_id, hv]
    · rw [Category.assoc, a.cart.1.w, ← Category.assoc, hu1, Category.assoc, hv, hbase]
  have k1 : (u ≫ mF.φ) ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x := by
    rw [Category.assoc, mF.cart.1.w, ← Category.assoc, hu1]
  have k2 : (u ≫ mF.φ) ≫ Z.m0.toSABMap.φ = w₀ ≫ Y.m0.toSABMap.φ := by
    rw [Category.assoc, hF0, ← e1, Category.assoc, hF0']
  have k3 : (u ≫ mF.φ) ≫ Z.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v ≫ m.φ := by
    rw [Category.assoc, hFm, ← Category.assoc, e2, Category.assoc]
  subst hw₀
  exact ⟨Over.homMk (u ≫ mF.φ) k1, k2, k3⟩

theorem exists_move (Y : Model Xo c β') (Z : Model Xo c β) {xR : Sp R ⟶ gen Y} {xZ : Sp R ⟶ gen Z}
    {x : Sp K ⟶ Xo.XF c} (hY : x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR) (hZ : x ≫ Z.jQ = spMap (algebraMap R K) ≫ xZ)
    (χ : 𝓞 E →+* R) {n : ℕ} (vR : Fin n → (epsAt (xR ≫ genι Y) ⟶ Y.t.G))
    (hvR : IsEigBasisAt Y.t.act (xR ≫ genι Y) χ vR) {v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin n → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)} (hs : SameVecs Y x v vb)
    (hb : ∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) :
    ∃ vZ : Fin n → (epsAt (xZ ≫ genι Z) ⟶ Z.t.G), IsEigBasisAt Z.t.act (xZ ≫ genι Z) χ vZ ∧
      ∀ vK : Fin n → (epsAt ((x ≫ Z.jQ) ≫ genι Z) ⟶ Z.t.G),
        (∀ i, (vK i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vZ i).left) → SameVecs Z x v vK := by
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.ModFam.exists_sabPull (x ≫ toX Xo c) Xo.univ.t
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (xZ ≫ genι Z) Z.t
  obtain ⟨t', ⟨m'⟩⟩ := GlobalTheory.ModFam.exists_sabPull (xR ≫ genι Y) Y.t
  obtain ⟨a, mF, hF0, hFm⟩ := exists_ident Z hZ mK m
  obtain ⟨a', mF', hF0', hFm'⟩ := exists_ident Y hY mK m'
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map R K t t' tK a a'
  obtain ⟨e, he, hbe⟩ := BdryUnit.exists_eigEquiv m.cart m.act (𝟙 _) (xZ ≫ genι Z) (Category.id_comp _).symm
  obtain ⟨e', he', hbe'⟩ := BdryUnit.exists_eigEquiv m'.cart m'.act (𝟙 _) (xR ≫ genι Y) (Category.id_comp _).symm
  obtain ⟨f, hf, hbf⟩ := BdryUnit.exists_eigEquiv ψ.cart ψ.act (𝟙 _) (𝟙 _) (Category.id_comp _).symm
  obtain ⟨v₀, rfl⟩ : ∃ v₀ : Fin n → _, vR = fun i => e' (f (v₀ i)) :=
    ⟨fun i => f.symm (e'.symm (vR i)), funext fun i => by simp⟩
  refine ⟨fun i => e (v₀ i), (hbe χ n v₀).1 ((hbf χ n v₀).2 ((hbe' χ n fun i => f (v₀ i)).2 hvR)), fun vK hK i => ?_⟩
  obtain ⟨w', h1, h2⟩ := hs i
  have h3 := h2.trans (hb i)
  rw [he', hf] at h3
  obtain ⟨w, h4, h5⟩ := exists_lift_vec hψ hF0 hFm hF0' hFm' (Over.w (v₀ i)) w' h3
  refine ⟨w, h4.trans h1, h5.trans ?_⟩
  rw [hK i, he]

theorem unit_in_integral_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → Restricts Z U τ σZ σ → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (j : c.F →+* R) (xR : Sp R ⟶ gen Y) (x : Sp K ⟶ Xo.XF c) (V : Set (gen Y)) vR wR v w vb wb, FrY Y V τ j xR vR wR → FrU Xo c U τ ((algebraMap R K).comp j) x v w → x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR → SameVecs Y x v vb → SameVecs Y x w wb → (∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) → (∀ i, (wb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (wR i).left) → ∃ u : Rˣ, σ K x v w = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' Z U τ σZ σ hsec hnz hres R K _ _ _ _ _ _ j xR x V vR wR v w vb wb
    hR hU hx hv hw ev ew
  obtain ⟨xZ, h1, h2, h3⟩ := exists_ext Z U j x hU.1 hU.2.1
  obtain ⟨vZ, hvZ, sv⟩ := exists_move Y Z hx h2 _ vR hR.2.2.1 hv ev
  obtain ⟨wZ, hwZ, sw⟩ := exists_move Y Z hx h2 _ wR hR.2.2.2 hw ew
  have hZ : FrY Z (compactOf Z U) τ j xZ vZ wZ := ⟨h1, h3, hvZ, hwZ⟩
  obtain ⟨vK, wK, hK, a, b⟩ := exists_pull (algebraMap R K) hZ h2
  obtain ⟨u, hu⟩ := hnz R j xZ vZ wZ hZ
  refine ⟨u, ?_⟩
  rw [← hres K _ x v w vK wK hU hK (sv vK a) (sw wK b), hu]
  exact hsec.1 R K (algebraMap R K) (Chart.dualMapR (algebraMap R K)) j _ xZ _ vZ wZ vK wK
    (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) hZ hK h2 a b

end GlobalTheory.DetLine.DvrUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSplittingPairIdentity
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScal.LocAt

theorem liftV_one_mul' {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans' {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ) (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ)
    (hunit : ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ))
    (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁ := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨(R 0)⁻¹ • fun t => T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul']
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (_root_.GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.DblScal.LocAt

namespace GlobalTheory.DblScal.LocAt

theorem locOps : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → ∀ v : Pl (F := F), GlobalTheory.DblScal.LocOps omd v := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP dd omd hS v g hg φ hφ
  refine acts_of_comm v B.ψ hP.base.std (omd g) (fun Φ hΦ => hS.pres g Φ hΦ)
    (fun μ hμ Φ hΦ => hS.unit μ hμ g Φ hΦ) ?_ φ hφ
  intro u hu p q Φ hΦ
  set w := dd.e.symm (p, q) with hw
  have he : dd.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  let G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := ((g : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _)
  have h2 : u • (G - 1) = 0 := hg u hu
  have e2 : (u • w) * G.transpose = u • w := by
    have : (u • w) * G.transpose - u • w = w * (u • (G - 1)).transpose := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : actB (cA σ) g (u • w) = u • w := e2
  have h3 := hS.impl g (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

end GlobalTheory.DblScal.LocAt
end
end

