module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2679
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierLocal
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BigLineBundleKodairaOfIsProjOver
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.big_line_bundle_kodaira_of_isProjOver : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsProjOver p → ∀ (M A : LB X) (hM : letI := algebraΓOfHom p; IsBig k M) (hA : IsAmpleLB A), ∃ (a : ℕ) (D : CartierDiv X), 0 < a ∧ D.Eff ∧ a • cls M (letI := algebraΓOfHom p; hM.isLB) = cls A hA.isLB + toPic D := by
  first | exact @_root_.GlobalTheory.KodairaLemma.exists_nsmul_cls_eq_add_toPic_of_isBig | exact _root_.GlobalTheory.KodairaLemma.exists_nsmul_cls_eq_add_toPic_of_isBig | (intros; apply _root_.GlobalTheory.KodairaLemma.exists_nsmul_cls_eq_add_toPic_of_isBig <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorAgreementOnIsomorphismStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.divisor_agreement_on_isomorphism : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver (t ≫ q) → ∀ (U : Y₀.Opens), IsIso (t ∣_ U) → ∀ H : CartierDiv Y₁, ∃ H₀ : CartierDiv Y₀, ∀ y : Y₁, t y ∈ U → y ∉ (H - pullCart t H₀).supp := by
  first | exact @_root_.GlobalTheory.PullDiv.exists_pullCart_agree | exact _root_.GlobalTheory.PullDiv.exists_pullCart_agree | (intros; apply _root_.GlobalTheory.PullDiv.exists_pullCart_agree <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsRoundedDownDivisorStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_rounded_down_divisor : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Γ : CartierDiv Y) (m : ℕ), ∃ F : CartierDiv Y, (∀ z, F.mult z = Γ.mult z / (m : ℤ)) ∧ F.supp ≤ Γ.supp := by
  first | exact @_root_.GlobalTheory.exists_cartierDiv_mult_ediv | exact _root_.GlobalTheory.exists_cartierDiv_mult_ediv | (intros; apply _root_.GlobalTheory.exists_cartierDiv_mult_ediv <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegModPSquared
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair

namespace GlobalTheory

theorem charp_vanishing_liftable : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • CechPic.pull π (cls (L i) (h.isLB i)) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro p _ Y X g f π d _ hpb hproj hdp s L σ h K M A hM hA r b hr hb heq q hq
  have hprop : IsProper f := GlobalTheory.SchemeWords.isProper_of_isProjOver hproj
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  obtain ⟨κ, U, hcov, hdisj, hU⟩ := _root_.GlobalTheory.exists_integral_clopen_cover_of_smooth_field (ZMod p) X f
  refine _root_.GlobalTheory.coh_subsingleton_of_disjoint_cover X M κ U hM hcov hdisj q (fun c => ?_)
  have hint := (hU c).1
  have hcl := (hU c).2
  obtain ⟨W, ρ, hρ, hpb'⟩ := GlobalTheory.T.open_subscheme_closed_base_change (ZMod (p ^ 2)) (ZMod p)
    (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) Y X g f π (U c) (ZMod.ringHom_surjective _) hpb
  have hsm : SmoothOfRelativeDimension d ((U c).ι ≫ f) := by
    have := smoothOfRelativeDimension_comp (f := (U c).ι) 0 d f
    simpa using this
  have hproj' : IsProjOver ((U c).ι ≫ f) := by
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, (U c).ι ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  have h' := GlobalTheory.T.relative_snc_open_immersion (ZMod (p ^ 2)) Y W.toScheme g W.ι d s L σ h
  let K' : CanonLB ((U c).ι ≫ f) d := Classical.choice inferInstance
  have hA' : IsAmpleLB (A.pull (U c).ι) := hA.pull_of_isClosedImmersion (U c).ι
  have hK := GlobalTheory.T.canonical_bundle_open_restrict (ZMod p) X (U c).toScheme f (U c).ι d K K'
  refine GlobalTheory.T.kodaira_vanishing_mod_p_squared p W.toScheme (U c).toScheme (W.ι ≫ g) ((U c).ι ≫ f) ρ d hpb' hproj' hdp s
    (fun i => (L i).pull W.ι) (fun i => Cartier.secPull (σ i) W.ι) h' K' (M.pull (U c).ι) (A.pull (U c).ι)
    (pull_isLB hM _) hA' r b hr hb ?_ q hq
  have e2 := congrArg (CechPic.pull (U c).ι) heq
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_nsmul, map_add (f := _), map_sum] at e2
  rw [cls_pull hM (U c).ι, hK, cls_pull hA.isLB (U c).ι, e2]
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← pull_comp, ← hρ, pull_comp]
  rfl

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierLocalStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.log_resolution_multiplier_local : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ x : X, (KltAt p n Δ x ↔ ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w < m) ∧ (LcAt p n Δ x ↔ ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w ≤ m) := by
  first | exact @_root_.GlobalTheory.Discrepancy.kltAt_lcAt_iff_of_isLogRes | exact _root_.GlobalTheory.Discrepancy.kltAt_lcAt_iff_of_isLogRes | (intros; apply _root_.GlobalTheory.Discrepancy.kltAt_lcAt_iff_of_isLogRes <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealIndependent
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isMultIdeal_iff_regularAt : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J ↔ (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), (-F).RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  intro k _ _ X _ p n hproj η m G Y _ _ s _ K B F hη hm hres hF J
  have key := inMultAt_iff_regularAt_logRes k X p n hproj η m G Y s K B F hη hm hres hF
  unfold IsMultIdeal
  refine forall_congr' fun U => forall_congr' fun f => iff_congr Iff.rfl ?_
  constructor
  · intro H y hy
    by_cases h0 : fnOf U.1 (gen_mem hy) f = 0
    · rw [h0, map_zero]
      obtain ⟨g, hg⟩ := (-F).exists_isEqn y
      refine ⟨g, hg, ?_⟩
      rw [zero_mul]
      exact (regAt_zero (X := Y) (x := y))
    · have := (key (s y) (Units.mk0 _ h0)).1 (H (s y) hy _ rfl) y rfl
      simpa using this
  · intro H x hx u hu
    rw [key]
    rintro y rfl
    rw [hu]
    exact H y hx

end GlobalTheory.Discrepancy
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutRelativeSnc
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ModelSnc

def adjInv {k : Type} [Field k] (R : Subring k) (a : k) : Subring k :=
  (Polynomial.eval₂RingHom R.subtype a⁻¹).range

def toAdjInv {k : Type} [Field k] (R : Subring k) (a : k) : R →+* adjInv R a :=
  (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict.comp Polynomial.C

theorem subtype_comp_toAdjInv {k : Type} [Field k] (R : Subring k) (a : k) :
    (adjInv R a).subtype.comp (toAdjInv R a) = R.subtype := by
  ext r
  change Polynomial.eval₂ R.subtype a⁻¹ (Polynomial.C r) = (r : k)
  simp

theorem isUnit_toAdjInv {k : Type} [Field k] (R : Subring k) (a : R) (ha : (a : k) ≠ 0) :
    IsUnit (toAdjInv R (a : k) a) := by
  refine IsUnit.of_mul_eq_one ((Polynomial.eval₂RingHom R.subtype (a : k)⁻¹).rangeRestrict Polynomial.X) ?_
  apply Subtype.ext
  change Polynomial.eval₂ R.subtype (a : k)⁻¹ (Polynomial.C a) * Polynomial.eval₂ R.subtype (a : k)⁻¹ Polynomial.X = 1
  simp [ha]

theorem finiteType_adjInv {k : Type} [Field k] (R : Subring k) (hR : Algebra.FiniteType ℤ R) (a : k) :
    Algebra.FiniteType ℤ (adjInv R a) := by
  haveI := hR
  have hP : Algebra.FiniteType ℤ (Polynomial R) := inferInstance
  exact @Algebra.FiniteType.of_surjective _ _ _ _ _ _ _ _ hP
    (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict.toIntAlgHom
    (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict_surjective

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.ModelSnc

end

namespace GlobalTheory.ModelSnc

theorem exists_model_relSnc : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ), IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : RelSnc f₁ d L₁ σ₁) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h.isLB i) = CechPic.pull π (cls (L₁ i) (h₁.isLB i))) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  intro k _ X f d hf s L σ h M hM
  haveI : SmoothOfRelativeDimension d f := _root_.GlobalTheory.LogPair.smooth_of_relSnc k X f d s L σ h
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth d f
  obtain ⟨R, X₁, f₁, π, L₁, σ₁, h₁, M₁, hM₁, hR, hsm₁, hpr₁, hpb, hcl, hsame, hclM⟩ :=
    GlobalTheory.T.spread_out_smooth_proper k X f hsm hf s L σ h.isLB M hM
  have hX : RelSnc f d (fun i => (L₁ i).pull π) (fun i => Cartier.secPull (σ₁ i) π) :=
    GlobalTheory.T.relative_snc_same_divisor k X f d s L σ _ _ h (fun i => pull_isLB (h₁ i) π) hsame
  haveI := hsm₁
  haveI := hpr₁
  obtain ⟨a, ha, hsp⟩ := GlobalTheory.T.relative_snc_generic_spread R k R.subtype X₁ X f₁ f π d s L₁ σ₁ hpb h₁ hX
  set R' := adjInv R (a : k)
  set χ := toAdjInv R (a : k)
  have hχ : IsUnit (χ a) := isUnit_toAdjInv R a ha
  let g : pullback f₁ (spMap χ) ⟶ Sp R' := pullback.snd f₁ (spMap χ)
  let ρ : pullback f₁ (spMap χ) ⟶ X₁ := pullback.fst f₁ (spMap χ)
  have hρ : IsPullback ρ g f₁ (spMap χ) := IsPullback.of_hasPullback f₁ (spMap χ)
  have hZ := hsp R' χ hχ _ g ρ hρ
  have hcomp : spMap R.subtype = spMap R'.subtype ≫ spMap χ := by
    rw [← spMap_comp, subtype_comp_toAdjInv]
  have hw : π ≫ f₁ = (f ≫ spMap R'.subtype) ≫ spMap χ := by
    rw [Category.assoc, ← hcomp]; exact hpb.w
  let π' : X ⟶ pullback f₁ (spMap χ) := pullback.lift π (f ≫ spMap R'.subtype) hw
  have hπ' : π' ≫ ρ = π := pullback.lift_fst _ _ _
  have hg' : π' ≫ g = f ≫ spMap R'.subtype := pullback.lift_snd _ _ _
  have hpb' : IsPullback π' f g (spMap R'.subtype) := by
    refine IsPullback.of_right ?_ hg' hρ
    rw [hπ', ← hcomp]; exact hpb
  haveI : IsProper g := inferInstance
  refine ⟨R', pullback f₁ (spMap χ), g, π', fun i => (L₁ i).pull ρ, fun i => Cartier.secPull (σ₁ i) ρ, hZ,
    M₁.pull ρ, pull_isLB hM₁ ρ, finiteType_adjInv R hR _, inferInstance, hpb', fun i => ?_, ?_⟩
  · rw [hcl i, ← hπ', pull_comp]; rfl
  · rw [hclM, ← hπ', pull_comp]; rfl

end GlobalTheory.ModelSnc
end

