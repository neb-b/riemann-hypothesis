module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0008
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0013
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.UnitOfHeightOnePrimesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerAffineChart

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleMinusExceptionalStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.blowup_ample_minus_exceptional : ∀ (Y₀ Y₁ : Scheme.{0}) [IsNoetherian Y₀] [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData), FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ E : CartierDiv Y₁, E.Eff ∧ E.supp = (I.comap t).support ∧ ∀ᶠ c : ℕ in atTop, ∀ (P : LB Y₁) (hP : P.IsLB), cls P hP = c • CechPic.pull t (cls A hA.isLB) - toPic E → IsGenerated P := by
  first | exact @_root_.GlobalTheory.TwistBelow.exists_eff_isGenerated | exact _root_.GlobalTheory.TwistBelow.exists_eff_isGenerated | (intros; apply _root_.GlobalTheory.TwistBelow.exists_eff_isGenerated <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorBirationalCompare
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy.CanonIso

theorem isNormalScheme_of_smooth' {k : Type} [Field k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) [Smooth p] :
    GlobalTheory.IsNormalScheme Y :=
  (GlobalTheory.isNormalScheme_iff Y).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
    ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))

theorem ring_ne_top' {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) : E.ring ≠ ⊤ := fun h =>
  IsDiscreteValuationRing.not_isField E.ring (by
    rw [h]
    exact MulEquiv.isField (Field.toIsField X.functionField) Subring.topEquiv.toMulEquiv)

theorem isAt_of_through' {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {z : X} {E F : DivOver p} (hF : F.IsAt z) (hE : E.Through z) : E.IsAt z := by
  have hle : F.ring ≤ E.ring := fun f hf => hE f ((hF f).1 hf)
  have := ValuationSubring.eq_of_le_of_ne_top F.ring hle (ring_ne_top' E)
  exact fun f => this ▸ hF f

theorem not_mem_supp_sub_pullCart : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)] (U : Y₀.Opens), (U : Set Y₀).Nonempty → IsIso (t ∣_ U) → ∀ (η : RatForms q n), η ≠ 0 → ∀ (K₀ : CartierDiv Y₀) (K₁ : CartierDiv Y₁), IsDivOfForm K₀ η → IsDivOfForm K₁ (EtaleKlt.ratPull q t n η) → ∀ y : Y₁, t y ∈ U → y ∉ (K₁ - pullCart t K₀).supp := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ U hU hiso η hη K₀ K₁ h₀ h₁ y hy
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  haveI : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n (t ≫ q)
  haveI : GlobalTheory.IsNormalScheme Y₀ := isNormalScheme_of_smooth' q
  haveI : GlobalTheory.IsNormalScheme Y₁ := isNormalScheme_of_smooth' (t ≫ q)
  have hbir := _root_.GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict Y₀ Y₁ t U hU hiso
  have hpull : EtaleKlt.ratPull q t n η ≠ 0 := fun h =>
    hη ((_root_.GlobalTheory.EtaleKlt.ratPull_bijective_of_birational k Y₀ Y₁ q t hbir n).1 (h.trans (map_zero _).symm))
  rw [(GlobalTheory.T.cartier_divisor_mult_characterize Y₁ (K₁ - pullCart t K₀)).2.1 y]
  rintro ⟨z, hzy, hz⟩
  apply hz
  have htz : t z ∈ U := (hzy.map t.continuous).mem_open U.isOpen hy
  obtain ⟨hc, hm⟩ := _root_.GlobalTheory.Discrepancy.MultIso.coheight_eq_and_mult_pullCart Y₀ Y₁ t U hiso z htz
  have hsub : (K₁ - pullCart t K₀).mult z = K₁.mult z - (pullCart t K₀).mult z := by
    have := CartierDiv.mult_add (K₁ - pullCart t K₀) (pullCart t K₀) z
    rw [sub_add_cancel] at this
    omega
  rw [hsub, hm K₀, sub_eq_zero]
  by_cases h1 : Order.coheight z = 1
  · obtain ⟨E', hE'⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := t ≫ q) h1
    obtain ⟨E, hO⟩ := _root_.GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective k Y₀ Y₁ q t hbir E'
    obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := q) (z := t z) (hc ▸ h1)
    have hthr : E.Through (t z) := by
      intro f hf
      obtain ⟨a, rfl⟩ := hf
      exact (hO _).2 ((hE' _).2 ⟨t.stalkMap z a, (GlobalTheory.functionFieldMap_algebraMap t z a).symm⟩)
    have hE : E.IsAt (t z) := isAt_of_through' hF hthr
    rw [← _root_.GlobalTheory.Discrepancy.DivOver.formOrd_eq_mult_of_isDivOfForm k Y₁ (t ≫ q) n _ hpull K₁ h₁ E' z hE',
      ← _root_.GlobalTheory.Discrepancy.DivOver.formOrd_eq_mult_of_isDivOfForm k Y₀ q n η hη K₀ h₀ E (t z) hE]
    exact GlobalTheory.T.form_order_birational_pullback k Y₀ Y₁ q t hbir E' E hO n η hη
  · have a : K₁.mult z = 0 := by_contra fun h => h1 (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    have b : K₀.mult (t z) = 0 :=
      by_contra fun h => h1 (hc ▸ CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    rw [a, b]

end GlobalTheory.Discrepancy.CanonIso
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLiftStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.divisor_point_proper_lift : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ z : X, E.IsAt z → ∃ w : Y, s w = z ∧ E'.IsAt w := by
  first | exact @_root_.GlobalTheory.Discrepancy.DivOver.isAt_lift | exact _root_.GlobalTheory.Discrepancy.DivOver.isAt_lift | (intros; apply _root_.GlobalTheory.Discrepancy.DivOver.isAt_lift <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EffectiveMultipleDominates
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Domin

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

end GlobalTheory.Domin

private theorem exists_pow_eq_mul_of_mem_maximalIdeal_dim_le_one {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ringKrullDim R ≤ 1) (a p : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hp : p ≠ 0) :
    ∃ N : ℕ, ∃ b : R, a ^ N = p * b := by
  by_cases hpu : IsUnit p
  · exact ⟨0, ↑hpu.unit⁻¹, by simp⟩
  · haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by exact_mod_cast hR)
    have hmax : ∀ P : Ideal R, P.IsPrime → p ∈ P → P = IsLocalRing.maximalIdeal R := by
      intro P hP hpP
      rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (⟨P, hP⟩ : PrimeSpectrum R) with h | h
      · have h' := congrArg PrimeSpectrum.asIdeal h
        simp at h'
        rw [h'] at hpP
        exact absurd ((Submodule.mem_bot R).1 hpP) hp
      · have h' := congrArg PrimeSpectrum.asIdeal h
        simpa using h'
    have hrad : a ∈ (Ideal.span {p}).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      rintro P ⟨hPp, hP⟩
      rw [hmax P hP (hPp (Ideal.mem_span_singleton_self p))]
      exact ha
    have hle : Ideal.span {a} ≤ (Ideal.span {p}).radical := (Ideal.span_singleton_le_iff_mem _).2 hrad
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (Submodule.fg_span_singleton a)
    have : a ^ N ∈ Ideal.span {p} := hN (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨N, b, by rw [← hb, mul_comm]⟩

private theorem exists_nsmul_sub_regularAt_of_supp_le {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D E : CartierDiv X) (hE : E.Eff)
    (hsupp : D.supp ≤ E.supp) (z : X) (hz : Order.coheight z = 1) :
    ∃ c0 : ℕ, (z ∉ D.supp → c0 = 0) ∧ ∀ c : ℕ, c0 ≤ c → (c • E - D).RegularAt z 1 := by
  obtain ⟨gD, hgD⟩ := D.exists_isEqn z
  obtain ⟨gE, hgE⟩ := E.exists_isEqn z
  have hEq : ∀ c : ℕ, (c • E - D).IsEqn z (gE ^ c / gD) := fun c => (hgE.nsmul c).sub hgD
  obtain ⟨a, ha⟩ := CartierDiv.eff_iff.1 hE z gE hgE
  suffices key : ∃ c0 : ℕ, (z ∉ D.supp → c0 = 0) ∧ ∀ c : ℕ, c0 ≤ c → RegAt z ((gE ^ c / gD : (X.functionField)ˣ) : X.functionField) by
    obtain ⟨c0, h0, hc0⟩ := key
    exact ⟨c0, h0, fun c hc => (hEq c).regularAt_iff.2 (by rw [one_mul]; exact hc0 c hc)⟩
  by_cases hzD : z ∈ D.supp
  · have ha' : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hau
      exact (hgE.mem_supp_iff.1 (hsupp hzD)) ⟨a, hau, ha⟩
    obtain ⟨⟨q, ⟨p, hp⟩⟩, hpq⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (X.presheaf.stalk z))
      ((gD⁻¹ : (X.functionField)ˣ) : X.functionField)
    dsimp only at hpq
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    have hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1 := (ringKrullDim_stalk_le_one_iff z).2 hz.le
    obtain ⟨N, b, hab⟩ := exists_pow_eq_mul_of_mem_maximalIdeal_dim_le_one hdim a p ha' hp0
    refine ⟨N, fun h => absurd hzD h, fun c hc => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
    refine ⟨b * q * a ^ d, ?_⟩
    have hpK : algebraMap (X.presheaf.stalk z) X.functionField p ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, ← ha, div_eq_mul_inv,
      ← Units.val_inv_eq_inv_val, ← hpq, IsFractionRing.mk'_eq_div, ← map_pow, pow_add, hab]
    simp only [map_mul]
    field_simp
  · have hu : UnitAt z (gD : X.functionField) := by
      by_contra h
      exact hzD (hgD.mem_supp_iff.2 h)
    obtain ⟨u, hu, hugD⟩ := hu
    refine ⟨0, fun _ => rfl, fun c _ => ⟨a ^ c * ↑hu.unit⁻¹, ?_⟩⟩
    have h1 : algebraMap (X.presheaf.stalk z) X.functionField u *
        algebraMap (X.presheaf.stalk z) X.functionField (↑hu.unit⁻¹) = 1 := by
      rw [← map_mul]; simp
    have hne := left_ne_zero_of_mul_eq_one h1
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, ← ha, ← hugD, map_mul, map_pow,
      eq_div_iff hne, mul_assoc, mul_comm (algebraMap _ _ _) (algebraMap _ _ u), h1, mul_one]

private theorem eq_of_mem_supp_specializes_coheight_one {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (y z : X) (hy : y ∈ D.supp) (h : y ⤳ z)
    (hz : Order.coheight z = 1) : y = z := by
  by_contra hne
  have hzy : z ≤ y := h
  have hnot : ¬ y ≤ z := fun h' => hne (h.antisymm h').eq
  have hlt : z < y := lt_of_le_not_ge hzy hnot
  have hfin : Order.coheight y < ⊤ := lt_of_le_of_lt (Order.coheight_anti hzy) (by simp [hz])
  have h1 := Order.coheight_strictAnti hlt hfin
  rw [hz] at h1
  have h0 : Order.coheight y = 0 := ENat.lt_one_iff_eq_zero.1 h1
  have hη : genericPoint X ⤳ y := genericPoint_specializes y
  by_cases hyη : genericPoint X ≤ y
  · have hyeq : y = genericPoint X := (Specializes.antisymm hyη hη).eq
    exact D.genericPoint_notMem_supp (hyeq ▸ hy)
  · have hlt2 : y < genericPoint X := lt_of_le_not_ge hη hyη
    have h2 := Order.coheight_strictAnti hlt2 (lt_of_le_of_lt (Order.coheight_anti (show y ≤ genericPoint X from hη)) (by simp [h0]))
    rw [h0] at h2
    exact absurd h2 (by simp)

private theorem finite_coheight_one_inter_supp {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (D : CartierDiv X) :
    {z : X | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨S, hSirr, hSeq⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible D.supp
  refine Set.Finite.subset (S.finite_toSet.biUnion fun k _ => (show {x : X | IsGenericPoint x (k : Set X)}.Subsingleton
    from fun x hx y hy => hx.eq hy).finite) ?_
  rintro z ⟨hz, hzD⟩
  have hzS : z ∈ (S.sup id : TopologicalSpace.Closeds X) := by rw [← hSeq]; exact hzD
  have hex : z ∈ (S.sup id : TopologicalSpace.Closeds X) → ∃ k ∈ S, z ∈ k :=
    Finset.sup_induction (p := fun C : TopologicalSpace.Closeds X => z ∈ C → ∃ k ∈ S, z ∈ k)
      (fun h => by rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at h; exact absurd h (Set.notMem_empty z))
      (fun a ha b hb h => by
        rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_sup] at h
        rcases h with h | h
        exacts [ha h, hb h])
      (fun k hk h => ⟨k, hk, h⟩)
  obtain ⟨k, hkS, hzk⟩ := hex hzS
  have hirr := hSirr ⟨k, hkS⟩
  have ht : IsGenericPoint hirr.genericPoint (k : Set X) := hirr.isGenericPoint_genericPoint k.isClosed
  have hkD : (k : Set X) ⊆ D.supp := by
    have : k ≤ D.supp := by rw [hSeq]; exact Finset.le_sup (f := id) hkS
    exact this
  have hteq := eq_of_mem_supp_specializes_coheight_one D _ z (hkD ht.mem) (ht.specializes hzk) hz
  exact Set.mem_biUnion hkS (show IsGenericPoint z (k : Set X) from hteq ▸ ht)


open GlobalTheory.Domin in
theorem GlobalTheory.effDominates : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [CompactSpace X] (D E : CartierDiv X), E.Eff → D.supp ≤ E.supp → ∃ c : ℕ, (c • E - D).Eff := by
  intro X _ _ _ _ D E hE hsupp
  classical
  have hfin := finite_coheight_one_inter_supp D
  let c0 : X → ℕ := fun z =>
    if hz : Order.coheight z = 1 then Classical.choose (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz) else 0
  refine ⟨hfin.toFinset.sup c0, ?_⟩
  have hreg : ∀ z : X, Order.coheight z = 1 → (hfin.toFinset.sup c0 • E - D).RegularAt z 1 := by
    intro z hz
    have hspec := Classical.choose_spec (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz)
    apply hspec.2
    have hc0 : c0 z = Classical.choose (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz) := by simp [c0, hz]
    rw [← hc0]
    by_cases hzD : z ∈ D.supp
    · exact Finset.le_sup (f := c0) (hfin.mem_toFinset.2 ⟨hz, hzD⟩)
    · rw [hc0, hspec.1 hzD]
      exact Nat.zero_le _
  intro x
  obtain ⟨g, hg⟩ := (hfin.toFinset.sup c0 • E - D).exists_isEqn x
  rw [hg.regularAt_iff, one_mul]
  apply regAt_of_forall_coheight_eq_one
  intro z hzx hz
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  have hgz := hU z (hzx.mem_open U.isOpen hxU)
  have h1 := hgz.regularAt_iff.1 (hreg z hz)
  rwa [one_mul] at h1
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesLogChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtLog

variable {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)


include hU in
theorem unitAt_fnOf_iff_not_mem {y : X} (hy : y ∈ U) (s : Γ(X, U)) :
    UnitAt y (fnOf U (gen_mem hy) s) ↔ s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [unitAt_fnOf_iff hy, GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hy]


include hU in
theorem regAt_iff_frac {y : X} (hy : y ∈ U) (g : X.functionField) :
    RegAt y g ↔ ∃ a b : Γ(X, U), b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      g * fnOf U (gen_mem hy) b = fnOf U (gen_mem hy) a := by
  constructor
  · intro hg
    exact GlobalTheory.FieldPair.regAt_exists_fraction hU hy hg
  · rintro ⟨a, b, hb, e⟩
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    have eg : g = fnOf U (gen_mem hy) a * (fnOf U (gen_mem hy) b)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hu.ne_zero]
    rw [eg]
    exact (regAt_fnOf hy _ a).mul hu.inv.regAt


include hU in
theorem unitAt_iff_frac {y : X} (hy : y ∈ U) (g : X.functionField) :
    UnitAt y g ↔ ∃ a b : Γ(X, U), a ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧ g * fnOf U (gen_mem hy) b = fnOf U (gen_mem hy) a := by
  constructor
  · intro hg
    obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy g).1 hg.regAt
    refine ⟨a, b, ?_, hb, e⟩
    rw [← unitAt_fnOf_iff_not_mem hU hy, ← e]
    exact hg.mul (GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb)
  · rintro ⟨a, b, ha, hb, e⟩
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    have hua := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy ha
    have eg : g = fnOf U (gen_mem hy) a * (fnOf U (gen_mem hy) b)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hu.ne_zero]
    rw [eg]
    exact hua.mul hu.inv


include hU in
theorem primeIdealOf_le_of_specializes {y z : X} (hy : y ∈ U) (hz : z ∈ U) (hzy : z ⤳ y) :
    (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro s hs
  by_contra hs'
  rw [← GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hy] at hs'
  exact (GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hz s).1 (hzy.mem_open (X.basicOpen s).isOpen hs') hs


include hU in
theorem exists_specializes_of_le {y : X} (hy : y ∈ U) (Q : Ideal Γ(X, U)) (hQ : Q.IsPrime)
    (hQP : Q ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    ∃ (z : X) (hz : z ∈ U), z ⤳ y ∧ (hU.primeIdealOf ⟨z, hz⟩).asIdeal = Q := by
  refine ⟨(GlobalTheory.QCoh.pointOfPrime hU ⟨Q, hQ⟩ : X), (GlobalTheory.QCoh.pointOfPrime hU ⟨Q, hQ⟩).2, ?_, ?_⟩
  · have h1 := ((PrimeSpectrum.le_iff_specializes ⟨Q, hQ⟩ (hU.primeIdealOf ⟨y, hy⟩)).mp hQP).map
      hU.fromSpec.continuous
    rw [hU.fromSpec_primeIdealOf ⟨y, hy⟩] at h1
    exact h1
  · rw [GlobalTheory.QCoh.primeIdealOf_pointOfPrime]

theorem isLogChart_of_isEtCoord : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp (ZMod p)) (U : X.Opens) (h : genericPoint X ∈ U) {n : ℕ} (t : Fin n → Γ(X, U))
    (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (Z : Set X), IsAffineOpen U →
    IsEtCoord f U t → (∀ j, (x j : X.functionField) = fnOf U h (t j)) →
    (∀ y ∈ U, y ∈ Z ↔ ∃ j ∈ J, ¬ UnitAt y (x j : X.functionField)) → IsLogChart Z U x J := by
  intro p _ X _ f U h n t x J Z hU hEt hx hZ
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  letI : Algebra (ZMod p) Γ(X, U) := (cstOn f U).toAlgebra
  haveI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  have hEt' : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale := hEt
  have hA : ∀ s : Γ(X, U), algebraMap Γ(X, U) X.functionField s = fnOf U h s := fun _ => rfl
  have ht : ∀ j, algebraMap Γ(X, U) X.functionField (t j) ≠ 0 := fun j => by
    rw [hA, ← hx j]; exact (x j).ne_zero
  have hxt : x = fun j => Units.mk0 _ (ht j) := funext fun j => Units.ext (hx j)
  have hB := GlobalTheory.T.fraction_field_coordinates_dlog p Γ(X, U) t hEt' X.functionField ht
  have hprod : ∀ S : Finset (Fin n),
      algebraMap Γ(X, U) X.functionField (∏ j ∈ S, t j) = ∏ j ∈ S, (x j : X.functionField) :=
    fun S => by rw [map_prod]; exact Finset.prod_congr rfl fun j _ => (hx j).symm
  refine ⟨fun y hy => ⟨fun i => ?_, ?_, ?_, ?_⟩, fun y hy g => ?_⟩
  · rw [hx i]; exact regAt_fnOf hy h (t i)
  · rw [hxt]; exact hB.1
  · intro g hg
    obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy g).1 (mem_locRing.1 hg)
    obtain ⟨ca, hca⟩ := hB.2 a
    obtain ⟨cb, hcb⟩ := hB.2 b
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    refine ⟨fun i => (fnOf U h b)⁻¹ * (fnOf U h (ca i) - g * fnOf U h (cb i)), fun i => ?_, ?_⟩
    · exact mul_mem (mem_locRing.2 hu.inv.regAt) (sub_mem (mem_locRing.2 (regAt_fnOf hy h _))
        (mul_mem hg (mem_locRing.2 (regAt_fnOf hy h _))))
    · have hB0 : fnOf U h b ≠ 0 := hu.ne_zero
      have key : dK g = (fnOf U h b)⁻¹ • (dK (fnOf U h a) - g • dK (fnOf U h b)) := by
        have e' : g * fnOf U h b = fnOf U h a := e
        rw [← e']
        simp only [dK, Derivation.leibniz]
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hB0, one_smul]
      simp only [hA] at hca hcb
      rw [key]
      simp only [dK] at hca hcb ⊢
      rw [hca, hcb, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx i, smul_smul, ← sub_smul, smul_smul, mul_comm g]
  · intro S g m hm hg
    obtain ⟨a, b, hb, e⟩ := GlobalTheory.T.root_of_monomial_quotient_integral p Γ(X, U) t hEt' (hU.primeIdealOf ⟨y, hy⟩).asIdeal
      X.functionField S g m hm (by
        obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy _).1 (mem_locRing.1 hg)
        exact ⟨a, b, hb, by rw [hprod]; exact e⟩)
    exact mem_locRing.2 ((regAt_iff_frac hU hy _).2 ⟨a, b, hb, by rw [← hprod]; exact e⟩)
  · have hZc : ∀ z (hz : z ∈ U), z ∉ Z ↔ ∀ j ∈ J, t j ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
      intro z hz
      rw [hZ z hz]
      simp only [not_exists, not_and, not_not]
      refine forall₂_congr fun j _ => ?_
      rw [hx j]
      exact unitAt_fnOf_iff_not_mem hU hz (t j)
    have hU' := GlobalTheory.T.unit_of_height_one_primes p Γ(X, U) t hEt' (hU.primeIdealOf ⟨y, hy⟩).asIdeal X.functionField J ht g
    refine Iff.trans ?_ (hU'.trans ?_)
    · constructor
      · intro hL Q hQ hQP hJ
        obtain ⟨z, hz, hzy, rfl⟩ := exists_specializes_of_le hU hy Q hQ hQP
        exact (unitAt_iff_frac hU hz g).1 (hL z hzy ((hZc z hz).2 hJ))
      · intro hL z hzy hzZ
        have hz : z ∈ U := hzy.mem_open U.isOpen hy
        exact (unitAt_iff_frac hU hz g).2 (hL _ inferInstance
          (primeIdealOf_le_of_specializes hU hy hz hzy) ((hZc z hz).1 hzZ))
    · subst hxt
      exact exists_congr fun u => exists_congr fun m => and_congr_left' (unitAt_iff_frac hU hy u).symm

end GlobalTheory.EtLog
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSmoothProjectiveModel
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_smooth_projective_birational_model : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s), SmoothOfRelativeDimension n (s ≫ p) ∧ IsProjOver (s ≫ p) ∧ Function.Bijective (functionFieldMap s) := by
  first | exact @_root_.GlobalTheory.BirModel.exists_smooth_projective_model | exact _root_.GlobalTheory.BirModel.exists_smooth_projective_model | (intros; apply _root_.GlobalTheory.BirModel.exists_smooth_projective_model <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChartStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_snc_chart : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ y : Y, ∃ (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u := by
  first | exact @_root_.GlobalTheory.Discrepancy.exists_isSncChart | exact _root_.GlobalTheory.Discrepancy.exists_isSncChart | (intros; apply _root_.GlobalTheory.Discrepancy.exists_isSncChart <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerAffineChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.finrank_kaehler_affine_chart : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (U : X.Opens) (c : ∀ i, (L i).ι) (hc : ∀ i, U ≤ (L i).U (c i)) (x : X) (K : Type) [Field K] [Algebra Γ(X, U) K], IsAffineOpen U → x ∈ U → (∀ a : Γ(X, U), algebraMap Γ(X, U) K a ≠ 0 ↔ x ∈ X.basicOpen a) → (letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra; Module.finrank K (K ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d ∧ LinearIndependent K (fun i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} => (1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i) ((σ i).f (c i))))) → ∃ C : SncChart f d L σ, x ∈ C.U := by
  first | exact @_root_.GlobalTheory.LogPair.ChartPt.exists_chart | exact _root_.GlobalTheory.LogPair.ChartPt.exists_chart | (intros; apply _root_.GlobalTheory.LogPair.ChartPt.exists_chart <;> assumption)
end

