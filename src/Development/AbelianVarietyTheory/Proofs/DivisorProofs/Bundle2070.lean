module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceDominatingLocalDomainComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DvrDom

theorem exists_fractions_of_essFiniteType : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (O : Subring κ) (hc : ∀ a : ℂ, algebraMap ℂ κ a ∈ O), ((algebraMap ℂ κ).codRestrict O hc).EssFiniteType → ∃ G : Finset κ, (∀ x ∈ G, x ∈ O) ∧ ∀ o ∈ O, ∃ b ∈ Algebra.adjoin ℂ (G : Set κ), ∃ d ∈ Algebra.adjoin ℂ (G : Set κ), d ≠ 0 ∧ d⁻¹ ∈ O ∧ o = b / d := by
  classical
  intro κ _ _ O hc h
  letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O hc).toAlgebra
  have h' : Algebra.EssFiniteType ℂ O := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : O => (x : κ)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set O),
      ((x : O) : κ) ∈ Algebra.adjoin ℂ ((s.image (fun x : O => (x : κ)) : Finset κ) : Set κ) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Algebra.subset_adjoin
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy => simpa using Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => simpa using Subalgebra.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set O))) O) (IsUnit.submonoid O)) (⟨v, hv⟩ : O)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set O)) : O) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set O)) : O) : κ) * (((u⁻¹ : Oˣ) : O) : κ) = 1 := by
    rw [← hu']
    change (((u : O) * ((u⁻¹ : Oˣ) : O) : O) : κ) = ((1 : O) : κ)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set O)) : O) : κ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : O => (z : κ)) hm
  simp only at hmL
  refine ⟨((a : O) : κ), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set O)) : O) : κ),
    key _ (m : Algebra.adjoin ℂ (s : Set O)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Oˣ) : O).2
  · rw [eq_div_iff hd0]
    simpa using hmL

theorem exists_minimal_prime_le : ∀ {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (a : R), a ≠ 0 → a ∈ P → ∃ Q : Ideal R, Q.IsPrime ∧ a ∈ Q ∧ Q ≤ P ∧ Q ≠ ⊥ ∧ ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q := by
  intro R _ _ _ P _ a ha haP
  have hle : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 haP
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hle
  have hQp : Q.IsPrime := hQ.1.1
  have haQ : a ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self a)
  have hQ0 : Q ≠ ⊥ := fun h => ha (by rw [h] at haQ; exact (Ideal.mem_bot).1 haQ)
  have hht : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  refine ⟨Q, hQp, haQ, hQP, hQ0, fun p hp hp0 hpQ => ?_⟩
  by_contra hne
  have hlt : p < Q := lt_of_le_of_ne hpQ hne
  haveI := hp
  haveI := hQp
  have h1 : p.height + 1 ≤ Q.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hp1 : 1 ≤ p.height :=
    Order.one_le_iff_ne_zero.mpr (fun h => hp0 (Ideal.height_eq_zero_iff_eq_bot.1 h))
  have h2 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left hp1 1).trans (h1.trans hht)
  exact absurd h2 (by decide)

theorem exists_place_dominating : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (O : Subring κ) (hO : IsLocModel (algebraMap ℂ κ) O), letI := hO.isLocalRing;
  ¬ IsField O → ∃ F : Place (algebraMap ℂ κ), F.Contains O ∧ ∀ f : O, f ∈ IsLocalRing.maximalIdeal O → (f : κ) ≠ 0 → 0 < F.ord f := by
  intro κ _ _ O hO
  letI := hO.isLocalRing
  intro hnf
  classical
  obtain ⟨G, hGO, hGfrac⟩ := exists_fractions_of_essFiniteType O hO.const_mem hO.essFiniteType
  letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O hO.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType
  haveI : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℂ O
  obtain ⟨Y, hY⟩ := (IsNoetherian.noetherian (IsLocalRing.maximalIdeal O) :
    (IsLocalRing.maximalIdeal O).FG)

  obtain ⟨V, hOV⟩ := (LocalSubring.mk O).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := (LocalSubring.le_def).1 hOV
  have hOV' : ∀ x ∈ O, x ∈ V := fun x hx => hle hx
  have hVnu : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O → ∀ hx : (x : κ) ∈ V,
      (⟨x, hx⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
    intro x hxm hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxm
    exact hxm (hloc.map_nonunit x hu)

  have hm0 : IsLocalRing.maximalIdeal O ≠ ⊥ := fun h =>
    hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  let Y' : Finset O := Y.filter (fun y : O => (y : κ) ≠ 0)
  have hY'ne : Y'.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hm0
    rw [← hY, Submodule.span_eq_bot]
    intro y hy
    by_contra hy0
    have : y ∈ Y' := Finset.mem_filter.2 ⟨hy, fun h => hy0 (Subtype.ext h)⟩
    rw [hne] at this
    exact absurd this (Finset.notMem_empty _)
  obtain ⟨a, haY', hamax⟩ := Y'.exists_max_image (fun y : O => V.valuation (y : κ)) hY'ne
  obtain ⟨haY, ha0⟩ := Finset.mem_filter.1 haY'
  have hdivV : ∀ y ∈ Y, (y : κ) / a ∈ V := by
    intro y hy
    by_cases hy0 : (y : κ) = 0
    · rw [hy0, zero_div]; exact V.zero_mem
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
    have h1 := hamax y (Finset.mem_filter.2 ⟨hy, hy0⟩)
    have h2 : V.valuation (a : κ) ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    exact (div_le_one₀ (zero_lt_iff.2 h2)).2 h1

  let T : Finset κ := G ∪ Y.image (fun y : O => (y : κ)) ∪ Y.image (fun y : O => (y : κ) / a)
  have hTV : ∀ x ∈ T, x ∈ V := by
    intro x hx
    simp only [T, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with (hx | ⟨y, -, rfl⟩) | ⟨y, hy, rfl⟩
    · exact hOV' x (hGO x hx)
    · exact hOV' _ y.2
    · exact hdivV y hy
  have hGT : Algebra.adjoin ℂ (G : Set κ) ≤ Algebra.adjoin ℂ (T : Set κ) :=
    Algebra.adjoin_mono (by intro x hx; simp [T, Finset.mem_coe.1 hx])
  have hfracT : ∀ f : κ, ∃ u ∈ Algebra.adjoin ℂ (T : Set κ), ∃ v ∈ Algebra.adjoin ℂ (T : Set κ),
      v ≠ 0 ∧ f * v = u := by
    intro f
    obtain ⟨x, hx, z, hz, hz0, hfz⟩ := hO.frac f
    obtain ⟨b, hb, d, hd, hd0, -, rfl⟩ := hGfrac x hx
    obtain ⟨b', hb', d', hd', hd0', -, rfl⟩ := hGfrac z hz
    have hb0' : b' ≠ 0 := by rintro rfl; exact hz0 (zero_div _)
    refine ⟨b * d', Subalgebra.mul_mem _ (hGT hb) (hGT hd'), b' * d,
      Subalgebra.mul_mem _ (hGT hb') (hGT hd), mul_ne_zero hb0' hd0, ?_⟩
    field_simp at hfz
    linear_combination hfz
  have hcV : ∀ z : ℂ, algebraMap ℂ κ z ∈ V := fun z => hOV' _ (hO.const_mem z)
  obtain ⟨R, hcR, hft, hTR, hRV, hRn, hRi, hRf⟩ := _root_.GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring V T hcV hTV hfracT
  haveI := hRn
  haveI := hRi
  haveI := hRf
  have hadjR : ∀ x ∈ Algebra.adjoin ℂ (T : Set κ), x ∈ R := by
    let R' : Subalgebra ℂ κ := { R with algebraMap_mem' := hcR }
    have : Algebra.adjoin ℂ (T : Set κ) ≤ R' := Algebra.adjoin_le (fun x hx => hTR x hx)
    exact fun x hx => this hx

  let ι : R →+* V :=
    { toFun := fun r => ⟨r, hRV r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let P : Ideal R := (IsLocalRing.maximalIdeal V).comap ι
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have haT : (a : κ) ∈ T := by simp [T, haY]
  let a' : R := ⟨a, hTR _ haT⟩
  have ha'0 : a' ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
  have ha'P : a' ∈ P := hVnu a (hY ▸ Submodule.subset_span haY) _
  obtain ⟨Q, hQp, haQ, hQP, hQ0, hmin⟩ := exists_minimal_prime_le P a' ha'0 ha'P
  haveI := hQp
  obtain ⟨W, hWd, hRW, hinvW, hninvW, hWfrac⟩ := _root_.GlobalTheory.exists_dvr_localization_of_minimal_prime R Q hQ0 hmin

  have hcW : ∀ z : ℂ, algebraMap ℂ κ z ∈ W := fun z => hRW ⟨_, hcR z⟩
  have hWft : ((algebraMap ℂ κ).codRestrict W hcW).EssFiniteType :=
    GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div κ (algebraMap ℂ κ) R hcR W hcW
      (fun x hx => hRW ⟨x, hx⟩) hft (fun e he => by
        obtain ⟨b, s, hs, rfl⟩ := hWfrac e he
        exact ⟨b, b.2, s, s.2, hinvW s hs, rfl⟩)
  let F : Place (algebraMap ℂ κ) := ⟨W, hcW, hWd, hWft⟩
  have hOW : ∀ o ∈ O, o ∈ W := by
    intro o ho
    obtain ⟨b, hb, d, hd, hd0, hdi, rfl⟩ := hGfrac o ho
    let d' : R := ⟨d, hadjR _ (hGT hd)⟩
    have hd'Q : d' ∉ Q := by
      intro hdQ
      have hm : ι d' ∈ IsLocalRing.maximalIdeal V := hQP hdQ
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
      apply hm
      exact IsUnit.of_mul_eq_one (⟨d⁻¹, hOV' _ hdi⟩ : V) (Subtype.ext (mul_inv_cancel₀ hd0))
    rw [div_eq_mul_inv]
    exact mul_mem (hRW ⟨b, hadjR _ (hGT hb)⟩) (hinvW d' hd'Q)
  refine ⟨F, hOW, ?_⟩
  intro f hf hf0
  have hspan : ∀ x ∈ Submodule.span O (Y : Set O), ∃ w ∈ W, ((x : O) : κ) = a * w := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      refine ⟨(y : κ) / a, hRW ⟨_, hTR _ ?_⟩, ?_⟩
      · simp only [T, Finset.mem_union, Finset.mem_image]
        exact Or.inr ⟨y, hy, rfl⟩
      · field_simp
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, ex⟩ := hx
      obtain ⟨w', hw', ey⟩ := hy
      exact ⟨w + w', add_mem hw hw', by push_cast; rw [ex, ey]; ring⟩
    | smul c x _ hx =>
      obtain ⟨w, hw, ex⟩ := hx
      refine ⟨c * w, mul_mem (hOW _ c.2) hw, ?_⟩
      rw [smul_eq_mul, Subring.coe_mul, ex]; ring
  rw [← hY] at hf
  obtain ⟨w, hw, efw⟩ := hspan f hf
  have hw0 : w ≠ 0 := by rintro rfl; exact hf0 (by rw [efw, mul_zero])
  have haW : (a : κ) ∈ W := hRW a'
  have hainv : (a : κ)⁻¹ ∉ W := hninvW a' haQ ha'0
  have h1 : 0 ≤ F.ord (a : κ) := (F.ord_nonneg_iff ha0).2 haW
  have h2 : ¬ 0 ≤ F.ord ((a : κ)⁻¹) := fun h => hainv ((F.ord_nonneg_iff (inv_ne_zero ha0)).1 h)
  have h3 : 0 ≤ F.ord w := (F.ord_nonneg_iff hw0).2 hw
  rw [F.ord_inv] at h2
  rw [efw, F.ord_mul ha0 hw0]
  omega

end GlobalTheory.DvrDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem gp_comp {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (h : X ⟶ Sp R) :
    gp X ≫ h = spMap (cst h) := by
  apply ext_of_isAffine
  rw [gp, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  ext a
  have e : CommRingCat.ofHom (cst h) =
      (Scheme.ΓSpecIso _).inv ≫ h.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := rfl
  simp [e]

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (hd : ringKrullDim O ≤ 1) {a : O} (ha : a ∈ maximalIdeal O) (v : K) :
    ∃ N : ℕ, ∃ c : O, algebraMap O K a ^ N * v = algebraMap O K c := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) v
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  haveI : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hrad : a ∈ (Ideal.span {y}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hne : J ≠ ⊥ := fun h => hy0 (by
      have := hJ (Ideal.mem_span_singleton_self y); rw [h] at this; exact (Submodule.mem_bot _).1 this)
    have : J.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot J hne
    rw [IsLocalRing.eq_maximalIdeal this]; exact ha
  obtain ⟨N, hN⟩ := hrad
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hN
  refine ⟨N, c * x, ?_⟩
  have hy' : algebraMap O K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  rw [← map_pow, ← hc, map_mul, map_mul]
  field_simp

theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {z : X} {g : X.functionField} (h : RegAt z g) (n : ℕ) :
    RegAt z (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one z).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem eq_of_specializes {X : Scheme.{0}} [IsIntegral X] {z w : X} (hd : ringKrullDim (X.presheaf.stalk z) ≤ 1)
    (hwz : w ⤳ z) (hw : w ≠ genericPoint X) : w = z := by
  by_contra hne
  have hw' : w ∈ Set.range (X.fromSpecStalk z) := by rw [Scheme.range_fromSpecStalk]; exact hwz
  obtain ⟨p, rfl⟩ := hw'
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec X).specializes trivial
  obtain ⟨q, hq⟩ := hη
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hp : p.asIdeal = ⊥ := by
    by_contra h
    haveI := p.isPrime
    have hm := Ideal.isMaximal_of_isPrime_of_ne_bot p.asIdeal h
    have : p = closedPoint _ := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    apply hne; rw [this, Scheme.fromSpecStalk_closedPoint]
  have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
    show p.asIdeal ≤ q.asIdeal; rw [hp]; exact bot_le)
  have h1 : X.fromSpecStalk z p ⤳ genericPoint X := hq ▸ hpq.map (X.fromSpecStalk z).continuous
  have h2 : genericPoint X ⤳ X.fromSpecStalk z p := (genericPoint_spec X).specializes trivial
  exact hw (h1.antisymm h2).eq

theorem θ_comp_c₀ (σ : Setup) (x : Sp σ.R) :
    (σ.θ x).comp σ.c₀ = (cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl₁, hl₂⟩ := σ.hθ x
  have w := (σ.cart x).w
  simp only [Category.assoc] at w
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    calc spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀ := by
          simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
      _ = l ≫ σ.φ x ≫ σ.A.hom ≫ awayMap σ.f := by
          rw [Setup.c₀, ← gp_comp, ← Category.assoc, ← hl₂]; simp only [Category.assoc]
      _ = l ≫ (σ.V x).ι ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [w]
      _ = gp _ ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [← Category.assoc l, hl₁]
      _ = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
          rw [← Category.assoc, gp_comp]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 e)
  simpa using e'

theorem zeroAt_cst {R : Type} [CommRing R] {Y : Scheme.{0}} [IsIntegral Y] (h : Y ⟶ Sp R) (r : R) (z : Y)
    (hz : r ∈ (h z).asIdeal) : ZeroAt z (cst h r) := by
  rw [zeroAt_iff]
  refine ⟨regAt_fnOf (U := ⊤) trivial trivial _, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (x := z) (U := ⊤) trivial (gen_mem (x := z) trivial) _).1 hu
  rw [RingHom.comp_apply, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  exact h1 hz

theorem exists_pow_mul_mem_codimOne_regular_chart : ∀ (σ : Setup) (x : Sp σ.R) (u : σ.A.left.functionField), ∃ m : ℕ, σ.c₀ σ.f ^ m * u ∈ σ.W x := by
  intro σ x u
  haveI := (σ.C x).semi
  haveI : Smooth (σ.C x).G.hom := IsSemiAbelian.smooth
  haveI : QuasiCompact (σ.C x).G.hom := IsSemiAbelian.quasiCompact
  haveI : IsLocallyNoetherian (σ.C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom
  haveI : CompactSpace (σ.C x).G.left := QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom
  haveI : IsNoetherian (σ.C x).G.left := {}
  haveI : TopologicalSpace.NoetherianSpace (σ.C x).G.left := IsNoetherian.noetherianSpace
  have hg : σ.θ x (σ.c₀ σ.f) = cst (σ.C x).G.hom (σ.ρ x σ.f) := RingHom.congr_fun (θ_comp_c₀ σ x) σ.f
  set g := cst (σ.C x).G.hom (σ.ρ x σ.f)
  set v := σ.θ x u
  let P : Set (σ.C x).G.left := {z | ¬ RegAt z v}
  have hP : IsClosed P := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hzU, a, ha⟩ := RegAt.exists_fnOf (not_not.1 hz)
    exact ⟨U, fun y hy => not_not.2 (ha ▸ regAt_fnOf hy _ a), U.isOpen, hzU⟩
  obtain ⟨S, hS, hirr, hPS⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible ⟨P, hP⟩
  let F : Set (σ.C x).G.left := ⋃ t ∈ S, {w | IsGenericPoint w (t : Set _)}
  have hF : F.Finite := hS.biUnion fun t _ => Set.Subsingleton.finite fun a ha b hb => ha.eq hb
  have hPt : ∀ t ∈ S, (t : Set (σ.C x).G.left) ⊆ P := fun t ht => by
    have : t ≤ sSup S := le_sSup ht
    rw [← hPS] at this
    exact this
  let C : TopologicalSpace.Closeds (σ.C x).G.left :=
    ⟨⋃ t ∈ S, (t : Set _), hS.isClosed_biUnion fun t _ => t.isClosed⟩
  have hPC : P ⊆ (C : Set _) := by
    have : sSup S ≤ C := sSup_le fun t ht y hy => Set.mem_iUnion₂.2 ⟨t, ht, hy⟩
    rw [← hPS] at this
    exact this
  have key : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → z ∈ P → z ∈ F := by
    intro z hz hzP
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 (hPC hzP)
    have hw : IsGenericPoint (hirr t ht).genericPoint (t : Set _) := by
      have := (hirr t ht).isGenericPoint_genericPoint_closure
      rwa [t.isClosed.closure_eq] at this
    have hwP : (hirr t ht).genericPoint ∈ P := hPt t ht hw.mem
    have hwη : (hirr t ht).genericPoint ≠ genericPoint _ := fun h => hwP (h ▸ regAt_genericPoint v)
    have := eq_of_specializes hz.1.le (hw.specializes hzt) hwη
    exact Set.mem_iUnion₂.2 ⟨t, ht, this ▸ hw⟩
  have hpt : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → ∃ N : ℕ, RegAt z (g ^ N * v) := by
    intro z hz
    obtain ⟨a, ha, hag⟩ := zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2
    obtain ⟨N, c, hc⟩ := exists_pow_mul_mem hz.1.le ha v
    exact ⟨N, c, by rw [← hc, hag]⟩
  classical
  let N : (σ.C x).G.left → ℕ := fun z => if h : Vert (σ.C x).G.hom (σ.ρ x σ.f) z then Classical.choose (hpt z h) else 0
  refine ⟨hF.toFinset.sup N, fun z hz => ?_⟩
  have hgz : RegAt z g := (zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2).regAt
  rw [map_mul, map_pow, hg]
  by_cases hzP : z ∈ P
  · have hle : N z ≤ hF.toFinset.sup N := Finset.le_sup (hF.mem_toFinset.2 (key z hz hzP))
    have hN : RegAt z (g ^ N z * v) := by
      simp only [N, dif_pos hz]; exact Classical.choose_spec (hpt z hz)
    rw [← Nat.sub_add_cancel hle, pow_add, _root_.mul_assoc]
    exact (regAt_pow hgz _).mul hN
  · exact (regAt_pow hgz _).mul (not_not.1 hzP)

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCyclotomicAwayToFieldPrimitiveRoot
section
open GlobalTheory.SiegelTor

namespace GlobalTheory.CycLift

theorem exists_hom_to_field : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
    ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  intro M hM K _ y hy hMK
  obtain ⟨p, hcp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharZero (WittVector p K) := by
      obtain ⟨q, hq⟩ := CharP.exists (WittVector p K)
      have h1 : ((q : ℕ) : K) = 0 := by
        have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (CharP.cast_eq_zero (WittVector p K) q)
        rwa [map_natCast, map_zero] at this
      have h2 : p ∣ q := (CharP.cast_eq_zero_iff K p q).1 h1
      rcases CharP.char_is_prime_or_zero (WittVector p K) q with h | h
      · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp h).1 h2
        subst h3
        exact absurd (CharP.cast_eq_zero (WittVector p K) p) (WittVector.p_nonzero p K)
      · subst h
        exact CharP.charP_to_charZero _
    let π : WittVector p K →+* K := WittVector.constantCoeff
    have hcc : ∀ x : K, π (WittVector.teichmuller p x) = x := fun x => by simp [π]
    have hu : IsPrimitiveRoot (WittVector.teichmuller p y) M :=
      ⟨by rw [← map_pow, hy.pow_eq_one, map_one], fun l hl => hy.dvd_of_pow_eq_one l (by
        have := congrArg π hl
        rwa [map_pow, hcc, map_one] at this)⟩
    have hnV : IsUnit (M : WittVector p K) := by
      refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
      have : π (M : WittVector p K) ≠ 0 := by rw [map_natCast]; exact hMK.ne_zero
      exact this
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hu hnV
    exact ⟨π.comp f, by rw [RingHom.comp_apply, hfζ, hcc]⟩
  · haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hy hMK
    exact ⟨f, hfζ⟩

end GlobalTheory.CycLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSFamPrimePowSq
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

theorem exists_sFam_primePow_sq :
    ∀ g l : ℕ, 1 ≤ g → l.Prime → Odd l →
      ∃ j : ℕ, 1 ≤ j ∧ Nonempty (SFam g ((l ^ j) ^ 2) (zetaAway ((l ^ j) ^ 2))) := by
  intro g l hg hl _hodd
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam hLaws hLaws2 GlobalTheory.Moduli.cube_of_isLB
    GlobalTheory.thetaUnifAV_closed g l hg hl _hodd

  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have hn : (l ^ max j₀ 1) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl.ne_zero)

  have key := hj₀ (max j₀ 1) (le_max_left _ _) (cycAway ((l ^ max j₀ 1) ^ 2)) (cycBase hn)
    (cycAway ((l ^ max j₀ 1) ^ 2)).subtype (arBase_cycAway _ hn)
  rwa [cycBase_ζ hn] at key

end GlobalTheory.SiegelTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendIntegralPadicEvaluationGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ValExt

theorem exists_ext_centred : ∀ (p : ℕ) [Fact p.Prime] (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)] (𝔷 : Ideal B), Function.Injective (algebraMap A B) → (∀ b : B, (∀ σ : B ≃ₐ[A] B, σ b = b) → b ∈ Set.range (algebraMap A B)) → 𝔷.IsMaximal → ∀ ev : A →+* PadicAlgCl p, (∀ a, ‖ev a‖ ≤ 1) → (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < 1) → ∃ ev' : B →+* PadicAlgCl p, (∀ a, ev' (algebraMap A B a) = ev a) ∧ (∀ b, ‖ev' b‖ ≤ 1) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.NormExtensionBound.main
  | exact _root_.GlobalTheory.NormExtensionBound.main
  | (apply _root_.GlobalTheory.NormExtensionBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormExtensionBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormExtensionBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormExtensionBound.main ..)

end GlobalTheory.ValExt
end

