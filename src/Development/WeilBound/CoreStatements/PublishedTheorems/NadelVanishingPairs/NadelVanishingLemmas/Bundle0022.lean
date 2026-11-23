module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorAgreementOnIsomorphism
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.PullDiv

theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem exists_pullCart_agree : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver (t ≫ q) → ∀ (U : Y₀.Opens), IsIso (t ∣_ U) → ∀ H : CartierDiv Y₁, ∃ H₀ : CartierDiv Y₀, ∀ y : Y₁, t y ∈ U → y ∉ (H - pullCart t H₀).supp := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hP U hU H
  classical
  have : CompactSpace Y₁ := compactSpace_of_isProjOver hP
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n (t ≫ q)

  have hinj : ∀ w₁ w₂ : Y₁, t w₁ ∈ U → t w₂ ∈ U → t w₁ = t w₂ → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ e
    have hb : Function.Injective (t ∣_ U) :=
      ((ConcreteCategory.bijective_of_isIso ((t ∣_ U).base))).1
    have := @hb ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ (Subtype.ext ((morphismRestrict_base_coe t U _).trans
      (e.trans (morphismRestrict_base_coe t U ⟨w₂, h₂⟩).symm)))
    exact congrArg Subtype.val this
  let c : Y₀ → ℤ := fun z => if h : ∃ w, t w = z ∧ z ∈ U then H.mult h.choose else 0
  have hc : ∀ w, t w ∈ U → c (t w) = H.mult w := by
    intro w hw
    have h : ∃ w', t w' = t w ∧ t w ∈ U := ⟨w, rfl, hw⟩
    simp only [c, dif_pos h]
    have e := h.choose_spec
    rw [hinj _ _ (by rw [e.1]; exact hw) hw e.1]
  have hsupp : Function.support c ⊆ t '' Function.support H.mult := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      exact ⟨w, by simpa [hc w hw] using hz, rfl⟩
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  have hfin : (Function.support c).Finite := (H.finite_support_mult.image _).subset hsupp
  have hcod : ∀ z, c z ≠ 0 → Order.coheight z = 1 := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      rw [hc w hw] at hz
      rw [← (_root_.GlobalTheory.Discrepancy.MultIso.coheight_eq_and_mult_pullCart Y₀ Y₁ t U hU w hw).1]
      exact CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.exists_cartier_with_multiplicities Y₀ (fun x => AbelianProjective.ufd_stalk q x) c hfin hcod
  refine ⟨H₀, fun y hy hmem => ?_⟩
  have : GlobalTheory.IsNormalScheme Y₁ := (isNormalScheme_iff Y₁).mpr fun x =>
    ⟨inferInstance, have := AbelianProjective.ufd_stalk (t ≫ q) x
      UniqueFactorizationMonoid.instIsIntegrallyClosed⟩
  obtain ⟨z, hzy, hz⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y₁ (H - pullCart t H₀)).2.1 y).1 hmem
  have hzU : t z ∈ U := (hzy.map t.continuous).mem_open U.isOpen hy
  apply hz
  have hm := CartierDiv.mult_add (H - pullCart t H₀) (pullCart t H₀) z
  rw [sub_add_cancel, (_root_.GlobalTheory.Discrepancy.MultIso.coheight_eq_and_mult_pullCart Y₀ Y₁ t U hU z hzU).2 H₀, hH₀, hc z hzU] at hm
  omega

end GlobalTheory.PullDiv
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeDivisorsSncBoundaryStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_prime_divisors_snc_boundary : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ B : Closeds Y, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∃ (r : ℕ) (w : Fin r → Y) (D : Fin r → CartierDiv Y) (σ : ∀ i, (toLB (D i)).Sec), Function.Injective w ∧ (∀ i, (D i).mult (w i) = 1 ∧ ∀ v, v ≠ w i → (D i).mult v = 0) ∧ (∀ v, Order.coheight v = 1 → v ∈ B → ∃ i, v = w i) ∧ RelSnc q n (fun i => toLB (D i)) σ := by
  first | exact @_root_.GlobalTheory.SncComp.relSnc_components | exact _root_.GlobalTheory.SncComp.relSnc_components | (intros; apply _root_.GlobalTheory.SncComp.relSnc_components <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsRoundedDownDivisor
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

private theorem unitAt_of_ord_eq_zero_coheight_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {v : X}
    (hv : Order.coheight v = 1) {h : X.functionField} (h0 : h ≠ 0)
    (hord : Scheme.ord h v = 0) : UnitAt v h := by
  haveI := hufd v
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk v) := krullDimLE_of_coheight_le hv.le
  by_cases hF : IsField (X.presheaf.stalk v)
  · obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk v) h
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨b', hbb'⟩ := hF.mul_inv_cancel hb0
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply h0
      rw [← hab, map_zero, zero_div]
    obtain ⟨a', haa'⟩ := hF.mul_inv_cancel ha0
    refine ⟨a * b', ?_, ?_⟩
    · refine isUnit_iff_exists_inv.mpr ⟨a' * b, ?_⟩
      calc a * b' * (a' * b) = (a * a') * (b * b') := by ring
        _ = 1 := by rw [haa', hbb', one_mul]
    · rw [← hab, map_mul]
      have : algebraMap (X.presheaf.stalk v) X.functionField b *
          algebraMap (X.presheaf.stalk v) X.functionField b' = 1 := by
        rw [← map_mul, hbb', map_one]
      rw [eq_div_iff (fun h' => hb0 (IsFractionRing.injective (X.presheaf.stalk v) X.functionField
        (by rw [h', map_zero]))), mul_assoc, mul_comm _ (algebraMap _ _ b), this, mul_one]
  · haveI : IsDiscreteValuationRing (X.presheaf.stalk v) := by
      have hmax : ∀ I : Ideal (X.presheaf.stalk v), I ≠ ⊥ → I.IsPrime → I.IsMaximal :=
        Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance
      have hne : IsLocalRing.maximalIdeal (X.presheaf.stalk v) ≠ ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hF
      have key := (IsDiscreteValuationRing.TFAE (X.presheaf.stalk v) hF).out 4 1
      exact key.mp ⟨inferInstance, ⟨IsLocalRing.maximalIdeal _, ⟨hne, inferInstance⟩,
        fun P hP => IsLocalRing.eq_maximalIdeal (hmax P hP.1 hP.2)⟩⟩
    have h1 : Scheme.ordHom v hv h = 1 := by
      have := (Scheme.ord_eq_iff hv h0 (n := 0)).mp hord
      simpa using this
    have hmem : h ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk v) (K := X.functionField)) :=
      MonoidHom.mem_mker.mpr h1
    rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    exact ⟨a, ha, rfl⟩

private theorem Scheme_ord_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (v : X) :
    Scheme.ord (1 : X.functionField) v = 0 := by
  have h := Scheme.ord_mul (x := v) (one_ne_zero : (1 : X.functionField) ≠ 0) one_ne_zero
  rw [mul_one] at h
  omega

private theorem Scheme_ord_units_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (v : X) :
    Scheme.ord ((g⁻¹ : (X.functionField)ˣ) : X.functionField) v =
      - Scheme.ord (g : X.functionField) v := by
  have h := Scheme.ord_mul (x := v) g.ne_zero (g⁻¹).ne_zero
  rw [Units.mul_inv, Scheme_ord_one] at h
  omega

private theorem unitAt_of_ord_eq_zero_on_open {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {y : X} (U : X.Opens)
    (hy : y ∈ U) (h : (X.functionField)ˣ)
    (hord : ∀ v ∈ U, Scheme.ord (h : X.functionField) v = 0) : UnitAt y (h : X.functionField) := by
  haveI : GlobalTheory.IsNormalScheme X :=
    ⟨fun x => inferInstance, fun x => by haveI := hufd x; infer_instance⟩
  have key : ∀ g : (X.functionField)ˣ, (∀ v ∈ U, Scheme.ord (g : X.functionField) v = 0) →
      RegAt y (g : X.functionField) := by
    intro g hg
    apply regAt_of_forall_coheight_eq_one
    intro z hz hz1
    exact (unitAt_of_ord_eq_zero_coheight_one hufd hz1 g.ne_zero (hg z (hz.mem_open U.isOpen hy))).regAt
  obtain ⟨a, ha⟩ := key h hord
  obtain ⟨b, hb⟩ := key h⁻¹ (fun v hv => by rw [Scheme_ord_units_inv, hord v hv, neg_zero])
  refine ⟨a, ?_, ha⟩
  have hab : algebraMap (X.presheaf.stalk y) X.functionField (a * b) =
      algebraMap (X.presheaf.stalk y) X.functionField 1 := by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact isUnit_iff_exists_inv.mpr ⟨b, IsFractionRing.injective _ _ hab⟩

theorem exists_cartierDiv_mult_ediv : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Γ : CartierDiv Y) (m : ℕ), ∃ F : CartierDiv Y, (∀ z, F.mult z = Γ.mult z / (m : ℤ)) ∧ F.supp ≤ Γ.supp := by
  intro k _ _ Y _ _ q n _ hproj Γ m
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hufd : ∀ x : Y, UniqueFactorizationMonoid (Y.presheaf.stalk x) :=
    fun x => AbelianProjective.ufd_stalk (K := k) q x
  haveI : NoetherianSpace Y := ModelSum.noetherianSpace_of_isProjOver hproj
  haveI : CompactSpace Y := ⟨NoetherianSpace.isCompact _⟩
  have hsupp : Function.support (fun z => Γ.mult z / (m : ℤ)) ⊆ Function.support Γ.mult := by
    intro z hz h0
    apply hz
    simp only [h0, Int.zero_ediv]
  obtain ⟨F, hF⟩ := CartierDiv.exists_mult_eq_of_locallyFactorial Y hufd
    (fun z => Γ.mult z / (m : ℤ)) ((CartierDiv.finite_support_mult Γ).subset hsupp)
    (fun z hz => CartierDiv.coheight_eq_one_of_mult_ne_zero (hsupp hz))
  refine ⟨F, hF, ?_⟩
  intro x hx
  by_contra hxΓ
  have hΓx : Γ.IsEqn x 1 := by
    by_contra h
    exact hxΓ h
  obtain ⟨W, hxW, hW⟩ := hΓx.exists_nhds
  obtain ⟨g, hg⟩ := F.exists_isEqn x
  obtain ⟨V, hxV, hV⟩ := hg.exists_nhds
  have hunit : UnitAt x (g : Y.functionField) :=
    unitAt_of_ord_eq_zero_on_open hufd (W ⊓ V) ⟨hxW, hxV⟩ g (fun v hv => by
      rw [← (hV v hv.2).mult_eq, hF v, (hW v hv.1).mult_eq, Units.val_one, Scheme_ord_one,
        Int.zero_ediv])
  exact (hg.mem_supp_iff.mp hx) hunit

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KodairaVanishingModPSquaredStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.kodaira_vanishing_mod_p_squared : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • CechPic.pull π (cls (L i) (h.isLB i)) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  first | exact @_root_.GlobalTheory.CharPVanish.charp_of_lift | exact _root_.GlobalTheory.CharPVanish.charp_of_lift | (intros; apply _root_.GlobalTheory.CharPVanish.charp_of_lift <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealLocalMembership
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.MultLoc

theorem isProper_of_isProjOver_nadel_vanishing {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

noncomputable def multHom (z : Y) : CartierDiv Y →+ ℤ :=
  AddMonoidHom.mk' (fun D => D.mult z) (fun D E => CartierDiv.mult_add D E z)

theorem mult_neg' (D : CartierDiv Y) (z : Y) : (-D).mult z = -D.mult z :=
  map_neg (multHom z) D

theorem mult_sub' (D E : CartierDiv Y) (z : Y) : (D - E).mult z = D.mult z - E.mult z :=
  map_sub (multHom z) D E

theorem mult_nsmul' (D : CartierDiv Y) (r : ℕ) (z : Y) : (r • D).mult z = r * D.mult z := by
  rw [← nsmul_eq_mul]; exact map_nsmul (multHom z) r D

end GlobalTheory.MultLoc


open GlobalTheory.MultLoc in
theorem GlobalTheory.Discrepancy.inMultAt_iff_regularAt_logRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (u : X.functionFieldˣ), InMultAt p n η m G x u ↔ ∀ y : Y, s y = x → (-F).RegularAt y (functionFieldMap s (u : X.functionField)) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm hres hF x u
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hres.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.isNormalScheme_of_smooth (s ≫ p)
  haveI : IsProper s := by
    haveI := isProper_of_isProjOver_nadel_vanishing hp
    haveI := isProper_of_isProjOver_nadel_vanishing hres.proj
    exact IsProper.of_comp s p
  set Γ := pullCart s G - m • K with hΓ
  set η' := EtaleKlt.ratPull p s n η with hη'def
  have hη' : η' ≠ 0 := fun h =>
    hη ((_root_.GlobalTheory.EtaleKlt.ratPull_bijective_of_birational k X Y p s hres.bir n).1 (h.trans (map_zero _).symm))
  have hdisc : ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E →
      ∀ g : X.functionFieldˣ, discrep E' η' m (fnPull s g) = discrep E η m g := by
    intro E' E hO g
    simp only [discrep, hη'def, GlobalTheory.BirOrd.formOrd_ratPull_of_over k X Y p s hres.bir E' E hO n η hη,
      _root_.GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective k X Y p s hres.bir E' E hO g]
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have eu : functionFieldMap s (u : X.functionField) = ((fnPull s u : Y.functionFieldˣ) : Y.functionField) := rfl
  constructor
  · intro hu y hy
    rw [eu, _root_.GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes Y (-F) y (fnPull s u)]
    intro z hz
    rw [mult_neg', hF z]
    by_cases hc : Order.coheight z = 1
    · obtain ⟨E', hE'⟩ : ∃ E' : DivOver (s ≫ p), E'.IsAt z :=
        DivOver.exists_isAt_of_coheight_eq_one hc
      obtain ⟨E, hO⟩ := _root_.GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective k X Y p s hres.bir E'
      have hEx : E.Through x := hy ▸ _root_.GlobalTheory.Discrepancy.DivOver.Over.through_image k X Y p s E' E hO y (hE'.through hz)
      obtain ⟨g, hg⟩ := G.exists_isEqn x
      have h1 := hu g hg E hEx
      have h2 : E.ord u = Scheme.ord ((fnPull s u : Y.functionFieldˣ) : Y.functionField) z := by
        rw [← _root_.GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective k X Y p s hres.bir E' E hO u, hE'.ord_eq]
      have hgy : (pullCart s G).IsEqn y (fnPull s g) := isEqn_pullCart s (by rw [hy]; exact hg)
      obtain ⟨V, hV, hgV⟩ := hgy.exists_nhds
      have h3 := GlobalTheory.T.discrepancy_formula_divisor k Y (s ≫ p) n η' hη' K (pullCart s G) m hm hres.div E' z
        (fnPull s g) hE' (hgV z (hz.mem_open V.isOpen hV))
      rw [hdisc E' E hO g, ← hΓ] at h3
      rw [h2, h3] at h1
      set o := Scheme.ord ((fnPull s u : Y.functionFieldˣ) : Y.functionField) z
      have h4 : ((Γ.mult z : ℤ) : ℚ) < ((((o + 1) * m : ℤ)) : ℚ) := by
        push_cast
        have h6 : ((Γ.mult z : ℤ) : ℚ) / m < o + 1 := by rw [neg_div] at h1; linarith
        rwa [div_lt_iff₀ hmq] at h6
      have h5 := Int.ediv_lt_of_lt_mul hmz (by exact_mod_cast h4)
      omega
    · have h0 : Γ.mult z = 0 := by
        by_contra h; exact hc (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
      rw [Scheme.ord_eq_zero_of_coheight_neq_one hc, h0]
      simp
  · intro hR g hg E hE
    obtain ⟨E', hO⟩ := _root_.GlobalTheory.Discrepancy.DivOver.exists_over k X Y p s hres.bir E
    obtain ⟨y, hy, hE'y⟩ := GlobalTheory.T.divisor_center_proper_lift k X Y p s hres.bir inferInstance E' E hO x hE
    obtain ⟨f, hf⟩ := F.exists_isEqn y
    have hreg := hf.neg.regularAt_iff.1 (hR y hy)
    have hord : E'.ord f ≤ E'.ord (fnPull s u) := by
      have h0 : 0 ≤ E'.ord (fnPull s u * f⁻¹) := (E'.ord_nonneg_iff _).2 (hE'y _ hreg)
      rw [E'.ord_mul, E'.ord_inv] at h0
      omega
    set G' := pullCart s G - m • F with hG'
    have hg' : G'.IsEqn y (fnPull s g / f ^ m) :=
      (isEqn_pullCart s (by rw [hy]; exact hg)).sub (hf.nsmul m)
    have hmod : ∀ w, (G' - m • K).mult w = Γ.mult w % m := by
      intro w
      have e : G' - m • K = Γ - m • F := by rw [hG', hΓ]; abel
      rw [e, mult_sub', mult_nsmul', hF w, Int.emod_def]
    have hsupp : (G' - m • K).supp ≤ B := by
      intro w hw
      obtain ⟨z, hzw, hz0⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y (G' - m • K)).2.1 w).1 hw
      refine hres.supp (((GlobalTheory.T.cartier_divisor_mult_characterize Y Γ).2.1 w).2 ⟨z, hzw, fun h0 => hz0 ?_⟩)
      rw [hmod, h0, Int.zero_emod]
    have hcrit := (GlobalTheory.T.klt_of_snc_coefficients k Y (s ≫ p) n η' hη' K G' m B hm hres.div hres.snc hsupp y _ hg'
      E' hE'y).1 fun w _ => by rw [hmod]; exact Int.emod_lt_of_pos _ hmz
    have hd : discrep E' η' m (fnPull s g / f ^ m) = discrep E η m g + E'.ord f := by
      rw [← hdisc E' E hO g]
      simp only [discrep, div_eq_mul_inv, E'.ord_mul, E'.ord_inv, E'.ord_pow]
      push_cast
      field_simp
      ring
    rw [hd] at hcrit
    have h6 : (E'.ord f : ℚ) ≤ E.ord u := by
      rw [← _root_.GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective k X Y p s hres.bir E' E hO u]; exact_mod_cast hord
    linarith
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncGenericSpreadStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_generic_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_spread | exact _root_.GlobalTheory.LogPair.relSnc_spread | (intros; apply _root_.GlobalTheory.LogPair.relSnc_spread <;> assumption)
end

