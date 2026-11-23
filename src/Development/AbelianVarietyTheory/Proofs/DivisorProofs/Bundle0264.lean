module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0237
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCompletionFlat
section
open IsLocalRing

namespace GlobalTheory.RegularCompletionPackage

theorem exists_regular_completion :
    ∀ (R₁ Ω : Type) [CommRing R₁] [IsRegularLocalRing R₁] [Field Ω] (u : R₁ →+* Ω),
      RingHom.ker u = maximalIdeal R₁ →
      ∃ (C : Type) (_ : CommRing C) (_ : IsRegularLocalRing C) (c : R₁ →+* C) (uC : C →+* Ω),
        c.Flat ∧ (maximalIdeal R₁).map c = maximalIdeal C ∧ IsAdicComplete (maximalIdeal C) C ∧
        RingHom.ker uC = maximalIdeal C ∧ uC.comp c = u := by
  intro R₁ Ω _ _ _ u hu
  set C := AdicCompletion (maximalIdeal R₁) R₁
  haveI : IsRegularLocalRing C := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R₁
  have hbij := AdicCompletion.residueField_map_bijective_of_fg (R := R₁)
    (maximalIdeal R₁).fg_of_isNoetherianRing
  let e : ResidueField R₁ ≃+* ResidueField C :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap R₁ C)) hbij
  let ub : ResidueField R₁ →+* Ω := Ideal.Quotient.lift (maximalIdeal R₁) u
    (fun a ha => by rw [← RingHom.mem_ker, hu]; exact ha)
  let uC : C →+* Ω := (ub.comp e.symm.toRingHom).comp (residue C)
  have hcomp : uC.comp (algebraMap R₁ C) = u := by
    ext r
    simp only [uC, RingHom.comp_apply]
    have : residue C (algebraMap R₁ C r) = e (residue R₁ r) := by
      simp [e, ResidueField.map_residue]
    rw [this]
    simp [ub]
    rfl
  refine ⟨C, inferInstance, inferInstance, algebraMap R₁ C, uC,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
    (AdicCompletion.maximalIdeal_eq_map).symm, inferInstance, ?_, hcomp⟩
  ext x
  rw [RingHom.mem_ker]
  simp only [uC, RingHom.comp_apply]
  constructor
  · intro h
    have h1 : e.symm (residue C x) = 0 := (injective_iff_map_eq_zero ub).1 ub.injective _ h
    have h2 : residue C x = 0 := by simpa using h1
    simpa [residue_eq_zero_iff] using h2
  · intro h
    rw [(residue_eq_zero_iff x).2 h]
    simp

end GlobalTheory.RegularCompletionPackage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomPadicAlgClNeZero
section
open IsLocalRing

namespace GlobalTheory.CurvePoint

theorem exists_ringHom_padicAlgCl_ne_zero : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  intro B _ _ _ _ _ hfin h hh

  set p := ringChar (ResidueField B) with hpdef
  have hp0 : p ≠ 0 := by
    intro h0
    haveI : CharP (ResidueField B) 0 := by rw [← h0]; exact ringChar.charP _
    haveI : CharZero (ResidueField B) := CharP.charP_to_charZero _
    exact not_finite (ResidueField B)
  have hp : p.Prime := (CharP.char_is_prime_or_zero (ResidueField B) p).resolve_right hp0
  haveI hF : Fact p.Prime := ⟨hp⟩
  have hpm : (p : B) ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hpB : (p : B) ≠ 0 := Nat.cast_ne_zero.2 hp0

  obtain ⟨q, hq, hxq, hmax⟩ := GlobalTheory.T.exists_prime_not_mem_forall_gt_eq_maximalIdeal' B (h * p) (mul_ne_zero hh hpB) (Ideal.mul_mem_left _ _ hpm)
  have hhq : h ∉ q := fun hq' => hxq (Ideal.mul_mem_right _ _ hq')
  have hpq : (p : B) ∉ q := fun hq' => hxq (Ideal.mul_mem_left _ _ hq')
  have hqm : q ≤ maximalIdeal B := le_maximalIdeal hq.ne_top
  set C := B ⧸ q
  haveI : Nontrivial C := Ideal.Quotient.nontrivial_iff.2 hq.ne_top
  haveI : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let π : B →+* C := Ideal.Quotient.mk q
  have hπm : ∀ b ∈ maximalIdeal B, π b ∈ maximalIdeal C := by
    intro b hb hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h1 : b * c' - 1 ∈ q := Ideal.Quotient.eq.1 (by simpa [π] using hc)
    have h2 : b * c' - 1 ∈ maximalIdeal B := hqm h1
    have h3 : b * c' ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hb
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ h3 h2))
  have hmC : ∀ c ∈ maximalIdeal C, ∃ b ∈ maximalIdeal B, π b = c := by
    intro c hc
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b, fun hb => hc ?_, rfl⟩
    exact hb.map π
  have hfinC : Finite (ResidueField C) := by
    let f : ResidueField B → ResidueField C :=
      Ideal.Quotient.lift (maximalIdeal B) ((residue C).comp π) (fun b hb => by
        rw [RingHom.comp_apply, residue_eq_zero_iff]; exact hπm b hb)
    refine Finite.of_surjective f ?_
    intro y
    obtain ⟨c, rfl⟩ := residue_surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨residue B b, rfl⟩
  have hpC : (p : C) ≠ 0 := by
    rw [← map_natCast π, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hpq
  have hpmC : (p : C) ∈ maximalIdeal C := by rw [← map_natCast π]; exact hπm _ hpm
  have hdim : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C := by
    intro P hP hP0
    refine le_antisymm (le_maximalIdeal hP.ne_top) ?_
    have hlt : q < P.comap π := by
      refine lt_of_le_of_ne (fun b hb => ?_) (fun he => hP0 ?_)
      · show π b ∈ P; rw [Ideal.Quotient.eq_zero_iff_mem.2 hb]; exact P.zero_mem
      · rw [eq_bot_iff]; intro c hc
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        have : b ∈ q := he ▸ hc
        exact (Submodule.mem_bot _).2 (Ideal.Quotient.eq_zero_iff_mem.2 this)
    have hc := hmax _ (Ideal.comap_isPrime π P) hlt
    intro c hc'
    obtain ⟨b, hb, rfl⟩ := hmC c hc'
    have : b ∈ P.comap π := hc ▸ hb
    exact this

  obtain ⟨N, hN⟩ : ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hle, hP⟩ => ?_
    have hP0 : P ≠ ⊥ := fun h0 => hpC (by rw [h0] at hle; exact (Submodule.mem_bot _).1 (hle (Ideal.mem_span_singleton_self _)))
    exact (hdim P hP hP0).ge
  obtain ⟨D, _, _, _, hDfin, ι, hι⟩ := _root_.GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain p C hfinC hpC hpmC hdim
  have hpD : (p : D) ≠ 0 := by
    rw [← map_natCast ι]; exact fun h0 => hpC (hι (by rw [h0, map_zero]))
  obtain ⟨φ, hφ, hφ1⟩ := _root_.GlobalTheory.PadicEmb.exists_embedding p D hpD
  refine ⟨p, hF, (φ.comp ι).comp π, fun b => hφ1 _, fun b hb => ?_, ?_⟩
  · have hc := hπm b hb
    have hcN : π b ^ N ∈ Ideal.span {(p : C)} := hN (Ideal.pow_mem_pow hc N)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hcN
    have key : ‖(φ.comp ι) (π b)‖ ^ N < 1 ^ N := by
      rw [← norm_pow, ← map_pow, ← hd, map_mul, norm_mul, one_pow, map_natCast]
      calc ‖(φ.comp ι) d‖ * ‖(p : PadicAlgCl p)‖ ≤ 1 * ‖(p : PadicAlgCl p)‖ :=
            mul_le_mul_of_nonneg_right (hφ1 _) (norm_nonneg _)
        _ < 1 := by
          rw [one_mul]
          have e : ((p : ℚ_[p]) : PadicAlgCl p) = (p : PadicAlgCl p) := by simp
          rw [← e, norm_algebraMap']; exact Padic.norm_p_lt_one
    exact lt_of_pow_lt_pow_left₀ N zero_le_one key
  · intro h0
    apply hhq
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hι (hφ (by simpa using h0))

end GlobalTheory.CurvePoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftBasicOpenPairAgree
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Pair

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) =
      x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩

theorem chartHom_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by
  subst e; rfl

def strHom {R : Type} [CommRing R] (X : Over (Sp R)) (V : X.left.Opens) : R →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appLE ⊤ V (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)).hom

theorem fromSpec_over {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = spMap (strHom X V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Sp R)) hV
    (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]; rfl

theorem chartHom_comp_strHom {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens}
    (hV : IsAffineOpen V) {S : Type} [CommRing S] (f : R →+* S) (u : Sp S ⟶ X.left) (hu : u ⁻¹ᵁ V = ⊤)
    (hf : u ≫ X.hom = spMap f) : (chartHom V u hu).comp (strHom X V) = f := by
  have e : spMap ((chartHom V u hu).comp (strHom X V)) = spMap f := by
    rw [spMap_comp', ← fromSpec_over X hV, ← Category.assoc, chart_rebuild, hf]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem smooth_strHom {R : Type} [CommRing R] (X : Over (Sp R)) [Smooth X.hom] {V : X.left.Opens}
    (hV : IsAffineOpen V) : (strHom X V).Smooth := by
  have h1 : RingHom.Smooth (X.hom.appLE ⊤ V le_top).hom :=
    X.hom.smooth_appLE (isAffineOpen_top (Sp R)) hV le_top
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  exact h2.comp h1

theorem awayMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (c : R) : Function.Surjective (Localization.awayMap π c) :=
  (IsLocalization.Away.map_surjective_iff _ _ π c).2 fun y =>
    let ⟨x, hx⟩ := hπ y; ⟨x, 0, by simp [hx]⟩

theorem ker_awayMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    RingHom.ker (Localization.awayMap π c) = (RingHom.ker π).map (algebraMap R (Localization.Away c)) := by
  exact IsLocalization.ker_map (S := Localization.Away c) (Localization.Away (π c)) π
    (M := Submonoid.powers c) (Submonoid.map_powers π c)

theorem ker_awayMap_sq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hsq : RingHom.ker π ^ 2 = ⊥) (c : R) : RingHom.ker (Localization.awayMap π c) ^ 2 = ⊥ := by
  rw [ker_awayMap, ← Ideal.map_pow, hsq, Ideal.map_bot]

theorem awayMap_comp_algebraMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    (Localization.awayMap π c).comp (algebraMap R (Localization.Away c)) =
      (algebraMap R₀ (Localization.Away (π c))).comp π :=
  IsLocalization.map_comp _

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem red_comp {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) {Y : Scheme.{0}} (g₀ : Sp R₀ ⟶ Y)
    (c d : R) (hcd : c ∣ d) (e : Sp (Localization.Away c) ⟶ Y)
    (he : spMap (Localization.awayMap π c) ≫ e = spMap (algebraMap R₀ (Localization.Away (π c))) ≫ g₀)
    (r : Localization.Away c →+* Localization.Away d)
    (hr : r.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away d)) :
    spMap (Localization.awayMap π d) ≫ spMap r ≫ e =
      spMap (algebraMap R₀ (Localization.Away (π d))) ≫ g₀ := by
  have hu : IsUnit (algebraMap R₀ (Localization.Away (π d)) (π c)) :=
    isUnit_of_dvd_unit (map_dvd _ (map_dvd π hcd)) (IsLocalization.Away.algebraMap_isUnit (π d))
  let h : Localization.Away (π c) →+* Localization.Away (π d) := IsLocalization.Away.lift (π c) hu
  have e1 : (Localization.awayMap π d).comp r = h.comp (Localization.awayMap π c) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [RingHom.comp_assoc, hr, awayMap_comp_algebraMap, RingHom.comp_assoc, awayMap_comp_algebraMap,
      ← RingHom.comp_assoc, IsLocalization.Away.lift_comp]
  rw [← Category.assoc, ← spMap_comp', e1, spMap_comp', Category.assoc, he, ← Category.assoc,
    ← spMap_comp', IsLocalization.Away.lift_comp]

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem equiv_restrict {R : Type} [CommRing R] (a b : R)
    (eP : Localization.Away (a * b) ≃ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b))
    (ρ : Localization.Away a →+* Localization.Away (a * b))
    (hρ : ρ.comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)))
    (y : Localization.Away a) :
    eP (ρ y) = algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) y := by
  have e : (eP.toAlgHom : Localization.Away (a * b) →+* _).comp ρ =
      algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    rw [RingHom.comp_assoc, hρ, eP.toAlgHom.comp_algebraMap]
    exact IsScalarTower.algebraMap_eq _ _ _
  exact RingHom.congr_fun e y

theorem exists_awayEquiv {R : Type} [CommRing R] (a b : R) :
    Nonempty (Localization.Away (a * b) ≃ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b)) :=
  ⟨IsLocalization.algEquiv (Submonoid.powers (a * b)) _ _⟩

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem comp_over {Y : Scheme.{0}} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (e : Sp B ⟶ Y)
    (p : Y ⟶ Sp A) (f : A →+* B) (he : e ≫ p = spMap f) (r : B →+* C) (g : A →+* C) (hr : r.comp f = g) :
    (spMap r ≫ e) ≫ p = spMap g := by
  rw [Category.assoc, he, ← spMap_comp', hr]

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue


open GlobalTheory.SecGlue.Pair in
set_option maxHeartbeats 1000000 in
theorem exists_pair_lift_comb : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  intro R R₀ _ _ π hπ hsq X hX g₀ hg₀ a b V hV ea hea hea₀ heaV eb heb heb₀
  haveI := hX
  letI : Algebra R Γ(X.left, V) := (strHom X V).toAlgebra
  haveI : Algebra.Smooth R Γ(X.left, V) := smooth_strHom X hV

  have hρ : (IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b).comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayRight_eq a b)
  have hρ' : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a).comp (algebraMap R (Localization.Away b)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayLeft_eq b a)
  generalize IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b = ρ at hρ ⊢
  generalize IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a = ρ' at hρ' ⊢
  have hred : spMap (Localization.awayMap π (a * b)) ≫ spMap ρ' ≫ eb =
      spMap (Localization.awayMap π (a * b)) ≫ spMap ρ ≫ ea :=
    (red_comp π g₀ b (a * b) (dvd_mul_left b a) eb heb₀ ρ' hρ').trans
      (red_comp π g₀ a (a * b) (dvd_mul_right a b) ea hea₀ ρ hρ).symm
  have h2 : (spMap ρ ≫ ea) ⁻¹ᵁ V = ⊤ := preimage_spMap_comp_eq_top ρ heaV
  have hbV : (spMap ρ' ≫ eb) ⁻¹ᵁ V = ⊤ :=
    (_root_.GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero (Localization.Away (a * b)) (Localization.Away (π (a * b))) (Localization.awayMap π (a * b))
      (awayMap_surjective π hπ _) (ker_awayMap_sq π hsq _) X.left (spMap ρ' ≫ eb) (spMap ρ ≫ ea) hred V).trans h2

  let φ : Γ(X.left, V) →ₐ[R] Localization.Away a :=
    { chartHom V ea heaV with
      commutes' := fun r => RingHom.congr_fun (chartHom_comp_strHom X hV _ ea heaV hea) r }

  obtain ⟨eP⟩ := exists_awayEquiv a b
  have hePc : (eP.toAlgHom : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
      (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) :=
    eP.toAlgHom.comp_algebraMap
  have heP := equiv_restrict a b eP ρ hρ
  have heb' : (spMap ρ' ≫ eb) ≫ X.hom = spMap (algebraMap R (Localization.Away (a * b))) :=
    comp_over eb X.hom _ heb ρ' _ hρ'
  let ψ : Γ(X.left, V) →ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b) :=
    { (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp (chartHom V (spMap ρ' ≫ eb) hbV) with
      commutes' := fun r => by
        show eP (chartHom V (spMap ρ' ≫ eb) hbV (strHom X V r)) = _
        rw [← RingHom.comp_apply, chartHom_comp_strHom X hV _ _ hbV heb', AlgEquiv.commutes] }
  have hJ : RingHom.ker (Localization.awayMap π a) ^ 2 = ⊥ := ker_awayMap_sq π hsq a
  have hcond : ∀ x, ψ x - algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) ∈
      (RingHom.ker (Localization.awayMap π a)).map (algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))) := by
    intro x
    have hd : chartHom V (spMap ρ' ≫ eb) hbV x - chartHom V (spMap ρ ≫ ea) h2 x ∈
        RingHom.ker (Localization.awayMap π (a * b)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero,
        ← chartHom_spMap_comp V _ _ hbV (preimage_spMap_comp_eq_top _ hbV),
        ← chartHom_spMap_comp V _ _ h2 (preimage_spMap_comp_eq_top _ h2)]
      exact RingHom.congr_fun (chartHom_congr V hred _ _) x
    rw [ker_awayMap] at hd
    have h3 := Ideal.mem_map_of_mem (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)) hd
    rw [Ideal.map_map, show (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
        (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) from
        RingHom.ext fun r => eP.commutes r, map_sub] at h3
    rw [ker_awayMap, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have e2 : algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) =
        eP (chartHom V (spMap ρ ≫ ea) h2 x) := by
      rw [chartHom_spMap_comp V ρ ea heaV h2 x, heP]
      rfl
    rw [e2]
    exact h3
  obtain ⟨N₀, hN⟩ := _root_.GlobalTheory.SecGlue.exists_sqZero_extend_pow R Γ(X.left, V) (Localization.Away a) (RingHom.ker (Localization.awayMap π a)) hJ (algebraMap R (Localization.Away a) b) φ ψ hcond
  refine ⟨N₀, fun N hN' => ?_⟩
  obtain ⟨χ, hχJ, hχ⟩ := hN N hN'
  have htop := fromSpec_comp_top hV (χ : Γ(X.left, V) →+* Localization.Away a)
  refine ⟨spMap (χ : Γ(X.left, V) →+* Localization.Away a) ≫ hV.fromSpec, ?_, ?_, htop, ?_⟩
  · rw [Category.assoc, fromSpec_over, ← spMap_comp']
    exact congrArg spMap (RingHom.ext fun r => χ.commutes r)
  · rw [← hea₀, ← chart_rebuild hV ea heaV, ← Category.assoc, ← Category.assoc, ← spMap_comp',
      ← spMap_comp']
    refine congrArg (fun f => spMap f ≫ hV.fromSpec) (RingHom.ext fun x => ?_)
    have := hχJ x
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  · refine ⟨h2, preimage_spMap_comp_eq_top ρ htop, fun i => by rw [Matrix.cons_val_fin_one]; exact hbV, fun x => ?_⟩
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rw [chartHom_spMap_comp V ρ _ htop, chartHom_fromSpec hV _ htop, chartHom_spMap_comp V ρ ea heaV]
    apply eP.injective
    rw [map_add (f := _), map_mul, map_sub, map_pow, heP, heP, AlgEquiv.commutes,
      IsScalarTower.algebraMap_apply R (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))]
    exact hχ x

end GlobalTheory.SecGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilteredColimitCohomologyTransportQuasiIso
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem hom_d_apply {C D : AbCx} (φ : C ⟶ D) (i j : ℤ) (x : C.X i) :
    φ.f j (C.d i j x) = D.d i j (φ.f i x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, HomologicalComplex.Hom.comm]

theorem nat_f_apply {N M : CommRingCat.{0} ⥤ AbCx} (ε : N ⟶ M) {A B : CommRingCat.{0}} (g : A ⟶ B) (n : ℤ)
    (x : (N.obj A).X n) : (ε.app B).f n ((N.map g).f n x) = (M.map g).f n ((ε.app A).f n x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, ε.naturality]

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contH_transport_quasiIso : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M), (∀ A, SurjH (ε.app A) ∧ InjH (ε.app A)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro N M ε hε hN J _ _ D c hc n
  obtain ⟨hN1, hN2⟩ := hN J D c hc n
  have nat : ∀ (j : J) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      (ε.app c.pt).f m ((N.map (c.ι.app j)).f m x) = (M.map (c.ι.app j)).f m ((ε.app (D.obj j)).f m x) :=
    fun j m x => nat_f_apply ε (B := c.pt) (c.ι.app j) m x
  have dN : ∀ (j : J) (m m' : ℤ) (x : ((N).obj (D.obj j)).X m),
      (N.map (c.ι.app j)).f m' (((N).obj (D.obj j)).d m m' x) = ((N).obj c.pt).d m m' ((N.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (N).obj c.pt) (N.map (c.ι.app j)) m m' x
  have dM : ∀ (j : J) (m m' : ℤ) (x : ((M).obj (D.obj j)).X m),
      (M.map (c.ι.app j)).f m' (((M).obj (D.obj j)).d m m' x) = ((M).obj c.pt).d m m' ((M.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (M).obj c.pt) (M.map (c.ι.app j)) m m' x
  refine ⟨fun z hz => ?_, fun j w hw ⟨y, hy⟩ => ?_⟩
  · obtain ⟨c', y1, hc', h1⟩ := (hε c.pt).1 n z hz
    obtain ⟨j, w, y2, hw, h2⟩ := hN1 c' hc'
    refine ⟨j, (ε.app (D.obj j)).f n w, y1 + (ε.app c.pt).f (n - 1) y2, ?_, ?_⟩
    · rw [← hom_d_apply, hw, map_zero]
    · rw [← nat, h2, map_add (f := _), h1, map_add (f := _), hom_d_apply]
      abel
  · obtain ⟨c1, y1, hc1, h1⟩ := (hε (D.obj j)).1 n w hw
    have hcz : ((N).obj c.pt).d n (n + 1) ((N.map (c.ι.app j)).f n c1) = 0 := by
      rw [← dN, hc1, map_zero]
    obtain ⟨b, hb⟩ := (hε c.pt).2 n _ hcz ⟨y + (show ((M).obj c.pt).X (n - 1) from (M.map (c.ι.app j)).f (n - 1) y1), by
      rw [nat, h1, map_add (f := _), hy, map_add (f := _), dM]⟩
    obtain ⟨k, f, y2, h2⟩ := hN2 j c1 hc1 ⟨b, hb.symm⟩
    refine ⟨k, f, (ε.app (D.obj k)).f (n - 1) y2 - (M.map (D.map f)).f (n - 1) y1, ?_⟩
    have e1 : w = (ε.app (D.obj j)).f n c1 - ((M).obj (D.obj j)).d (n - 1) n y1 := by
      rw [h1]; abel
    rw [e1, map_sub, map_sub, ← nat_f_apply, h2, hom_d_apply, hom_d_apply]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWeightSpaceProjectiveTensorEqStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_weightSpace_projective_tensor_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  first | (exact @GlobalTheory.WtRank.weight_finrank_eq) | (exact GlobalTheory.WtRank.weight_finrank_eq) | (intros; apply GlobalTheory.WtRank.weight_finrank_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumConjClassesCentralizerOrbitsEqPairOrbitsStatement
section
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_conjClasses_centralizer_orbits_eq_pairOrbits : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) = pairSum F := by
  first | exact @GlobalTheory.OrbitUnfold.finsum_conjClasses_centralizer_orbits | exact GlobalTheory.OrbitUnfold.finsum_conjClasses_centralizer_orbits | (intros; apply GlobalTheory.OrbitUnfold.finsum_conjClasses_centralizer_orbits <;> assumption)
end

