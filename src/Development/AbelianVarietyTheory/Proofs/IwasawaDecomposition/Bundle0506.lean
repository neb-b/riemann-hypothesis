module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ValuesEqOfCommonPoint
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnCharts
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.SecGlueInt

open GlobalTheory.Reg.ChartCompat (comp_eq away_lift away_inj)
open GlobalTheory.Reg.SecGlue (chart_comp eq_of_fields)

def zchar {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) (t : J → Sˣ) : S := ((∏ i, t i ^ e i : Sˣ) : S)

theorem zchar_mul {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) (t t' : J → Sˣ) :
    zchar e (t * t') = zchar e t * zchar e t' := by
  simp only [zchar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul]

theorem zchar_one {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) : zchar e (1 : J → Sˣ) = 1 := by
  simp [zchar]

theorem zchar_map {J K S T : Type} [Fintype J] [Field K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (φ : S →ₐ[K] T) (e : J → ℤ) (t : J → Sˣ) :
    zchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (zchar e t) := by
  have : (∏ i, Units.map (φ : S →* T) (t i) ^ e i) = Units.map (φ : S →* T) (∏ i, t i ^ e i) := by
    simp only [map_prod, map_zpow]
  unfold zchar
  rw [this]
  rfl


set_option maxHeartbeats 1000000 in
attribute [local instance 1100] Subalgebra.algebra OreLocalization.instAlgebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem chart_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z) (hb : zchar e C.t * b C.Z ∈ C.R) (hb' : zchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = zchar e t * ψ ⟨_, hb⟩ := by
  intro E _ _ _ H Dw l Xo c hev h C C' L _ _ ψ ψ' z z' t hz hz' hbor
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c
  have U := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c
  obtain ⟨g, hg, hopn⟩ := C'.opn C.R L ψ C.y z hz ⟨ψ', z', t⁻¹, hz', (G L).2.2.1 t z z' hbor⟩
  have hg0 : g ≠ 0 := fun e => hg (by rw [e, map_zero])
  have hg1 : C.R.val g ≠ 0 := fun e => hg0 (Subtype.ext e)
  have hZ : C.Z = C'.Z := by
    obtain ⟨ψ0, z0, t0, h1, h2⟩ := hopn (Om C.Z) C.R.val (Ne.isUnit hg1) C.yg C.gen
    exact comp_eq C C' ψ0 z0 t0 h1 h2
  refine ⟨hZ, ?_⟩
  obtain ⟨Z, R, sm, frac, y, yg, tC, gen, bor, mono, opn⟩ := C
  obtain ⟨Z', R', sm', frac', y', yg', tC', gen', bor', mono', opn'⟩ := C'
  dsimp only at *
  subst hZ
  intro e b hb hb'
  let S := Localization.Away g
  let lam : R →ₐ[c.F] S := IsScalarTower.toAlgHom c.F R S
  have hlam : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨mu, hmu⟩ : ∃ m : S →ₐ[c.F] Om Z, m.comp lam = R.val := away_lift g R.val hg1
  obtain ⟨nu, hnu⟩ : ∃ m : S →ₐ[c.F] L, m.comp lam = ψ := away_lift g ψ hg
  have hinj : Function.Injective mu := away_inj g mu (by rw [hmu]; exact Subtype.val_injective)
  obtain ⟨w, hw⟩ := hev.bc R S lam y
  obtain ⟨φ, v, s, hv, hs⟩ := hopn S lam hlam w hw

  obtain ⟨vmu, hvmu⟩ := hev.bc S (Om Z) mu v
  have m1 : FrMap mu w yg := frMap_cancel _ _ _ lam mu y w yg hw (by rw [hmu]; exact gen)
  have b1 := frBorBC _ _ mu s v w vmu yg hs hvmu m1
  have m2 : FrMap (mu.comp φ) y' vmu := frMap_trans _ _ _ φ mu y' v vmu hv hvmu
  have b2 := (G _).2.1 _ _ _ _ _ b1 ((G _).2.1 _ _ _ _ _ ((G _).2.2.1 _ _ _ bor) bor')
  have e1 : mu.comp φ = R'.val := mono' _ _ _ _ _ _ m2 gen' b2
  have e2 : vmu = yg' := (U _ _ R'.val y').1 _ _ (e1 ▸ m2) gen'
  subst e2
  have e3 : tC = tC' * fun i => Units.map (mu : S →* Om Z) (s i) :=
    (G _).2.2.2 _ _ _ _ bor ((G _).2.1 _ _ _ _ _ bor' b1)

  obtain ⟨vnu, hvnu⟩ := hev.bc S L nu v
  have m3 : FrMap nu w z := frMap_cancel _ _ _ lam nu y w z hw (by rw [hnu]; exact hz)
  have b3 := frBorBC _ _ nu s v w vnu z hs hvnu m3
  have m4 : FrMap (nu.comp φ) y' vnu := frMap_trans _ _ _ φ nu y' v vnu hv hvnu
  have b4 := (G _).2.1 _ _ _ _ _ b3 hbor
  have e4 : nu.comp φ = ψ' := mono' _ _ _ _ _ _ m4 hz' b4
  have e5 : vnu = z' := (U _ _ ψ' y').1 _ _ (e4 ▸ m4) hz'
  subst e5
  have e6 : (fun i => Units.map (nu : S →* L) (s i)) * t = 1 :=
    (G _).2.2.2 _ _ _ _ b4 ((G _).1 _)
  have e7 : lam ⟨_, hb⟩ = zchar e s * φ ⟨_, hb'⟩ := by
    apply hinj
    have a1 : mu (lam ⟨_, hb⟩) = zchar e tC * b Z := DFunLike.congr_fun hmu ⟨_, hb⟩
    have a2 : mu (φ ⟨_, hb'⟩) = zchar e tC' * b Z := DFunLike.congr_fun e1 ⟨_, hb'⟩
    have a0 : zchar e tC = zchar e tC' * mu (zchar e s) :=
      (congrArg (zchar e) e3).trans ((zchar_mul _ _ _).trans (congrArg _ (zchar_map mu e s)))
    rw [map_mul, a1, a2]
    linear_combination (b Z) * a0
  have a3 : ψ ⟨_, hb⟩ = nu (zchar e s) * ψ' ⟨_, hb'⟩ := by
    rw [← hnu, ← e4, AlgHom.comp_apply, AlgHom.comp_apply, e7, map_mul]
  have a4 : nu (zchar e s) * zchar e t = 1 := by
    rw [← zchar_map, ← zchar_mul, e6, zchar_one]
  linear_combination (-(zchar e t)) * a3 - (ψ' ⟨_, hb'⟩) * a4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Val

variable {h : GenFrEx Xo c} {e : Ix Dw → ℤ} {b : ∀ Z : Comp Xo c, Om Z}
  (hb : ∀ C : FChart h, zchar e C.t * b C.Z ∈ C.R)

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
def Val {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (C : FChart h) (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S) (t : Ix Dw → Sˣ),
    FrMap ψ C.y z ∧ FrBor t z y ∧ v = zchar e t * ψ ⟨_, hb C⟩

theorem val_unique (hl : EvLaws Xo c) {L : Type} [Field L] [Algebra c.F L] {y : FrPt Xo c L} {v v' : L}
    (h1 : Val hb y v) (h2 : Val hb y v') : v = v' := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨C', ψ', z', t', hz', ht', rfl⟩ := h2
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L
  have := (chart_compat E H Dw l Xo c hl h C C' L ψ ψ' z z' _ hz hz'
    (hmul _ _ _ _ _ ht (hinv _ _ _ ht'))).2 e b (hb C) (hb C')
  rw [this, ← mul_assoc, ← zchar_mul, mul_comm t, mul_inv_cancel_left]

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem val_map (hl : EvLaws Xo c) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {y' : FrPt Xo c T} (hy : FrMap φ y y') {v : S} (h1 : Val hb y v) :
    Val hb y' (φ v) := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨z', hz'⟩ := hl.bc S T φ z
  refine ⟨C, φ.comp ψ, z', _, frMap_trans _ _ _ ψ φ _ _ _ hz hz', frBorBC _ _ φ t z y z' y' ht hz' hy, ?_⟩
  rw [zchar_map, map_mul]; rfl

theorem val_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    (hy : FrBor t y y') {v : S} (h1 : Val hb y v) : Val hb y' (zchar e t * v) := by
  obtain ⟨C, ψ, z, t₀, hz, ht, rfl⟩ := h1
  refine ⟨C, ψ, z, t₀ * t, hz, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c S).2.1 _ _ _ _ _ ht hy, ?_⟩
  rw [zchar_mul]; ring

theorem val_ex (hA : Atlas h) {L : Type} [Field L] [Algebra c.F L] (y : FrPt Xo c L) : ∃ v, Val hb y v := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA L y
  exact ⟨_, C, ψ, z, t, h1, h2, rfl⟩

theorem val_gen (hA : Atlas h) (Z : Comp Xo c) : Val hb (genFr h Z) (b Z) := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA _ (genFr h Z)
  obtain rfl := chart_comp Z C ψ z t h1 h2
  refine ⟨C, C.R.val, C.yg, C.t⁻¹, C.gen, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ C.bor, ?_⟩
  show b C.Z = zchar e C.t⁻¹ * (zchar e C.t * b C.Z)
  rw [← mul_assoc, ← zchar_mul, inv_mul_cancel, zchar_one, one_mul]

def Rep {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g s : S) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (χ : S →ₐ[c.F] L) (w : FrPt Xo c L) (v : L),
    FrMap χ y w → Val hb w v → χ g * v = χ s

theorem exists_rep (hl : EvLaws Xo c) (hA : Atlas h) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ s, Rep hb y 1 s := by
  let I : Ideal S :=
    { carrier := {g | ∃ s, Rep hb y g s}
      zero_mem' := ⟨0, fun L _ _ χ w v _ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨s, hs⟩ ⟨s', hs'⟩
        exact ⟨s + s', fun L _ _ χ w v h1 h2 => by
          rw [map_add (f := _), map_add (f := _), add_mul, hs L χ w v h1 h2, hs' L χ w v h1 h2]⟩
      smul_mem' := by
        rintro r g ⟨s, hs⟩
        exact ⟨r * s, fun L _ _ χ w v h1 h2 => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hs L χ w v h1 h2]⟩ }
  by_contra hne
  have hI : I ≠ ⊤ := fun hI => hne ((Ideal.eq_top_iff_one I).1 hI)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  have := hP.isPrime
  let χ₀ : S →ₐ[c.F] FractionRing (S ⧸ P) :=
    (IsScalarTower.toAlgHom c.F (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ c.F P)
  obtain ⟨w₀, hw₀⟩ := hl.bc _ _ χ₀ y
  obtain ⟨C, ψ₀, z₀, t₀, h1, h2⟩ := hA _ w₀
  obtain ⟨g, hg, hloc⟩ := C.opn S _ χ₀ y w₀ hw₀ ⟨ψ₀, z₀, t₀, h1, h2⟩
  let lam : S →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F S _
  have hu : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨w', hw'⟩ := hl.bc _ _ lam y
  obtain ⟨ψ, z, t, h3, h4⟩ := hloc _ lam hu w' hw'
  have hv : Val hb w' (zchar e t * ψ ⟨_, hb C⟩) := ⟨C, ψ, z, t, h3, h4, rfl⟩
  generalize zchar e t * ψ ⟨_, hb C⟩ = u at hv
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g u
  have hmem : g ^ (n + 1) ∈ I := by
    refine ⟨g * a, fun L _ _ χ w v h5 h6 => ?_⟩
    by_cases hχ : χ g = 0
    · simp [hχ]
    · let mu : Localization.Away g →ₐ[c.F] L :=
        IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := χ) (by
          rintro ⟨_, k, rfl⟩
          simpa using (IsUnit.mk0 _ hχ).pow k)
      have hmu' : ∀ x, mu (algebraMap S _ x) = χ x := fun x => by
        simp [mu]
      have hmu : mu.comp lam = χ := AlgHom.ext hmu'
      have h7 : FrMap mu w' w := frMap_cancel _ _ _ lam mu y w' w hw' (by rw [hmu]; exact h5)
      have h8 := val_unique hb hl h6 (val_map hb hl mu h7 hv)
      have h9 := congrArg mu ha
      rw [map_mul, map_pow, hmu', hmu'] at h9
      rw [h8, map_mul, map_pow, ← h9]
      ring
  have hgP : g ∈ P := this.mem_of_pow_mem _ (hIP hmem)
  apply hg
  show algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P g) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hgP, map_zero]

end Val

theorem exists_sec_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, zchar a C.t * b C.Z ∈ C.R) → ∃ g ∈ GlobalTheory.AllWt.secZ Xo c a, ∀ Z, evC h Z g = b Z := by
  intro E _ _ _ H Dw l Xo c hl h hA a b hb
  have hred : ∀ p : TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  choose g hg using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_rep hb hl hA y
  have hg' : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (L : Type) [Field L] [Algebra c.F L] (χ : p.R →ₐ[c.F] L)
      (w : FrPt Xo c L) (v : L), FrMap χ y w → Val hb w v → χ (g p y) = v := by
    intro p y L _ _ χ w v h1 h2
    rw [← hg p y L χ w v h1 h2, map_one, one_mul]
  refine ⟨g, GlobalTheory.AllWt.mem_secZ.2 ⟨fun p q φ y z hz => ?_, fun p t y y' hy => ?_⟩, fun Z => ?_⟩
  · have := hred q
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ z
    obtain ⟨v, hv⟩ := val_ex hb hA w
    rw [hg' q z L χ w v hw hv]
    exact (hg' p y L (χ.comp φ) w v (frMap_trans _ _ _ φ χ y z w hz hw) hv).symm
  · have := hred p
    show g p y' = zchar a t * g p y
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ y
    obtain ⟨w', hw'⟩ := hl.bc _ _ χ y'
    obtain ⟨v, hv⟩ := val_ex hb hA w
    have hv' := val_bor hb (frBorBC _ _ χ t y y' w w' hy hw hw') hv
    rw [hg' p y' L χ w' _ hw' hv', map_mul, hg' p y L χ w v hw hv, zchar_map]
  · have hh := hl.test _ (genFr h Z)
    unfold evC evR evalAt
    rw [dite_eq_left hh]
    exact hg' _ _ _ _ _ _ hh.choose_spec.choose_spec.choose_spec (val_gen hb hA Z)

theorem exists_secZ_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c) (w : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, ((∏ i, C.t i ^ w i : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R) → ∃ f ∈ GlobalTheory.AllWt.secZ Xo c w, ∀ Z, evC h Z f = b Z := by
  intro E _ _ _ H Dw l Xo c h w b hb
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  exact exists_sec_of_regular E H Dw l Xo c hL h (hA h) w b hb

end GlobalTheory.SecGlueInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalCMTripleExponentialOfPeriod
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.CuspFrom.PeriodTriple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}

theorem exists_isExp_of_sabMap {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} (B : GlobalTheory.CM.PAT H (Sp ℂ))
    (m : SABMap B.t t y) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (hP : IsPeriod D ty P)
    (hol : IsHolTo Set.univ fun z => (e z).left) (add : ∀ z w, e (z + w) = e z * e w) (onto : Function.Surjective e)
    (ker : ∀ z, e z = 1 ↔ z ∈ P.range) (lin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (weil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) :
    ∃ ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G), GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [hid, Category.id_comp]
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (RingHom.id ℂ))) y hy
  have hp' : ∀ z, (p.symm (e z)).left ≫ m.φ = (e z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => p.symm (e z), hP, ?_, fun z w => ?_, p.symm.surjective.comp onto, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · refine ThetaPoint.isHolTo_fibre m.cart.1 _ (fun z => (Over.w (p.symm (e z))).trans hid) ?_
    have h : (fun z => (p.symm (e z)).left ≫ m.cm.F) = fun z => (e z).left := funext hp'
    exact h ▸ hol
  · beta_reduce
    rw [add, map_mul]
  · exact (map_eq_one_iff _ p.symm.injective).trans (ker z)
  · beta_reduce
    rw [lin, p.symm_apply_eq]
    apply Over.OverMorphism.ext
    rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
    exact congrArg (· ≫ _) (hp' z).symm
  · exact (GlobalTheory.CM.ExCompare.weilIs_iff m _ _ hy k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (weil k a b c hk hc)

theorem exists_isExp_of_rank_zero (l : Level H) (hD : D.p + D.q = 0) (hP : IsPeriod D ty P) :
    ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)),
      GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  obtain ⟨B, hB, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H D l _ _ _ _
    (Models.RankZero.zeroObj hD l (spMap (algebraMap (KA l) ℂ)))
  have hz : IsIso B.t.G.hom := by
    rw [hB]
    exact Models.RankZero.isIso_zeroTriple _
  have := Models.RankZero.subsingleton_La hD
  have h0 : ∀ z : Fin g → ℂ, z = 0 := fun z => by
    have hz : z ∈ Submodule.span ℝ (Set.range P) := hP.2.2.2.1 ▸ Submodule.mem_top
    refine (Submodule.span_le (p := ⊥)).2 ?_ hz
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a 0, map_zero]
    exact Submodule.zero_mem _
  refine ⟨B, fun _ => 1, hP, fun U f => ⟨?_, differentiableOn_const _⟩, fun _ _ => (_root_.mul_one _).symm,
    fun x => ⟨0, Models.RankZero.hom_unique hz _ _⟩, fun z => ⟨fun _ => ⟨0, by rw [map_zero, h0 z]⟩, fun _ => rfl⟩,
    fun _ _ => Models.RankZero.hom_unique hz _ _, fun k a b c hk hc => ?_⟩
  · simp only [Set.mem_univ, true_and]
    exact isOpen_const
  · have e : c = 1 := Units.ext (by rw [hc, Subsingleton.elim b 0, map_zero]; simp)
    rw [e, unitOn, map_one]
    exact Models.RankZero.weilIs_zero hz B.t.PP.isLB (Models.RankZero.triv_rig hz _) _ _ _

end GlobalTheory.CuspFrom.PeriodTriple

namespace GlobalTheory.CuspFrom

theorem exists_pat_isExp_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)), IsTypeFn H DB.p DB.q ty → IsPeriod DB ty PB → ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB ty PB ex := by
  intro E _ _ _ H l₀ DB g ty PB hty hP
  rcases Nat.eq_zero_or_pos (DB.p + DB.q) with h0 | hpq
  · exact PeriodTriple.exists_isExp_of_rank_zero l₀ h0 hP
  have kn := known_holds
  obtain ⟨l, hA⟩ : ∃ l : Level H, l.A = 1 := ⟨{ l₀ with A := 1, A_pos := one_pos }, rfl⟩
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, -, -, ⟨add, onto, hol, -⟩, ker, lin, weil, -⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws
    E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty DB LinearMap.id PB
    ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨U, hU, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H DB l _ _ _ _ Xo.univ
  obtain ⟨B, m, -⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ y U
  exact ⟨B, PeriodTriple.exists_isExp_of_sabMap B (hU ▸ m) e hP hol add onto ker lin weil⟩

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
section
noncomputable section

section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjBlowup

theorem eq_top_of_forall_notMem {W : Scheme.{0}} (I : W.IdealSheafData) (h : ∀ w, w ∉ I.support) : I = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, eq_bot_iff]
  exact fun w hw => (h w hw).elim

theorem effCartier_top (W : Scheme.{0}) : FinalTheorems.EffCartier (⊤ : W.IdealSheafData) := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, 1, hx, one_mem _, by simp⟩

theorem mem_support_comap {W X : Scheme.{0}} (J : X.IdealSheafData) (g : W ⟶ X) (w : W) :
    w ∈ (J.comap g).support ↔ g w ∈ J.support := by
  rw [Scheme.IdealSheafData.support_comap]; rfl

theorem exists_blowup {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) :
    ∃ (X' : Scheme.{0}) (b : X' ⟶ X), FinalTheorems.Blowup b J ∧ IsProjOver (b ≫ s) ∧
      ∀ V : X.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (b ∣_ V) := by
  obtain ⟨L, m, σ, hσ⟩ := GlobalTheory.T.exists_sections_generate_ideal_projective R X s hs J
  have : IsProper (PSpace.str R m) := isProper_str R m
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let U : X.Opens := J.support.compl
  have hU : ∀ x : U.toScheme, U.ι x ∉ J.support := fun x => x.2
  have htop : ∀ {W : Scheme.{0}} (g : W ⟶ X), (∀ w, g w ∉ J.support) → J.comap g = ⊤ := fun g hg =>
    eq_top_of_forall_notMem _ fun w hw => hg w ((mem_support_comap J g w).1 hw)
  obtain ⟨φ, hφ, hφσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X U _ L m σ U.ι (U.ι ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ U.ι hσ)
    (by rw [htop _ hU]; exact effCartier_top _)
  let b := graphClosure.fst s (PSpace.str R m) U.ι φ hφ.symm
  let c := graphClosure.snd s (PSpace.str R m) U.ι φ hφ.symm
  let j := graphClosure.incl s (PSpace.str R m) U.ι φ hφ.symm
  have hjb : j ≫ b = U.ι := graphClosure.incl_fst ..
  have hjc : j ≫ c = φ := graphClosure.incl_snd ..
  have hbc : Proportional σ b c := .of_comp j (by rwa [hjb, hjc])
  refine ⟨_, b, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance inferInstance fun t => ?_,
    fun W g hg => ?_⟩, ?_,
    fun V hV => graphClosure.isIso_fst_restrict_of_le _ _ _ _ _ V (by rw [Scheme.Opens.opensRange_ι]; exact hV)⟩
  · rw [mem_support_comap, ← Scheme.Hom.comp_apply, hjb]; exact hU t
  · obtain ⟨ψ, hψ, hψσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X W _ L m σ g (g ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ g hσ) hg
    have hd := GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier W _ hg
    let d := Scheme.Opens.ι (X := W) (J.comap g).support.compl
    have hdU : ∀ t, (d ≫ g) t ∉ J.support := fun t ht => t.2 ((mem_support_comap J g _).2 ht)
    let w := IsOpenImmersion.lift U.ι (d ≫ g) (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨_, hdU t⟩, rfl⟩)
    have hw : w ≫ U.ι = d ≫ g := IsOpenImmersion.lift_fac ..
    have hw' : d ≫ ψ = w ≫ φ := _root_.GlobalTheory.ProjBlowup.eq_of_proportional R X _ L m σ (d ≫ g) _ _ (htop _ hdU ▸ GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ (d ≫ g) hσ)
      (by rw [Category.assoc, hψ, Category.assoc, hφ, reassoc_of% hw]) (hψσ.comp d) (hw ▸ hφσ.comp w)
    have key : ∀ h : W ⟶ _, h ≫ b = g → d ≫ h = w ≫ j := fun h hh => by
      have H := graphClosure.isPullback_incl s (PSpace.str R m) U.ι φ hφ.symm
      have e : w ≫ U.ι = (d ≫ h) ≫ b := by rw [hw, Category.assoc, hh]
      have h1 := H.lift_fst w (d ≫ h) e
      rw [Category.comp_id] at h1
      rw [← H.lift_snd w (d ≫ h) e, h1]
    have hl := graphClosure.lift_fst s (PSpace.str R m) U.ι φ hφ.symm g ψ hψ.symm d w hw.symm hw'
    exact ⟨_, hl, fun h hh => hom_ext_of_isSchemeTheoreticallyDominant d b ((key h hh).trans (key _ hl).symm)
      (hh.trans hl.symm)⟩
  · obtain ⟨n, i, hi, e⟩ := ProjSpace.isProjOver_of_isPullback (IsPullback.of_hasPullback s (PSpace.str R m)) hs
      (ProjSpace.isProjOver_pspace_str R m)
    exact ⟨n, graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm ≫ i, inferInstance, by
      rw [Category.assoc, e, graphClosure.ι_fst_assoc]⟩

end GlobalTheory.ProjBlowup

end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.ProjBlowup

section
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isDiscreteValuationRing_coeff {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    IsDiscreteValuationRing (c.V W) := by
  have := c.fin
  have : NumberField c.F := {}
  refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

end

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZero
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem rootDiscr_ne_zero : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ), rootDiscr m ≠ 0 := by
  intro ι _ m
  unfold rootDiscr
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun j _ =>
    Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [sub_ne_zero]
  intro h
  have h2 := X_injective (σ := Root m) (R := ℝ) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h2
  exact (Finset.mem_Iio.mp hi).ne h2.symm

end GlobalTheory.GoodMetric
end

