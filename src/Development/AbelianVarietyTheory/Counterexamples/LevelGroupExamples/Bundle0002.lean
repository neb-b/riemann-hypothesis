module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.InducedEqOne
section
noncomputable section

namespace GlobalTheory.DeltaPinTest

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem noDelta_phiPin (nab : NabV Xo c) (m : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (noDelta Xo c nab m n).PhiPin (fun _ => 1) 1 (fun _ => 0) := by
  haveI hs : Subsingleton (LaJ Xo c (noDelta Xo c nab m n)) := by
    apply Submodule.Quotient.subsingleton_iff.2
    show Ideal.map _ ⊤ • ⊤ = ⊤
    rw [Ideal.map_top, Submodule.top_smul]
  refine ⟨fun _ _ _ => rfl, fun _ _ => Subsingleton.elim _ _, fun _ _ _ _ => by simp, rfl,
    Subsingleton.elim _ _, fun q => ?_⟩
  haveI : Unique (Fin n → LaJ Xo c (noDelta Xo c nab m n)) := uniqueOfSubsingleton (fun _ => 0)
  rw [finsum_unique]
  have hz : ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) = 1 := by
    have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    apply Subtype.ext
    rw [Nat.div_one]
    exact (Complex.isPrimitiveRoot_exp _ h0).pow_eq_one
  show (noDelta Xo c nab m n).eF 1 = (noDelta Xo c nab m n).eF 1 * ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) ^ _
  rw [hz]
  exact ((congrArg _ (one_zpow _)).trans (mul_one _)).symm

end GlobalTheory.DeltaPinTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LevelGroupEqTopOfCoprime
section
noncomputable section

namespace GlobalTheory.LevelGroupTest

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem natCast_mem_half (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := by
    rw [← l.prod]; exact Ideal.mul_le_left
  exact h (Ideal.subset_span rfl)

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

end GlobalTheory.LevelGroupTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TransformIndicator
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClassSumProbe
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

set_option autoImplicit false in
open NumberField MvPolynomial in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
private theorem mfr_ne_bot : _root_.Formalism.L2.Pj.Mfr l ≠ ⊥ := by
  intro h
  have hM := l.prod
  have h3 := l.three_le
  unfold _root_.Formalism.L2.Pj.Mfr at h
  rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hM
  exact absurd (Nat.cast_eq_zero.mp hM) (by omega)


set_option autoImplicit false in
open NumberField MvPolynomial in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
theorem _root_.GlobalTheory.ClassSumProbe.finite_conj_half :
    Finite (Dw.La ⧸ (_root_.Formalism.L2.Pj.Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) := by
  haveI := Dw.fin
  haveI : Finite (𝓞 E ⧸ _root_.Formalism.L2.Pj.Mfr l) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ mfr_ne_bot
  exact Module.finite_of_finite (𝓞 E ⧸ _root_.Formalism.L2.Pj.Mfr l)

end GlobalTheory.ClassSumProbe
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg
section
noncomputable section

namespace GlobalTheory.IntegralFrameCheck

open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero

section Dvr

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem vV_algebraMap_nonneg (a : V) : 0 ≤ vV V (algebraMap V K' a) := by
  by_cases ha : algebraMap V K' a = 0
  · rw [ha]; simp [vV]
  · have hv : valV V (algebraMap V K' a) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
    have := (WithZero.log_le_log (valV_ne_zero (V := V) ha) one_ne_zero).2 hv
    simp only [WithZero.log_one] at this
    simp only [vV]; omega

theorem vV_one : vV V (1 : K') = 0 := by simp [vV]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  induction n with
  | zero => simp [vV]
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero n hx) hx, ih]; push_cast; ring

variable {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K'']
  [IsFractionRing V' K'']

theorem vV_map_unit (i : K' →+* K'') (hi : ∀ a : V, i (algebraMap V K' a) ∈ Set.range (algebraMap V' K''))
    (u : Vˣ) : vV V' (i (algebraMap V K' u)) = 0 := by
  have hne : ∀ w : Vˣ, i (algebraMap V K' w) ≠ 0 := fun w =>
    ((w.isUnit.map (algebraMap V K')).map i).ne_zero
  have h0 : ∀ w : Vˣ, 0 ≤ vV V' (i (algebraMap V K' w)) := fun w => by
    obtain ⟨b, hb⟩ := hi w
    rw [← hb]; exact vV_algebraMap_nonneg b
  have h1 := vV_mul (V := V') (hne u) (hne u⁻¹)
  rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, vV_one] at h1
  have := h0 u
  have := h0 u⁻¹
  omega

theorem exists_vV_map (i : K' →+* K'') (hi : ∀ a : V, i (algebraMap V K' a) ∈ Set.range (algebraMap V' K'')) :
    ∃ r : ℕ, ∀ x, vV V' (i x) = (r : ℤ) * vV V x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hp0 : algebraMap V K' p ≠ 0 := by
    simpa using hp.ne_zero
  have hr : 0 ≤ vV V' (i (algebraMap V K' p)) := by
    obtain ⟨b, hb⟩ := hi p
    rw [← hb]; exact vV_algebraMap_nonneg b
  have hp1 : vV V (algebraMap V K' p) = 1 := by
    have h : valV V (algebraMap V K' p) = WithZero.exp (-1 : ℤ) := by
      unfold valV
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      refine HeightOneSpectrum.intValuation_singleton _ hp.ne_zero ?_
      exact hp.maximalIdeal_eq
    simp [vV, h]
  refine ⟨(vV V' (i (algebraMap V K' p))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hr]
  have key : ∀ a : V, a ≠ 0 → vV V' (i (algebraMap V K' a)) =
      vV V' (i (algebraMap V K' p)) * vV V (algebraMap V K' a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hp
    have hu : algebraMap V K' u ≠ 0 := (u.isUnit.map (algebraMap V K')).ne_zero
    have hu0 : vV V (algebraMap V K' u) = 0 :=
      vV_map_unit (V' := V) (RingHom.id K') (fun a => ⟨a, rfl⟩) u
    rw [map_mul, map_pow, map_mul, map_pow,
      vV_mul ((map_ne_zero i).2 hu) (pow_ne_zero n ((map_ne_zero i).2 hp0)),
      vV_mul hu (pow_ne_zero n hp0), vV_pow ((map_ne_zero i).2 hp0), vV_pow hp0, vV_map_unit i hi u, hu0, hp1]
    ring
  intro x
  by_cases hx : x = 0
  · subst hx; simp [vV]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap V K' b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have e : algebraMap V K' a / algebraMap V K' b * algebraMap V K' b = algebraMap V K' a :=
    div_mul_cancel₀ _ hb'
  have h1 := vV_mul (V := V) hx hb'
  have h2 := vV_mul (V := V') ((map_ne_zero i).2 hx) ((map_ne_zero i).2 hb')
  rw [← map_mul, e, key a ha0, key b hb0] at h2
  rw [e] at h1
  rw [h1] at h2
  linarith

end Dvr

theorem nval_map_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)}
    {T T' : CDVR} {io : K →+* T.Fr} {io' : K →+* T'.Fr} {e e' : ℕ}
    (ho : OverLa la T.V io e) (ho' : OverLa la T'.V io' e') (i : T.Fr →+* T'.Fr)
    (hc : ∀ a, i (io a) = io' a)
    (hi : ∀ a : T.V, i (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) :
    ∃ r : ℕ, 0 < r ∧ e' = r * e ∧ (∀ x, vV T'.V (i x) = (r : ℤ) * vV T.V x) ∧
      ∀ x, nval T'.V e' (i x) = nval T.V e x := by
  obtain ⟨r, hr⟩ := exists_vV_map i hi
  obtain ⟨a, ha⟩ := la.valuation_exists_uniformizer K
  have h1 : vLa la a = 1 := by simp [vLa, ha]
  have h2 := hr (io a)
  rw [hc, ho'.2, ho.2, h1] at h2
  have he : e' = r * e := by
    have : (e' : ℤ) = (r * e : ℕ) := by push_cast; linarith
    exact_mod_cast this
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · have := ho'.1; rw [he, h] at this; simp at this
    · exact h
  exact ⟨r, hr0, he, hr, fun x => he ▸ nval_bc i hr0 hr e x⟩


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem intAll_ramified {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (h : Formalism.L2.PjFree.IntAll Xo c)
    (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (hf : T.FinRes) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (r : ℕ) (y' : IntFr Xo c T' io'), 0 < r ∧ OverLa la T'.V io' (r * e) ∧
      T'.FinRes ∧
      letI := io.toAlgebra; letI := io'.toAlgebra
      ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
        (∀ x, vV T'.V (φ x) = (r : ℤ) * vV T.V x) ∧ (∀ x, nval T'.V (r * e) (φ x) = nval T.V e x) ∧
        FrMap φ y z ∧ FrBor t z y'.1 := by
  obtain ⟨T', io', e', y', ho', hf', φ, z, t, hφ, hz, hb⟩ := h la T io e ho hf y
  let _ := io.toAlgebra
  let _ := io'.toAlgebra
  obtain ⟨r, hr, rfl, h1, h2⟩ := nval_map_of_overLa ho ho' φ.toRingHom (fun a => φ.commutes a) hφ
  exact ⟨T', io', r, y', hr, ho', hf', φ, z, t, h1, h2, hz, hb⟩

end GlobalTheory.IntegralFrameCheck
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelPairing

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  have h1 := H.bar_eq (H.bar a)
  have h2 := H.bar_eq a
  change ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [h1, h2, IsCMField.complexConj_apply_apply]

theorem cSep_spec (l : Level H) : cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
  have h : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    obtain ⟨m, hm, mb, hmb, hsum⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ _)
    refine ⟨mb, hmb, ?_⟩
    have : mb - 1 = -m := by rw [← hsum]; ring
    rw [this]; exact neg_mem hm
  unfold cSep
  rw [dite_eq_left h]
  exact h.choose_spec

theorem dvd_EF_of_mem (x y : Dw.La) {a : 𝓞 E} (ha : a ∈ Ideal.span {(l.M : 𝓞 E)}) :
    (l.M : ℤ) ∣ Dw.EF x (a • y) := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  have : (b * (l.M : 𝓞 E)) • y = (l.M : ℤ) • (b • y) := by
    rw [mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul (𝓞 E)]; simp
  rw [this, map_zsmul]
  exact Dvd.intro _ rfl

theorem mul_mem_M {a b : 𝓞 E} (ha : a ∈ l.Mb) (hb : b ∈ Mfr l) : a * b ∈ Ideal.span {(l.M : 𝓞 E)} :=
  l.prod ▸ Ideal.mul_mem_mul ha hb

theorem bar_mem_Mb {a : 𝓞 E} (ha : a ∈ Mfr l) : H.bar a ∈ l.Mb := by
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 ha
  have : H.bar ((H.bar : 𝓞 E →+* 𝓞 E) b) = b := bar_bar H b
  rwa [this]

theorem dvd_right (x : Dw.La) {y : Dw.La} (hy : y ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ Dw.EF x (cSep l • y) := by
  refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun u v hu hv => ?_)
  · rw [← mul_smul, mul_comm]; exact dvd_EF_of_mem _ _ (mul_mem_M ha (cSep_spec l).1)
  · rw [smul_add, map_add (f := _)]; exact dvd_add hu hv

theorem dvd_left {x : Dw.La} (y : Dw.La) (hx : x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ Dw.EF x (cSep l • y) := by
  refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) (fun u v hu hv => ?_)
  · rw [Dw.adj, ← mul_smul]; exact dvd_EF_of_mem _ _ (mul_mem_M (bar_mem_Mb ha) (cSep_spec l).1)
  · rw [map_add (f := _), LinearMap.add_apply]; exact dvd_add hu hv

theorem pairL_congr {n : ℕ} (x0 x0' x x' : Fin n → Dw.La)
    (h0 : ∀ b, x0 b - x0' b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La))
    (h1 : ∀ b, x b - x' b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ pairL (l := l) x0 x - pairL (l := l) x0' x' := by
  unfold pairL
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun b _ => ?_
  have : Dw.EF (x0 b) (cSep l • x b) - Dw.EF (x0' b) (cSep l • x' b) =
      Dw.EF (x0 b - x0' b) (cSep l • x b) + Dw.EF (x0' b) (cSep l • (x b - x' b)) := by
    simp [smul_sub]
  rw [this]
  exact dvd_add (dvd_left _ (h0 b)) (dvd_right _ (h1 b))

theorem zetaM_coe (c : Coeff l) : ((zetaM c : c.F) : ℂ) = zeta l.M := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hA : l.A ≠ 0 := l.A_pos.ne'
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM hA
  have hk0 : k ≠ 0 := by rintro rfl; simp [hk] at hM'
  have hdiv : l.M' / l.M = k := by rw [hk]; exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hM)
  unfold zetaM
  rw [hdiv]
  change (zeta l.M') ^ k = _
  unfold zeta
  rw [← Complex.exp_nat_mul, hk]
  congr 1
  have : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have : (l.M : ℂ) ≠ 0 := by exact_mod_cast hM
  push_cast
  field_simp

theorem zetaM_prim (c : Coeff l) : IsPrimitiveRoot (zetaM c) l.M := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  refine IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) ?_ Subtype.val_injective
  have := zetaM_coe c
  change IsPrimitiveRoot ((zetaM c : c.F) : ℂ) l.M
  rw [this]
  exact Complex.isPrimitiveRoot_exp l.M hM

theorem levRep_mk (x : Dw.La) :
    levRep (Submodule.Quotient.mk x : LevQ Dw l) - x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) :=
  (Submodule.Quotient.eq _).1 (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (Submodule.Quotient.mk x : LevQ Dw l)))

theorem zpow_congr (c : Coeff l) {a b : ℤ} (h : (l.M : ℤ) ∣ a - b) : zetaM c ^ a = zetaM c ^ b := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : zetaM c ≠ 0 := (zetaM_prim c).ne_zero hM
  have := ((zetaM_prim c).zpow_eq_one_iff_dvd (a - b)).2 h
  rw [zpow_sub₀ h0, div_eq_one_iff_eq (zpow_ne_zero _ h0)] at this
  exact this

theorem levelFourierDatum_mk (c : Coeff l) {n : ℕ} (x0 x : Fin n → Dw.La) :
    x0Dat c x0 (fun b => (Submodule.Quotient.mk (x b) : LevQ Dw l)) = zetaM c ^ pairL (l := l) x0 x :=
  zpow_congr c (pairL_congr _ _ _ _ (fun b => by simp) (fun b => levRep_mk (x b)))

theorem exists_eq_smul_of_dvd (x : Dw.La) (m : ℕ) (hm : m ≠ 0) (h : ∀ y, (m : ℤ) ∣ Dw.EF x y) :
    ∃ z, x = (m : ℤ) • z := by
  let f : Dw.La →ₗ[ℤ] ℤ :=
    { toFun := fun y => Dw.EF x y / m
      map_add' := fun a b => by rw [map_add (f := _), Int.add_ediv_of_dvd_left (h a)]
      map_smul' := fun k a => by
        rw [map_zsmul]; simp only [smul_eq_mul, RingHom.id_apply]; exact Int.mul_ediv_assoc _ (h a) }
  obtain ⟨z, hz⟩ := Dw.unimod.2 f
  refine ⟨z, Dw.unimod.1 ?_⟩
  ext y
  rw [map_zsmul, hz]
  simp only [LinearMap.smul_apply, smul_eq_mul, f, LinearMap.coe_mk, AddHom.coe_mk]
  exact (Int.mul_ediv_cancel' (h y)).symm

theorem mem_of_dvd {x : Dw.La} (h : ∀ y, (l.M : ℤ) ∣ Dw.EF x (cSep l • y)) :
    x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨z, hz⟩ := exists_eq_smul_of_dvd (H.bar (cSep l) • x) l.M hM (fun y => by
    rw [Dw.adj, bar_bar]; exact h y)
  have h1 : H.bar (cSep l - 1) ∈ Mfr l := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (cSep_spec l).2
  have hMm : (l.M : 𝓞 E) ∈ Mfr l := by
    have : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l := l.prod ▸ Ideal.mul_le_right
    exact this (Ideal.subset_span rfl)
  have : x = (l.M : 𝓞 E) • z - H.bar (cSep l - 1) • x := by
    rw [map_sub, map_one, sub_smul, one_smul, hz, ← Int.cast_smul_eq_zsmul (𝓞 E)]; simp
  rw [this]
  exact sub_mem (Submodule.smul_mem_smul hMm trivial) (Submodule.smul_mem_smul h1 trivial)

theorem levelFourierDatum_eq_iff (c : Coeff l) {n : ℕ} (x0 x0' : Fin n → Dw.La) :
    x0Dat c x0 = x0Dat c x0' ↔ ∀ b, x0 b - x0' b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  constructor
  · intro h b
    refine mem_of_dvd fun y => ?_
    have h1 := congrFun h (fun i => (Submodule.Quotient.mk ((Pi.single b y : Fin n → Dw.La) i) : LevQ Dw l))
    rw [levelFourierDatum_mk, levelFourierDatum_mk] at h1
    have h0 : zetaM c ≠ 0 := (zetaM_prim c).ne_zero hM
    have h2 : (l.M : ℤ) ∣ pairL (l := l) x0 (Pi.single b y) - pairL (l := l) x0' (Pi.single b y) := by
      rw [← (zetaM_prim c).zpow_eq_one_iff_dvd, zpow_sub₀ h0, h1, div_self (zpow_ne_zero _ h0)]
    have h3 : ∀ u : Fin n → Dw.La, pairL (l := l) u (Pi.single b y) = Dw.EF (u b) (cSep l • y) := by
      intro u
      unfold pairL
      rw [Finset.sum_eq_single b]
      · simp
      · intro i _ hi; simp [Pi.single_eq_of_ne hi]
      · simp
    rw [h3, h3] at h2
    simpa using h2
  · intro h
    funext q
    exact zpow_congr c (pairL_congr _ _ _ _ h (fun b => by simp))

theorem finite_LevQ : Finite (LevQ Dw l) := by
  haveI := Dw.fin
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hb : l.Mb ≠ ⊥ := by
    intro h
    have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    have := this (Ideal.subset_span rfl)
    rw [h, Ideal.mem_bot] at this
    exact hM (by exact_mod_cast this)
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  haveI : Module.Finite (𝓞 E ⧸ l.Mb) (LevQ Dw l) := Module.Finite.of_restrictScalars_finite (𝓞 E) _ _
  exact Module.finite_of_finite (𝓞 E ⧸ l.Mb)

end GlobalTheory.LevelPairing
end
end

