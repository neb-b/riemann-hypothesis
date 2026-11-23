module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsConjSplitPointLatticeLinearMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunction
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryOfConjugateSplitPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.ConjIsometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem conj_of_sq {ρ : ℂ} (hρ : ρ ^ 2 = -(H.d : ℂ)) : starRingEnd ℂ ρ = -ρ := by
  have h1 : (starRingEnd ℂ ρ) ^ 2 = ρ ^ 2 := by rw [← map_pow, hρ]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h
    rw [hx] at hρ
    have h5 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast hρ
    have h6 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg x]
  · exact h

theorem bar_rt : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun a : 𝓞 E => φ (a : E)) H.rt_sq
    simpa using this
  apply Subtype.ext
  show ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E)
  apply φ.injective
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, conj_of_sq h4]
  simp

theorem cmHost_bar_halfIntegerGenerator : H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, bar_rt, map_ofNat] at h
  apply mul_left_cancel₀ (two_ne_zero (α := 𝓞 E))
  linear_combination h + H.two_weight_eq_one_add_root

theorem bar_mul_wE (s : ℤ × ℤ) :
    H.bar (wE H s) * wE H s = ((s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) : ℤ) : 𝓞 E) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (H.d : ℤ) + 1 = 4 * m := ⟨((H.d : ℤ) + 1) / 4, by have := H.d_mod; omega⟩
  have e : ((H.d : ℤ) + 1) / 4 = m := by omega
  have hm' : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hm
  have hw : H.w0 * (1 - H.w0) = (m : 𝓞 E) := by
    have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h4
    linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'
  rw [e, wE, map_add (f := _), map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
  push_cast
  linear_combination (s.2 : 𝓞 E) ^ 2 * hw

theorem form_smul_smul (D : Datum H) (c : 𝓞 E) (N : ℤ) (h : H.bar c * c = N) (x y : D.La) :
    D.EF (c • x) (c • y) = N * D.EF x y := by
  rw [D.adj, smul_smul, h, Int.cast_smul_eq_zsmul, map_zsmul, smul_eq_mul]

theorem form_skew (D : Datum H) (x y : D.La) : D.EF x y = -D.EF y x := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt] at h
  linarith

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem form_lat_eq_zero {D : Datum H} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {a b : D.La}
    (ha : a ∈ lat hP H.rt0) (hb : b ∈ lat hP (-H.rt0)) : D.EF a b = 0 := by
  obtain ⟨Hm, -, -, hE⟩ := hP.2.2.2.2
  have h1 := hE (H.rt • a) (H.rt • b)
  rw [form_smul_smul D H.rt H.d (by rw [bar_rt]; push_cast; linear_combination -H.rt_sq),
    period_rt_smul hP ha, period_rt_smul hP hb] at h1
  have h2 : hermForm Hm (H.rt0 • P a) ((-H.rt0) • P b) = -(H.d : ℂ) * hermForm Hm (P a) (P b) := by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [star_neg, ← starRingEnd_apply, conj_of_sq H.sqrt_neg_disc_sq, ← H.sqrt_neg_disc_sq]
    ring
  rw [h2] at h1
  simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
    hE] at h1
  push_cast at h1
  have h6 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have : (D.EF a b : ℝ) = 0 := by nlinarith
  exact_mod_cast this

theorem surjective_of_isometry {D D' : Datum H} (hr : D.p + D.q = D'.p + D'.q) (Φ : D.La →ₗ[𝓞 E] D'.La)
    (hi : Function.Injective Φ) (hΦ : ∀ a b, D'.EF (Φ a) (Φ b) = D.EF a b) : Function.Surjective Φ := by
  have := D.fin
  have := D'.fin
  have := D'.proj
  have h0 : Module.finrank (𝓞 E) (D'.La ⧸ LinearMap.range Φ) = 0 := by
    have h1 := (LinearMap.range Φ).finrank_quotient_add_finrank
    rw [LinearMap.finrank_range_of_inj hi, D.rank, D'.rank] at h1
    omega
  intro y
  obtain ⟨x, hx⟩ := D.unimod.2 ((D'.EF y).comp (Φ.restrictScalars ℤ))
  have hx' : ∀ z, D'.EF (y - Φ x) (Φ z) = 0 := fun z => by
    rw [map_sub, LinearMap.sub_apply, hΦ, hx]; simp
  obtain ⟨c, hc, hcw⟩ := Module.finrank_eq_zero_iff.1 h0 (Submodule.Quotient.mk (y - Φ x))
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcw
  obtain ⟨v, hv⟩ := hcw
  have hv0 : v = 0 := D.unimod.1 (by
    ext z
    rw [← hΦ, hv, D'.adj, ← map_smul, hx']; simp)
  rw [hv0, map_zero] at hv
  exact ⟨x, (sub_eq_zero.1 ((smul_eq_zero.1 hv.symm).resolve_left hc)).symm⟩

theorem exp_eq_zeta (n : ℕ) (m : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) = zeta n ^ (-m) := by
  rw [zeta, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ}

theorem conj_pairing (F : FamilyUnif Xo σ ty) (τ : ℂ ≃+* ℂ) {i i' : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    {P' : (F.Di i').La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i') ty P')
    (hu : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P') {n : ℕ} (hn : 0 < n) {x y : (F.Di i).La} {x' y' : (F.Di i').La}
    (hx : spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P x)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' x')).left)
    (hy : spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P y)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' y')).left) :
    τ (zeta n) ^ (-(F.Di i).EF x y) = zeta n ^ (-(F.Di i').EF x' y') := by
  let c : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((F.Di i).EF x y : ℂ) / n))
  let c' : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((F.Di i').EF x' y' : ℂ) / n))
  have W := F.ex_weil i P hP n x y c hn rfl
  have W' := F.ex_weil i' P' hP' n x' y' c' hn rfl
  let h : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have W₁ := CommPairing.weilIs_pull globalFns_holds
    ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩ Xo.univ.t.PP.isLB h W
  have e' : Units.map h.left.appTop.hom.toMonoidHom (unitOn c) =
      unitOn (Units.map (τ : ℂ →+* ℂ).toMonoidHom c) :=
    Units.ext (congrArg (fun q => q.hom c.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : ℂ →+* ℂ)))).symm
  have ex : h ≫ F.ex i P ((n : ℂ)⁻¹ • P x) = F.ex i' P' ((n : ℂ)⁻¹ • P' x') := Over.OverMorphism.ext hx
  have ey : h ≫ F.ex i P ((n : ℂ)⁻¹ • P y) = F.ex i' P' ((n : ℂ)⁻¹ • P' y') := Over.OverMorphism.ext hy
  rw [e', ex, ey] at W₁
  have k := congrArg Units.val (weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ _ _ _ _ _ W₁ W')
  rw [← map_zpow₀, ← exp_eq_zeta, ← exp_eq_zeta]
  exact k

end GlobalTheory.CompRat.ConjIsometry

namespace GlobalTheory.CompRat


open ConjIsometry in
theorem exists_isometry_of_conj_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA τ hτ C io hio i P hP i' P' hP' hs hu
  obtain ⟨Φ, hinj, hp, hm, hact⟩ :=
    _root_.GlobalTheory.ConjSplit.exists_conj_lattice_map E H D l Xo σ g ty F h1 hσ hty hA τ hτ C io hio i P hP i' P' hP' hs hu
  have hiso : ∀ x y, (F.Di i').EF (Φ x) (Φ y) = (F.Di i).EF x y := by
    intro x y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := y)))
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b') := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := _root_.GlobalTheory.CompRat.Acts.main E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (hact n s hn hs a ha b hb) (hact n s hn hs a' ha' b' hb')
      have hN := _root_.GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = N at hN hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = N := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP H.rt0, ∀ v ∈ lat hP (-H.rt0),
          (F.Di i').EF (Φ u) (Φ v) = 0 ∧ (F.Di i').EF (Φ v) (Φ u) = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' ((hp u).2 hu) ((hm v).2 hv)
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φ (wE H s • a + H.bar (wE H s) • b)) (Φ (wE H s • a' + H.bar (wE H s) • b')) =
          N * (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) := by
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [(o _ (Submodule.smul_mem _ _ ha) _ (Submodule.smul_mem _ _ hb')).1,
          (o _ (Submodule.smul_mem _ _ ha') _ (Submodule.smul_mem _ _ hb)).2, (o _ ha _ hb').1, (o _ ha' _ hb).2]
        simp only [map_smul Φ]
        rw [form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hN] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b')).natAbs + 1) (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, hp, hm, hact⟩

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsPeriodSpaces
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

noncomputable section

namespace GlobalTheory.CompSystem

open GlobalTheory.CompIdem GlobalTheory.CompFun

theorem orthogonal_of_fibres {R ι : Type} [CommRing R] [Fintype ι] (e : ι → R) (he : ∀ i, IsIdempotentElem (e i))
    (k : PrimeSpectrum R → ι) (h : ∀ i z, e i ∉ z.asIdeal ↔ k z = i) :
    (∀ i j, i ≠ j → e i * e j = 0) ∧ ∑ i, e i = 1 := by
  classical
  have ho : ∀ i j, i ≠ j → e i * e j = 0 := by
    intro i j hij
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem ((he i).mul (he j)) IsIdempotentElem.zero ?_
    ext z
    refine iff_of_false (fun hz => ?_) (fun hz => hz (zero_mem _))
    have hz' : e i * e j ∉ z.asIdeal := hz
    exact hij (((h i z).1 fun h1 => hz' (z.asIdeal.mul_mem_right _ h1)).symm.trans
      ((h j z).1 fun h1 => hz' (z.asIdeal.mul_mem_left _ h1)))
  refine ⟨ho, ?_⟩
  have hs : IsIdempotentElem (∑ i, e i) :=
    (OrthogonalIdempotents.mk he fun i j hij => ho i j hij).isIdempotentElem_sum
  refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem hs IsIdempotentElem.one ?_
  ext z
  refine iff_of_true (fun hz => ?_) (fun hz => z.2.ne_top ((Ideal.eq_top_iff_one _).2 hz))
  refine (h (k z) z).2 rfl ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (k z))] at hz
  refine (Ideal.add_mem_iff_left _ (sum_mem fun j hj => ?_)).1 hz
  by_contra hc
  exact (Finset.mem_erase.1 hj).1 ((h j z).1 hc).symm

theorem exists_complex_point {K : Type} [Field K] (σ : K →+* ℂ) {Y : Scheme.{0}} (s : Y ⟶ Sp K)
    [LocallyOfFiniteType s] {V : Set Y} (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ p : Sp ℂ ⟶ Y, p ≫ s = spMap σ ∧ p (IsLocalRing.closedPoint ℂ) ∈ V := by
  let g := pullback.snd s (spMap σ)
  let π := pullback.fst s (spMap σ)
  have hy : Surjective (spMap σ) :=
    ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have := LocallyOfFiniteType.jacobsonSpace g
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, rfl⟩ := π.surjective z
  obtain ⟨x, hx, hc'⟩ := nonempty_inter_closedPoints (Z := π ⁻¹' V) ⟨w, hz⟩
    (hV.preimage π.continuous).isLocallyClosed
  have hc : IsClosed ({x} : Set _) := hc'
  refine ⟨pointOfClosedPoint g x hc ≫ π, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · exact (congrArg (π · ∈ V) (pointOfClosedPoint_apply g x hc _)).mpr hx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem exists_indicator_test (hA : AllTest Xo c) (U : Set (Xo.XF c)) (hU : IsClopen U) :
    ∃ χ ∈ sec Xo c 0 0, (∀ (p : TRing c.F) (y : FrPt Xo c p.R), IsIdempotentElem (χ p y) ∧
      ∀ z : PrimeSpectrum p.R, χ p y ∉ z.asIdeal ↔ basePt y z ∈ U) ∧
      ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S),
      IsIdempotentElem (evR Xo c χ y) ∧
        ∀ z : PrimeSpectrum S, evR Xo c χ y ∉ z.asIdeal ↔ basePt y z ∈ U := by
  have hex : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃ e : p.R, IsIdempotentElem e ∧
      ∀ z : PrimeSpectrum p.R, e ∉ z.asIdeal ↔ basePt y z ∈ U := by
    intro p y
    obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (hU.preimage (basePt y).continuous)
    exact ⟨e, he, fun z => (Set.ext_iff.1 h z).symm⟩
  choose χ hi hχ using hex
  have hmap : ∀ (p : TRing c.F) (S : Type) [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R)
      (w : FrPt Xo c S), w.x = spMap φ.toRingHom ≫ y.x →
      ∀ z : PrimeSpectrum S, φ (χ p y) ∉ z.asIdeal ↔ basePt w z ∈ U := by
    intro p S _ _ φ y w h z
    rw [basePt_map φ y w h]
    exact hχ p y (PrimeSpectrum.comap φ.toRingHom z)
  have hw : ∀ (p : TRing c.F) (t : Ix D → (p.R)ˣ), wchar (ex D 0 0) t = 1 := by
    intro p t
    refine Finset.prod_eq_one fun i _ => ?_
    have : ex D 0 0 i = 0 := by rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
    rw [this, pow_zero]
  refine ⟨χ, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, fun p y => ⟨hi p y, hχ p y⟩, fun S _ _ _ y => ?_⟩
  · refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi q z) ((hi p y).map φ) ?_
    ext w
    exact (hχ q z w).trans (hmap p q.R φ y z h.1 w).symm
  · rw [hw, _root_.one_mul]
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi p y') (hi p y) ?_
    ext w
    have := hχ p y' w
    rw [basePt_congr y y' h.1] at this
    exact this.trans (hχ p y w).symm
  · have h := hA S y
    have e : evR Xo c χ y = h.choose_spec.choose (χ h.choose h.choose_spec.choose_spec.choose) := dif_pos h
    rw [e]
    exact ⟨(hi _ _).map _, hmap _ S _ _ y h.choose_spec.choose_spec.choose_spec.1⟩

theorem exists_index_map (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (hcl : FnAlgClosed (Xo := Xo) (c := c)) :
    ∃ k : Xo.XF c → Fin F.n, (∀ i, IsClopen (k ⁻¹' {i})) ∧ ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P,
      IsPeriod (F.Di i) ty P → y.x = F.u i P → k (basePt (S := CAt σ) y (IsLocalRing.closedPoint ℂ)) = i := by
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := c.fin
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  let pr : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ →
      (p ≫ pr) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, CompIdem.spMap_comp]
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    refine const_on_component_of_closed σ s (fun Z x hx => ?_) (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
    have hx' : IsIntegral c.F (A := kap Z) x := hx
    obtain ⟨k, hk⟩ := hcl Z (algebraMap (kap Z) (Om Z) x) hx'.algebraMap.isAlgebraic
    rw [IsScalarTower.algebraMap_apply c.F (kap Z) (Om Z)] at hk
    exact ⟨k, (algebraMap (kap Z) (Om Z)).injective hk⟩
  have hex : ∀ z : Xo.XF c, ∃ i : Fin F.n, ∃ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ ∧
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i := by
    intro z
    obtain ⟨p, hp, hz⟩ := exists_complex_point σ s (isOpen_connectedComponent_of_noetherianSpace z)
      ⟨z, mem_connectedComponent⟩
    obtain ⟨i, P, hP, e⟩ := F.onto _ (hover p hp)
    exact ⟨i, p, hp, hz, e ▸ ht i P hP⟩
  choose k hk using hex
  have hk' : ∀ (z : Xo.XF c) (q : Sp ℂ ⟶ Xo.XF c), q ≫ s = spMap σ →
      q (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z → t (q ≫ pr) = k z := by
    intro z q hq hz
    obtain ⟨p, hp, h1, h2⟩ := hk z
    rw [← h2]
    exact hconst q p hq hp (connectedComponent_eq h1 ▸ hz)
  have hkc : ∀ z w, w ∈ connectedComponent z → k w = k z := by
    intro z w h
    obtain ⟨p, hp, h1, h2⟩ := hk w
    exact Fin.ext (h2.symm.trans (hk' z p hp (connectedComponent_eq h ▸ h1)))
  refine ⟨k, fun i => ?_, fun y i P hP hy => ?_⟩
  · refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hkc z w hw).symm.trans h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hkc z w hw).trans hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  · let p : Sp ℂ ⟶ Xo.XF c := basePt (S := CAt σ) y
    have hp : p ≫ s = spMap σ := pullback.lift_snd _ _ _
    have hp' : t (p ≫ pr) = i := by
      have : p ≫ pr = F.u i P := (pullback.lift_fst _ _ _).trans hy
      rw [this]
      exact ht i P hP
    exact Fin.ext ((hk' _ p hp mem_connectedComponent).symm.trans hp')

theorem exists_orthogonal_idempotents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : Fin F.n → Rul Xo c, (∀ i, χ i ∈ sec Xo c 0 0) ∧ (∀ i, χ i * χ i = χ i) ∧ (∀ i i', i ≠ i' → χ i * χ i' = 0) ∧ ∑ i, χ i = 1 ∧ ∀ (y : FrPt Xo c (CAt σ)) (i i' : Fin F.n) P, IsPeriod (F.Di i') ty P → y.x = F.u i' P → toC (evR Xo c (χ i) y) = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo c σ g ty F hcl
  classical
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.allSixLaws.1.secBaseChange E H D l Xo c
  obtain ⟨k, hk, hv⟩ := exists_index_map σ F hcl
  choose χ h1 h2 h3 using fun i => exists_indicator_test hA _ (hk i)
  have ho := fun (p : TRing c.F) (y : FrPt Xo c p.R) => orthogonal_of_fibres (fun i => χ i p y)
    (fun i => (h2 i p y).1) (fun z => k (basePt y z)) fun i z => (h2 i p y).2 z
  refine ⟨χ, h1, fun i => ?_, fun i j hij => ?_, ?_, fun y i i' P hP hy => ?_⟩
  · funext p y
    exact (h2 i p y).1.eq
  · funext p y
    exact (ho p y).1 i j hij
  · funext p y
    rw [Finset.sum_apply, Finset.sum_apply]
    exact (ho p y).2
  · have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    obtain ⟨h4, h5⟩ := h3 i (CAt σ) y
    let v : ℂ := evR Xo c (χ i) (S := CAt σ) y
    have h6 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔
        k (basePt (S := CAt σ) y (IsLocalRing.closedPoint ℂ)) = i := h5 (IsLocalRing.closedPoint ℂ)
    have h8 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔ v ≠ 0 := by
      show v ∉ IsLocalRing.maximalIdeal ℂ ↔ _
      rw [IsLocalRing.notMem_maximalIdeal, isUnit_iff_ne_zero]
    rw [h8, hv y i' P hP hy] at h6
    have h9 : IsIdempotentElem v := h4
    show v = _
    split_ifs with h
    · exact (IsIdempotentElem.iff_eq_zero_or_one.1 h9).resolve_left (h6.2 h)
    · exact not_not.1 (mt h6.1 h)

end GlobalTheory.CompSystem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPeriodSpacePermOfComplexAut
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjPermutesAnyLevel

open GlobalTheory.ConjPermutes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_map (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : ∀ x : KA l, σ x = (x : ℂ)) (τ : ℂ ≃+* ℂ)
    (hτ : ∀ x : KA l, τ (x : ℂ) = x) :
    ∃ π : Fin F.n → Fin F.n, ConjugationPermutesPeriods F τ π := by
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := RingHom.ext fun x => by
    show τ (σ x) = σ x
    rw [hA, hτ]
  have hon : ∀ i P, IsPeriod (F.Di i) ty P → ∃ i' P', IsPeriod (F.Di i') ty P' ∧
      F.u i' P' = spMap (τ : ℂ →+* ℂ) ≫ F.u i P := fun i P hP =>
    F.onto _ (by rw [Category.assoc, F.over_σ i P hP, ConjPermutes.spMap_comp, hτσ])
  choose P₀ hP₀ using exists_period F hty
  choose π P₁ hP₁ hu₁ using fun i => hon i (P₀ i) (hP₀ i)
  refine ⟨π, fun i P hP => ?_⟩
  obtain ⟨i', P', hP', hu'⟩ := hon i P hP
  obtain ⟨c₀⟩ : Nonempty (Coeff l) := inferInstance
  obtain ⟨c, -, hc⟩ := _root_.GlobalTheory.CompRat.exists_coeff_idempotents_any_level E H D l Xo σ g ty F hD hσ hty hA c₀
  obtain ⟨e, he, hv⟩ := hc (π i)
  let j : c.F →+* ℂ := (τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom
  have hj : (τ : ℂ →+* ℂ).comp j = c.F.val.toRingHom := RingHom.ext fun a => τ.apply_symm_apply _
  have hjσ : σ = j.comp (IntermediateField.inclusion c.le).toRingHom := RingHom.ext fun x => by
    rw [hA]
    exact (τ.symm_apply_eq.2 (hτ x).symm).symm
  have w : ∀ Q, IsPeriod (F.Di i) ty Q →
      F.u i Q ≫ Xo.s = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := fun Q hQ => by
    rw [F.over_σ i Q hQ, ConjPermutes.spMap_comp, ← hjσ]
  have key : ∀ Q (hQ : IsPeriod (F.Di i) ty Q) k Q', IsPeriod (F.Di k) ty Q' →
      F.u k Q' = spMap (τ : ℂ →+* ℂ) ≫ F.u i Q →
      τ (valAt' (X := Xo.XF c) (pullback.lift _ _ (w Q hQ)) ⊤ e) = if k = π i then 1 else 0 := by
    intro Q hQ k Q' hQ' h
    rw [← hv k Q' hQ' (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift _ _ (w Q hQ))
      (by rw [Category.assoc, pullback.lift_fst, h]) (by rw [Category.assoc, pullback.lift_snd, ConjPermutes.spMap_comp, hj]),
      valAt'_spMap_comp]
    rfl
  have hconst := _root_.GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel E H D l Xo σ g ty F hD hσ hty c j e {0, 1} (Set.toFinite _)
    (fun x _ => valAt'_idem x he) i P (P₀ i) hP (hP₀ i) (pullback.lift _ _ (w P hP))
    (pullback.lift _ _ (w _ (hP₀ i))) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have h₁ := key P hP i' P' hP' hu'
  rw [hconst, key _ (hP₀ i) (π i) (P₁ i) (hP₁ i) (hu₁ i), if_pos rfl] at h₁
  obtain rfl : i' = π i := by
    by_contra hne
    rw [if_neg hne] at h₁
    exact one_ne_zero h₁
  exact ⟨P', hP', hu'.symm⟩

theorem exists_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ τ : ℂ ≃+* ℂ, (∀ x : KA l, τ (x : ℂ) = x) → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  intro E _ _ _ H D l Xo σ g ty F hD hσ hty hA τ hτ
  obtain ⟨π, hπ⟩ := exists_map F hD hσ hty hA τ hτ
  obtain ⟨π', hπ'⟩ := exists_map F hD hσ hty hA τ.symm (fun x => τ.symm_apply_eq.2 (hτ x).symm)
  have hinv : Function.LeftInverse π' π := fun i => by
    obtain ⟨P, hP⟩ := exists_period F hty i
    obtain ⟨P', hP', h'⟩ := hπ i P hP
    obtain ⟨P'', hP'', h''⟩ := hπ' (π i) P' hP'
    have e : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := RingHom.ext fun a => τ.symm_apply_apply a
    have e' : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id (CommRingCat.of ℂ)
    rw [← h', ← Category.assoc, ConjPermutes.spMap_comp, e, e', Category.id_comp] at h''
    exact (F.disj _ _ _ _ hP hP'' h'').symm
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 hinv.injective), hπ⟩

end GlobalTheory.ConjPermutesAnyLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfDefiniteStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p = 0 ∨ D.q = 0 → SplitLat D := by
  first | exact @GlobalTheory.CompRat.splitLat_of_definite | exact GlobalTheory.CompRat.splitLat_of_definite | (intros; apply GlobalTheory.CompRat.splitLat_of_definite <;> assumption)
end

