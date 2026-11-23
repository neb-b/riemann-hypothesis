module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFactorOfMemRange
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ

theorem tsum_mem_range_of_norm_cut (T : CDVR) {K : Type} [NormedField K] [CompleteSpace K] (i' : T.Fr →+* K)
    (hn : ∀ x : T.Fr, ‖i' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V T.Fr)) (t : T.V)
    (ht : ‖i' (algebraMap T.V T.Fr t)‖ < 1) (a : ℕ → T.V) :
    ∃ L : T.V, i' (algebraMap T.V T.Fr L) =
      ∑' k : ℕ, i' (algebraMap T.V T.Fr (a k)) * i' (algebraMap T.V T.Fr t) ^ k := by
  set φ : T.V →+* K := i'.comp (algebraMap T.V T.Fr) with hφ
  have hle : ∀ v : T.V, ‖φ v‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  change ‖φ t‖ < 1 at ht
  change ∃ L : T.V, φ L = ∑' k : ℕ, φ (a k) * φ t ^ k
  have htm : t ∈ IsLocalRing.maximalIdeal T.V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    have h1 : ‖φ u‖ * ‖φ (u⁻¹ : T.Vˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul]; simp
    have h2 := hle (u⁻¹ : T.Vˣ)
    nlinarith [norm_nonneg (φ u), norm_nonneg (φ (u⁻¹ : T.Vˣ))]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by
    simpa using hπ.ne_zero
  have hπn : ‖φ π‖ < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖i' (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hc
    obtain ⟨v, hv⟩ := (hn _).1 h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hv, map_one, mul_inv_cancel₀ hπ0]
  have hpow : ∀ (n : ℕ) (x : T.V), x ∈ IsLocalRing.maximalIdeal T.V ^ n → ‖φ x‖ ≤ ‖φ π‖ ^ n := by
    intro n x hx
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
    obtain ⟨b, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle b)
  let S : ℕ → T.V := fun n => ∑ k ∈ Finset.range n, a k * t ^ k
  have hS : ∀ {m n : ℕ}, m ≤ n →
      S m ≡ S n [SMOD (IsLocalRing.maximalIdeal T.V ^ m • ⊤ : Submodule T.V T.V)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    simp only [S]
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    refine Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ ?_
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (Ideal.pow_mem_pow htm k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal T.V) (M := T.V) inferInstance hS
  refine ⟨L, ?_⟩
  have hsum : Summable fun k : ℕ => φ (a k) * φ t ^ k := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) ht) fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle _)
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, φ (a k) * φ t ^ k) Filter.atTop (nhds (φ L)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπn)
    have h3 := hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h3
    have h4 := hpow n _ h3
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [S, map_sub, map_sum] using h4
  exact tendsto_nhds_unique h2 h1

theorem exists_factor_of_mem_range {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* C) (g : B →+* C)
    (hg : Function.Injective g) (h : ∀ a, ∃ b, g b = f a) : ∃ e : A →+* B, g.comp e = f := by
  choose e he using h
  refine ⟨{ toFun := e, map_one' := hg ?_, map_mul' := fun x y => hg ?_, map_zero' := hg ?_,
            map_add' := fun x y => hg ?_ }, RingHom.ext he⟩ <;> simp [he]

theorem eval_factors_through_cdvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv T' : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K) (j : Tv.V →+* T'.V) (i' : T'.Fr →+* K), ϖ ≠ 0 → (∀ v, i' (algebraMap T'.V T'.Fr (j v)) = ιT (algebraMap Tv.V Tv.Fr v)) → (∀ x : T'.Fr, ‖i' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V T'.Fr)) → ∀ (t : T'.V) (Y : ArcLt Dw → T'.V) (ev : ArcSR Dw Tv.V ϖ →+* K), ‖i' (algebraMap T'.V T'.Fr t)‖ < 1 → (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * i' (algebraMap T'.V T'.Fr t) ^ k) → (∀ x, ev (arcXR Dw Tv.V ϖ x) = i' (algebraMap T'.V T'.Fr (Y x))) → ∃ (e₀ : PowerSeries Tv.V →+* T'.V) (e₁ : ArcSR Dw Tv.V ϖ →+* T'.Fr), e₀.comp (PowerSeries.C (R := Tv.V)) = j ∧ e₁.comp (arcιR Dw Tv.V ϖ) = (algebraMap T'.V T'.Fr).comp e₀ ∧ (∀ x, e₁ (arcXR Dw Tv.V ϖ x) = algebraMap T'.V T'.Fr (Y x)) ∧ i'.comp e₁ = ev := by
  intro E _ _ _ H Dw Tv T' ϖ K _ _ _ ιT j i' _ hj hn t Y ev ht hp hX
  have hinj : Function.Injective (i'.comp (algebraMap T'.V T'.Fr)) :=
    i'.injective.comp (IsFractionRing.injective T'.V T'.Fr)
  have h0 : ∀ p : PowerSeries Tv.V,
      ∃ b, (i'.comp (algebraMap T'.V T'.Fr)) b = (ev.comp (arcιR Dw Tv.V ϖ)) p := by
    intro p
    obtain ⟨L, hL⟩ := tsum_mem_range_of_norm_cut T' i' hn t ht (fun k => j (PowerSeries.coeff k p))
    refine ⟨L, ?_⟩
    simp only [RingHom.comp_apply]
    rw [hL, hp]
    simp only [hj]
  obtain ⟨e₀, he₀⟩ := exists_factor_of_mem_range _ _ hinj h0
  have hpoly : ∀ a : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V),
      ev (algebraMap _ (ArcSR Dw Tv.V ϖ) a) ∈ i'.fieldRange := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C p =>
      obtain ⟨b, hb⟩ := h0 p
      exact ⟨_, hb⟩
    | add p q hp' hq' => rw [map_add (f := _), map_add (f := _)]; exact add_mem hp' hq'
    | mul_X p x hp' =>
      rw [map_mul (algebraMap _ (ArcSR Dw Tv.V ϖ)) p, map_mul ev]
      exact mul_mem hp' ⟨_, (hX x).symm⟩
  have h1 : ∀ z : ArcSR Dw Tv.V ϖ, ∃ b, i' b = ev z := by
    intro z
    obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj
      (Submonoid.powers (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw Tv.V)) z
    have hu := (IsLocalization.map_units (ArcSR Dw Tv.V ϖ) s).map ev
    have hz' := congrArg ev hz
    rw [map_mul ev] at hz'
    have : ev z ∈ i'.fieldRange := by
      rw [eq_div_of_mul_eq hu.ne_zero hz']
      exact div_mem (hpoly _) (hpoly _)
    exact this
  obtain ⟨e₁, he₁⟩ := exists_factor_of_mem_range _ _ i'.injective h1
  refine ⟨e₀, e₁, ?_, ?_, fun x => ?_, he₁⟩
  · refine RingHom.ext fun v => hinj ?_
    have h2 := RingHom.congr_fun he₀ (PowerSeries.C v)
    simp only [RingHom.comp_apply] at h2 ⊢
    rw [h2, hp, tsum_eq_single 0, hj]
    · simp
    · intro k hk
      simp [PowerSeries.coeff_C, hk]
  · refine RingHom.ext fun p => i'.injective ?_
    have h2 := RingHom.congr_fun he₀ p
    have h3 := RingHom.congr_fun he₁ (arcιR Dw Tv.V ϖ p)
    simp only [RingHom.comp_apply] at h2 h3 ⊢
    rw [h2, h3]
  · apply i'.injective
    rw [← hX x]
    exact RingHom.congr_fun he₁ _

end GlobalTheory.ArcQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinSiteSiteAlg
section
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FreeQuotientRank Formalism.L2.Pj Formalism.L2.Pj.QAt

section Norm

variable {V F C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F] [NormedField C] (f : F →+* C)
  (hf : ∀ v : V, ‖f (algebraMap V F v)‖ ≤ 1)

include hf

omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V F] in
theorem norm_map_unit_eq_one (u : Vˣ) : ‖f (algebraMap V F u)‖ = 1 := by
  have h : ‖f (algebraMap V F u)‖ * ‖f (algebraMap V F (u⁻¹ : Vˣ))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  exact le_antisymm (hf _) (h.ge.trans (mul_le_of_le_one_right (norm_nonneg _) (hf _)))

theorem norm_map_eq_zpow_vV {π : V} (hπ : Irreducible π) {x : F} (hx : x ≠ 0) :
    ‖f x‖ = ‖f (algebraMap V F π)‖ ^ vV V x := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  have hv : vV V (u • algebraMap V F π ^ n) = n := by
    rw [vV, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      PlaceCompletion.valV_algebraMap_of_isUnit u.isUnit,
      PlaceCompletion.valV_algebraMap_of_irreducible hπ, one_mul, ← WithZero.exp_zsmul,
      WithZero.log_exp]
    simp
  rw [hv, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, norm_mul, norm_zpow,
    norm_map_unit_eq_one f hf, one_mul]

theorem norm_map_le_one_iff {π : V} (hπ : Irreducible π) (h1 : ‖f (algebraMap V F π)‖ < 1) (x : F) :
    ‖f x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V F) := by
  refine ⟨fun h => ?_, by rintro ⟨v, rfl⟩; exact hf v⟩
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have h0 : 0 < ‖f (algebraMap V F π)‖ := norm_pos_iff.2 ((map_ne_zero f).2
    ((map_ne_zero_iff _ (IsFractionRing.injective V F)).2 hπ.ne_zero))
  rw [norm_map_eq_zpow_vV f hf hπ hx, zpow_le_one_iff_right_of_lt_one₀ h0 h1] at h
  refine PlaceCompletion.exists_algebraMap_eq_of_valV_le_one ?_
  rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [vV] at h
  omega

end Norm


open DiscEval in
theorem exists_finSite_siteAlg :
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)),
      (∃ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes ∧ OverLa w Tv.V io 1) ∧
      ∀ (Tv : CDVR) (io : K₁ →+* Tv.Fr) (e : ℕ), Tv.FinRes → OverLa w Tv.V io e →
        ∃ (Z : FinSite K₁ w) (ιT : Tv.Fr →+* Z.K), ιT.comp io = Z.ι ∧
          (∀ x : Tv.Fr, ‖ιT x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap Tv.V Tv.Fr)) ∧ SiteAlg Z Tv ιT := by
  intro K₁ _ _ w
  refine ⟨?_, fun Tv io e hfin ho => ?_⟩
  · obtain ⟨T, io, h1, h2, -⟩ := PlaceCompletion.exists_initial_completion K₁ w
    exact ⟨T, io, h2, h1⟩
  haveI : Finite (IsLocalRing.ResidueField Tv.V) := hfin
  obtain ⟨p, _, _, _⟩ := exists_padicInt_algebra_finite Tv.V
  obtain ⟨i, hinj, hi⟩ := exists_injective_norm_le_one (p := p) Tv.V
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let ιT : Tv.Fr →+* ℂ_[p] := IsFractionRing.lift hinj
  have hι : ∀ v, ιT (algebraMap Tv.V Tv.Fr v) = i v := fun v => IsFractionRing.lift_algebraMap hinj v
  have hf : ∀ v, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := fun v => by rw [hι]; exact hi v
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  have h0 : 0 < ‖i π‖ := norm_pos_iff.2 ((map_ne_zero_iff i hinj).2 hπ.ne_zero)
  have h1 : ‖i π‖ < 1 :=
    (hi π).lt_of_ne fun h => hπ.not_isUnit ((norm_map_eq_one_iff i hi hinj π).1 h)
  let Z : FinSite K₁ w :=
    { K := ℂ_[p]
      ι := ιT.comp io
      r := ‖i π‖ ^ e
      r_pos := pow_pos h0 e
      r_lt := pow_lt_one₀ h0.le h1 ho.1.ne'
      norm_ι := fun x hx => by
        rw [RingHom.comp_apply, norm_map_eq_zpow_vV ιT hf hπ ((map_ne_zero io).2 hx), hι, ho.2 x,
          zpow_mul, zpow_natCast]
        rfl
      K₀ := algField p
      res := residueFieldInfiniteOn_algField p
      S := algDisc p
      S_disc := fun _ ht => ht.2
      S_dense := algDisc_dense p
      S_units := mul_mem_algDisc p }
  refine ⟨Z, ιT, rfl, norm_map_le_one_iff ιT hf hπ (by rw [hι]; exact h1), ?_⟩
  intro (s : Finset ℂ_[p]) hs
  have hsK : (s : Set ℂ_[p]) ⊆ algField p := fun x hx => (hs x hx).1.elim id fun h => h.1
  haveI := finiteDimensional_genField i hi s.finite_toSet
  set L := genField i (s : Set ℂ_[p])
  haveI : CharZero (integralClosure ℤ_[p] L) := RingHom.charZero (intEmb L)
  let T' : CDVR := { V := integralClosure ℤ_[p] L, cpl := isAdicComplete_integralClosure L }
  obtain ⟨j, hj⟩ := exists_comp_eq_of_mem_range _ (intEmb_injective L) i fun a =>
    (mem_range_intEmb_iff _ _).2 ⟨map_mem_genField i hi hsK a, hi a⟩
  let i' : FractionRing (integralClosure ℤ_[p] L) →+* ℂ_[p] := IsFractionRing.lift (intEmb_injective L)
  have hi' : ∀ v, i' (algebraMap _ _ v) = intEmb L v := fun v =>
    IsFractionRing.lift_algebraMap (intEmb_injective L) v
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[p] L)
  refine ⟨T', j, i', finite_residueField_integralClosure L, isLocalHom_of_intEmb_eq i hi L hinj hj,
    fun v => (hi' _).trans ((hj v).trans (hι v).symm),
    norm_map_le_one_iff i' (fun v => by rw [hi']; exact norm_intEmb_le_one L v) hπ' (by
      rw [hi', ← mem_maximalIdeal_iff_norm]
      exact hπ'.not_isUnit), fun x hx => ?_⟩
  obtain ⟨v, hv⟩ := (mem_range_intEmb_iff L x).2 ⟨mem_genField_of_mem i hi hsK hx, (hs x hx).2⟩
  exact ⟨v, (hi' v).trans hv⟩

end GlobalTheory.ArcQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramePeriodsAlongIsotropicFlowAndBlockChange
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.PerFlow

open Matrix
open scoped ComplexConjugate ComplexOrder

section aux

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma perFr_mem (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X x v τ.1 i =
      if hi : X.p0 + i < r then ((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) ⟨X.p0 + i, hi⟩ else 0 := by
  unfold perFr
  rw [dif_pos τ.2]

lemma perFr_conj (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (j : Fin r)
    (hj : (j : ℕ) = X.p0 - 1 - i) :
    perFr X x v (conjEmb τ.1) i = hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
  have hcc : conjEmb (conjEmb τ.1) = τ.1 := by
    ext a; simp [conjEmb]
  have h1 : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have h2 : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [hcc]; exact τ.2
  have h3 : X.p0 - 1 - i < r := hj ▸ j.2
  unfold perFr
  rw [dite_eq_right h1, dif_pos h2, dif_pos h3]
  have key : ∀ (σ : E →+* ℂ) (hσ : σ ∈ X.Ψ), σ = τ.1 →
      hermC σ X.Gm (FD.col (mat x ⟨σ, hσ⟩) ⟨X.p0 - 1 - i, h3⟩) (Data.emb σ v) =
        hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
    intro σ hσ h
    subst h
    have : (⟨X.p0 - 1 - i, h3⟩ : Fin r) = j := Fin.ext hj.symm
    rw [this]
  exact key _ h2 hcc

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (u : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ u =
      u + (s * τ.1 X.κ0 * hermC τ.1 X.Gm u (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  rw [EmbeddingHermitianPairs.flowMat_eq, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    EmbeddingHermitianPairs.wv_dot, X.tau_kappa0]
  funext a
  simp
  ring

lemma flow_mem {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) (x : Frame X.Ψ r)
    (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X (X.flow ξ s x) v τ.1 i =
      perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i := by
  simp only [perFr_mem]
  split_ifs with hi
  · have hm : mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl
    have hinv : (X.flowMat ξ τ (s τ))⁻¹ = X.flowMat ξ τ (-s τ) := by
      apply inv_eq_right_inv
      rw [EmbeddingHermitianPairs.flowMat_mul X hξ, add_neg_cancel, EmbeddingHermitianPairs.flowMat_zero]
    have he : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm v ξ) :=
      EmbeddingHermitianPairs.hermC_emb _ _ _ _
    rw [hm, Matrix.mul_inv_rev, hinv, ← mulVec_mulVec, flowMat_mulVec, mulVec_add, mulVec_smul, he,
      map_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp

lemma flow_conj (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r)
    (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (hi : i < X.p0) :
    perFr X (X.flow ξ s x) v (conjEmb τ.1) i =
      perFr X x v (conjEmb τ.1) i -
        s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i := by
  have hlt : X.p0 - 1 - i < r := by have := X.p0_le; omega
  simp only [perFr_conj X _ _ τ i ⟨_, hlt⟩ rfl]
  have hc : FD.col (mat (X.flow ξ s x) τ) ⟨_, hlt⟩ =
      X.flowMat ξ τ (s τ) *ᵥ FD.col (mat x τ) ⟨_, hlt⟩ := rfl
  have he : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm v ξ) :=
    EmbeddingHermitianPairs.hermC_emb _ _ _ _
  have he' : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 v) = conj (τ.1 (herm X.Gm v ξ)) := by
    rw [← he, hermC_conj τ.1 X.Gm_herm]
  have hk : conj (τ.1 X.κ0) = -τ.1 X.κ0 := by
    rw [← EmbeddingHermitianPairs.emb_cc', X.cc_kappa0, map_neg]
  have h2 : conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) = -τ.1 X.κ0 * conj (τ.1 (herm X.Gm v ξ)) := by
    rw [← hk, ← map_mul, ← map_mul]; rfl
  rw [hc, flowMat_mulVec, hermC_add_left, hermC_smul_left, he', h2]
  ring

def blockEquiv : Fin X.p0 ⊕ Fin (r - X.p0) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by have := X.p0_le; omega))

lemma blockEquiv_inl (a : Fin X.p0) : blockEquiv X (.inl a) = Fin.castLE X.p0_le a := by
  apply Fin.ext; simp [blockEquiv]

lemma blockEquiv_inr (a : Fin (r - X.p0)) : ((blockEquiv X (.inr a) : Fin r) : ℕ) = X.p0 + a := by
  simp [blockEquiv]

def blk (P : Matrix (Fin X.p0) (Fin X.p0) ℂ) (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.reindex (blockEquiv X) (blockEquiv X) (fromBlocks P 0 0 Q)

lemma blk_mul (P P' : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q Q' : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) :
    blk X P Q * blk X P' Q' = blk X (P * P') (Q * Q') := by
  simp [blk, fromBlocks_multiply]

lemma blk_one : blk X 1 1 = 1 := by
  simp [blk]

lemma blk_mulVec_inr (P : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (w : Fin r → ℂ) (i : Fin (r - X.p0)) :
    (blk X P Q *ᵥ w) (blockEquiv X (.inr i)) = ∑ k, Q i k * w (blockEquiv X (.inr k)) := by
  simp only [mulVec, dotProduct]
  rw [← (blockEquiv X).sum_comp]
  simp [blk, Fintype.sum_sum_type]

lemma col_mul_blk (M : Matrix (Fin r) (Fin r) ℂ) (P : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (j : Fin X.p0) :
    FD.col (M * blk X P Q) (Fin.castLE X.p0_le j) =
      ∑ k, P k j • FD.col M (Fin.castLE X.p0_le k) := by
  funext a
  simp only [FD.col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ← blockEquiv_inl]
  rw [← (blockEquiv X).sum_comp]
  simp [blk, Fintype.sum_sum_type, mul_comm]

lemma block_change (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ)
    (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ) (hA : ∀ τ, (A τ).det ≠ 0) (hB : ∀ τ, (B τ).det ≠ 0) :
    ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ),
      (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧
      ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  let P : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ :=
    fun τ => ((B τ).submatrix Fin.revPerm Fin.revPerm)ᵀ
  have hP : ∀ τ, (P τ).det ≠ 0 := fun τ => by
    simp only [P, det_transpose, det_submatrix_equiv_self]; exact hB τ
  let x' : Frame X.Ψ r := fun τ => (mat x τ * blk X (P τ) (A τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
  have hm : ∀ τ, mat x' τ = mat x τ * blk X (P τ) (A τ)⁻¹ := fun τ => rfl
  have hone : ∀ τ, blk X (P τ) (A τ)⁻¹ * blk X (P τ)⁻¹ (A τ) = 1 := fun τ => by
    rw [blk_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hP τ)),
      nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hA τ)), blk_one]
  have hcol : ∀ τ j, X.colP x' τ j = ∑ k, P τ k j • X.colP x τ k := fun τ j => by
    unfold Data.colP
    rw [hm, col_mul_blk]
  refine ⟨x', AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩, fun v τ => ⟨fun i => ?_, fun i => ?_⟩⟩
  · rw [hm, det_mul]
    refine mul_ne_zero (hx τ).1 fun h0 => ?_
    have := congrArg det (hone τ)
    rw [det_mul, h0] at this
    simp at this
  · have hg : X.gramPos x' τ = (P τ)ᵀ * X.gramPos x τ * ((P τ)ᵀ)ᴴ := by
      ext a b
      rw [Data.gramPos_apply, hcol, hcol, hermC_sum_right]
      simp only [Matrix.mul_apply, hermC_smul_right, hermC_sum_left, hermC_smul_left,
        conjTranspose_apply, transpose_apply, Data.gramPos_apply, Complex.star_def]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hg]
    refine (X.gramPos_posDef hx τ).mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (by rw [det_transpose]; exact hP τ)))
  · have hlt : ∀ k : Fin (r - X.p0), X.p0 + k < r := fun k => by have := k.2; omega
    have hidx : ∀ k : Fin (r - X.p0), (⟨X.p0 + k, hlt k⟩ : Fin r) = blockEquiv X (.inr k) :=
      fun k => Fin.ext (blockEquiv_inr X k).symm
    simp only [perFr_mem, dif_pos (hlt _), hidx]
    rw [hm, Matrix.mul_inv_rev, inv_eq_right_inv (hone τ), ← mulVec_mulVec, blk_mulVec_inr]
  · have hr : ∀ (y : Frame X.Ψ r) (k : Fin X.p0), perFr X y v (conjEmb τ.1) k =
        hermC τ.1 X.Gm (X.colP y τ k.rev) (Data.emb τ.1 v) := fun y k =>
      perFr_conj X y v τ k (Fin.castLE X.p0_le k.rev) (by simp [Fin.val_rev]; omega)
    simp only [hr]
    rw [hcol, hermC_sum_left, ← Equiv.sum_comp Fin.revPerm]
    simp [P, hermC_smul_left]

end aux

theorem perFr_flow_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ ξ, herm X.Gm ξ ξ = 0 → ∀ (s : X.Ψ → ℂ), ∀ x ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ) (i : ℕ), perFr X (X.flow ξ s x) v τ.1 i = perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i ∧ (i < X.p0 → perFr X (X.flow ξ s x) v (conjEmb τ.1) i = perFr X x v (conjEmb τ.1) i - s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i)) ∧ ∀ x ∈ X.dom, ∀ (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ), (∀ τ, (A τ).det ≠ 0) → (∀ τ, (B τ).det ≠ 0) → ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ), (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧ ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  intro E _ _ _ r X
  exact ⟨fun ξ hξ s x _ v τ i => ⟨flow_mem X hξ s x v τ i, flow_conj X ξ s x v τ i⟩,
    fun x hx A B hA hB => block_change X x hx A B hA hB⟩

end GlobalTheory.PerFlow
end

