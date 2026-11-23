module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import ReciprocityTheory.DualLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
section
open GlobalTheory.SliceSchwartz
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def padL {κ κ' : Type} (h : κ → V) : κ ⊕ κ' → V := Sum.elim h 0

def qOp {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (s : κ ⊕ κ₁' → V) : ℂ :=
  P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr)

abbrev pd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) :
    SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap X ℂ) w

theorem pd_apply {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) (f : SchwartzMap X ℂ) (x : X) :
    pd w f x = fderiv ℝ f x w := by
  simp [pd, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem clm_sup_bound {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : SchwartzMap X ℂ →L[ℂ] SchwartzMap Y ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : SchwartzMap X ℂ,
      s.sup (schwartzSeminormFamily ℂ Y ℂ) (T f) ≤ C * s'.sup (schwartzSeminormFamily ℂ X ℂ) f := by
  have hp : Continuous ((s.sup (schwartzSeminormFamily ℂ Y ℂ)).comp T.toLinearMap) :=
    (Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ Y ℂ).continuous_seminorm i).comp
      T.continuous
  obtain ⟨s', C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X ℂ) _ hp
  refine ⟨s', C, C.2, fun f => ?_⟩
  have := hC f
  simpa [Seminorm.smul_apply, NNReal.smul_def] using this

end GlobalTheory.SliceOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionRestrictClopenFactorization
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem clopen_cut_closedImmersion : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  intro X Z₁ i hi U hU
  have hVc : IsClosed (Set.range (i ⁻¹ᵁ U).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact hU.preimage i.base.hom.continuous
  haveI : IsClosedImmersion (i ⁻¹ᵁ U).ι := IsClosedImmersion.of_isPreimmersion _ hVc
  refine ⟨(i ⁻¹ᵁ U), (i ⁻¹ᵁ U).ι ≫ i, inferInstance, fun T g => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ (i ⁻¹ᵁ U).ι, by simp⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    have : ((i ⁻¹ᵁ U).ι.base (z.base t)) ∈ (i ⁻¹ᵁ U : Set Z₁) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    simpa [Scheme.Hom.comp_base] using this
  · rintro ⟨⟨y, rfl⟩, hg⟩
    have h : Set.range y.base ⊆ Set.range (i ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      have := hg ⟨t, rfl⟩
      simpa using this
    exact ⟨IsOpenImmersion.lift (i ⁻¹ᵁ U).ι y h, by rw [← Category.assoc, IsOpenImmersion.lift_fac]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe
section
open GlobalTheory

namespace GlobalTheory

open MvPolynomial

variable {R : Type} [CommRing R] {n : ℕ}

theorem eval_mem_span_pow_of_le_degree (z : Fin n → R) (m : ℕ) (P : MvPolynomial (Fin n) R)
    (hP : ∀ β, P.coeff β ≠ 0 → m ≤ β.degree) :
    MvPolynomial.eval z P ∈ Ideal.span (Set.range z) ^ m := by
  rw [MvPolynomial.eval_eq]
  refine Ideal.sum_mem _ fun β hβ => ?_
  have h1 := monoVal_mem_pow z (⟨β, rfl⟩ : MonoDeg (Fin n) β.degree)
  exact Ideal.mul_mem_left _ _
    (Ideal.pow_le_pow_right (hP β (MvPolynomial.mem_support_iff.mp hβ)) h1)

theorem exists_eval_eq_shift (z : Fin n → R) (P : MvPolynomial (Fin n) R)
    (hP : ∀ β, P.coeff β ∈ Ideal.span (Set.range z)) :
    ∃ G : MvPolynomial (Fin n) R, MvPolynomial.eval z G = MvPolynomial.eval z P ∧
      ∀ γ, G.coeff γ ≠ 0 → ∃ β j, P.coeff β ≠ 0 ∧ γ = β + Finsupp.single j 1 := by
  classical
  choose g hg using fun β => (Ideal.mem_span_range_iff_exists_fun).mp (hP β)
  refine ⟨∑ β ∈ P.support, ∑ j, MvPolynomial.monomial (β + Finsupp.single j 1) (g β j), ?_, ?_⟩
  · have key : ∀ β j, MvPolynomial.eval z (MvPolynomial.monomial (β + Finsupp.single j 1) (g β j))
        = g β j * z j * monoVal z β := by
      intro β j
      rw [MvPolynomial.eval_monomial]
      change _ * monoVal z _ = _
      rw [monoVal_add, monoVal_single, pow_one]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, key]
    rw [MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_mul, hg β]
    rfl
  · intro γ hγ
    rw [MvPolynomial.coeff_sum] at hγ
    obtain ⟨β, hβ, hβ'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
    rw [MvPolynomial.coeff_sum] at hβ'
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ'
    rw [MvPolynomial.coeff_monomial] at hj
    split_ifs at hj with h
    · exact ⟨β, j, MvPolynomial.mem_support_iff.mp hβ, h.symm⟩
    · exact absurd rfl hj

theorem weightedRelation_step (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D k : ℕ) (H : MvPolynomial (Fin n) R)
    (hH : ∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β)
    (h0 : MvPolynomial.eval z H = 0) :
    (∀ β : Fin n →₀ ℕ, β.degree = k → H.coeff β ∈ Ideal.span (Set.range z)) ∧
      ∃ H' : MvPolynomial (Fin n) R,
        (∀ β, H'.coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β) ∧
        MvPolynomial.eval z H' = 0 ∧
        ∀ β : Fin n →₀ ℕ, Finsupp.weight w β = D → k + 1 ≤ β.degree → H'.coeff β = H.coeff β := by
  classical
  set Hk := MvPolynomial.homogeneousComponent k H with hHk
  have hcoeffk : ∀ β, Hk.coeff β = if β.degree = k then H.coeff β else 0 := fun β =>
    MvPolynomial.coeff_homogeneousComponent _ _ _
  have hrest : ∀ β, (H - Hk).coeff β = if β.degree = k then 0 else H.coeff β := by
    intro β
    rw [MvPolynomial.coeff_sub, hcoeffk]
    split_ifs <;> simp
  have hrest' : ∀ β, (H - Hk).coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β := by
    intro β hβ
    rw [hrest] at hβ
    split_ifs at hβ with h
    · exact absurd rfl hβ
    · have := hH β hβ
      exact ⟨by omega, this.2⟩
  have hmem : MvPolynomial.eval z Hk ∈ Ideal.span (Set.range z) ^ (k + 1) := by
    have h1 := eval_mem_span_pow_of_le_degree z (k + 1) (H - Hk) fun β hβ => (hrest' β hβ).1
    have h2 : MvPolynomial.eval z Hk = - MvPolynomial.eval z (H - Hk) := by
      rw [map_sub, h0]
      ring
    rw [h2]
    exact neg_mem h1
  have hI : ∀ β, Hk.coeff β ∈ Ideal.span (Set.range z) :=
    (isQuasiRegularSeq_self_iff z).mp hz k Hk
      (MvPolynomial.homogeneousComponent_isHomogeneous k H) hmem
  refine ⟨fun β hβ => ?_, ?_⟩
  · have := hI β
    rwa [hcoeffk, if_pos hβ] at this
  obtain ⟨G, hG, hGs⟩ := exists_eval_eq_shift z Hk hI
  have hGw : ∀ γ, G.coeff γ ≠ 0 → k + 1 ≤ γ.degree ∧ D + 1 ≤ Finsupp.weight w γ := by
    intro γ hγ
    obtain ⟨β, j, hβ, rfl⟩ := hGs γ hγ
    rw [hcoeffk] at hβ
    split_ifs at hβ with hd
    · have := hH β hβ
      have hj := hw j
      simp only [map_add (f := _), Finsupp.degree_single, Finsupp.weight_single, one_smul, hd]
      exact ⟨le_rfl, by omega⟩
    · exact absurd rfl hβ
  refine ⟨(H - Hk) + G, ?_, ?_, ?_⟩
  · intro β hβ
    rw [MvPolynomial.coeff_add] at hβ
    by_cases h1 : (H - Hk).coeff β = 0
    · rw [h1, zero_add] at hβ
      have := hGw β hβ
      exact ⟨this.1, by omega⟩
    · exact hrest' β h1
  · rw [map_add (f := _), hG, ← map_add (f := _), sub_add_cancel, h0]
  · intro β hβw hβd
    rw [MvPolynomial.coeff_add, hrest, if_neg (by omega)]
    by_cases h : G.coeff β = 0
    · rw [h, add_zero]
    · have := hGw β h
      omega

theorem weightedRelation_coeff_mem (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D : ℕ) (j : ℕ) : ∀ (k : ℕ) (H : MvPolynomial (Fin n) R),
    (∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β) →
    MvPolynomial.eval z H = 0 → ∀ α : Fin n →₀ ℕ, α.degree = k + j →
    Finsupp.weight w α = D → H.coeff α ∈ Ideal.span (Set.range z) := by
  induction j with
  | zero =>
    intro k H hH h0 α hα _
    exact (weightedRelation_step z w hw hz D k H hH h0).1 α hα
  | succ j ih =>
    intro k H hH h0 α hα hαw
    obtain ⟨-, H', h1, h2, h3⟩ := weightedRelation_step z w hw hz D k H hH h0
    rw [← h3 α hαw (by omega)]
    exact ih (k + 1) H' h1 h2 α (by omega) hαw

theorem coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero {R : Type} [CommRing R] {n : ℕ}
    (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i) (hz : IsQuasiRegularSeq R z) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsWeightedHomogeneous w D)
    (h0 : MvPolynomial.eval z F = 0) (α : Fin n →₀ ℕ) :
    F.coeff α ∈ Ideal.span (Set.range z) := by
  by_cases hα : F.coeff α = 0
  · rw [hα]
    exact zero_mem _
  exact weightedRelation_coeff_mem z w hw hz D α.degree 0 F
    (fun β hβ => ⟨Nat.zero_le _, (hF hβ).ge⟩) h0 α (zero_add _).symm (hF hα)

theorem weightedRelation_coeff_mem_span : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R)
    (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) :=
  fun z w hw hz D F hF h0 α =>
    coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero z w hw hz D F hF h0 α

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowEqZeroOfDegreeLt
section
open MvPowerSeries ReciprocityTheory.PGsh

namespace GlobalTheory.LgSubst

theorem coeff_pow_eq_zero_of_degree_lt {M : ℕ} {C : Type} [CommRing C]
    (f : MvPowerSeries (Fin M) C) (hf : constantCoeff f = 0) (m : ℕ) (α : Fin M →₀ ℕ)
    (h : α.degree < m) : coeff α (f ^ m) = 0 := by
  apply coeff_of_lt_order
  have h1 : 1 ≤ f.order := one_le_order_iff_constCoeff_eq_zero.2 hf
  have h2 : (m : ℕ∞) ≤ (f ^ m).order :=
    le_trans (by simpa using nsmul_le_nsmul_right h1 m) (le_order_pow _)
  exact lt_of_lt_of_le (by exact_mod_cast h) h2

theorem coeff_subst_of_pow_support {M : ℕ} {C : Type} [Field C] (p : ℕ) (hp : 2 ≤ p)
    (L : PowerSeries C) (hL : ∀ m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m L = 0)
    (s : MvPowerSeries (Fin M) C) (hs : constantCoeff s = 0) (α : Fin M →₀ ℕ) :
    coeff α (PowerSeries.subst s L) =
      ∑ n ∈ Finset.range (α.degree + 1), PowerSeries.coeff (p ^ n) L * coeff α (s ^ (p ^ n)) := by
  classical
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have hinj : Function.Injective (fun n : ℕ => p ^ n) := Nat.pow_right_injective hp
  rw [PowerSeries.coeff_subst hsub]
  rw [finsum_eq_sum_of_support_subset (s := (Finset.range (α.degree + 1)).image (fun n => p ^ n))]
  · rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp only [smul_eq_mul]
  · intro m hm
    rw [Function.mem_support] at hm
    by_cases hpt : ∃ n, m = p ^ n
    · obtain ⟨n, rfl⟩ := hpt
      rw [Finset.coe_image, Set.mem_image]
      refine ⟨n, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hn
      apply hm
      have hlt : n < p ^ n := Nat.lt_pow_self (by omega)
      rw [coeff_pow_eq_zero_of_degree_lt s hs _ α (by omega), smul_zero]
    · push_neg at hpt
      exact absurd (by rw [hL m hpt, zero_smul]) hm

theorem subst_sum_lgCurve_eq_lgSum : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → ∀ (d M : ℕ) (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C), (∀ a, G.IsPTypical p (γ a)) → ∀ (t : Fin d → MvPowerSeries (Fin M) C), (∀ a, constantCoeff (t a) = 0) → ∀ e : Fin d, subst t (∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) e)) = lgSum p (fun a n => G.lc p (γ a) n) t e := by
  intro C _ _ v p hp d M G γ hγ t ht e
  have hts : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have step : ∀ a, subst t (PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) e))
      = PowerSeries.subst (t a) (G.lgCurve (γ a) e) := by
    intro a
    rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X a).const hts]
    simp only [subst_X hts]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hts, map_sum]
  simp only [coe_substAlgHom, step]
  ext α
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [coeff_subst_of_pow_support p hp.two_le _ (fun m hm => hγ _ e m hm) _ (ht _) α]
  rw [Finset.sum_comm]
  rfl

end GlobalTheory.LgSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoequifiberedGeneratedSubalgebraQuasiCoherent
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem isLocalizationAway_subring {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A')
    (S : Subring A) (S' : Subring A') (hρ : ∀ a ∈ S, ρ a ∈ S') (s : A) (hs : s ∈ S)
    (hloc : letI := ρ.toAlgebra; IsLocalization.Away s A')
    (hu : ∃ v ∈ S', ρ s * v = 1) (hd : ∀ a : A, ρ a ∈ S' → ∃ m : ℕ, s ^ m * a ∈ S) :
    (letI := (ρ.restrict S S' hρ).toAlgebra
     IsLocalization.Away (⟨s, hs⟩ : S) S') := by
  let := ρ.toAlgebra
  let := (ρ.restrict S S' hρ).toAlgebra
  refine .mk _ ?_ (fun z ↦ ?_) fun a b hab ↦ ?_
  · obtain ⟨v, hv, hsv⟩ := hu
    exact .of_mul_eq_one (⟨v, hv⟩ : S') (Subtype.ext hsv)
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := A') s (z : A')
    have ha' : ρ a = (z : A') * ρ s ^ n := ha.symm
    have hmem : ρ a ∈ S' := ha' ▸ S'.mul_mem z.2 (S'.pow_mem (hρ s hs) n)
    obtain ⟨m, hm⟩ := hd a hmem
    refine ⟨n + m, ⟨s ^ m * a, hm⟩, Subtype.ext ?_⟩
    change (z : A') * ρ s ^ (n + m) = ρ (s ^ m * a)
    rw [map_mul, map_pow, ha', pow_add]
    ring
  · have h : ρ a = ρ b := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') s (a := (a : A)) (b := (b : A)) h
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

end GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem coequifibered_subNat (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))
    (hd : ∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) →
      ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) :
    (subNat F α V T).Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  have hloc := Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp hα U f
  have hnat : (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) =
      (α.app (op (X.basicOpen f))).hom ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) := by
    have := congr($(α.naturality (homOfLE (X.basicOpen_le f)).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  have hu : ∃ v ∈ sub F α V T (X.basicOpen f),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) * v = 1 := by
    obtain ⟨w, hw⟩ : ∃ w : Γ(X, X.basicOpen f),
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f * w = 1 :=
      (X.toRingedSpace.isUnit_res_basicOpen f).exists_right_inv
    refine ⟨(α.app (op (X.basicOpen f))).hom w, algebraMap_mem_sub F α V T _ w, ?_⟩
    rw [hnat, ← map_mul, hw, map_one]
  exact isLocalizationAway_subring (F.map (homOfLE (X.basicOpen_le f)).op).hom
    (sub F α V T U.1) (sub F α V T (X.basicOpen f)) (fun a ha ↦ res_mem_sub F α V T _ ha)
    _ (algebraMap_mem_sub F α V T U.1 f) hloc hu (hd U.1 U.2 f)

end GlobalTheory.QcSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommensurableConjRangeGLSubringStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commensurable_conj_range_gl_map_subtype : ∀ {B : Type} [CommRing B] (R : Subring B) (n : ℕ) (c : R), Finite (R ⧸ Ideal.span {c * c}) → ∀ g : GL (Fin n) B, (∀ i j, (c : B) * (g : Matrix (Fin n) (Fin n) B) i j ∈ R) → (∀ i j, (c : B) * ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) → Subgroup.Commensurable ((GeneralLinearGroup.map R.subtype).range.map (MulAut.conj g).toMonoidHom) (GeneralLinearGroup.map R.subtype).range := by
  first | (exact @GlobalTheory.commensurable_conj_range_GL_subring) | (exact GlobalTheory.commensurable_conj_range_GL_subring) | (intros; apply GlobalTheory.commensurable_conj_range_GL_subring  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommensurableMapConjProdPiStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commensurable_map_conj_prod_pi' : ∀ {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)] (H : Subgroup A) (K : ∀ i, Subgroup (B i)) (g : A × ((i : Fin m) → B i)), Subgroup.Commensurable (H.map (MulAut.conj g.1).toMonoidHom) H → (∀ i, Subgroup.Commensurable ((K i).map (MulAut.conj (g.2 i)).toMonoidHom) (K i)) → Subgroup.Commensurable ((H.prod (Subgroup.pi Set.univ K)).map (MulAut.conj g).toMonoidHom) (H.prod (Subgroup.pi Set.univ K)) := by
  first | (exact @GlobalTheory.commensurable_map_conj_prod_pi) | (exact GlobalTheory.commensurable_map_conj_prod_pi) | (intros; apply GlobalTheory.commensurable_map_conj_prod_pi  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjDualPartsKilledOfPerfectPairingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_dual_parts_killed_of_perfect_pairing : ∀ (O : Type) [CommRing O] (bar : O →+* O) (U : Type) [CommRing U] [IsDomain U] (M M' : Type) [CommGroup M] [CommGroup M'] (α : O → M →* M) (α' : O → M' →* M'), (∀ y, α 1 y = y) → (∀ a b y, α (a * b) y = α a (α b y)) → (∀ a b y, α (a + b) y = α a y * α b y) → (∀ x, α' 1 x = x) → (∀ a b x, α' (a * b) x = α' a (α' b x)) → (∀ a b x, α' (a + b) x = α' a x * α' b x) → (∀ a, bar (bar a) = a) → ∀ (e : M' →* M →* Uˣ) (e' : M →* M' →* Uˣ), Function.Injective e → Function.Injective e' → (∀ a x y, e (α' a x) y = e x (α (bar a) y)) → (∀ a y x, e' (α a y) x = e' y (α' (bar a) x)) → ∀ (u w : Ideal O) (n : ℕ), u ≤ w → u ⊔ u.map bar = ⊤ → (∀ a ∈ (u * u.map bar) ^ n, (∀ y, α a y = 1) ∧ ∀ x, α' a x = 1) → (∀ y, (∃ m : ℕ, ∀ a ∈ u ^ m, α a y = 1) → ∀ a ∈ w, α a y = 1) → Finite {y : M // ∀ a ∈ w, α a y = 1} → (∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1) ∧ Nat.card {x : M' // ∀ a ∈ w.map bar, α' a x = 1} = Nat.card {y : M // ∀ a ∈ w, α a y = 1} := by
  first | (exact @GlobalTheory.DualParts.conj_dual_parts) | (exact GlobalTheory.DualParts.conj_dual_parts) | (intros; apply GlobalTheory.DualParts.conj_dual_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulMulSelfOfUnitaryConjStatement
section
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary : ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  first | exact @GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | exact GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | (intros; apply GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationDerivCutoffPolynomialMemUnitarySpan
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Pc1

private theorem sg_sq' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg; split_ifs <;> simp

private theorem conj_sg' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (starRingEnd ℂ) (sg ε a) = sg ε a := by
  unfold sg; split_ifs <;> simp

private theorem lieU_decomposition {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) :
    ∃ A B : Mat n, LieU ε A ∧ LieU ε B ∧ Z = A + Complex.I • B := by
  refine ⟨Matrix.of fun a b => (Z a b + (starRingEnd ℂ) (barM ε Z a b)) / 2,
    Matrix.of fun a b => -Complex.I * (Z a b - (starRingEnd ℂ) (barM ε Z a b)) / 2, ?_, ?_, ?_⟩
  · intro a b
    have ha := sg_sq' ε a
    have hb := sg_sq' ε b
    simp only [barM, Matrix.of_apply, map_div₀, map_add (f := _), map_neg, map_mul, conj_sg',
      Complex.conj_conj, map_ofNat]
    linear_combination (-(starRingEnd ℂ) (Z a b) / 2 * (sg ε b * sg ε b)) * ha
      + (-(starRingEnd ℂ) (Z a b) / 2) * hb
  · intro a b
    have ha := sg_sq' ε a
    have hb := sg_sq' ε b
    simp only [barM, Matrix.of_apply, map_div₀, map_sub, map_neg, map_mul, conj_sg',
      Complex.conj_conj, map_ofNat, Complex.conj_I]
    linear_combination (-Complex.I * (starRingEnd ℂ) (Z a b) / 2 * (sg ε b * sg ε b)) * ha
      + (-Complex.I * (starRingEnd ℂ) (Z a b) / 2) * hb
  · ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination ((Z a b - (starRingEnd ℂ) (barM ε Z a b)) / 2) * Complex.I_mul_I

theorem dZ_add_smul {n : ℕ} (ε : Fin n → Bool) (A B : Mat n) (c : ℂ) :
    dZ ε (A + c • B) = dZ ε A + c • dZ ε B := by
  apply MvPolynomial.derivation_ext
  rintro (x | x)
  · simp only [dZ, Derivation.add_apply, Derivation.smul_apply, mkDerivation_X, Sum.elim_inl,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, smul_eq_C_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [dZ, Derivation.add_apply, Derivation.smul_apply, mkDerivation_X, Sum.elim_inr, barM,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_neg, smul_eq_C_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem adBas_add_smul {n : ℕ} (ε : Fin n → Bool) (A B : Mat n) (c : ℂ) (H : ℝ → ℝ)
    (P : GlobalTheory.PsCo.Pc1.Poly n) :
    adBas ε (A + c • B) H P = adBas ε A H P + c • adBas ε B H P := by
  funext g
  have hC : ev g (C c) = c := by simp [ev]
  simp only [adBas, bas, dZ_add_smul, Derivation.add_apply, Derivation.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_C_mul, map_add, map_mul, hC]
  ring

theorem adBas_mem_adSpanM  : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ)
    (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H →
    GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  intro n ε Z H P hH
  obtain ⟨A, B, hA, hB, rfl⟩ := lieU_decomposition ε Z
  rw [adBas_add_smul]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨A, H, P, hA, hH, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨B, H, P, hB, hH, rfl⟩))

end GlobalTheory.PsCo.Pc1
end

