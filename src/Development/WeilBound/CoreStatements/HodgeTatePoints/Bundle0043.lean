module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0042
public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0022
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0012

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CcInjAlg
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

theorem mulVec_injective_map_iff {k k₂ m n : Type} [Field k] [Field k₂] [Fintype m] [Fintype n] (f : k →+* k₂)
    (M : Matrix m n k) : Function.Injective (M.map f).mulVec ↔ Function.Injective M.mulVec := by
  letI := f.toAlgebra
  rw [Matrix.mulVec_injective_iff, Matrix.mulVec_injective_iff]
  exact linearIndependent_algebraMap_comp_iff (R := k) (S := k₂) (v := M.col)

theorem conjInj_iff_fromRows {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
    (p : ℕ) : ConjInj B p ↔ Function.Injective (Matrix.fromRows (hw B p) (am B p).transpose).mulVec := by
  have e : (Matrix.fromRows (hw B p) (am B p).transpose).mulVec =
      (Equiv.sumArrowEquivProdArrow (Fin d) (Fin d) R).symm ∘ alpha B p := by
    funext u
    rw [Matrix.fromRows_mulVec, Function.comp_apply, alpha_apply]
    rfl
  rw [e, Equiv.comp_injective, ConjInj]

theorem conjInj_map {k k₂ : Type} [Field k] [Field k₂] {f : k →+* k₂} {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    {B : FB k d O} {B₂ : FB k₂ d O} (h : IsMapOf f B B₂) (p : ℕ) : ConjInj B₂ p ↔ ConjInj B p := by
  obtain ⟨h1, h2⟩ := (map_mats k k₂ f d O B B₂ h).2.2 p
  rw [conjInj_iff_fromRows, conjInj_iff_fromRows, ← mulVec_injective_map_iff f, h1, h2, Matrix.fromRows_map,
    Matrix.transpose_map]

end PositivityTheory.HtPt.Cc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ChIsDeg
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ch

theorem unitAt_div {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    unitAt ξ p (s / t) := by
  have key : ∀ {s t : Ω}, Λ.IsGenAt p s → Λ.IsGenAt p t → s / t ∈ regAt ξ p := by
    intro s t hs ht
    have : s ∈ Submodule.span (regAt ξ p) {t} := by
      rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self s
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    have ha' : (a : Ω) * t = s := ha
    rw [← ha', mul_div_cancel_right₀ _ ht.1]
    exact a.2
  exact ⟨div_ne_zero hs.1 ht.1, key hs ht, by rw [inv_div]; exact key ht hs⟩

theorem isdeg_unique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' := by
  intro X Ω _ ξ K _ C z Y Λ n n' hξ ⟨h₀, h, s₀, s, r, g₀, g, hr, hf, e⟩
    ⟨h₀', h', s₀', s', r', g₀', g', hr', hf', e'⟩
  obtain ⟨φ, hφ, hu⟩ := ValHom.exists_valAt_hom X Ω ξ K z h₀ hξ
  have u₀ := unitAt_div g₀' g₀
  let c : K := φ ⟨s₀' / s₀, u₀.2.1⟩
  have hc : c ≠ 0 := ((hu ⟨_, u₀.2.1⟩).2 u₀).ne_zero
  have key : ∀ i, C.v i (r i) = C.v i (r' i) * C.v i c := by
    intro i
    obtain ⟨ψ, hψ, hv⟩ := ValHom.exists_valAt_hom X Ω ξ _ (Y.x i) (h i) hξ
    have u := unitAt_div (g i) (g' i)
    have hun : IsUnit (ψ ⟨_, u.2.1⟩) := (hv ⟨_, u.2.1⟩).2 u
    have hval := _root_.GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change X Ω ξ _ K (C.v i).valuationSubring.subtype (Y.x i) _ _
      ((hψ _ _).2 ⟨u.2.1, rfl⟩) (by rw [Y.gen i]; exact h₀)
    rw [Y.gen i] at hval
    obtain ⟨m1, e1⟩ := (hφ _ _).1 hval
    obtain ⟨m2, e2⟩ := (hφ _ _).1 (hr i).2
    obtain ⟨m3, e3⟩ := (hφ _ _).1 (hr' i).2
    have hone : C.v i ((C.v i).valuationSubring.subtype (ψ ⟨_, u.2.1⟩)) = 1 := by
      obtain ⟨w, hw⟩ := hun.exists_right_inv
      have h1 : C.v i ((ψ ⟨_, u.2.1⟩ : (C.v i).valuationSubring) : K) * C.v i (w : K) = 1 := by
        rw [← map_mul, ← MulMemClass.coe_mul, hw]; simp
      exact le_antisymm (ψ ⟨_, u.2.1⟩).2 (h1 ▸ mul_le_of_le_one_right' w.2)
    have : r i = (C.v i).valuationSubring.subtype (ψ ⟨_, u.2.1⟩) * (r' i * c) := by
      rw [← e1, ← e2, ← e3, ← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      have := (g' i).1
      have := g₀'.1
      have := g₀.1
      simp only [MulMemClass.coe_mul]
      field_simp
    rw [this, map_mul, hone, one_mul, map_mul]
  have h2 : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i (r i)) =
      (C.w i : ℤ) * WithZero.log (C.v i (r' i)) + (C.w i : ℤ) * WithZero.log (C.v i c) := by
    intro i
    rw [key, WithZero.log_mul ((Valuation.ne_zero_iff _).2 (hr' i).1)
      ((Valuation.ne_zero_iff _).2 hc), mul_add]
  rw [e, e']
  simp only [h2]
  rw [finsum_add_distrib (hf'.subset fun i hi h1 => hi (by simp [h1]))
    ((C.fin c hc).subset fun i hi h1 => hi (by simp [h1])), C.prod c hc, add_zero]

end PositivityTheory.HtPt.Ch
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CiField
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

open MvPolynomial PositivityTheory.HtPt.Gf

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {K : Type} [Field K]

theorem cone_homog (y : (Σ k, J k) → K) {g : MRing J} {d : B → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = C (aeval y g) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mConeMap, aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]
  congr 1
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Finset.prod_pow_eq_pow_sum, hg m hm k]

theorem exists_homog_val {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ = 1) (f : MRing J) :
    ∃ (N : ℕ) (g : MRing J), IsMultiHomog g (fun _ => N) ∧ aeval w g = aeval w f := by
  classical
  have hm : ∀ e, aeval w (mon c e) = 1 := fun e => by simp [aeval_mon, hc]
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, fun m hm k => ?_, rfl⟩
    have : m = 0 := by
      by_contra h
      exact mem_support_iff.1 hm (by rw [coeff_C, if_neg (Ne.symm h)])
    simp [this]
  | add f g hf hg =>
    obtain ⟨N, f', h1, h2⟩ := hf
    obtain ⟨M, g', h3, h4⟩ := hg
    refine ⟨N + M, f' * mon c (fun _ => M) + g' * mon c (fun _ => N), hom_add (hom_mul h1 (hom_mon _ _))
      (hom_of_eq (hom_mul h3 (hom_mon _ _)) fun k => add_comm _ _), ?_⟩
    simp only [map_add (f := _), map_mul, hm, h2, h4, mul_one]
  | mul_X f q hf =>
    obtain ⟨N, f', h1, h2⟩ := hf
    refine ⟨N + 1, f' * mon (Function.update c q.1 q.2) (fun _ => 1), hom_mul h1 (hom_mon _ _), ?_⟩
    rw [map_mul, map_mul, h2, aeval_mon, aeval_X, Finset.prod_eq_single q.1 (fun l _ hl => by
      rw [Function.update_of_ne hl, hc, one_pow]) (by simp), Function.update_self, pow_one]

theorem birational_of_frac {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ = 1)
    (hfr : ∀ s : K, ∃ f g : MRing J, aeval w g ≠ 0 ∧ aeval w f = s * aeval w g) : Birational w := by
  intro s
  have hm : ∀ e, aeval w (mon c e) = 1 := fun e => by simp [aeval_mon, hc]
  obtain ⟨f, g, h0, h⟩ := hfr s
  obtain ⟨N, f', h1, h2⟩ := exists_homog_val hc f
  obtain ⟨M, g', h3, h4⟩ := exists_homog_val hc g
  refine ⟨fun _ => N + M, f' * mon c (fun _ => M), g' * mon c (fun _ => N), hom_mul h1 (hom_mon _ _),
    hom_of_eq (hom_mul h3 (hom_mon _ _)) fun k => add_comm _ _, ?_, ?_⟩
  · rwa [map_mul, hm, h4, mul_one]
  · rw [map_mul, map_mul, hm, hm, h2, h4, mul_one, mul_one, h]

theorem isFunctionField_of_dim {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K] {w : (Σ k, J k) → K} {c : ∀ k, J k}
    (hc : ∀ k, w ⟨k, c k⟩ = 1) (hb : Birational w) {W : Ideal (MRing J)} (hW : mCoordIdeal w = W)
    (hp : (p : MRing J) ∈ W) (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞)) :
    GroundTheory.FunctionField.IsFunctionField (ZMod p) K := by
  refine GlobalTheory.CompanionTheory.Ar.Flat.isFunctionField_of_fg_trdeg ?_ ?_
  · refine IntermediateField.fg_def.2 ⟨Set.range w, Set.finite_range w, top_le_iff.1 fun s _ => ?_⟩
    have key : ∀ f : MRing J, aeval w f ∈ IntermediateField.adjoin (ZMod p) (Set.range w) := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C a => simp
      | add f g hf hg => rw [map_add]; exact add_mem hf hg
      | mul_X f q hf => rw [map_mul, aeval_X]; exact mul_mem hf (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
    obtain ⟨d, g, h, -, -, h0, h1⟩ := hb s
    rw [← div_eq_iff h0] at h1
    exact h1 ▸ div_mem (key g) (key h)
  · have hker : RingHom.ker (mConeMap w).toRingHom = W := hW
    have hprime : W.IsPrime := hker ▸ RingHom.ker_isPrime _
    have hchar : CharP (MRing J ⧸ W) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
      rw [← map_natCast (Ideal.Quotient.mk W), Ideal.Quotient.eq_zero_iff_mem]; exact hp)
    let _ := ZMod.algebra (MRing J ⧸ W) p
    haveI : FaithfulSMul (ZMod p) (MRing J ⧸ W) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
    have : IsScalarTower ℤ (ZMod p) (MRing J ⧸ W) := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
    have : Algebra.FiniteType (ZMod p) (MRing J ⧸ W) :=
      Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) _
    obtain ⟨n, h1, h2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ZMod p) (A := MRing J ⧸ W)
    have hn : n = 1 + Fintype.card B := by
      rw [hdim] at h1
      exact_mod_cast h1.symm
    let μ : MRing J ⧸ W →+* MvPolynomial B K :=
      Ideal.Quotient.lift W (mConeMap w).toRingHom fun a ha => (hker.ge ha :)
    have hμ : Function.Injective μ := RingHom.lift_injective_of_ker_le_ideal W _ hker.le
    let _ := μ.toAlgebra
    have hμ' : ∀ f, algebraMap (MRing J ⧸ W) (MvPolynomial B K) (Ideal.Quotient.mk W f) = mConeMap w f :=
      fun f => rfl
    have : FaithfulSMul (MRing J ⧸ W) (MvPolynomial B K) := (faithfulSMul_iff_algebraMap_injective _ _).2 hμ
    have : IsScalarTower (ZMod p) (MRing J ⧸ W) (MvPolynomial B K) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
    have hX : ∀ k, IsAlgebraic (MRing J ⧸ W) (X k : MvPolynomial B K) := fun k => by
      have := isAlgebraic_algebraMap (A := MvPolynomial B K) (Ideal.Quotient.mk W (X ⟨k, c k⟩))
      rw [hμ'] at this
      simpa [mConeMap, hc] using this
    have : Algebra.IsAlgebraic (MRing J ⧸ W) (MvPolynomial B K) := ⟨fun f => by
      induction f using MvPolynomial.induction_on with
      | C s =>
        obtain ⟨d, g, h, hg, hh, h0, h1⟩ := hb s
        refine IsAlgebraic.of_smul (y := Ideal.Quotient.mk W h) (mem_nonZeroDivisors_of_ne_zero fun e => ?_) ?_
        · have h3 := hμ' h
          rw [e, map_zero, cone_homog w hh] at h3
          exact mul_ne_zero (mt C_eq_zero.1 h0)
            (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) h3.symm
        · have h3 := isAlgebraic_algebraMap (A := MvPolynomial B K) (Ideal.Quotient.mk W g)
          rw [hμ', cone_homog w hg, h1, map_mul, mul_assoc, mul_comm, ← cone_homog w hh] at h3
          rwa [Algebra.smul_def, hμ']
      | add f g hf hg => exact hf.add hg
      | mul_X f k hf => exact hf.mul (hX k)⟩
    have e1 := trdeg_add_eq (ZMod p) (MRing J ⧸ W) (A := MvPolynomial B K)
    have e2 := trdeg_add_eq (ZMod p) K (A := MvPolynomial B K)
    rw [h2, trdeg_eq_zero, add_zero, hn] at e1
    rw [MvPolynomial.trdeg_of_isDomain, ← e1, Cardinal.lift_id, Cardinal.mk_fintype, Nat.cast_add, Nat.cast_one] at e2
    exact (Cardinal.add_nat_inj _).1 e2

theorem curve_field : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 := by
  intro B _ J _ W p _ ⟨hprime, ⟨S, hS, hWS⟩, hrel⟩ hchar hdim
  choose c hc using hrel
  have hp := natCast_mem_of_charOf hchar
  let F := FractionRing (MRing J ⧸ W)
  let π : MRing J →+* F := (algebraMap (MRing J ⧸ W) F).comp (Ideal.Quotient.mk W)
  have hπ : ∀ f, π f = 0 ↔ f ∈ W := fun f => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective (MRing J ⧸ W) F)
  have ht : ∀ k, π (X ⟨k, c k⟩) ≠ 0 := fun k h => hc k ((hπ _).1 h)
  let w' : (Σ k, J k) → F := fun q => π (X q) / π (X ⟨q.1, c q.1⟩)
  let K := Subfield.closure (Set.range w')
  let w : (Σ k, J k) → K := fun q => ⟨w' q, Subfield.subset_closure ⟨q, rfl⟩⟩
  have hw : ∀ k, w ⟨k, c k⟩ = 1 := fun k => Subtype.ext (div_self (ht k))
  have hK : CharP K p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (K.subtype.injective (by
    rw [map_natCast, map_zero, ← map_natCast π, hπ]; exact hp))
  let ε : MvPolynomial B K →+* F := eval₂Hom K.subtype fun k => π (X ⟨k, c k⟩)
  have hε : ε.comp (mConeMap w).toRingHom = π := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun q => ?_
    · simp
    · change ε (mConeMap w (X q)) = _
      rw [mConeMap, aeval_X, map_mul, eval₂Hom_C, eval₂Hom_X']
      exact div_mul_cancel₀ _ (ht _)
  have hε' : ∀ f, ε (mConeMap w f) = π f := fun f => RingHom.congr_fun hε f
  have hW : mCoordIdeal w = W := by
    refine le_antisymm (fun f hf => (hπ f).1 ?_) (hWS.le.trans (Ideal.span_le.2 fun f hf => ?_))
    · rw [← hε', show mConeMap w f = 0 from hf, map_zero]
    · obtain ⟨a, ha⟩ := hS f hf
      refine mem_mCoordIdeal ha ?_
      have h1 := (hε' f).trans ((hπ f).2 (hWS.ge (Ideal.subset_span hf)))
      rw [cone_homog w ha, map_mul, eval₂Hom_C, map_prod, mul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact (map_eq_zero_iff _ K.subtype.injective).1 h1
      · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h1
        rw [map_pow, eval₂Hom_X'] at hk
        exact absurd hk (pow_ne_zero _ (ht k))
  have hb : Birational w := birational_of_frac hw fun s => by
    have hr : Subring.closure (Set.range w') ≤ (K.subtype.comp (aeval w : MRing J →ₐ[ℤ] K).toRingHom).range := by
      refine Subring.closure_le.2 ?_
      rintro _ ⟨q, rfl⟩
      exact ⟨X q, congrArg K.subtype (aeval_X w q)⟩
    obtain ⟨y, hy, z, hz, e⟩ := Subfield.mem_closure_iff.1 s.2
    obtain ⟨f, rfl⟩ := hr hy
    obtain ⟨g, rfl⟩ := hr hz
    have e' : aeval w f / aeval w g = s := K.subtype.injective (by rw [map_div₀]; exact e)
    by_cases h0 : aeval w g = 0
    · exact ⟨0, 1, by simp, by simp [← e', h0]⟩
    · exact ⟨f, g, h0, (div_eq_iff h0).1 e'⟩
  let _ := ZMod.algebra K p
  exact ⟨K, inferInstance, inferInstance, isFunctionField_of_dim hw hb hW hp hdim, w, hW, hb,
    fun k => ⟨c k, hw k ▸ one_ne_zero⟩⟩

end PositivityTheory.HtPt.Ci
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CiIsDeg
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

theorem chart_block {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {B : Type} [Fintype B]
    {J : B → Type} {y : (Σ k, J k) → Ω} {c : (k : B) → J k} {p : Cpt ξ} (hc : InChart ξ (segre y) c p) (k : B) :
    y ⟨k, c k⟩ ≠ 0 ∧ ∀ j, y ⟨k, j⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  refine ⟨h0 k, fun j => ?_⟩
  have h1 := hc.2 (Function.update c k j)
  rw [Conj.segre, Conj.segre, ← Finset.prod_div_distrib, Finset.prod_eq_single k (fun l _ hl => by
    rw [Function.update_of_ne hl, div_self (h0 l)]) (by simp), Function.update_self] at h1
  exact h1

theorem isdeg_coord : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) := by
  intro X Ω _ ξ K _ C z Y B _ J _ y w Λ S a e₀ h₀ h tie hw hz hS hΛ
  classical
  have hξ := tie.gen
  have hval : ∀ k c, w ⟨k, c⟩ ≠ 0 → y ⟨k, c⟩ ≠ 0 ∧ ∀ j, ValAt ξ z (y ⟨k, j⟩ / y ⟨k, c⟩) (w ⟨k, j⟩ / w ⟨k, c⟩) := by
    intro k c hc
    obtain ⟨h1, h2⟩ := hw.2 k c (IsUnit.mk0 _ hc)
    refine ⟨h1, fun j => ?_⟩
    obtain ⟨r, hr, e⟩ := h2 j
    rwa [e, mul_div_cancel_right₀ _ hc]
  choose c₀ hc₀ using hw.1
  replace hc₀ := fun k => (hc₀ k).ne_zero
  have ch₀ : InChart ξ (segre y) c₀ ⟨centre z, h₀⟩ := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (hval k _ (hc₀ k)).1, fun c' => ?_⟩
    rw [Conj.segre, Conj.segre, ← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Val.mem ((hval k _ (hc₀ k)).2 _) h₀
  choose c hc using fun i => tie.cover ⟨centre (Y.x i), h i⟩
  have hint : ∀ i k j, ∃ ρ : K, C.v i ρ ≤ 1 ∧ ValAt ξ z (y ⟨k, j⟩ / y ⟨k, c i k⟩) ρ := by
    intro i k j
    obtain ⟨ρ, hρ⟩ := Val.of_mem ((chart_block (hc i) k).2 j)
    have := LieTangent.valAt_base hξ (C.v i).valuationSubring.subtype hρ
    rw [Y.gen i] at this
    exact ⟨_, ρ.2, this⟩
  have hne : ∀ i k, w ⟨k, c i k⟩ ≠ 0 := by
    intro i k h0
    obtain ⟨ρ, -, hρ⟩ := hint i k (c₀ k)
    have h1 := Val.mul hρ ((hval k _ (hc₀ k)).2 (c i k))
    rw [div_mul_div_cancel₀ (chart_block (hc i) k).1, div_self (hval k _ (hc₀ k)).1, h0, zero_div, mul_zero] at h1
    exact zero_ne_one (LieTangent.valAt_unique hξ h1 (Val.one h₀))
  have hsup : ∀ i k, (Finset.univ.sup fun j : J k => C.v i (w ⟨k, j⟩)) = C.v i (w ⟨k, c i k⟩) := by
    intro i k
    refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j : J k => C.v i (w ⟨k, j⟩))
      (Finset.mem_univ _))
    obtain ⟨ρ, h1, hρ⟩ := hint i k j
    rw [LieTangent.valAt_unique hξ hρ ((hval k _ (hne i k)).2 j), map_div₀] at h1
    exact (div_le_one₀ ((C.v i).pos_iff.2 (hne i k))).1 h1
  have hgen : ∀ p ∈ S, ∀ c, InChart ξ (segre y) c p → Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e₀) := fun p hp c hc =>
    ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_block hc k).1) hΛ.1, hΛ.2 p hp c hc⟩
  have hF : (⋃ q : {q : Σ k, J k // w q ≠ 0}, {i | C.v i (w q.1) ≠ 1}).Finite :=
    Set.finite_iUnion fun q => C.fin _ q.2
  have hgood : ∀ i ∉ hF.toFinset, ∀ q, w q ≠ 0 → C.v i (w q) = 1 := by
    intro i hi q hq
    by_contra hcon
    exact hi (hF.mem_toFinset.2 (Set.mem_iUnion.2 ⟨⟨q, hq⟩, hcon⟩))
  have hfs : ∀ f : C.I → ℤ, (∀ i ∉ hF.toFinset, f i = 0) → ∑ᶠ i, f i = ∑ i ∈ hF.toFinset, f i := fun f hf =>
    finsum_eq_sum_of_support_subset f fun i hi => by_contra fun hc => hi (hf i hc)
  have hr : ∀ i ∉ hF.toFinset, C.v i (∏ k, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k) = 1 := by
    intro i hi
    simp only [map_prod, map_zpow₀, map_div₀, hgood i hi _ (hne i _), hgood i hi _ (hc₀ _), div_one, one_zpow,
      Finset.prod_const_one]
  refine ⟨h₀, h, _, _, fun i => ∏ k, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k, hgen _ hz _ ch₀,
    fun i => hgen _ (hS i) _ (hc i), fun i => ⟨Finset.prod_ne_zero_iff.2 fun k _ =>
      zpow_ne_zero _ (div_ne_zero (hne i k) (hc₀ k)), ?_⟩, hF.subset fun i hi => ?_, ?_⟩
  · rw [mul_div_mul_right _ _ hΛ.1, ← Finset.prod_div_distrib]
    refine Val.prod h₀ _ fun k => ?_
    rw [← div_zpow]
    refine Val.zpow ((hval k _ (hc₀ k)).2 _) ?_ _
    rw [inv_div, inv_div]
    exact (hval k _ (hne i k)).2 _
  · by_contra hcon
    exact hi (hr i fun h' => hcon (hF.mem_toFinset.1 h'))
  · have hlog : ∀ i, WithZero.log (C.v i (∏ k, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k)) =
        ∑ k, a k * (WithZero.log (C.v i (w ⟨k, c i k⟩)) - WithZero.log (C.v i (w ⟨k, c₀ k⟩))) := by
      intro i
      have key : ∀ T : Finset B, WithZero.log (C.v i (∏ k ∈ T, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k)) =
          ∑ k ∈ T, a k * (WithZero.log (C.v i (w ⟨k, c i k⟩)) - WithZero.log (C.v i (w ⟨k, c₀ k⟩))) := by
        intro T
        induction T using Finset.induction_on with
        | empty => simp
        | insert k T hk ih =>
          rw [Finset.prod_insert hk, Finset.sum_insert hk, map_mul, WithZero.log_mul, ih, map_zpow₀,
            WithZero.log_zpow, map_div₀, WithZero.log_div, smul_eq_mul]
          · exact (Valuation.ne_zero_iff _).2 (hne i k)
          · exact (Valuation.ne_zero_iff _).2 (hc₀ k)
          · exact (Valuation.ne_zero_iff _).2 (zpow_ne_zero _ (div_ne_zero (hne i k) (hc₀ k)))
          · exact (Valuation.ne_zero_iff _).2 (Finset.prod_ne_zero_iff.2 fun k _ =>
              zpow_ne_zero _ (div_ne_zero (hne i k) (hc₀ k)))
      exact key _
    have hp : ∀ k, ∑ i ∈ hF.toFinset, (C.w i : ℤ) * WithZero.log (C.v i (w ⟨k, c₀ k⟩)) = 0 := fun k => by
      rw [← hfs _ fun i hi => by rw [hgood i hi _ (hc₀ k)]; simp]
      exact C.prod _ (hc₀ k)
    rw [hfs _ fun i hi => by rw [hr i hi]; simp]
    simp only [coordDeg, hsup, hlog, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hfs _ fun i hi => by rw [hgood i hi _ (hne i k)]; simp]
    simp only [mul_left_comm _ (a k), mul_sub, ← Finset.mul_sum, Finset.sum_sub_distrib, hp, mul_zero, sub_zero]

end PositivityTheory.HtPt.Ci
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.InhConj
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc


open GroundTheory.FunctionField in
def ffCurve (k K : Type) [Field k] [Field K] [Algebra k K] [IsFunctionField k K] : ACurve K where
  I := Place k K
  v := fun v => v.valuation
  w := fun v => v.deg
  fin := fun x hx => (Place.finite_ord_ne_zero (k := k) x).subset fun v hv h0 => hv (by
    rw [v.valuation_eq_exp_neg_ord hx, h0]; simp)
  prod := fun x _ => by
    have h := Divisor.deg_divisor (k := k) x
    rw [Divisor.deg_apply, Finsupp.sum] at h
    have e : ∀ v : Place k K, (v.deg : ℤ) * WithZero.log (v.valuation x) =
        -((divisor x : Divisor k K) v * v.deg) := fun v => by
      rw [divisor_apply, Place.ord]; ring
    simp only [e]
    rw [finsum_neg_distrib, finsum_eq_sum_of_support_subset (s := (divisor x : Divisor k K).support), h, neg_zero]
    intro v hv
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    exact fun h0 => hv (by simp only [h0, zero_mul])

private theorem place_nonempty_of_isFunctionField (k K : Type) [Field k] [Field K] [Algebra k K]
    [GroundTheory.FunctionField.IsFunctionField k K] : Nonempty (GroundTheory.FunctionField.Place k K) := by
  obtain ⟨t, ht, -⟩ := GroundTheory.FunctionField.IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hR : IsIntegrallyClosedIn (integralClosure k K).toSubring K := by infer_instance
  have htR : t ∉ (integralClosure k K).toSubring := fun h => ht (IsIntegral.isAlgebraic h)
  obtain ⟨V, hV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn htR
  exact ⟨⟨V, fun h => htV (h ▸ trivial), fun c => hV (isIntegral_algebraMap (x := c))⟩⟩

theorem inh_ff : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K], ∃ C : ACurve K, IsFFCurve k C ∧ Nonempty C.I ∧ ∀ i (x : K), IsAlgebraic k x → C.v i x ≤ 1 := by
  intro k K _ _ _ _
  refine ⟨ffCurve k K, ⟨Equiv.refl _, fun i => ⟨rfl, rfl⟩⟩, place_nonempty_of_isFunctionField k K, ?_⟩
  intro i x hx
  obtain ⟨v, rfl⟩ : ∃ v : GroundTheory.FunctionField.Place k K, v = i := ⟨i, rfl⟩
  show v.valuation x ≤ 1
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have hd := GroundTheory.FunctionField.divisor_eq_zero_of_isAlgebraic hx h0
    have ho : v.ord x = 0 := by
      have e := GroundTheory.FunctionField.divisor_apply (k := k) x v
      rw [hd] at e
      exact e.symm
    rw [v.valuation_eq_exp_neg_ord h0, ho]
    simp

end PositivityTheory.HtPt.Cc
end
end

