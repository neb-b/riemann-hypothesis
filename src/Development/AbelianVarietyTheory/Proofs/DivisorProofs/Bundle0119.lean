module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallEqOfIntegralDvr
section
namespace GlobalTheory

theorem unitBall_eq_of_integral_dvr (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W]
    [Algebra.IsIntegral V W] [IsLocalHom (algebraMap V W)]
    (hinj : Function.Injective (algebraMap V W))
    (κ : FractionRing V →+* PadicAlgCl p) (κ' : FractionRing W →+* PadicAlgCl p)
    (hc : ∀ v : V, κ' (algebraMap W (FractionRing W) (algebraMap V W v)) =
      κ (algebraMap V (FractionRing V) v))
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
  classical
  have hW1 : ∀ w : W, ‖κ' (algebraMap W (FractionRing W) w)‖ ≤ 1 := by
    intro w
    let vP : Valuation (PadicAlgCl p) NNReal := Valued.v
    have hmem : ∀ a : V, κ (algebraMap V (FractionRing V) a) ∈ vP.integer := by
      intro a
      rw [Valuation.mem_integer_iff]
      show ‖κ (algebraMap V (FractionRing V) a)‖₊ ≤ 1
      exact NNReal.coe_le_coe.1 (by simpa using (hV _).2 ⟨a, rfl⟩)
    let ψ : V →+* vP.integer :=
      (κ.comp (algebraMap V (FractionRing V))).codRestrict vP.integer hmem
    obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := V) w
    have hint : IsIntegral vP.integer (κ' (algebraMap W (FractionRing W) w)) := by
      refine ⟨q.map ψ, hqm.map ψ, ?_⟩
      have hcomp : (algebraMap vP.integer (PadicAlgCl p)).comp ψ =
          (κ'.comp (algebraMap W (FractionRing W))).comp (algebraMap V W) :=
        RingHom.ext fun a => (hc a).symm
      rw [Polynomial.eval₂_map, hcomp]
      have h0 : (κ'.comp (algebraMap W (FractionRing W))) (q.eval₂ (algebraMap V W) w) = 0 := by
        rw [hq, map_zero]
      exact (Polynomial.hom_eval₂ q (algebraMap V W) _ w).symm.trans h0
    have h1 := (Valuation.integer.integers vP).mem_of_integral hint
    rw [Valuation.mem_integer_iff] at h1
    have h2 : ‖κ' (algebraMap W (FractionRing W) w)‖₊ ≤ 1 := h1
    have h3 : ((‖κ' (algebraMap W (FractionRing W) w)‖₊ : NNReal) : ℝ) ≤ 1 := by exact_mod_cast h2
    simpa using h3
  have hunit : ∀ u : Wˣ, ‖κ' (algebraMap W (FractionRing W) u)‖ = 1 := by
    intro u
    have hm : ‖κ' (algebraMap W (FractionRing W) u)‖ *
        ‖κ' (algebraMap W (FractionRing W) ↑u⁻¹)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have ha := hW1 u
    have hb := hW1 ↑u⁻¹
    refine le_antisymm ha ?_
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (κ' (algebraMap W (FractionRing W) u)))]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hπK0 : algebraMap V (FractionRing V) π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm)
  have hπ1 : ‖κ (algebraMap V (FractionRing V) π)‖ < 1 := by
    refine lt_of_le_of_ne ((hV _).2 ⟨π, rfl⟩) fun h => hπ.not_isUnit ?_
    have hinv : ‖κ (algebraMap V (FractionRing V) π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv, h, inv_one]
    obtain ⟨a, ha⟩ := (hV _).1 hinv
    refine isUnit_iff_exists_inv.2 ⟨a, IsFractionRing.injective V (FractionRing V) ?_⟩
    rw [map_mul, ha, mul_inv_cancel₀ hπK0, map_one]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hϖ1 : ‖κ' (algebraMap W (FractionRing W) ϖ)‖ < 1 := by
    have hπW0 : algebraMap V W π ≠ 0 := fun h =>
      hπ.ne_zero (hinj (h.trans (map_zero _).symm))
    obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπW0 hϖ
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at he
      exact hπ.not_isUnit (isUnit_of_map_unit (algebraMap V W) π (he ▸ u.isUnit))
    have hnorm : ‖κ' (algebraMap W (FractionRing W) ϖ)‖ ^ e < 1 := by
      have h := congrArg norm (hc π)
      rw [he, map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow, hunit, one_mul] at h
      rw [← h] at hπ1
      exact hπ1
    by_contra hge
    exact absurd hnorm (not_lt.2 (one_le_pow₀ (not_lt.1 hge)))
  intro x
  constructor
  · intro hx
    by_contra hxW
    rcases ValuationRing.isInteger_or_isInteger W x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact hxW ⟨a, ha⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxW ⟨0, map_zero _⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact hx0 (inv_eq_zero.1 ha.symm)
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hn
      apply hxW
      refine ⟨↑u⁻¹, ?_⟩
      have h1 : algebraMap W (FractionRing W) ↑u * algebraMap W (FractionRing W) ↑u⁻¹ = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [eq_inv_of_mul_eq_one_right h1, ← hn, ha, inv_inv]
    have hsmall : ‖κ' x⁻¹‖ < 1 := by
      rw [← ha, hn, map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow, hunit, one_mul]
      exact pow_lt_one₀ (norm_nonneg _) hϖ1 hn0
    have hprod : ‖κ' x‖ * ‖κ' x⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
    have h0 := norm_nonneg (κ' x⁻¹)
    nlinarith
  · rintro ⟨w, rfl⟩
    exact hW1 w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRealOfCongrOne
section
open NumberField

namespace GlobalTheory.UnitReal

theorem unit_real_of_congr_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime →
    ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E) := by
  intro E _ _ _ q hq hqt u hu φ
  set I : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with hI
  set c : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hc
  set v : (𝓞 E)ˣ := IsCMField.unitsComplexConj E u with hv
  have hvc : (v : 𝓞 E) = c u := rfl
  have hv1 : (v : 𝓞 E) - 1 ∈ I := by
    rw [hI, Ideal.mem_span_singleton] at hu ⊢
    obtain ⟨y, hy⟩ := hu
    refine ⟨c y, ?_⟩
    rw [hvc, ← map_one c, ← map_sub, hy, map_mul, map_natCast]
  set ζ : (𝓞 E)ˣ := (IsCMField.unitsMulComplexConjInv E u : (𝓞 E)ˣ) with hζ
  have hζv : ζ * v = u := by rw [hζ, IsCMField.unitsMulComplexConjInv_apply, inv_mul_cancel_right]
  have hζ1 : Ideal.Quotient.mk I (ζ : 𝓞 E) = 1 := by
    have a1 : Ideal.Quotient.mk I (u : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hu
    have a2 : Ideal.Quotient.mk I (v : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hv1
    have := congrArg (fun x : (𝓞 E)ˣ => Ideal.Quotient.mk I (x : 𝓞 E)) hζv
    simp only [Units.val_mul, map_mul, a1, a2, mul_one] at this
    exact this
  have ht : ζ ^ Nat.card (Units.torsion E) = 1 := by
    have h4 : (IsCMField.unitsMulComplexConjInv E u) ^ Nat.card (Units.torsion E) = 1 := pow_card_eq_one'
    have := congrArg Subtype.val h4
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    exact this
  have hζeq : ζ = 1 := by
    by_contra hne
    have hne' : (ζ : 𝓞 E) - 1 ≠ 0 := by
      rw [sub_ne_zero]; intro h; exact hne (Units.ext h)
    have hsum : ∑ j ∈ Finset.range (Nat.card (Units.torsion E)), (ζ : 𝓞 E) ^ j = 0 := by
      have := mul_geom_sum ((ζ : 𝓞 E)) (Nat.card (Units.torsion E))
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_left hne'
    have hmod := congrArg (Ideal.Quotient.mk I) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_pow, hζ1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, map_zero] at hmod
    have hmem : ((Nat.card (Units.torsion E) : ℕ) : 𝓞 E) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hmod
    rw [hI, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hn := congrArg (Algebra.norm ℤ) hy
    rw [map_mul] at hn
    have e1 : ∀ n : ℕ, Algebra.norm ℤ ((n : 𝓞 E)) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      intro n
      rw [← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]
    rw [e1, e1] at hn
    have hd : 0 < Module.finrank ℤ (𝓞 E) := by
      rw [RingOfIntegers.rank]; exact Module.finrank_pos
    have hdvd : (q : ℤ) ∣ (Nat.card (Units.torsion E) : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [hn]; exact Dvd.dvd.mul_right (dvd_pow_self _ hd.ne') _
    have hdvd' : q ∣ Nat.card (Units.torsion E) ^ Module.finrank ℤ (𝓞 E) := by exact_mod_cast hdvd
    exact hqt (hq.dvd_of_dvd_pow hdvd')
  have huv : (v : 𝓞 E) = u := by rw [← hζv, hζeq, one_mul]
  have hE : IsCMField.complexConj E ((u : 𝓞 E) : E) = ((u : 𝓞 E) : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) huv
    exact this
  rw [← IsCMField.complexEmbedding_complexConj, hE]

end GlobalTheory.UnitReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCocycleCoboundaryOfTrivialOnStabilisers
section
namespace GlobalTheory

theorem unitary_cocycle_coboundary_of_trivial_on_stabilisers :
    ∀ {X G : Type} [Group G] (mv : X → G → X) (z : X → G → ℂ), (∀ x, mv x 1 = x) →
      (∀ x g g', mv x (g * g') = mv (mv x g) g') → (∀ x g, ‖z x g‖ = 1) →
      (∀ x g g', z x (g * g') = z x g * z (mv x g) g') → (∀ x g, mv x g = x → z x g = 1) →
      ∃ c : X → ℂ, (∀ x, ‖c x‖ = 1) ∧ ∀ x g, c x * z x g = c (mv x g) := by
  intro X G _ mv z h1 hmul hn hz hs
  have key : ∀ b h h', mv b h = mv b h' → z b h = z b h' := by
    intro b h h' e
    have e1 : mv b (h * h'⁻¹) = b := by
      rw [hmul, e, ← hmul, mul_inv_cancel, h1]
    have e2 := hz b (h * h'⁻¹) h'
    rw [hs b _ e1, e1, one_mul, inv_mul_cancel_right] at e2
    exact e2
  let s : Setoid X :=
    { r := fun x y => ∃ g, mv x g = y
      iseqv :=
        { refl := fun x => ⟨1, h1 x⟩
          symm := by
            rintro x y ⟨g, rfl⟩
            exact ⟨g⁻¹, by rw [← hmul, mul_inv_cancel, h1]⟩
          trans := by
            rintro x y w ⟨g, rfl⟩ ⟨g', rfl⟩
            exact ⟨g * g', hmul _ _ _⟩ } }
  let b : X → X := fun x => (Quotient.mk s x).out
  have hb : ∀ x, ∃ g, mv (b x) g = x := fun x => Quotient.mk_out (s := s) x
  have hbe : ∀ x g, b (mv x g) = b x := by
    intro x g
    have : Quotient.mk s (mv x g) = Quotient.mk s x :=
      (Quotient.sound (s := s) (⟨g, rfl⟩ : ∃ g', mv x g' = mv x g)).symm
    simp only [b, this]
  choose γ hγ using hb
  refine ⟨fun x => z (b x) (γ x), fun x => hn _ _, fun x g => ?_⟩
  have e := hz (b x) (γ x) g
  rw [hγ] at e
  have e' := hγ (mv x g)
  show z (b x) (γ x) * z x g = z (b (mv x g)) (γ (mv x g))
  rw [hbe] at e' ⊢
  rw [← e]
  apply key
  rw [hmul, hγ, e']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOne
section
open MeasureTheory

namespace GlobalTheory.UnitaryChart

open Topology Filter

theorem hasStrictFDerivAt_ofFn_prod {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedRing E] [NormedAlgebra ℝ E] :
    ∀ (N : ℕ) (g : Fin N → F → E) (g' : Fin N → F →L[ℝ] E),
      (∀ i, g i 0 = 1 ∧ HasStrictFDerivAt (g i) (g' i) 0) →
      (List.ofFn fun i => g i 0).prod = 1 ∧
        HasStrictFDerivAt (fun t => (List.ofFn fun i => g i t).prod) (∑ i, g' i) 0 := by
  intro N
  induction N with
  | zero =>
    intro g g' _
    simpa using hasStrictFDerivAt_const (𝕜 := ℝ) (1 : E) (0 : F)
  | succ N ih =>
    intro g g' h
    obtain ⟨h1, h2⟩ := ih (fun i => g i.succ) (fun i => g' i.succ) (fun i => h i.succ)
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    refine ⟨by rw [h1, (h 0).1, mul_one], ?_⟩
    have h3 := (h 0).2.mul' h2
    refine (h3.congr_fderiv ?_)
    ext y
    simp [h1, (h 0).1, add_comm]

theorem unitary_list_prod {E : Type} [Ring E] (σ : E → E) (hm : ∀ a b, σ (a * b) = σ b * σ a)
    (h1 : σ 1 = 1) (l : List E) (hl : ∀ u ∈ l, σ u * u = 1 ∧ u * σ u = 1) :
    σ l.prod * l.prod = 1 ∧ l.prod * σ l.prod = 1 := by
  induction l with
  | nil => simp [h1]
  | cons a l ih =>
    obtain ⟨i1, i2⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
    obtain ⟨a1, a2⟩ := hl a List.mem_cons_self
    rw [List.prod_cons, hm]
    constructor
    · calc σ l.prod * σ a * (a * l.prod) = σ l.prod * (σ a * a) * l.prod := by noncomm_ring
        _ = 1 := by rw [a1, mul_one, i1]
    · calc a * l.prod * (σ l.prod * σ a) = a * (l.prod * σ l.prod) * σ a := by noncomm_ring
        _ = 1 := by rw [i2, mul_one, a2]

theorem eq_of_skew_eq {E : Type} [NormedRing E] [NormedAlgebra ℝ E] {u v u' v' : E}
    (hu : u' * u = 1) (hv : v * v' = 1)
    (h : u - u' = v - v') (nu : ‖1 - u'‖ ≤ 1 / 2) (nv : ‖1 - v'‖ ≤ 1 / 2) : u = v := by
  set w := u - v with hw
  have e1 : w = u' - v' := by
    rw [hw]; exact sub_eq_sub_iff_sub_eq_sub.mp h
  have e2 : u' * w * v' = v' - u' := by
    calc u' * w * v' = (u' * u) * v' - u' * (v * v') := by rw [hw]; noncomm_ring
      _ = v' - u' := by rw [hu, hv, one_mul, mul_one]
  have e3 : (2 : ℝ) • w = (1 - u') * w + w * (1 - v') - (1 - u') * w * (1 - v') := by
    have : (1 - u') * w + w * (1 - v') - (1 - u') * w * (1 - v') = w - u' * w * v' := by
      noncomm_ring
    rw [this, e2, two_smul]
    nth_rewrite 2 [e1]
    abel
  have n0 := norm_nonneg w
  have n1 : ‖(1 - u') * w‖ ≤ 1 / 2 * ‖w‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right nu n0)
  have n2 : ‖w * (1 - v')‖ ≤ ‖w‖ * (1 / 2) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left nv n0)
  have n3 : ‖(1 - u') * w * (1 - v')‖ ≤ 1 / 2 * ‖w‖ * (1 / 2) :=
    (norm_mul_le _ _).trans (mul_le_mul n1 nv (norm_nonneg _) (by positivity))
  have n4 : 2 * ‖w‖ ≤ ‖(1 - u') * w‖ + ‖w * (1 - v')‖ + ‖(1 - u') * w * (1 - v')‖ := by
    have : ‖(2 : ℝ) • w‖ = 2 * ‖w‖ := by rw [norm_smul]; simp
    rw [← this, e3]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have : ‖w‖ = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem exists_skew_coord {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) {N : ℕ} (e : Fin N → E) (hσ : ∀ a, σ (σ a) = a)
    (hli : LinearIndependent ℝ e) (he : ∀ i, σ (e i) = -e i)
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) :
    ∃ P : E →L[ℝ] (Fin N → ℝ), (∀ t : Fin N → ℝ, P (∑ i, t i • e i) = t) ∧
      (∀ m, σ m = m → P m = 0) ∧ ∀ u v, P u = P v → u - σ u = v - σ v := by
  let T : (Fin N → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ e
  have hT : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.mpr hli.fintypeLinearCombination_injective
  obtain ⟨Q, hQ⟩ := T.exists_leftInverse_of_injective hT
  have hQT : ∀ t, Q (∑ i, t i • e i) = t := fun t => by
    have := LinearMap.congr_fun hQ t
    simpa [T, Fintype.linearCombination_apply] using this
  let π : E →ₗ[ℝ] E := (1 / 2 : ℝ) • (LinearMap.id - σ)
  have hπ : ∀ m, π m = (1 / 2 : ℝ) • (m - σ m) := fun m => rfl
  refine ⟨LinearMap.toContinuousLinearMap (Q ∘ₗ π), fun t => ?_, fun m hm => ?_, fun u v h => ?_⟩
  · have : σ (∑ i, t i • e i) = -∑ i, t i • e i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, he]
    change Q (π _) = t
    rw [hπ, this, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
    norm_num
    simpa using hQT t
  · change Q (π _) = 0
    rw [hπ, hm, sub_self, smul_zero, map_zero]
  · change Q (π u) = Q (π v) at h
    have h2 : Q (π (u - v)) = 0 := by rw [map_sub, map_sub, h, sub_self]
    have h3 : σ (π (u - v)) = -π (u - v) := by
      rw [hπ, map_smul, map_sub, hσ, ← smul_neg, neg_sub]
    obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hsp _ h3)
    rw [← hy, hQT] at h2
    have h4 : π (u - v) = 0 := by rw [← hy, h2]; simp
    rw [hπ, smul_eq_zero] at h4
    rcases h4 with h4 | h4
    · norm_num at h4
    · rw [map_sub] at h4
      exact sub_eq_sub_iff_sub_eq_sub.mp (sub_eq_zero.mp h4)

theorem second_kind_chart : ∀ (E : Type) [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E) (N : ℕ) (e : Fin N → E) (c : Fin N → ℝ → E), (∀ a, σ (σ a) = a) → (∀ a b, σ (a * b) = σ b * σ a) → σ 1 = 1 → LinearIndependent ℝ e → (∀ i, σ (e i) = -e i) → (∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) → (∀ i, c i 0 = 1 ∧ HasStrictDerivAt (c i) (e i) 0 ∧ ∀ t, σ (c i t) * c i t = 1 ∧ c i t * σ (c i t) = 1) → ∃ (s S K : ℝ) (W : Set E), 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : E) ∧ ∀ x ∈ W, σ x * x = 1 → x * σ x = 1 → ∃ f : (Fin N → ℝ) → (Fin N → ℝ), (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧ (List.ofFn fun i => c i (f t i)).prod * x = (List.ofFn fun i => c i (t i)).prod) ∧ ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by
  intro E _ _ _ σ N e c hσ hm h1 hli he hsp hc
  set Θ : (Fin N → ℝ) → E := fun t => (List.ofFn fun i => c i (t i)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact (hc i).2.2 _)
  let T : (Fin N → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)
  have hT : ∀ t, T t = ∑ i, t i • e i := fun t => by simp [T]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    hasStrictFDerivAt_ofFn_prod N (fun i (t : Fin N → ℝ) => c i (t i)) _ (fun i =>
      ⟨(hc i).1, HasStrictFDerivAt.comp (0 : Fin N → ℝ) (g := c i)
        (hc i).2.1.hasStrictFDerivAt
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i).hasStrictFDerivAt⟩)
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_skew_coord σ e hσ hli he hsp
  have hΨ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hΨ0 : P (Θ 0) = 0 := by rw [h0]; exact hP2 _ h1
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  obtain ⟨U₁, hU₁, hA⟩ := hΨ.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
  obtain ⟨L, U₂, hU₂, hL⟩ := hD.exists_lipschitzOnWith
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := by fun_prop
    exact this.eventually_le_const (by simp [h1])
  have hΘt : Tendsto Θ (𝓝 0) (𝓝 1) := h0 ▸ hD.continuousAt
  let U : Set (Fin N → ℝ) := U₁ ∩ U₂ ∩ {t | ‖1 - σ (Θ t)‖ ≤ 1 / 2} ∩ Metric.closedBall 0 1
  have hUn : U ∈ 𝓝 0 :=
    inter_mem (inter_mem (inter_mem hU₁ hU₂) (hΘt.eventually hnear))
      (Metric.closedBall_mem_nhds _ one_pos)
  have hV : (fun t => P (Θ t)) '' U ∈ 𝓝 (0 : Fin N → ℝ) := by
    have := hΨ.map_nhds_eq_of_equiv
    rw [hΨ0] at this
    rw [← this]
    exact image_mem_map hUn
  have hM : Tendsto (fun p : (Fin N → ℝ) × E => Θ p.1 * σ p.2) (𝓝 0 ×ˢ 𝓝 1) (𝓝 1) := by
    have a : Tendsto σ (𝓝 1) (𝓝 1) := by
      simpa [h1] using hσc.tendsto 1
    simpa using (hΘt.comp tendsto_fst).mul (a.comp tendsto_snd)
  have hPM : Tendsto (fun p : (Fin N → ℝ) × E => P (Θ p.1 * σ p.2)) (𝓝 0 ×ˢ 𝓝 1) (𝓝 0) := by
    have a : Tendsto P (𝓝 1) (𝓝 0) := by
      simpa [hP2 _ h1] using P.continuous.tendsto 1
    exact a.comp hM
  obtain ⟨A, hAn, W, hWn, hAW⟩ := Filter.mem_prod_iff.mp ((hM.eventually hnear).and (hPM hV))
  obtain ⟨s, hs, hsA⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hAn hU₁)
  have hcube : ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), t ∈ A ∩ U₁ := by
    intro t ht
    apply hsA
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hs.le]
    intro i
    have := ht i (Set.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  refine ⟨s, 1, 2 * (‖P‖ * (L * (‖(1 : E)‖ + 1))), W ∩ Metric.closedBall 1 1, hs, by positivity,
    inter_mem hWn (Metric.closedBall_mem_nhds _ one_pos), fun x hx hx1 hx2 => ?_⟩
  have hxn : ‖x‖ ≤ ‖(1 : E)‖ + 1 := norm_le_of_mem_closedBall hx.2
  have key : ∀ t : Fin N → ℝ, ∃ y : Fin N → ℝ, t ∈ A → y ∈ U ∧ Θ y * x = Θ t := by
    intro t
    by_cases ht : t ∈ A
    · obtain ⟨k1, y, hy, k2⟩ := hAW (Set.mk_mem_prod ht hx.1)
      refine ⟨y, fun _ => ⟨hy, ?_⟩⟩
      have hv : Θ t * σ x * σ (Θ t * σ x) = 1 := by
        rw [hm, hσ]
        calc Θ t * σ x * (x * σ (Θ t)) = Θ t * (σ x * x) * σ (Θ t) := by noncomm_ring
          _ = 1 := by rw [hx1, mul_one, (hU t).2]
      have := eq_of_skew_eq (hU y).1 hv (hP3 _ _ k2) hy.1.2 k1
      rw [this, mul_assoc, hx1, mul_one]
    · exact ⟨0, fun h => absurd h ht⟩
  choose f hf using key
  refine ⟨f, fun t ht => ?_, fun t ht t' ht' => ?_⟩
  · obtain ⟨a, b⟩ := hf t (hcube t ht).1
    exact ⟨mem_closedBall_zero_iff.mp a.2, b⟩
  · obtain ⟨a, b⟩ := hf t (hcube t ht).1
    obtain ⟨a', b'⟩ := hf t' (hcube t' ht').1
    have k1 := hA t (hcube t ht).2 t' (hcube t' ht').2
    have k2 : ‖t - t'‖ ≤ 2 * ‖P (Θ t) - P (Θ t')‖ := by
      have k3 : ‖t - t'‖ ≤ ‖P (Θ t) - P (Θ t')‖ + ‖P (Θ t) - P (Θ t') - (t - t')‖ := by
        have := norm_sub_le (P (Θ t) - P (Θ t')) (P (Θ t) - P (Θ t') - (t - t'))
        simpa using this
      have k4 : ‖P (Θ t) - P (Θ t') - (t - t')‖ ≤ 1 / 2 * ‖t - t'‖ := by simpa using k1
      linarith
    have k5 : ‖Θ (f t) - Θ (f t')‖ ≤ L * ‖f t - f t'‖ := by
      simpa [dist_eq_norm] using hL.dist_le_mul _ a.1.1.2 _ a'.1.1.2
    have k6 : ‖P (Θ t) - P (Θ t')‖ ≤ ‖P‖ * (L * ‖f t - f t'‖ * (‖(1 : E)‖ + 1)) := by
      rw [← map_sub, ← b, ← b', ← sub_mul]
      refine (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact (norm_mul_le _ _).trans (mul_le_mul k5 hxn (norm_nonneg _) (by positivity))
    calc ‖t - t'‖ ≤ 2 * (‖P‖ * (L * ‖f t - f t'‖ * (‖(1 : E)‖ + 1))) := by linarith
      _ = _ := by ring

end GlobalTheory.UnitaryChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTensorPlacesSlots
section
open Matrix
open scoped Classical

namespace GlobalTheory

theorem pi_prod_rows_orthonormal {K : Type} [Fintype K] [DecidableEq K] {κ : K → Type}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)] [DecidableEq (∀ k, κ k)]
    (A : ∀ k, Matrix (κ k) (κ k) ℂ)
    (hA : ∀ k a b, ∑ y, A k a y * star (A k b y) = if a = b then 1 else 0)
    (T T'' : ∀ k, κ k) :
    ∑ x : ∀ k, κ k, (∏ k, A k (T k) (x k)) * star (∏ k, A k (T'' k) (x k)) =
      if T = T'' then 1 else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k y => A k (T k) y * star (A k (T'' k) y))]
  rw [Finset.prod_congr rfl (fun k _ => hA k (T k) (T'' k)), Finset.prod_boole]
  by_cases hT : T = T''
  · subst hT; simp
  · rw [if_neg hT, if_neg]
    intro hall
    exact hT (funext fun k => hall k (Finset.mem_univ k))

theorem unitary_tensor_places_positions : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι]
    [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) →
    (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈
      Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by
  intro J ι _ _ _ _ n C hC
  have hC' : ∀ j (a b : ι), ∑ y, C j a y * star (C j b y) = if a = b then 1 else 0 := by
    intro j a b
    have := congrFun (congrFun ((mem_unitaryGroup_iff).1 (hC j)) a) b
    simpa only [Matrix.mul_apply, star_apply, Matrix.one_apply] using this
  have hD : ∀ j (S S'' : Fin (n j) → ι),
      ∑ y : Fin (n j) → ι, (∏ r, C j (S r) (y r)) * star (∏ r, C j (S'' r) (y r)) =
        if S = S'' then 1 else 0 := fun j =>
    pi_prod_rows_orthonormal (κ := fun _ => ι) (fun _ => C j) (fun _ => hC' j)
  have key := pi_prod_rows_orthonormal (κ := fun j => Fin (n j) → ι)
    (fun j => of fun S S' : Fin (n j) → ι => ∏ r, C j (S r) (S' r))
    (fun j a b => by simpa only [of_apply] using hD j a b)
  rw [mem_unitaryGroup_iff]
  ext T T''
  simpa only [Matrix.mul_apply, star_apply, of_apply, Matrix.one_apply] using key T T''

end GlobalTheory
end

