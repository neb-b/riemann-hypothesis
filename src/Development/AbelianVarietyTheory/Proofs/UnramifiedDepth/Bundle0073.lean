module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvPFirstOrderOfEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem prod_pow_of_mul_eq_zero {A κ : Type} [CommRing A] [Fintype κ] [DecidableEq κ] (x : κ → A)
    (hx : ∀ i j, x i * x j = 0) (k : κ → ℕ) :
    ∏ i, x i ^ k i = ∏ i, (0 : A) ^ k i + ∑ i, if k = Pi.single i 1 then x i else 0 := by
  by_cases h0 : k = 0
  · subst h0
    rw [Finset.sum_eq_zero fun i _ => if_neg fun h => by simpa using congrFun h i]
    simp
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
  have hi : k i ≠ 0 := hi
  rw [Finset.prod_eq_zero (f := fun i => (0 : A) ^ k i) (Finset.mem_univ i) (zero_pow hi), zero_add,
    Finset.sum_eq_single i (fun j _ hj => if_neg fun h => hi (by rw [h]; simp [hj.symm])) (by simp)]
  split_ifs with h
  · subst h
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  · by_cases h1 : k i = 1
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
      have hji : j ≠ i := by rintro rfl; simp [h1] at hj
      have hj0 : k j ≠ 0 := by simpa [hji] using hj
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩), h1, pow_one]
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      rw [hm, pow_succ', mul_assoc (x j), ← mul_assoc (x i), hx, zero_mul]
    · refine Finset.prod_eq_zero (Finset.mem_univ i) (pow_eq_zero_of_le (m := 2) (by omega) ?_)
      rw [pow_two, hx]

theorem evalPoints_first_order_of_sq_eq_zero {R : Type} [CommRing R] {d : ℕ} (ph : PS R 3 d) {A : Type} [CommRing A] [Algebra R A]
    (e : A) (he : e ^ 2 = 0) (u : Fin d → R) (b b' : Fin d → A) (hb : ∀ j, IsNilpotent (b j))
    (hb' : ∀ j, IsNilpotent (b' j)) :
    evP ![fun j => u j • e, b, b'] ph = evP ![0, b, b'] ph + e * evP ![b, b'] (c2 ph u) := by
  have hx : ∀ i j, (u i • e) * (u j • e) = 0 := fun i j => by
    rw [smul_mul_smul_comm, ← pow_two, he, smul_zero]
  obtain ⟨N₁, -, h₁⟩ := evBasic_exists_pow b hb
  obtain ⟨N₂, -, h₂⟩ := evBasic_exists_pow b' hb'
  obtain ⟨N, hN, h₁, h₂⟩ : ∃ N, 2 ≤ N ∧ (∀ j, b j ^ N = 0) ∧ ∀ j, b' j ^ N = 0 :=
    ⟨N₁ + N₂ + 2, by omega, fun j => pow_eq_zero_of_le (by omega) (h₁ j),
      fun j => pow_eq_zero_of_le (by omega) (h₂ j)⟩
  have h3 : ∀ x : Fin d → A, (∀ j, x j ^ N = 0) →
      ∀ q : Fin 3 × Fin d, (![x, b, b'] : Fin 3 → Fin d → A) q.1 q.2 ^ N = 0 := by
    rintro x hx ⟨i, j⟩
    fin_cases i
    exacts [hx j, h₁ j, h₂ j]
  have h2 : ∀ q : Fin 2 × Fin d, (![b, b'] : Fin 2 → Fin d → A) q.1 q.2 ^ N = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [h₁ j, h₂ j]
  have hp : ∀ (x : Fin d → A) (n : Fin 3 × Fin d → ℕ),
      ∏ q : Fin 3 × Fin d, (![x, b, b'] : Fin 3 → Fin d → A) q.1 q.2 ^ n q = (∏ j, x j ^ n (0, j)) *
        ∏ q : Fin 2 × Fin d, (![b, b'] : Fin 2 → Fin d → A) q.1 q.2 ^ n (q.1.succ, q.2) := by
    intro x n
    rw [Fintype.prod_prod_type, Fin.prod_univ_succ, Fintype.prod_prod_type]
    rfl
  unfold evP
  rw [evBasic_nEval_eq_tEval _ _ N (h3 _ fun j => pow_eq_zero_of_le hN (by rw [pow_two, hx])),
    evBasic_nEval_eq_tEval _ _ N (h3 0 fun j => zero_pow (by omega)),
    evBasic_nEval_eq_tEval _ _ N h2, evBasic_tEval_eq_sum, evBasic_tEval_eq_sum, evBasic_tEval_eq_sum]
  simp only [hp, prod_pow_of_mul_eq_zero _ hx, add_mul, mul_add, Finset.sum_add_distrib, Pi.zero_apply,
    add_right_inj]
  have hc : ∀ mu, MvPowerSeries.coeff mu (c2 ph u) = ∑ i, u i * MvPowerSeries.coeff
    (mu.mapDomain (fun q : Fin 2 × Fin d => (q.1.succ, q.2)) + Finsupp.single ((0 : Fin 3), i) 1) ph :=
    fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hc, map_sum, Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, zero_mul, mul_zero]
  rw [Finset.sum_comm, Finset.sum_comm (t := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  have hinj : Function.Injective (fun q : Fin 2 × Fin d => ((q.1.succ, q.2) : Fin 3 × Fin d)) :=
    fun q q' h => by
      simp only [Prod.mk.injEq, Fin.succ_inj] at h
      exact Prod.ext h.1 h.2
  refine Finset.sum_nbij' (fun n q => n (q.1.succ, q.2))
    (fun m q => (Fin.cons (Pi.single i 1) (fun a j => m (a, j)) : Fin 3 → Fin d → ℕ) q.1 q.2) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hn ⊢
    exact fun q => hn.1 _
  · intro m hm
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hm ⊢
    refine ⟨?_, rfl⟩
    rintro ⟨a, j⟩
    refine Fin.cases ?_ (fun a => hm (a, j)) a
    simp only [Fin.cons_zero, Finset.mem_range, Pi.single_apply]
    split_ifs <;> omega
  · intro n hn
    funext ⟨a, j⟩
    exact Fin.cases (congrFun (Finset.mem_filter.1 hn).2 j).symm (fun _ => rfl) a
  · intro m _
    rfl
  · intro n hn
    have hn0 : ∀ j, n (0, j) = (Pi.single i 1 : Fin d → ℕ) j := congrFun (Finset.mem_filter.1 hn).2
    have : (Finsupp.equivFunOnFinite.symm fun q : Fin 2 × Fin d => n (q.1.succ, q.2)).mapDomain
        (fun q : Fin 2 × Fin d => ((q.1.succ, q.2) : Fin 3 × Fin d)) + Finsupp.single ((0 : Fin 3), i) 1 =
        Finsupp.equivFunOnFinite.symm n := by
      ext ⟨a, j⟩
      refine Fin.cases ?_ (fun a => ?_) a
      · rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _
          (by rintro ⟨q, hq⟩; exact Fin.succ_ne_zero _ (congrArg Prod.fst hq))]
        simp [hn0, Finsupp.single_apply, Pi.single_apply, eq_comm]
      · rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective hinj _ (a, j),
          Finsupp.single_eq_of_ne (fun h => Fin.succ_ne_zero _ (congrArg Prod.fst h))]
        simp
    rw [this, map_mul, Algebra.smul_def]
    ring

theorem evalPoints_first_order_of_eq_one : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ (u : Fin d → R) (b b' : Fin d → A), (∀ j, IsNilpotent (b j)) → (∀ j, IsNilpotent (b' j)) → evP ![fun j => u j • e, b, b'] ph = 1 + e * evP ![b, b'] (c2 ph u) := by
  intro R _ d ph hph A _ _ e he u b b' hb hb'
  rw [evalPoints_first_order_of_sq_eq_zero ph e he u b b' hb hb']
  congr 1
  have hn : ∀ q : Fin 2 × Fin d, IsNilpotent ((![b, b'] : Fin 2 → Fin d → A) q.1 q.2) := by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [hb j, hb' j]
  have h := congrArg (fun f => nEval f fun q : Fin 2 × Fin d => (![b, b'] : Fin 2 → Fin d → A) q.1 q.2) hph
  beta_reduce at h
  rw [nEval_one hn, ev, ChartCompare.nEval_subst _ _ _ _ hn] at h
  · rw [← h, evP]
    congr 1
    funext ⟨i, j⟩
    fin_cases i
    · exact (ChartCompare.nEval_zero _ hn).symm
    · exact (ChartCompare.nEval_X _ hn (0, j)).symm
    · exact (ChartCompare.nEval_X _ hn (1, j)).symm
  · rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]

end GlobalTheory.AlphaPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvalPowerSeriesEqOneOfTwoAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AlphaPair

section TwoAxes

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}

theorem axes_monomial_sub_mem (I : Ideal A) (a : Fin d → A) (ha : ∀ j, a j ∈ I) (m : Fin d → ℕ) :
    (∏ j, a j ^ m j) - ∏ j, (0 : A) ^ m j ∈ I := by
  rw [← Ideal.Quotient.eq]
  simp only [map_prod, map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (ha _), map_zero]

theorem axes_mul_eq_zero {e x y : A} (he : e ^ 2 = 0) (hx : x ∈ Ideal.span {e}) (hy : y ∈ Ideal.span {e}) :
    x * y = 0 := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  linear_combination (u * v) * he

theorem evalPoints_second_difference (f : PS R 3 d) {e : A} (he : e ^ 2 = 0) (a a' b : Fin d → A)
    (ha : ∀ j, a j ∈ Ideal.span {e}) (ha' : ∀ j, a' j ∈ Ideal.span {e}) (hb : ∀ j, IsNilpotent (b j)) :
    evP ![a, a', b] f + evP ![0, 0, b] f = evP ![0, a', b] f + evP ![a, 0, b] f := by
  obtain ⟨N, hN0, hN⟩ := evBasic_exists_pow b hb
  have sq : ∀ x ∈ Ideal.span {e}, x ^ (N + 2) = 0 := fun x hx => by
    rw [pow_add, sq, axes_mul_eq_zero he hx hx, mul_zero]
  have key : ∀ c c' : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → (∀ j, c' j ∈ Ideal.span {e}) →
      evP ![c, c', b] f = ReciprocityTheory.PGsh.Be2.tEval (N + 2) f
        (fun q : Fin 3 × Fin d => ![c, c', b] q.1 q.2) := fun c c' hc hc' => by
    refine evBasic_nEval_eq_tEval f _ (N + 2) ?_
    rintro ⟨i, j⟩
    fin_cases i
    · exact sq _ (hc j)
    · exact sq _ (hc' j)
    · show b j ^ (N + 2) = 0
      rw [pow_add, hN, zero_mul]
  have h0 : ∀ j, (0 : Fin d → A) j ∈ Ideal.span {e} := fun _ => Ideal.zero_mem _
  rw [key a a' ha ha', key 0 0 h0 h0, key 0 a' h0 ha', key a 0 ha h0]
  unfold ReciprocityTheory.PGsh.Be2.tEval
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Fintype.prod_prod_type, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply]
  have h := axes_mul_eq_zero he (axes_monomial_sub_mem _ a ha fun j => m (0, j))
    (axes_monomial_sub_mem _ a' ha' fun j => m (1, j))
  rw [← mul_add, ← mul_add]
  congr 1
  linear_combination (∏ j, b j ^ (m (2, j) : ℕ)) * h

theorem evalPoints_eval_axis {u v : Fin d → PS R 2 d} {f : PS R 3 d}
    (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) (hv : ∀ j, MvPowerSeries.constantCoeff (v j) = 0)
    (h : ev (n := 2) ![u, v, pt R d 1] f = 1) (c b : Fin d → A)
    (hc : ∀ j, IsNilpotent (c j)) (hb : ∀ j, IsNilpotent (b j)) (x y : Fin d → A)
    (hx : ∀ j, evP ![c, b] (u j) = x j) (hy : ∀ j, evP ![c, b] (v j) = y j) :
    evP ![x, y, b] f = 1 := by
  have hn : ∀ q : Fin 2 × Fin d, IsNilpotent (![c, b] q.1 q.2) := by
    rintro ⟨i, j⟩
    fin_cases i
    · exact hc j
    · exact hb j
  have h1 := congrArg (evP ![c, b]) h
  unfold evP ev at h1
  rw [nEval_one hn, ChartCompare.nEval_subst _ _ _ _ hn] at h1
  · rw [← h1]
    unfold evP
    congr 1
    funext ⟨i, j⟩
    fin_cases i
    · exact (hx j).symm
    · exact (hy j).symm
    · exact (ChartCompare.nEval_X (R₀ := R) _ hn ((1 : Fin 2), j)).symm
  · rintro ⟨i, j⟩
    fin_cases i
    · exact hu j
    · exact hv j
    · exact MvPowerSeries.constantCoeff_X _

end TwoAxes

theorem evalPoints_eq_one_of_two_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ a a' b : Fin d → A, (∀ j, a j ∈ Ideal.span {e}) → (∀ j, a' j ∈ Ideal.span {e}) → (∀ j, IsNilpotent (b j)) → evP ![a, a', b] ph = 1 := by
  intro R _ d ph h₁ h₂ A _ _ e he a a' b ha ha' hb
  have nil : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → ∀ j, IsNilpotent (c j) := fun c hc j =>
    ⟨2, by rw [sq, axes_mul_eq_zero he (hc j) (hc j)]⟩
  have hn : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) →
      ∀ q : Fin 2 × Fin d, IsNilpotent (![c, b] q.1 q.2) := by
    rintro c hc ⟨i, j⟩
    fin_cases i
    · exact nil c hc j
    · exact hb j
  have e₁ : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → evP ![0, c, b] ph = 1 := fun c hc =>
    evalPoints_eval_axis (fun _ => map_zero _) (fun _ => MvPowerSeries.constantCoeff_X _) h₁ c b (nil c hc) hb 0 c
      (fun _ => ChartCompare.nEval_zero _ (hn c hc))
      (fun j => ChartCompare.nEval_X (R₀ := R) _ (hn c hc) ((0 : Fin 2), j))
  have e₂ : evP ![a, 0, b] ph = 1 :=
    evalPoints_eval_axis (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => map_zero _) h₂ a b (nil a ha) hb a 0
      (fun j => ChartCompare.nEval_X (R₀ := R) _ (hn a ha) ((0 : Fin 2), j))
      (fun _ => ChartCompare.nEval_zero _ (hn a ha))
  have h := evalPoints_second_difference ph he a a' b ha ha' hb
  rw [e₁ a' ha', e₂, e₁ 0 fun _ => Ideal.zero_mem _] at h
  exact add_right_cancel h

end GlobalTheory.AlphaPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsTorusExtensionOnPointsModIdeal
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorExtPoints

variable {S S' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem exists_lift {X Y : Scheme.{0}} (q : X ⟶ Y) [Smooth q] {A : Type} [CommRing A] [Algebra Ω A]
    (π : A →ₐ[Ω] Ω) (hn : IsNilpotent (RingHom.ker π)) (y : Sp A ⟶ Y) (x₀ : Sp Ω ⟶ X)
    (h : x₀ ≫ q = spMap (π : A →+* Ω) ≫ y) : ∃ x : Sp A ⟶ X, spMap (π : A →+* Ω) ≫ x = x₀ ∧ x ≫ q = y := by
  have hπ : Function.Surjective π := fun a => ⟨algebraMap Ω A a, π.commutes a⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ := exists_isAffineOpen_pair q (x₀ (closedPoint Ω)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen q hU hV hVU (CommRingCat.ofHom (π : A →+* Ω)) y x₀ h ?_
    (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · rintro _ ⟨p, rfl⟩
    obtain ⟨z, hz⟩ : p ∈ Set.range (PrimeSpectrum.comap (π : A →+* Ω)) := by
      refine (range_comap_of_surjective _ (π : A →+* Ω) hπ).ge ?_
      obtain ⟨n, hn⟩ := hn
      exact (Ideal.IsPrime.pow_le_iff (P := p.asIdeal) (hP := p.isPrime) n.succ_ne_zero).1 (by
        rw [pow_succ]
        exact Ideal.mul_le_left.trans (hn.le.trans bot_le))
    obtain rfl : z = closedPoint Ω := Subsingleton.elim _ _
    have e : q (x₀ (closedPoint Ω)) = y (spMap (π : A →+* Ω) (closedPoint Ω)) := congr($h (closedPoint Ω))
    rw [← hz]
    exact e ▸ hVU hxV
  · intro R C _ _ _ _ _ _ p hp φ
    have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
    have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
      convert hn using 1
      exact Ideal.ext fun b => Eq.congr_left (hp b)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
      Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩

def torPt (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] [Algebra Ω A] :
    (overAt s A ⟶ splitTorus S X) ≃* (Multiplicative X →* Aˣ) :=
  (splitTorusPointsEquiv S X (overAt s A)).trans
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv).monoidHomCongrRight

theorem torPt_nat (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] {A A' : Type} [CommRing A] [Algebra Ω A]
    [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A') (t : overAt s A ⟶ splitTorus S X) :
    torPt s X A' (homAt s f ≫ t) = (Units.map (f : A →* A')).comp (torPt s X A t) := by
  ext x
  change (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom
      (splitTorusPointsEquiv S X _ (homAt s f ≫ t) (Multiplicative.ofAdd x)).val =
    f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (splitTorusPointsEquiv S X _ t (Multiplicative.ofAdd x)).val)
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, Over.comp_left, Scheme.Hom.comp_appTop]
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* A'))) _)

theorem isTorExt_of_kernel (s : Sp Ω ⟶ S) {G B : Over S} [GrpObj G] [GrpObj B] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] [Smooth q.left]
    (hk : IsPullback i (toUnit _) q η[B]) :
    IsTorExt s s G B X (fun A _ _ => IsMonHom.monoidHom q (overAt s A))
      (fun A _ _ => (IsMonHom.monoidHom i (overAt s A)).comp (torPt s X A).symm.toMonoidHom) := by
  refine ⟨fun A A' _ _ _ _ f x => Category.assoc _ x q, fun A A' _ _ _ _ f χ => ?_, fun A _ _ χ χ' h => ?_,
    fun A _ _ x => ⟨fun h => ?_, ?_⟩, fun A _ _ π hn y hy => ?_⟩
  · obtain ⟨t, rfl⟩ := (torPt s X A).surjective χ
    rw [← torPt_nat]
    change (torPt s X A').symm _ ≫ i = _ ≫ (torPt s X A).symm _ ≫ i
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Category.assoc]
  · exact (torPt s X A).symm.injective (hk.hom_ext h (toUnit_unique _ _))
  · refine ⟨torPt s X A (hk.lift x (toUnit _) h), ?_⟩
    change (torPt s X A).symm _ ≫ i = _
    rw [MulEquiv.symm_apply_apply]
    exact hk.lift_fst _ _ _
  · rintro ⟨χ, rfl⟩
    change (_ ≫ i) ≫ q = toUnit _ ≫ η[B]
    rw [Category.assoc, hk.w, ← Category.assoc, toUnit_unique (_ ≫ _) (toUnit _)]
  · have h1 : (1 : overAt s Ω ⟶ G) ≫ q = homAt s π ≫ y := (map_one (IsMonHom.monoidHom q _)).trans hy.symm
    obtain ⟨x, hx, hq⟩ := exists_lift q.left π hn y.left (1 : overAt s Ω ⟶ G).left (congrArg (·.left) h1)
    exact ⟨Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w y), Over.OverMorphism.ext hx,
      Over.OverMorphism.ext hq⟩

theorem exists_ptEquiv {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') {t : T.left ⟶ S} (ht : t = T.hom ≫ f) :
    ∃ E : (T ⟶ G') ≃* (Over.mk t ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  subst ht
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_isTorExt_of_pullback {G B : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj G'] [GrpObj B] [GrpObj B']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left} (hG : IsGrpPullback G' G f φ)
    (hB : IsGrpPullback B' B f ψ) {s' : Sp Ω ⟶ S'} {s : Sp Ω ⟶ S} (hs : s' ≫ f = s) {X : Type} [AddCommGroup X]
    {τ' : PtHom s' s' G' B'} {io' : TorHom s' G' X} (h : IsTorExt s' s' G' B' X τ' io') :
    ∃ (τ : PtHom s s G B) (io : TorHom s G X), IsTorExt s s G B X τ io ∧
      ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt s A ⟶ G), ∃ x' : overAt s' A ⟶ G',
        x'.left ≫ φ = x.left ∧ (τ A x).left = (τ' A x').left ≫ ψ := by
  have ht : ∀ (A : Type) [CommRing A] [Algebra Ω A], spMap (algebraMap Ω A) ≫ s = (overAt s' A).hom ≫ f :=
    fun A _ _ => by rw [← hs]; exact (Category.assoc _ _ _).symm
  choose E hE using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hG (overAt s' A) (ht A)
  choose F hF using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hB (overAt s' A) (ht A)
  have nE : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ G'), E A' (homAt s' g ≫ x) = homAt s g ≫ E A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hE A' _).trans ((Category.assoc _ x.left φ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hE A x).symm)))
  have nF : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ B'), F A' (homAt s' g ≫ x) = homAt s g ≫ F A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hF A' _).trans ((Category.assoc _ x.left ψ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hF A x).symm)))
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨fun A _ _ => ((F A).toMonoidHom.comp (τ' A)).comp (E A).symm.toMonoidHom,
    fun A _ _ => (E A).toMonoidHom.comp (io' A),
    ⟨fun A A' _ _ _ _ g x => ?_, fun A A' _ _ _ _ g χ => ?_, fun A _ _ => (E A).injective.comp (h₃ A),
      fun A _ _ x => ?_, fun A _ _ π hn y hy => ?_⟩, fun A _ _ x => ?_⟩
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A' (τ' A' ((E A').symm _)) = _ ≫ F A (τ' A ((E A).symm _))
    rw [← nE, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, h₁, nF]
  · change E A' (io' A' _) = _ ≫ E A (io' A χ)
    rw [h₂, nE]
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A (τ' A ((E A).symm _)) = 1 ↔ ∃ χ, E A (io' A χ) = _
    rw [MulEquiv.symm_apply_apply, MulEquiv.map_eq_one_iff, h₄]
    exact exists_congr fun χ => (E A).injective.eq_iff.symm
  · obtain ⟨y, rfl⟩ := (F A).surjective y
    rw [← nF, MulEquiv.map_eq_one_iff] at hy
    obtain ⟨x, hx, rfl⟩ := h₅ A π hn y hy
    refine ⟨E A x, by rw [← nE, hx, map_one], ?_⟩
    change F A (τ' A ((E A).symm _)) = _
    rw [MulEquiv.symm_apply_apply]
  · refine ⟨(E A).symm x, (hE A _).symm.trans ?_, hF A _⟩
    rw [MulEquiv.apply_symm_apply]

theorem exists_isTorExt : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegPre W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (gt : Out.GtCoord I D 0 G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∃ (τ : PtHom (spMap β) (spMap β) G D.P.A) (io : TorHom (spMap β) G D.X), IsTorExt (spMap β) (spMap β) G D.P.A D.X τ io ∧ ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ gt.pG.left := by
  intro W _ _ I D G _ _ g Ω _ β hβ
  let β₀ : W ⧸ I ^ (0 + 1) →+* Ω := Ideal.Quotient.lift _ β (by simpa using hβ)
  have e : spMap β₀ ≫ Out.thick W I 0 = spMap β := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    rfl
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have := (H1.torus_dim (Sp (W ⧸ I ^ (0 + 1))) D.X).smooth
  have : Smooth g.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback g.i g.q g.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact g.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨τ, io, h, hτ⟩ := exists_isTorExt_of_pullback (isGrpPullback_pullback G (Out.thick W I 0))
    (isGrpPullback_pullback D.P.A (Out.thick W I 0)) e (isTorExt_of_kernel (spMap β₀) g.i g.q g.isKernel)
  refine ⟨τ, io, h, fun A _ _ x x₀ hx => ?_⟩
  obtain ⟨x', h₁, h₂⟩ := hτ A x
  have : IsClosedImmersion (Out.thick W I 0) := .spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain rfl : x₀ = x'.left := (cancel_mono (pullback.fst G.hom (Out.thick W I 0))).1 (hx.trans h₁.symm)
  exact h₂.trans (Category.assoc _ _ _)

end GlobalTheory.TorExtPoints
end
end

