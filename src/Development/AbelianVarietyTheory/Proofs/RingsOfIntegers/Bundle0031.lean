module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.FormalGroupCoeffSecondLinear
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardFunLevQ
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem GlobalTheory.PlaceInt.card_fun_levQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (n : ℕ), Nat.card (Fin n → LevQ Dw l) = l.M ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q) * n) := by
  intro E _ _ _ H Dw l n
  rw [Nat.card_fun, (GlobalTheory.card_levQ E H Dw l).2, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleEq
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open MvPowerSeries
open scoped Kronecker
namespace GlobalTheory.JacVal

section Series
variable {V : Type} [CommRing V] {σ τ : Type}

theorem exists_decomp [Fintype σ] (g : MvPowerSeries σ V) :
    ∃ k : σ → MvPowerSeries σ V, g = C (constantCoeff g) + ∑ i, X i * k i := by
  classical
  obtain ⟨k, -, hk⟩ := exists_eq_sum_X_mul (n := 0) (g := g - C (constantCoeff g))
    fun d hd => by
      have : d = 0 := by
        rw [← Finsupp.degree_eq_zero_iff]; omega
      subst this
      simp
  exact ⟨k, by rw [← hk]; ring⟩

theorem coeff_single_eq (q : τ) (f : MvPowerSeries τ V) :
    coeff (Finsupp.single q 1) f = constantCoeff (pderiv (R := V) q f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem coeff_single_mul (q : τ) (a b : MvPowerSeries τ V) (ha : constantCoeff a = 0) :
    coeff (Finsupp.single q 1) (a * b) = coeff (Finsupp.single q 1) a * constantCoeff b := by
  rw [coeff_single_eq, coeff_single_eq, Derivation.leibniz]
  simp [ha, _root_.mul_comm]

theorem coeff_single_C (q : τ) (c : V) : coeff (Finsupp.single q 1) (C c : MvPowerSeries τ V) = 0 := by
  rw [coeff_single_eq]; simp

theorem coeff_single_X [DecidableEq τ] (q p : τ) :
    coeff (Finsupp.single q 1) (X p : MvPowerSeries τ V) = if q = p then 1 else 0 := by
  rw [coeff_X]
  by_cases h : q = p
  · simp [h]
  · rw [if_neg, if_neg h]
    intro h'
    exact h (Finsupp.single_left_injective one_ne_zero h')

theorem const_hom [Fintype σ] (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V)
    (h : ∀ j, constantCoeff (ψ (X j)) = 0) (f : MvPowerSeries σ V) : constantCoeff (ψ f) = constantCoeff f := by
  obtain ⟨k, hk⟩ := exists_decomp f
  have hC : ψ (C (constantCoeff f)) = C (constantCoeff f) := ψ.commutes _
  conv_lhs => rw [hk]
  simp [hC, h]

theorem coeff_hom [Fintype σ] (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V)
    (h : ∀ j, constantCoeff (ψ (X j)) = 0) (f : MvPowerSeries σ V) (q : τ) :
    coeff (Finsupp.single q 1) (ψ f) = ∑ j, coeff (Finsupp.single j 1) f * coeff (Finsupp.single q 1) (ψ (X j)) := by
  classical
  obtain ⟨k, hk⟩ := exists_decomp f
  have hC : ψ (C (constantCoeff f)) = C (constantCoeff f) := ψ.commutes _
  have h1 : ∀ j, coeff (Finsupp.single j 1) f = constantCoeff (k j) := by
    intro j
    conv_lhs => rw [hk]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), coeff_single_C, zero_add, map_sum]
    rw [Finset.sum_congr rfl fun i _ => coeff_single_mul j (X i) (k i) (by simp)]
    simp [coeff_single_X]
  conv_lhs => rw [hk]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), hC, map_add (f := _), coeff_single_C, zero_add, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coeff_single_mul _ _ _ (h j), const_hom ψ h, h1, _root_.mul_comm]

theorem evC_hom [Fintype σ] (a : σ → MvPowerSeries τ V) (ha : ∀ j, constantCoeff (a j) = 0) :
    ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (X j) = a j) ∧ ∀ f, evC a f = ψ f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h : ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j :=
    ⟨substAlgHom hs, fun j => substAlgHom_X hs j⟩
  exact ⟨h.choose, h.choose_spec, fun f => by unfold GlobalTheory.PlaceInt.evC; rw [dite_eq_left h]⟩

theorem const_evC [Fintype σ] (a : σ → MvPowerSeries τ V) (ha : ∀ j, constantCoeff (a j) = 0)
    (f : MvPowerSeries σ V) : constantCoeff (evC a f) = constantCoeff f := by
  obtain ⟨ψ, h1, h2⟩ := evC_hom a ha
  rw [h2, const_hom ψ fun j => by rw [h1, ha]]

theorem coeff_evC [Fintype σ] (a : σ → MvPowerSeries τ V) (ha : ∀ j, constantCoeff (a j) = 0)
    (f : MvPowerSeries σ V) (q : τ) :
    coeff (Finsupp.single q 1) (evC a f) = ∑ j, coeff (Finsupp.single j 1) f * coeff (Finsupp.single q 1) (a j) := by
  obtain ⟨ψ, h1, h2⟩ := evC_hom a ha
  rw [h2, coeff_hom ψ fun j => by rw [h1, ha]]
  simp only [h1]

variable {d m : ℕ}

theorem addV_lin (G : FGLaw V d) (x y : Pt V m d) (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (i : Fin d) :
    constantCoeff (addV G.F x y i) = 0 ∧ ∀ q, coeff (Finsupp.single q 1) (addV G.F x y i) =
      coeff (Finsupp.single q 1) (x i) + coeff (Finsupp.single q 1) (y i) := by
  have ha : ∀ p : Fin 2 × Fin d, constantCoeff ((![x, y] : Fin 2 → Pt V m d) p.1 p.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    · exact hx j
    · exact hy j
  refine ⟨(const_evC _ ha _).trans (G.const i), fun q => (coeff_evC _ ha _ q).trans ?_⟩
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PullbackSections.Pf.EigA.formal_group_coeff_first_linear, PullbackSections.Pf.EigA.formal_group_coeff_second_linear, ite_mul, _root_.one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem fold_lin (G : FGLaw V d) (l : List (Pt V m d)) (hl : ∀ x ∈ l, ∀ i, constantCoeff (x i) = 0) :
    (∀ i, constantCoeff (l.foldr (addV G.F) 0 i) = 0) ∧ ∀ i q, coeff (Finsupp.single q 1) (l.foldr (addV G.F) 0 i) =
      (l.map fun x => coeff (Finsupp.single q 1) (x i)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hx := hl x List.mem_cons_self
    refine ⟨fun i => (addV_lin G x _ hx h1 i).1, fun i q => ?_⟩
    rw [List.foldr_cons, (addV_lin G x _ hx h1 i).2, h2, List.map_cons, List.sum_cons]

theorem compV_pt (φ : Pt V 1 d) (j : Fin m) (i : Fin d) :
    constantCoeff (compV φ (pt V d j) i) = constantCoeff (φ i) ∧
      ∀ q : Fin m × Fin d, coeff (Finsupp.single q 1) (compV φ (pt V d j) i) =
        if q.1 = j then coeff (Finsupp.single ((0 : Fin 1), q.2) 1) (φ i) else 0 := by
  have ha : ∀ p : Fin 1 × Fin d, constantCoeff ((![pt V d j] : Fin 1 → Pt V m d) p.1 p.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    simp [pt]
  refine ⟨const_evC _ ha _, fun q => (coeff_evC _ ha _ q).trans ?_⟩
  obtain ⟨a, b⟩ := q
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  by_cases h : a = j <;> simp [pt, coeff_single_X, h]

variable {O : Type} [CommRing O] [StarRing O]

theorem coeff_matV (B : FB V d O) {n : ℕ} (p : Matrix (Fin n) (Fin n) O) (x q : Fin n × Fin d) :
    coeff (Finsupp.single q 1) (matV B p (fun j => pt V (n := n) d j) x.1 x.2) =
      coeff (Finsupp.single ((0 : Fin 1), q.2) 1) (B.A.act (p x.1 q.1) x.2) := by
  unfold matV
  rw [(fold_lin B.G _ ?_).2, List.map_ofFn, List.sum_ofFn]
  · simp only [Function.comp, (compV_pt _ _ _).2]
    simp
  · intro y hy i
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    rw [(compV_pt _ _ _).1, B.A.const]

end Series

theorem det_blocks {K O L : Type} [CommRing K] [CommRing O] [Fintype L] {d n : ℕ} (M : O → Matrix (Fin d) (Fin d) K)
    (p : Matrix (Fin n) (Fin n) O) (s : L → O →+* K) (u : L → Fin d → K)
    (he : ∀ ℓ a, (M a).mulVec (u ℓ) = s ℓ a • u ℓ)
    (hb : ∀ v : Fin d → K, ∃! a : L → K, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) :
    (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2).det = ∏ ℓ, s ℓ p.det := by
  classical
  let U : Matrix (Fin d) L K := Matrix.of fun j ℓ => u ℓ j
  let W : Matrix L (Fin d) K := Matrix.of fun ℓ t => (hb (Pi.single t 1)).exists.choose ℓ
  have hUW : U * W = 1 := by
    ext j t
    have := (hb (Pi.single t 1)).exists.choose_spec j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [U, W, Matrix.of_apply]
    rw [Finset.sum_congr rfl fun ℓ _ => _root_.mul_comm _ _, this, Pi.single_apply]
  have hWU : W * U = 1 := by
    have h3 : U * (W * U) = U * (1 : Matrix L L K) := by rw [← Matrix.mul_assoc, hUW, Matrix.one_mul, Matrix.mul_one]
    ext ℓ ℓ'
    have := (hb fun j => (U * (1 : Matrix L L K)) j ℓ').unique (y₁ := fun ℓ => (W * U) ℓ ℓ')
      (y₂ := fun ℓ => (1 : Matrix L L K) ℓ ℓ')
      (fun j => by
        rw [← h3, Matrix.mul_apply (M := U)]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _)
      (fun j => by
        rw [Matrix.mul_apply (M := U)]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _)
    exact congrFun this ℓ
  have h1 : ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hUW, Matrix.mul_one, Matrix.one_kronecker_one]
  have h2 : ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hWU, Matrix.mul_one, Matrix.one_kronecker_one]
  have h3 : (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) =
      ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * Matrix.blockDiagonal fun ℓ => (s ℓ).mapMatrix p := by
    ext ⟨i, a⟩ ⟨j, ℓ⟩
    have := congrFun (he ℓ (p i j)) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply, U,
      Matrix.blockDiagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero, _root_.one_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [this, _root_.mul_comm]
    rfl
  have h4 : (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2) =
      ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * (Matrix.blockDiagonal fun ℓ => (s ℓ).mapMatrix p) *
        ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) := by
    rw [← h3, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [h4, Matrix.det_conj_of_mul_eq_one h1 h2, Matrix.det_blockDiagonal]
  exact Finset.prod_congr rfl fun ℓ _ => ((s ℓ).map_det p).symm

theorem jacM_eq_prod : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (n : ℕ) (p : Matrix (Fin n) (Fin n) O) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ v : Fin d → K, ∃! a : (Σ τ : Ty, Fin (r τ)) → K, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) → algebraMap V K (jacM B p) = ∏ τ, σ τ p.det ^ r τ := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ n p Ty _ r σ u he hb
  have h := det_blocks (dAct K B) p (fun ℓ : Σ τ : Ty, Fin (r τ) => σ ℓ.1) u he hb
  rw [Fintype.prod_sigma] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h, jacM, RingHom.map_det]
  congr 1
  ext x q
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, coeff_matV]
  show _ = coeff _ (MvPowerSeries.map (algebraMap V K) _)
  rw [coeff_map]

end GlobalTheory.JacVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfCastDvd
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.TorsFac

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem act_nat {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  have h0 : t.act.act 0 = 1 := by
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h2 := congrArg (fun f => (t.act.act 0)⁻¹ * f) h
    simp only [inv_mul_cancel, inv_mul_cancel_left] at h2
    exact h2.symm
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem act_pow {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (b : 𝓞 E) (n : ℕ) :
    (x ≫ t.act.act b) ^ n = x ≫ t.act.act (b * n) := by
  rw [t.act.mul, ← Category.assoc, act_nat]

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h
  exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h

theorem kill {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (N : ℕ)
    (h : KilledBy Xo l.Mb (t ^ N)) (a : 𝓞 E) (ha : a ∈ l.Mb) : t ≫ Xo.univ.t.act.act (N * a) = 1 := by
  rw [Xo.univ.t.act.mul, ← Category.assoc, act_nat]
  exact h a ha

omit [IsCMField E] in
theorem dvd_of_cast_dvd {p m : ℕ} (hp : p.Prime) (h : (p : 𝓞 E) ∣ (m : 𝓞 E)) : p ∣ m := by
  have h2 := map_dvd (Algebra.norm ℤ) h
  have e1 : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
  have e2 : (m : 𝓞 E) = algebraMap ℤ (𝓞 E) (m : ℤ) := by simp
  rw [e1, e2, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h2
  have hr : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
  rw [IsIntegrallyClosed.pow_dvd_pow_iff hr] at h2
  exact Int.natCast_dvd_natCast.mp h2

theorem split_once {M ℓ e n' : ℕ} (hp : ℓ.Prime) (h1 : ℓ ∣ M) (h2 : ¬ ℓ ^ 2 ∣ M) (h : M ∣ ℓ ^ e * n') :
    ∃ m k, M = ℓ * m ∧ n' = m * k := by
  obtain ⟨m, rfl⟩ := h1
  have hm : ¬ ℓ ∣ m := fun ⟨c, hc⟩ => h2 ⟨c, by rw [hc]; ring⟩
  have hcop : Nat.Coprime m (ℓ ^ e) :=
    Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left ((Dvd.intro_left ℓ rfl).trans h)
  exact ⟨m, k, rfl, hk⟩

private theorem sq_lemma' {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G)
    {N : ℕ} (hMN : l.M ∣ N) (hk : KilledBy Xo l.Mb (t ^ N)) : t ^ (N ^ 2) = 1 := by
  have hN : (N : 𝓞 E) ∈ l.Mb := by
    obtain ⟨q, rfl⟩ := hMN
    push_cast
    exact Ideal.mul_mem_right _ _ (M_mem l)
  rw [sq, pow_mul, ← act_nat Xo.univ.t (t ^ N) N]
  exact hk _ hN

private theorem natCast_mem_level_of_dvd {l : Level H} {k : ℕ} (h : l.M ∣ k) : (k : 𝓞 E) ∈ l.Mb := by
  obtain ⟨q, rfl⟩ := h
  push_cast
  exact Ideal.mul_mem_right _ _ (M_mem l)

private theorem dvd_lemma_3 {M ℓ e n' : ℕ} (hp : ℓ.Prime) (h2 : ¬ ℓ ^ 2 ∣ M) (h : M ∣ ℓ ^ e * n') :
    M ∣ ℓ * n' := by
  by_cases h1 : ℓ ∣ M
  · obtain ⟨m, k, rfl, rfl⟩ := split_once hp h1 h2 h
    exact ⟨k, by ring⟩
  · have hc : Nat.Coprime M (ℓ ^ e) :=
      Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 h1).symm
    exact Dvd.dvd.mul_left (hc.dvd_of_dvd_mul_left h) ℓ

theorem factorisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N ℓ : ℕ), Odd N → l.M ∣ N → ℓ.Prime → (¬ ℓ ∣ l.M → ∃ (n' j : ℕ), Nat.Coprime n' ℓ ∧ N = ℓ ^ j * n' ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) → (∃ i : ℕ, KilledBy Xo (l.Mb ^ i) t) → t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act ((ℓ : 𝓞 E) ^ j)) ^ (n' ^ 2 * 1) = 1 ∧ ∃ i : ℕ, t ^ (l.M ^ i) = 1) ∧ ∀ (α : 𝓞 E) (A : ℕ), α * H.bar α = (A : 𝓞 E) → ¬ ℓ ^ 2 ∣ l.M → ((A = ℓ ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨ (α = (ℓ : 𝓞 E) ∧ ℓ ∣ l.M)) → ∃ (n' Bn j : ℕ) (β : 𝓞 E), Nat.Coprime n' ℓ ∧ (N : 𝓞 E) = β * α * n' ∧ β * H.bar β = (Bn : 𝓞 E) ∧ A * Bn = ℓ ^ j ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) → (∃ i : ℕ, KilledBy Xo (l.Mb ^ i) t) → t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 := by
  intro E _ _ _ H Dw l Xo N ℓ hN hMN hp
  have hN0 : N ≠ 0 := hN.pos.ne'
  refine ⟨fun hℓM => ?_, fun α A hA h2 hc => ?_⟩
  · obtain ⟨j, n', hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 ℓ hp.one_lt.ne'
    have hcop : Nat.Coprime n' ℓ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
    have hMn : l.M ∣ n' := by
      have hc : Nat.Coprime l.M (ℓ ^ j) :=
        Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hℓM).symm
      exact hc.dvd_of_dvd_mul_left (hNe ▸ hMN)
    refine ⟨n', j, hcop, hNe, fun T t hk hi => ⟨sq_lemma' Xo t hMN hk, ?_, ?_⟩⟩
    · rw [act_pow]
      have he : (ℓ : 𝓞 E) ^ j * ((n' ^ 2 * 1 : ℕ) : 𝓞 E) = (N : 𝓞 E) * (n' : 𝓞 E) := by
        rw [hNe]; push_cast; ring
      rw [he]
      exact kill Xo t N hk _ (natCast_mem_level_of_dvd hMn)
    · obtain ⟨i, hi⟩ := hi
      refine ⟨i, ?_⟩
      rw [← act_nat Xo.univ.t t, Nat.cast_pow]
      exact hi _ (Ideal.pow_mem_pow (M_mem l) i)
  · have hℓN : ℓ ∣ N := by
      rcases hc with ⟨hA', hle⟩ | ⟨_, hℓM⟩
      · have hbM : H.bar α ∣ (l.M : 𝓞 E) := Ideal.mem_span_singleton.mp (hle (M_mem l))
        have haM : α ∣ (l.M : 𝓞 E) := by
          have h3 := map_dvd H.bar hbM
          rwa [bar_bar, map_natCast] at h3
        have hl : (ℓ : 𝓞 E) = α * H.bar α := by rw [hA, hA']
        have h4 : (ℓ : 𝓞 E) ∣ ((N ^ 2 : ℕ) : 𝓞 E) := by
          obtain ⟨q, rfl⟩ := hMN
          rw [hl]
          exact (mul_dvd_mul haM hbM).trans ⟨(q : 𝓞 E) ^ 2, by push_cast; ring⟩
        exact hp.dvd_of_dvd_pow (dvd_of_cast_dvd hp h4)
      · exact hℓM.trans hMN
    obtain ⟨N', hN'⟩ := hℓN
    have hN'0 : N' ≠ 0 := right_ne_zero_of_mul (hN' ▸ hN0)
    obtain ⟨e, n', hn', hN'e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN'0 ℓ hp.one_lt.ne'
    have hNe : N = ℓ ^ (e + 1) * n' := by rw [hN', hN'e]; ring
    have hcop : Nat.Coprime n' ℓ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
    have hMl : l.M ∣ ℓ * n' := dvd_lemma_3 hp h2 (by rw [← hNe]; exact hMN)
    have hmem : ((ℓ * n' : ℕ) : 𝓞 E) ∈ l.Mb := natCast_mem_level_of_dvd hMl
    rcases hc with ⟨hA', hle⟩ | ⟨hα, _⟩
    · have hl : (ℓ : 𝓞 E) = α * H.bar α := by rw [hA, hA']
      refine ⟨n', ℓ ^ (2 * e + 1), 2 * e + 2, (ℓ : 𝓞 E) ^ e * H.bar α, hcop, ?_, ?_, ?_,
        fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩
      · rw [hNe]; push_cast; rw [hl]; ring
      · rw [map_mul, map_pow, map_natCast, bar_bar]; push_cast; rw [hl]; ring
      · rw [hA']; ring
      · have htop : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
          rw [l.coprime]; exact Submodule.mem_top
        obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp htop
        have hy' : y ∈ Ideal.span {α} := by
          have h5 := Ideal.map_mono (f := (H.bar : 𝓞 E →+* 𝓞 E)) hle hy
          simpa [Ideal.map_span, bar_bar] using h5
        obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hy'
        have hb : (n' : 𝓞 E) * H.bar α ∈ l.Mb := by
          have h6 : (n' : 𝓞 E) * H.bar α = x * ((n' : 𝓞 E) * H.bar α) + z * ((ℓ * n' : ℕ) : 𝓞 E) := by
            push_cast
            linear_combination (-((n' : 𝓞 E) * H.bar α)) * hxy + (-((n' : 𝓞 E) * H.bar α)) * hz +
              (-(z * (n' : 𝓞 E))) * hl
          rw [h6]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ z hmem)
        rw [act_pow]
        have he : (ℓ : 𝓞 E) ^ e * H.bar α * ((n' ^ 2 * A : ℕ) : 𝓞 E) =
            (N : 𝓞 E) * ((n' : 𝓞 E) * H.bar α) := by
          rw [hNe, hA']; push_cast; ring
        rw [he]
        exact kill Xo t N hk _ hb
    · have hA2 : A = ℓ ^ 2 := by
        have h7 : ((A : ℕ) : 𝓞 E) = ((ℓ ^ 2 : ℕ) : 𝓞 E) := by
          rw [← hA, hα, map_natCast]; push_cast; ring
        exact Nat.cast_injective h7
      refine ⟨n', ℓ ^ (2 * e), 2 * e + 2, (ℓ : 𝓞 E) ^ e, hcop, ?_, ?_, ?_,
        fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩
      · rw [hNe, hα]; push_cast; ring
      · rw [map_pow, map_natCast]; push_cast; ring
      · rw [hA2]; ring
      · rw [act_pow, hA2]
        have he : (ℓ : 𝓞 E) ^ e * ((n' ^ 2 * ℓ ^ 2 : ℕ) : 𝓞 E) = (N : 𝓞 E) * ((ℓ * n' : ℕ) : 𝓞 E) := by
          rw [hNe]; push_cast; ring
        rw [he]
        exact kill Xo t N hk _ hmem

end GlobalTheory.TorsFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteBasisPowerSeriesSubstFiniteColength
section
open IsLocalRing MvPowerSeries

namespace GlobalTheory.FiniteColength

theorem finrank_quotient_eq_of_existsUnique {R : Type} [CommRing R] [Nontrivial R] {σ τ : Type}
    [Fintype τ] (ψ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R) {n : ℕ}
    (e : Fin n → MvPowerSeries σ R)
    (he : ∀ g, ∃! c : Fin n → MvPowerSeries τ R, g = ∑ i, ψ (c i) * e i) :
    Module.finrank R (MvPowerSeries σ R ⧸ Ideal.span (Set.range fun j => ψ (X j))) = n := by
  set I : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range fun j => ψ (X j)) with hI
  let L : (Fin n → R) →ₗ[R] (MvPowerSeries σ R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ Fintype.linearCombination R e
  have hL : ∀ a, L a = Ideal.Quotient.mk I (∑ i, algebraMap R _ (a i) * e i) := fun a => by
    simp [L, Fintype.linearCombination_apply, Algebra.smul_def]
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    rw [hL, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_range_iff_exists_fun] at ha
    obtain ⟨g, hg⟩ := ha
    choose c hc _ using fun j => he (g j)
    have h1 : ∑ i, algebraMap R _ (a i) * e i = ∑ i, ψ (∑ j, c j i * X j) * e i := by
      rw [← hg]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc j, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i, algebraMap R _ (a i) * e i = ∑ i, ψ (algebraMap R _ (a i)) * e i := by
      simp only [AlgHom.commutes]
    have h3 := (he _).unique h2 h1
    funext i
    have h4 := congrArg constantCoeff (congrFun h3 i)
    simpa [MvPowerSeries.algebraMap_apply] using h4
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc, -⟩ := he g
    refine ⟨fun i => constantCoeff (c i), ?_⟩
    rw [hL, eq_comm, Ideal.Quotient.eq, hc, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← sub_mul]
    exact Ideal.mul_mem_right _ _
      (algHom_sub_constantCoeff_mem ψ (K := I) (fun j => Ideal.subset_span ⟨j, rfl⟩) (c i))
  rw [← (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq]
  simp

theorem exists_basis_subst_finrank_quotient : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∃ (r : ℕ) (b : Fin r → MvPowerSeries σ V), Module.finrank V (MvPowerSeries σ V ⧸ Ideal.span (Set.range φ)) = r ∧ ∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i := by
  intro V _ _ _ _ _ σ _ φ h0 hM
  let ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries σ V :=
    substAlgHom (hasSubst_of_constantCoeff_zero h0)
  have hX : (fun j => ψ (X j)) = φ := funext fun j => substAlgHom_X _ j
  have h1 : ∀ j, constantCoeff (ψ (X j)) ∈ maximalIdeal V := fun j => by
    simp [congrFun hX j, h0]
  have h2 : FormalIsogeny.FiniteReduction fun j => ψ (X j) :=
    hX ▸ FormalIsogeny.finiteReduction_iff.2 hM
  obtain ⟨-, -, -, n, e, he⟩ :=
    FormalIsogeny.flat_injective_basis_of_finiteReduction ψ h1 h2 le_rfl
  refine ⟨n, e, ?_, fun f => ?_⟩
  · have := finrank_quotient_eq_of_existsUnique ψ e he
    rwa [hX] at this
  · have hψ : ∀ g, ψ g = MvPowerSeries.subst φ g := fun g => substAlgHom_apply _ g
    simpa only [hψ] using he f

end GlobalTheory.FiniteColength
end

