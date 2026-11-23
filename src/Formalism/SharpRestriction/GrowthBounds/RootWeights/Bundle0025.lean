module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0024
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.LaurentDegreesSubstitutionSubset

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorTraceFormula
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def smulRightLinear {K L W : Type} [Field K] [AddCommGroup L] [Module K L] [AddCommGroup W] [Module K W]
    (ξ : L →ₗ[K] K) : W →ₗ[K] (L →ₗ[K] W) where
  toFun := fun m => ξ.smulRight m
  map_add' := fun m m' => by ext x; simp
  map_smul' := fun c m => by
    ext x
    simp only [LinearMap.smulRight_apply, RingHom.id_apply, LinearMap.smul_apply]
    exact smul_comm _ _ _

theorem isotypic_projector_trace_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : IsotypicProjectorTraceFormula := by
  intro n K W _ _ _ _ _ E hE lam e he v0 hv0 hL P hP ι _ b m
  have hEL := restrictRepresentation_isRep E hE _ hL
  have hv0' := highest_vector_restrict E _ hL lam v0 (self_mem_cyclicSubmodule E v0) hv0
  have hcyc := cyclicSubmodule_restrict_eq_top E v0 hL
  have hPe := fun g => invariant_projection_equivariant D h2 (restrictRepresentation E _ hL) E hEL hE P hP g

  let Θ : W →ₗ[K] W := ∑ i, (LinearMap.applyₗ (b i)) ∘ₗ P ∘ₗ smulRightLinear (b.coord i)
  have hΘ : ∀ m, Θ m = ∑ i, P ((b.coord i).smulRight m) (b i) := by
    intro m
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
    rfl
  have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.eqLocus ((Fintype.card ι : K) • Θ) e := by
    refine iSup_le fun mu => ?_
    by_cases hmu : mu = lam
    · subst hmu
      refine Submodule.span_le.2 ?_
      rintro y ⟨u, hu, v, hv, rfl⟩
      have hy : u v ∈ isoSub E mu := Submodule.subset_span ⟨u, hu, v, hv, rfl⟩
      obtain ⟨φ, hφ, hφv⟩ := exists_equivariant_cyclic_to_hwv D h2 E hE mu v0 v hv0 hv hL
      obtain ⟨uL, _, huL⟩ := equivariant_lifts_monoid (restrictRepresentation E _ hL) E φ hφ hu
      have hm : u v = φ (uL ⟨v0, self_mem_cyclicSubmodule E v0⟩) := by rw [huL, hφv]
      obtain ⟨P0, hP0⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEL)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hL)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W φ) := by
        intro a c g
        ext x
        simp only [LinearMap.llcomp_apply, homRepresentation_apply, map_sub]
        rw [hφ]
      change ((Fintype.card ι : K) • Θ) (u v) = e (u v)
      rw [he.1 _ hy, LinearMap.smul_apply, hΘ, hm, Finset.smul_sum]
      set l := uL ⟨v0, self_mem_cyclicSubmodule E v0⟩ with hl
      have hterm : ∀ i, (Fintype.card ι : K) • P ((b.coord i).smulRight (φ l)) (b i) = (b.repr l i) • φ (b i) := by
        intro i
        have h3 : (b.coord i).smulRight (φ l) = LinearMap.llcomp K _ _ W φ ((b.coord i).smulRight l) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEL) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W φ) hT P0 P hP0 hP ((b.coord i).smulRight l)
        have h5 := schur_invariant_projection_trace D h2 _ hEL mu _ hv0' hcyc P0 hP0 ((b.coord i).smulRight l)
        rw [Module.finrank_eq_card_basis b, LinearMap.trace_smulRight] at h5
        rw [h3, ← h4, LinearMap.llcomp_apply, ← map_smul, ← LinearMap.smul_apply, h5]
        simp [Module.Basis.coord_apply]
      rw [Finset.sum_congr rfl fun i _ => hterm i]
      conv_rhs => rw [← b.sum_repr l]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
    · intro y hy
      have hWm : IsSubrepresentation E (isoSub E mu) := fun a c => isotypic_stable_under_gl_operator E mu a c
      have hEm := restrictRepresentation_isRep E hE _ hWm
      obtain ⟨P1, hP1⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEm)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hWm)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) := by
        intro a c g
        ext x
        simp
      have hzero : ∀ ξ : cyclicSubmodule E v0 →ₗ[K] K, P (ξ.smulRight y) = 0 := by
        intro ξ
        have h3 : ξ.smulRight y = LinearMap.llcomp K _ _ W (isoSub E mu).subtype
            (ξ.smulRight (⟨y, hy⟩ : isoSub E mu)) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEm) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) hT P1 P hP1 hP (ξ.smulRight (⟨y, hy⟩ : isoSub E mu))
        have hmem : ∀ x, P (ξ.smulRight y) x ∈ isoSub E mu := by
          intro x
          rw [h3, ← h4]
          simp
        have hv00 : P (ξ.smulRight y) ⟨v0, self_mem_cyclicSubmodule E v0⟩ = 0 := by
          by_contra h0
          have h6 := highest_vector_mem_isotypic E lam _ (equivariant_image_highest_vector _ E _ (hPe _) lam _ hv0' h0)
          exact h0 ((he.1 _ h6).symm.trans (he.2 mu hmu _ (hmem _)))
        ext x
        exact equivariant_kills_cyclic_of_zero _ E _ (hPe _) _ hv00 x (by rw [hcyc]; trivial)
      change ((Fintype.card ι : K) • Θ) y = e y
      rw [he.2 mu hmu y hy, LinearMap.smul_apply, hΘ]
      simp [hzero]
  have hm : m ∈ (⨆ mu, isoSub E mu) := by rw [isotypic_submodules_span_top D h2 n K W E hE]; trivial
  have := hle hm
  change ((Fintype.card ι : K) • Θ) m = e m at this
  rw [LinearMap.smul_apply, hΘ] at this
  exact this

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.RaiseLowerPowCommutatorOnWeight
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem descPochhammer_succ_eval_right (j : ℕ) (x : ℤ) :
    (descPochhammer ℤ (j + 1)).eval x = (descPochhammer ℤ j).eval x * (x - j) := by
  rw [descPochhammer_succ_right]
  simp

theorem descPochhammer_succ_eval_add_one (j : ℕ) (x : ℤ) :
    (descPochhammer ℤ (j + 1)).eval (x + 1) = (x + 1) * (descPochhammer ℤ j).eval x := by
  rw [descPochhammer_succ_left]
  simp

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem raise_lower_commutator_on_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} {mu : Fin n → ℤ} {z : V}
    (hz : z ∈ weightSp E mu) : E a b (E b a z) = E b a (E a b z) + (((mu a - mu b : ℤ)) : KK O) • z := by
  have hz' : z ∈ ⨅ c, LinearMap.ker (E c c - ((mu c : ℤ) : KK O) • (1 : Module.End (KK O) V)) := hz
  have hw : ∀ c, E c c z = ((mu c : ℤ) : KK O) • z := by
    intro c
    have h := (Submodule.mem_iInf _).mp hz' c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    exact h
  have hc := congrArg (fun f : Module.End (KK O) V => f z) (hE.1 a b b a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, eq_self_iff_true] at hc
  rw [hw a, hw b] at hc
  rw [← sub_eq_iff_eq_add', hc, Int.cast_sub, sub_smul]

theorem raise_lower_pow_commutator_on_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) {mu : Fin n → ℤ} {z : V}
    (hz : z ∈ weightSp E mu) (r : ℕ) :
    E a b (((E b a) ^ r) z) = ((E b a) ^ r) (E a b z) +
      ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • ((E b a) ^ (r - 1)) z := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e1 : ∀ s x, E b a (((E b a) ^ s) x) = ((E b a) ^ (s + 1)) x := by
      intro s x
      rw [pow_succ', Module.End.mul_apply]
    have hy := integral_operator_pow_shifts_weight hE hz b a r
    have h0 := raise_lower_commutator_on_weight (a := a) (b := b) hE hy
    have hA : (mu + (r : ℤ) • rootW b a) a = mu a - r := by
      simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
    have hB : (mu + (r : ℤ) • rootW b a) b = mu b + r := by
      simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
    rw [hA, hB] at h0
    have e2 : ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • E b a (((E b a) ^ (r - 1)) z) =
        ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • ((E b a) ^ r) z := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h
        simp
      · rw [e1, Nat.sub_add_cancel h]
    rw [← e1, h0, ih, map_add (f := _), map_smul, e1, e2, Nat.add_sub_cancel, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

theorem raise_pow_lower_pow_expansion {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) {nu : Fin n → ℤ} {y : V}
    (hy : y ∈ weightSp E nu) (k l : ℕ) :
    ((E a b) ^ k) (((E b a) ^ l) y) = ∑ j ∈ range (k + 1),
      ((((k.choose j * l.descFactorial j : ℕ)) : KK O) *
        (((descPochhammer ℤ j).eval (nu a - nu b + k - l) : ℤ) : KK O)) •
        ((E b a) ^ (l - j)) (((E a b) ^ (k - j)) y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have step : ∀ j ∈ range (k + 1),
        E a b (((E b a) ^ (l - j)) (((E a b) ^ (k - j)) y)) =
          ((E b a) ^ (l - j)) (((E a b) ^ (k + 1 - j)) y) +
          (((l - j : ℕ) : KK O) * (((((nu + ((k - j : ℕ) : ℤ) • rootW a b) a -
              (nu + ((k - j : ℕ) : ℤ) • rootW a b) b : ℤ)) : KK O) - ((l - j : ℕ) : KK O) + 1)) •
            ((E b a) ^ (l - (j + 1))) (((E a b) ^ (k + 1 - (j + 1))) y) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hw := integral_operator_pow_shifts_weight hE hy a b (k - j)
      rw [raise_lower_pow_commutator_on_weight hE hab hw (l - j)]
      congr 1
      · rw [← Module.End.mul_apply (E a b), ← pow_succ', show k - j + 1 = k + 1 - j by omega]
      · rw [show l - j - 1 = l - (j + 1) by omega, show k + 1 - (j + 1) = k - j by omega]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pow_succ', Module.End.mul_apply, ih, map_sum]
    simp only [map_smul]
    refine (Finset.sum_congr rfl (fun j hj => ?_)).trans
      (weighted_sum_shift_recombine (fun j => ((k.choose j * l.descFactorial j : ℕ) : KK O) *
          (((descPochhammer ℤ j).eval (nu a - nu b + k - l) : ℤ) : KK O))
        (fun j => (((k + 1).choose j * l.descFactorial j : ℕ) : KK O) *
          (((descPochhammer ℤ j).eval (nu a - nu b + ((k + 1 : ℕ) : ℤ) - l) : ℤ) : KK O))
        (fun j => ((l - j : ℕ) : KK O) * (((((nu + ((k - j : ℕ) : ℤ) • rootW a b) a -
              (nu + ((k - j : ℕ) : ℤ) • rootW a b) b : ℤ)) : KK O) - ((l - j : ℕ) : KK O) + 1))
        (fun j => ((E b a) ^ (l - j)) (((E a b) ^ (k + 1 - j)) y)) k ?_ ?_ ?_)
    · beta_reduce
      rw [step j hj]
    · simp
    · intro j hj
      beta_reduce
      have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
      have hA : (nu + ((k - j : ℕ) : ℤ) • rootW a b) a = nu a + ((k - j : ℕ) : ℤ) := by
        simp [rootW, Pi.single_apply, hab, hab.symm]
      have hB : (nu + ((k - j : ℕ) : ℤ) • rootW a b) b = nu b - ((k - j : ℕ) : ℤ) := by
        simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
      rw [hA, hB]
      have hx : nu a - nu b + ((k + 1 : ℕ) : ℤ) - (l : ℤ) = (nu a - nu b + (k : ℤ) - (l : ℤ)) + 1 := by
        push_cast
        ring
      rw [hx, descPochhammer_succ_eval_add_one, descPochhammer_succ_eval_right, Nat.choose_succ_succ, Nat.descFactorial_succ]
      have hch : (k.choose (j + 1) : KK O) * ((j : KK O) + 1) = (k.choose j : KK O) * ((k : KK O) - j) := by
        have := congrArg (Nat.cast : ℕ → KK O) (Nat.choose_succ_right_eq k j)
        push_cast [hjk] at this
        exact this
      generalize (descPochhammer ℤ j).eval (nu a - nu b + (k : ℤ) - (l : ℤ)) = P
      by_cases hjl : j ≤ l
      · push_cast [hjk, hjl]
        linear_combination (((l : KK O) - j) * (l.descFactorial j : KK O) * (P : KK O)) * hch
      · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        have h0' : l - j = 0 := by omega
        simp [h0, h0']
    · simp [Nat.choose_succ_self]

theorem raise_lower_dividedPower_binomial [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b)
    {nu : Fin n → ℤ} {y : V} (hy : y ∈ weightSp E nu) (k l : ℕ) :
    divPowE E a b k (divPowE E b a l y) = ∑ j ∈ range (k + 1),
      if j ≤ l then ((Ring.choose (nu a - nu b + k - l) j : ℤ) : KK O) •
        divPowE E b a (l - j) (divPowE E a b (k - j) y) else 0 := by
  simp only [divPowE, LinearMap.smul_apply, map_smul]
  rw [raise_pow_lower_pow_expansion hE hab hy k l, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  split_ifs with hjl
  · simp only [smul_smul]
    congr 1
    have hP : (descPochhammer ℤ j).eval (nu a - nu b + (k : ℤ) - (l : ℤ)) =
        (j.factorial : ℤ) * Ring.choose (nu a - nu b + (k : ℤ) - (l : ℤ)) j := by
      first
      | rw [Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
      | (rw [Ring.choose]; simp)
    rw [hP]
    have h1 : ((k.factorial : ℕ) : KK O) = (k.choose j : KK O) * j.factorial * (k - j).factorial := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
    have h2 : ((l.factorial : ℕ) : KK O) = ((l - j).factorial : KK O) * l.descFactorial j := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hjl).symm
    have h3 : (k.choose j : KK O) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
    have h4 : (l.descFactorial j : KK O) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
    have h5 : (j.factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h6 : ((k - j).factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h7 : ((l - j).factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [h1, h2]
    push_cast
    field_simp
  · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightEntryRestrictionMem
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def binomialFunctions : AddSubgroup (ℤ → ℤ) := AddSubgroup.closure (Set.range fun k : ℕ => fun w : ℤ => Ring.choose w k)

theorem binomialFunctions_shift_mem (s : ℤ) (k : ℕ) : (fun w : ℤ => Ring.choose (w + s) k) ∈ binomialFunctions := by
  have h : (fun w : ℤ => Ring.choose (w + s) k) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, Ring.choose s ij.2 • (fun w : ℤ => Ring.choose w ij.1) := by
    funext w
    rw [Ring.add_choose_eq (h := Commute.all w s), Finset.sum_apply]
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp [mul_comm]
  rw [h]
  exact AddSubgroup.sum_mem _ fun ij _ =>
    AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self ij.1)) _

private theorem ring_choose_eq_zero_of_nonneg_of_lt (x : ℤ) (k : ℕ) (h0 : 0 ≤ x) (hk : x < k) : Ring.choose x k = 0 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
  simp

private theorem ring_choose_self_of_eq (x : ℤ) (k : ℕ) (h : x = k) : Ring.choose x k = 1 := by
  subst h
  rw [Ring.choose_natCast, Nat.choose_self]
  simp

private theorem ring_choose_neg_one (k : ℕ) : Ring.choose (-1 : ℤ) k = (-1) ^ k := by
  induction k with
  | zero => simp [Ring.choose_zero_right]
  | succ k ih =>
    have h := Ring.choose_succ_succ (-1 : ℤ) k
    rw [neg_add_cancel, Ring.choose_zero_succ, ih] at h
    rw [pow_succ]
    linarith

theorem binomialFunctions_window_indicator (w0 : ℤ) (B : ℕ) : ∃ f ∈ binomialFunctions, ∀ w : ℤ, -(B : ℤ) ≤ w → w ≤ B →
    f w = if w = w0 then 1 else 0 := by
  induction B with
  | zero =>
    refine ⟨(if (0 : ℤ) = w0 then 1 else 0) • (fun w : ℤ => Ring.choose w 0),
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self 0)) _, ?_⟩
    intro w h1 h2
    have hw : w = 0 := by omega
    subst hw
    simp [Ring.choose_zero_right]
  | succ B ih =>
    obtain ⟨f, hf, hfw⟩ := ih
    have hg1 : (fun w : ℤ => Ring.choose (w + B) (2 * B + 1)) ∈ binomialFunctions := binomialFunctions_shift_mem _ _
    have hg2 : (fun w : ℤ => Ring.choose (w + ((B : ℤ) + 1)) (2 * B + 2)) ∈ binomialFunctions := binomialFunctions_shift_mem _ _
    set g1 : ℤ → ℤ := fun w : ℤ => Ring.choose (w + B) (2 * B + 1) with hg1d
    set g2 : ℤ → ℤ := fun w : ℤ => Ring.choose (w + ((B : ℤ) + 1)) (2 * B + 2) with hg2d
    set c1 : ℤ := (if (B : ℤ) + 1 = w0 then 1 else 0) - f ((B : ℤ) + 1) with hc1
    set c2 : ℤ := (if -((B : ℤ) + 1) = w0 then 1 else 0) - f (-((B : ℤ) + 1)) with hc2
    refine ⟨f + c1 • g2 + c2 • (g2 - g1),
      add_mem (add_mem hf (AddSubgroup.zsmul_mem _ hg2 _)) (AddSubgroup.zsmul_mem _ (sub_mem hg2 hg1) _), ?_⟩
    intro w h1 h2
    push_cast at h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases (by omega : (-(B : ℤ) ≤ w ∧ w ≤ B) ∨ w = B + 1 ∨ w = -((B : ℤ) + 1)) with h | h | h
    · have e1 : g1 w = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      have e2 : g2 w = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      rw [e1, e2, hfw w h.1 h.2]
      ring
    · subst h
      have e1 : g1 ((B : ℤ) + 1) = 1 := ring_choose_self_of_eq _ _ (by push_cast; ring)
      have e2 : g2 ((B : ℤ) + 1) = 1 := ring_choose_self_of_eq _ _ (by push_cast; ring)
      rw [e1, e2, hc1]
      ring
    · subst h
      have e1 : g1 (-((B : ℤ) + 1)) = -1 := by
        simp only [hg1d]
        rw [show -((B : ℤ) + 1) + B = -1 by ring, ring_choose_neg_one, pow_succ, pow_mul]
        simp
      have e2 : g2 (-((B : ℤ) + 1)) = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      rw [e1, e2, hc2]
      ring

section graded

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)

def diagonalMultiplier (a : Fin n) (f : ℤ → ℤ) (x : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ x.support, monomial m (x.coeff m * ((f (wtS LL S m a) : ℤ) : R))


open Classical in
def monomialRestriction (q : (ι × Fin n →₀ ℕ) → Prop) (x : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ x.support.filter q, monomial m (x.coeff m)

theorem coeff_diagonalMultiplier (a : Fin n) (f : ℤ → ℤ) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (diagonalMultiplier LL S a f x) m = x.coeff m * ((f (wtS LL S m a) : ℤ) : R) := by
  classical
  simp only [diagonalMultiplier, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul]

open Classical in
theorem coeff_monomialRestriction (q : (ι × Fin n →₀ ℕ) → Prop) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (monomialRestriction q x) m = if q m then x.coeff m else 0 := by
  simp only [monomialRestriction, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases hq : q m <;> by_cases hm : x.coeff m = 0 <;> simp [hq, hm]

theorem diagonalMultiplier_mem (W : Submodule R (MvPolynomial (ι × Fin n) R))
    (hW : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) (a : Fin n) (f : ℤ → ℤ) (hf : f ∈ binomialFunctions) :
    ∀ x ∈ W, diagonalMultiplier LL S a f x ∈ W := by
  have hb : ∀ (k : ℕ) (x : MvPolynomial (ι × Fin n) R),
      binomPol R LL S a k x = diagonalMultiplier LL S a (fun w => Ring.choose w k) x := by
    intro k x
    conv_lhs => rw [x.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [binomialOperator_monomial]
    rfl
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    intro x hx
    rw [← hb]
    exact hW a k x hx
  | zero =>
    intro x _
    have e : diagonalMultiplier LL S a 0 x = 0 := by
      ext m
      simp [coeff_diagonalMultiplier]
    rw [e]
    exact W.zero_mem
  | add f g _ _ hf hg =>
    intro x hx
    have e : diagonalMultiplier LL S a (f + g) x = diagonalMultiplier LL S a f x + diagonalMultiplier LL S a g x := by
      ext m
      simp [coeff_diagonalMultiplier, mul_add]
    rw [e]
    exact W.add_mem (hf x hx) (hg x hx)
  | neg f _ hf =>
    intro x hx
    have e : diagonalMultiplier LL S a (-f) x = -diagonalMultiplier LL S a f x := by
      ext m
      simp [coeff_diagonalMultiplier]
    rw [e]
    exact W.neg_mem (hf x hx)

theorem weightEntry_restriction_mem (W : Submodule R (MvPolynomial (ι × Fin n) R))
    (hW : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) (a : Fin n) (w0 : ℤ) :
    ∀ x ∈ W, monomialRestriction (fun m => wtS LL S m a = w0) x ∈ W := by
  intro x hx
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ m ∈ x.support, -(B : ℤ) ≤ wtS LL S m a ∧ wtS LL S m a ≤ B := by
    refine ⟨∑ m ∈ x.support, (wtS LL S m a).natAbs, fun m hm => ?_⟩
    have h := Finset.single_le_sum (f := fun m => (wtS LL S m a).natAbs) (fun _ _ => Nat.zero_le _) hm
    have h2 : |wtS LL S m a| ≤ ((∑ m ∈ x.support, (wtS LL S m a).natAbs : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h
    exact ⟨by linarith [neg_abs_le (wtS LL S m a)], by linarith [le_abs_self (wtS LL S m a)]⟩
  obtain ⟨f, hf, hfw⟩ := binomialFunctions_window_indicator w0 B
  have e : monomialRestriction (fun m => wtS LL S m a = w0) x = diagonalMultiplier LL S a f x := by
    ext m
    rw [coeff_monomialRestriction, coeff_diagonalMultiplier]
    by_cases hm : m ∈ x.support
    · rw [hfw _ (hB m hm).1 (hB m hm).2]
      split_ifs <;> simp
    · rw [MvPolynomial.mem_support_iff, not_not] at hm
      simp [hm]
  rw [e]
  exact diagonalMultiplier_mem LL S W hW a f hf x hx

end graded

theorem binomial_stable_contains_components : BinomialStableContainsComponents := by
  intro R _ ι _ LL n S W hW x hx nu
  classical
  have key : ∀ s : Finset (Fin n), monomialRestriction (fun m => ∀ a ∈ s, wtS LL S m a = nu a) x ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : monomialRestriction (fun m => ∀ a ∈ (∅ : Finset (Fin n)), wtS LL S m a = nu a) x = x := by
        ext m
        rw [coeff_monomialRestriction]
        simp
      rw [e]
      exact hx
    | @insert a s _ ih =>
      have e : monomialRestriction (fun m => ∀ b ∈ insert a s, wtS LL S m b = nu b) x =
          monomialRestriction (fun m => wtS LL S m a = nu a) (monomialRestriction (fun m => ∀ b ∈ s, wtS LL S m b = nu b) x) := by
        ext m
        rw [coeff_monomialRestriction, coeff_monomialRestriction, coeff_monomialRestriction]
        by_cases h1 : wtS LL S m a = nu a <;> by_cases h2 : ∀ b ∈ s, wtS LL S m b = nu b <;>
          simp [h1, h2, Finset.forall_mem_insert]
      rw [e]
      exact weightEntry_restriction_mem LL S W hW a (nu a) _ ih
  have e : weightComponent LL S nu x = monomialRestriction (fun m => ∀ a ∈ Finset.univ, wtS LL S m a = nu a) x := by
    ext m
    rw [coeff_weightComponent, coeff_monomialRestriction]
    by_cases h : wtS LL S m = nu
    · have h' : ∀ a ∈ (Finset.univ : Finset (Fin n)), wtS LL S m a = nu a := fun a _ => by rw [h]
      rw [if_pos h, if_pos h']
    · have h' : ¬ ∀ a ∈ (Finset.univ : Finset (Fin n)), wtS LL S m a = nu a :=
        fun h'' => h (funext fun a => h'' a (Finset.mem_univ a))
      rw [if_neg h, if_neg h']
  rw [e]
  exact key _

end Formalism.MainNotions.G.GLWeightTheory
end
end

