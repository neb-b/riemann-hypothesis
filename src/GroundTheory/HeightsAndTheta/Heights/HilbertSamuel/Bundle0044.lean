module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageGenDeg

open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff diffStep eventualValue intNum)
open fwdDiff

theorem mixedDiff_line {K : Type*} (b m₀ : K → ℤ) (h : (K → ℤ) → ℤ) (D : ℕ) (t : ℤ) :
    mixedDiff (fun _ : Fin D => b) h (m₀ + t • b) = ((fwdDiff 1)^[D] fun s : ℤ => h (m₀ + s • b)) (t - D) := by
  induction D generalizing t with
  | zero => simp [mixedDiff]
  | succ D ih =>
    have hs : mixedDiff (fun _ : Fin (D + 1) => b) h = diffStep b (mixedDiff (fun _ : Fin D => b) h) := by
      simp [mixedDiff, List.ofFn_succ]
    have h1 : m₀ + t • b - b = m₀ + (t - 1) • b := by rw [sub_smul, one_smul, add_sub_assoc]
    have e1 : t - ((D + 1 : ℕ) : ℤ) + 1 = t - D := by push_cast; ring
    have e2 : t - ((D + 1 : ℕ) : ℤ) = t - 1 - D := by push_cast; ring
    rw [hs, diffStep, h1, ih, ih, Function.iterate_succ_apply', fwdDiff, e1, e2]

theorem fwdDiff_iter_eq_poly (φ : ℤ → ℤ) (q : Polynomial ℚ) (D : ℕ) (s : ℤ)
    (h : ∀ j ≤ D, (φ (s + j) : ℚ) = q.eval ((s : ℚ) + j)) :
    (((fwdDiff 1)^[D] φ) s : ℚ) = ((fwdDiff 1)^[D] q.eval) (s : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  rw [h j hj']

theorem fwdDiff_iter_poly (q : Polynomial ℚ) {D : ℕ} (hq : q.natDegree ≤ D) (x : ℚ) :
    ((fwdDiff 1)^[D] q.eval) x = q.coeff D * D.factorial := by
  rcases hq.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [q.fwdDiff_iter_degree_eq_factorial]
    rw [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    rfl

def lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun k => if k = k₀ then Polynomial.X else Polynomial.C (m k)) p

theorem eval_lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) (t : ℚ) :
    (lineRestr p k₀ m).eval t = MvPolynomial.eval (fun k => if k = k₀ then t else m k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [lineRestr]
  | add p q hp hq => simp only [lineRestr, map_add (f := _), Polynomial.eval_add] at *; rw [hp, hq]
  | mul_X p k hp =>
    simp only [lineRestr, map_mul, Polynomial.eval_mul] at *
    rw [hp]
    by_cases hk : k = k₀ <;> simp [hk]

theorem natDegree_lineRestr_le {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) :
    (lineRestr p k₀ m).natDegree ≤ p.totalDegree := by
  rw [lineRestr]
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  refine Finset.sum_le_sum fun k _ => (Polynomial.natDegree_pow_le).trans ?_
  have : (if k = k₀ then (Polynomial.X : Polynomial ℚ) else Polynomial.C (m k)).natDegree ≤ 1 := by
    split_ifs <;> simp
  simpa using Nat.mul_le_mul_left (s k) this

theorem eventualValue_eq {K : Type*} (f : (K → ℤ) → ℤ) (e : ℚ) (h : ∀ᶠ m in Filter.atTop, (f m : ℚ) = e) :
    (eventualValue f : ℚ) = e := by
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := by
    obtain ⟨m, hm⟩ := h.exists
    exact ⟨f m, h.mono fun m' hm' => by exact_mod_cast hm'.trans hm.symm⟩
  unfold eventualValue
  rw [dite_eq_left hex]
  obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
  rw [← hm1]
  exact hm2

end BlockImageGenDeg


open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff eventualValue) in
open BlockImageGenDeg in
theorem BlockImageGenDeg.proof (hMHP : MultigradedHilbertPolynomial.Statement.{0})
    (hGFV : GenericFibreVar.Statement) (hHEP : GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.Statement.{0})
    (hHom : GenFibreHomog.Statement) (hImg : BlockImageHilb.Statement) (hBir : BlockBirationalHilbert.Statement)
    (hSand : PolySandwich.Statement) : BlockImageGenDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hA hB hI
  set PY := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPY
  set PX := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPX

  obtain ⟨⟨hprime, -, hrel⟩, hdim⟩ := hGFV K ι Ω y D hA
  obtain ⟨pY, a₀, hdeg, hpY⟩ := hMHP ℚ K ι PY D ⟨hprime, hHom K ι Ω y, hrel⟩ hdim

  have hXhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal (ι := GlobalTheory κ) PX := by
    rw [hPX, coordIdeal_eq_mCoordIdeal]; exact hHom Unit (GlobalTheory κ) Ω x
  obtain ⟨pX, hpX⟩ := hHEP ℚ Unit (GlobalTheory κ) PX hXhom
  obtain ⟨aX, haX⟩ := Filter.eventually_atTop.mp hpX
  set p₁ := lineRestr pX () 0 with hp₁
  have hX1 : ∀ n : ℕ, (aX ()).toNat ≤ n → (hilbFn PX (fun _ => (n : ℤ)) : ℚ) = p₁.eval (n : ℚ) := by
    intro n hn
    rw [haX (fun _ => (n : ℤ)) (fun u => by cases u; show aX () ≤ (n : ℤ); omega), hp₁, eval_lineRestr]
    simp

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]

  have hY1 : ∀ (m : K → ℕ) (s : ℕ), (∀ k, k ≠ k₀ → a₀ ≤ m k) → a₀ ≤ s →
      (hilbFn PY (fun k => if k = k₀ then (s : ℤ) else m k) : ℚ) =
        (lineRestr pY k₀ fun k => (m k : ℚ)).eval (s : ℚ) := by
    intro m s hm hs
    have := hpY (fun k => if k = k₀ then s else m k) fun k => by
      by_cases hk : k = k₀ <;> simp [hk, hs, hm k]
    rw [eval_lineRestr]
    convert this using 3 <;> (funext k; by_cases hk : k = k₀ <;> simp [hk])

  have hsand : ∀ m : K → ℕ, (∀ k, k ≠ k₀ → a₀ ≤ m k) →
      p₁.natDegree ≤ D ∧ p₁.coeff D = (lineRestr pY k₀ fun k => (m k : ℚ)).coeff D := by
    intro m hm
    obtain ⟨c, hc⟩ := hBir K ι Ω y k₀ hnz hB m
    refine hSand D c _ _ ((natDegree_lineRestr_le _ _ _).trans hdeg) ?_
    filter_upwards [Filter.eventually_ge_atTop (max a₀ (aX ()).toNat)] with n hn
    have h1 := hX1 n (le_of_max_le_right hn)
    have h2 := hX1 (n + c) ((le_of_max_le_right hn).trans (Nat.le_add_right _ _))
    rw [hImg K ι Ω κ y k₀ M N x hI] at h1 h2
    rw [← hY1 m n hm (le_of_max_le_left hn)]
    push_cast at h2
    rw [← h1, ← h2]
    exact ⟨by exact_mod_cast (hc n).1, by exact_mod_cast (hc n).2⟩
  have hdegX : p₁.natDegree ≤ D := (hsand (fun _ => a₀) fun _ _ => le_rfl).1

  have key : (eventualValue (mixedDiff (fun _ : Fin D => (1 : Unit → ℤ)) (hilbFn PX)) : ℚ) =
      eventualValue (mixedDiff (fun _ : Fin D => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) (hilbFn PY)) := by
    rw [eventualValue_eq (e := p₁.coeff D * D.factorial), eventualValue_eq (e := p₁.coeff D * D.factorial)]
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((a₀ : ℤ) + D), fun m hm => ?_⟩
      have hm' : ∀ k, (a₀ : ℤ) + D ≤ m k := hm
      have hline : m = (fun k => if k = k₀ then 0 else m k) + m k₀ • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ := by
        funext k; by_cases hk : k = k₀ <;> simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ (lineRestr pY k₀ fun k => ((m k).toNat : ℚ)) D,
        fwdDiff_iter_poly _ ((natDegree_lineRestr_le _ _ _).trans hdeg),
        (hsand (fun k => (m k).toNat) fun k _ => by have := hm' k; omega).2]
      intro j hj
      have hs : 0 ≤ m k₀ - D + j := by have := hm' k₀; omega
      have hkey : (fun k => if k = k₀ then 0 else m k) + (m k₀ - D + j) • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ =
          fun k => if k = k₀ then (((m k₀ - D + j).toNat : ℕ) : ℤ) else (((m k).toNat : ℕ) : ℤ) := by
        funext k
        by_cases hk : k = k₀
        · simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, Int.toNat_of_nonneg hs]
        · have := hm' k
          simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
          omega
      rw [hkey, hY1 (fun k => (m k).toNat) _ (fun k _ => by have := hm' k; omega) (by have := hm' k₀; omega)]
      congr 1
      rw [show (((m k₀ - D + j).toNat : ℕ) : ℚ) = ((m k₀ - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((aX ()).toNat + D : ℤ), fun m hm => ?_⟩
      have hm' : ((aX ()).toNat + D : ℤ) ≤ m () := hm ()
      have hline : m = 0 + m () • (1 : Unit → ℤ) := by funext u; cases u; simp
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ p₁ D, fwdDiff_iter_poly _ hdegX]
      intro j hj
      have hs : 0 ≤ m () - D + j := by omega
      have hkey : (0 : Unit → ℤ) + (m () - D + j) • (1 : Unit → ℤ) = fun _ => (((m () - D + j).toNat : ℕ) : ℤ) := by
        funext u; simp [Int.toNat_of_nonneg hs]
      rw [hkey, hX1 _ (by omega)]
      congr 1
      rw [show (((m () - D + j).toNat : ℕ) : ℚ) = ((m () - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring

  apply Int.cast_injective (α := ℚ)
  unfold genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum
  convert key using 6 <;> rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageHilb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageHilb

section Subst

variable {σ τ M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']

theorem isWeightedHomogeneous_aeval {w : σ → M} {w' : τ → M'} (ψ : M →+ M') (φ : σ → MvPolynomial τ ℚ)
    (hφ : ∀ i, IsWeightedHomogeneous w' (φ i) (ψ (w i))) {f : MvPolynomial σ ℚ} {m : M}
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w' (aeval φ f) (ψ m) := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero ℚ w' (ψ m)
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial d r hr =>
    rw [aeval_monomial, algebraMap_eq, ← hr, Finsupp.weight_apply, map_finsuppSum]
    refine IsWeightedHomogeneous.C_mul ?_ r
    simp only [map_nsmul]
    exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (hφ i).pow (d i)

end Subst

section Cone

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]

def mConeMapQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1

def valSpan {σ M : Type*} [AddCommMonoid M] (w : σ → M) (y : σ → Ω) (m : M) : Submodule ℚ Ω :=
  (weightedHomogeneousSubmodule ℚ w m).map (aeval y : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toLinearMap


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem map_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = RingHom.ker (mConeMapQ y) := by
  have hring : ((mConeMapQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMapQ, mConeMap]
    · intro i
      simp [mConeMapQ, mConeMap]
  have hker : mCoordIdeal y = (RingHom.ker (mConeMapQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [mCoordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))
    (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (mConeMapQ y))
  rw [e] at h
  rw [hker]
  exact h

theorem weight_blockWeight_apply (μ : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) μ k = ∑ i : ι k, μ ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem mConeMapQ_eq (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    mConeMapQ y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hf (mem_support_iff.mp hμ)]
  simp only [mConeMapQ, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem hilbFn_eq_finrank (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => (a k : ℤ)) =
      Module.finrank ℚ (valSpan (NumbersDVR.blockWeight ι) y a) := by
  rw [map_mCoordIdeal]
  set W := weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a
  set P := RingHom.ker (mConeMapQ y)
  let φ₁ : W →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P := (Ideal.Quotient.mkₐ ℚ P).toLinearMap ∘ₗ W.subtype
  let φ₂ : W →ₗ[ℚ] Ω := (aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap ∘ₗ W.subtype
  have hk : LinearMap.ker φ₁ = LinearMap.ker φ₂ := by
    ext ⟨f, hf⟩
    simp only [LinearMap.mem_ker, φ₁, φ₂, LinearMap.comp_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, P, RingHom.mem_ker]
    rw [mConeMapQ_eq y hf, mul_eq_zero, C_eq_zero,
      or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))]
  have h₁ : LinearMap.range φ₁ = NumbersDVR.gradedPiece P a := by
    simp only [φ₁, LinearMap.range_comp, Submodule.range_subtype, NumbersDVR.gradedPiece, W]
  have h₂ : LinearMap.range φ₂ = valSpan (NumbersDVR.blockWeight ι) y a := by
    simp only [φ₂, LinearMap.range_comp, Submodule.range_subtype, valSpan, W]
  have h := LinearEquiv.finrank_eq
    ((φ₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans φ₂.quotKerEquivRange)
  rw [h₁, h₂] at h
  unfold NumbersDVR.hilbFn
  rw [if_pos (fun k => Nat.cast_nonneg _)]
  show ((Module.finrank ℚ (NumbersDVR.gradedPiece P a) : ℕ) : ℤ) = _
  rw [h]

end Cone

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω] {κ : Type} [Fintype κ]

def fwdSubst (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (j : Ix κ) : MvPolynomial (Σ k, ι k) ℚ :=
  ∑ i, MvPolynomial.C ((M j i : ℤ) : ℚ) * MvPolynomial.X ⟨k₀, i⟩

def backSubst (k₀ : K) (N : Matrix (ι k₀) (Ix κ) ℤ) : (Σ k, ι k) → MvPolynomial (Ix κ) ℚ
  | ⟨k, i⟩ => if h : k = k₀ then ∑ j, MvPolynomial.C ((N (h ▸ i) j : ℤ) : ℚ) * MvPolynomial.X j else 0

theorem valSpan_eq {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ} {N : Matrix (ι k₀) (Ix κ) ℤ}
    {x : Ix κ → Ω} (hxy : IsBlockImage y k₀ M N x) (n : ℕ) :
    valSpan (NumbersDVR.blockWeight (GlobalTheory κ)) x (fun _ => n) = valSpan (NumbersDVR.blockWeight ι) y (Pi.single k₀ n) := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    let ψ : (Unit → ℕ) →+ (K → ℕ) :=
      { toFun := fun a => Pi.single k₀ (a ()), map_zero' := by simp, map_add' := fun a b => by simp [Pi.single_add] }
    have hφ : ∀ j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (fwdSubst k₀ M j)
        (ψ (NumbersDVR.blockWeight (GlobalTheory κ) j)) := fun j => by
      have e : ψ (NumbersDVR.blockWeight (GlobalTheory κ) j) = Pi.single k₀ 1 := by
        simp [ψ, NumbersDVR.blockWeight]
      rw [e]
      exact IsWeightedHomogeneous.sum _ _ _ fun i _ =>
        (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight ι) ⟨k₀, i⟩).C_mul _
    refine ⟨aeval (fwdSubst k₀ M) f, ?_, ?_⟩
    · simpa [ψ] using isWeightedHomogeneous_aeval ψ _ hφ hf
    · simp only [AlgHom.toLinearMap_apply]
      have e : (fun j => aeval y (fwdSubst k₀ M j)) = x := by
        funext j
        simp [fwdSubst, hxy.1 j]
      rw [← AlgHom.comp_apply, comp_aeval, e]
  · rintro _ ⟨g, hg, rfl⟩
    let ψ : (K → ℕ) →+ (Unit → ℕ) :=
      { toFun := fun a _ => ∑ k, a k, map_zero' := by ext; simp,
        map_add' := fun a b => by ext; simp [Finset.sum_add_distrib] }
    have hφ : ∀ p, IsWeightedHomogeneous (NumbersDVR.blockWeight (GlobalTheory κ)) (backSubst k₀ N p)
        (ψ (NumbersDVR.blockWeight ι p)) := by
      rintro ⟨k, i⟩
      have e : ψ (NumbersDVR.blockWeight ι ⟨k, i⟩) = fun _ => 1 := by
        funext u
        simp [ψ, NumbersDVR.blockWeight]
      rw [e]
      by_cases h : k = k₀
      · subst h
        simp only [backSubst, dite_true]
        refine IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_
        convert (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight (GlobalTheory κ)) j).C_mul _ using 1
        funext u
        simp [NumbersDVR.blockWeight]
      · simp only [backSubst, h, dite_false]
        exact isWeightedHomogeneous_zero ℚ _ _
    refine ⟨aeval (backSubst k₀ N) g, ?_, ?_⟩
    · simpa [ψ] using isWeightedHomogeneous_aeval ψ _ hφ hg
    · simp only [AlgHom.toLinearMap_apply]
      rw [← AlgHom.comp_apply, comp_aeval]
      refine hom_congr_vars (Subsingleton.elim _ _) (fun p hp _ => ?_) rfl
      obtain ⟨k, i⟩ := p
      obtain ⟨μ, hμ, hp⟩ := (mem_vars_iff_mem_support _).mp hp
      by_cases h : k = k₀
      · subst h
        simp [backSubst, hxy.2 i]
      · exfalso
        have hw := congrFun (hg (mem_support_iff.mp hμ)) k
        rw [weight_blockWeight_apply, Pi.single_eq_of_ne h] at hw
        have := Finset.single_le_sum (fun i' _ => Nat.zero_le (μ ⟨k, i'⟩)) (Finset.mem_univ i)
        rw [hw] at this
        exact (Finsupp.mem_support_iff.mp hp) (Nat.le_zero.mp this)

end Block

end BlockImageHilb


open BlockImageHilb in
theorem BlockImageHilb.proof : BlockImageHilb.Statement := by
  intro K _ _ ι _ Ω _ _ κ _ y k₀ M N x hxy n
  rw [coordIdeal_eq_mCoordIdeal]
  have e : (fun k => if k = k₀ then (n : ℤ) else 0) = fun k => ((Pi.single k₀ n : K → ℕ) k : ℤ) := by
    funext k
    by_cases h : k = k₀
    · subst h; simp
    · simp [h]
  rw [e, hilbFn_eq_finrank y (Pi.single k₀ n), ← valSpan_eq hxy n]
  exact hilbFn_eq_finrank (ι := GlobalTheory κ) x (fun _ => n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace BlockResolutionMixedIntegral

theorem proof (hB : BlockResolutionMixedBridge.Statement) (hI : BlockResolutionInterpIntegral.Statement) :
    BlockResolutionMixedIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  rw [hI D K ι Ω d A' hdeg hA']
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : ∀ j : Fin D, IsSmoothHerm (if j.val < i then A' else d.A) := fun j => by
    split_ifs
    · exact hA'
    · exact d.semipos.1
  have hpot : blockMixPot d.A A' D i = fun j z => Real.log ((if j.val < i then A' else d.A).h z) := by
    funext j z
    unfold blockMixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => AnResBridge.potOf d.R (if j.val < i then A' else d.A)) =
      fun j : Fin D => if j.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D K ι Ω d (fun j => if j.val < i then A' else d.A) A' hL hdeg hA', hres]

end BlockResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGraphDeg.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    IsBlockImage y k₀ M N x →
    ∃ (G : GenFibre (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M)))
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι (GlobalTheory κ)) (Sum.inr : Unit → K ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

