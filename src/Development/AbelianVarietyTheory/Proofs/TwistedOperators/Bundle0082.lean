module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
public import Formalism.LocalRingCardinality.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FractionalBaseInclusion
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPositiveBlockColumnEq
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.Twist.Boost

theorem reflectionBoost_matrix_conjTranspose_mul_self {n : ℕ} (e v : Fin n → ℂ) (t c : ℂ) (hee : star e ⬝ᵥ e = 1) (hvv : star v ⬝ᵥ v = 1)
    (hev : star e ⬝ᵥ v = t) (hve : star v ⬝ᵥ e = t) (hc : c * (1 + t) = 1) (hcs : star c = c) :
    (1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e))ᴴ *
      (1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e)) = 1 := by
  simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, conjTranspose_vecMulVec,
    star_star, hcs, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, vecMulVec_smul, star_add, add_dotProduct, dotProduct_add,
    hee, hvv, hev, hve]
  have hs2 : star (2 : ℂ) = 2 := by simp
  rw [hs2]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply, Pi.star_apply, smul_eq_mul]
  linear_combination (2 * c * ((e i + v i) * (star (e j) + star (v j))) - 2 * ((e i + v i) * star (e j)) - 2 * (e i * (star (e j) + star (v j)))) * hc

theorem exists_unitary_col (m : ℕ) (ε : Fin m → Bool) (z : Fin m) (u : Fin m → ℂ) (hz : ε z = true)
    (hneg : ∀ i, ε i = false → u i = 0) (hn : ∑ i, ‖u i‖ ^ 2 = 1) :
    ∃ k ∈ UJset ε, kᴴ * k = 1 ∧ ∀ i, k i z = u i := by
  set t : ℝ := ‖u z‖ with ht
  have t0 : 0 ≤ t := norm_nonneg _
  set φ : ℂ := if u z = 0 then 1 else u z / (t : ℂ) with hφdef
  have hφ : star φ * φ = 1 := by
    by_cases h : u z = 0
    · simp [hφdef, h]
    · have htn : (t : ℂ) ≠ 0 := by simp [ht, h]
      simp only [hφdef, h, if_false, star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [div_mul_div_comm, Complex.conj_mul', ← ht]
      field_simp
  have hφt : star φ * u z = (t : ℂ) := by
    by_cases h : u z = 0
    · simp [hφdef, h, ht]
    · have htn : (t : ℂ) ≠ 0 := by simp [ht, h]
      simp only [hφdef, h, if_false, star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [div_mul_eq_mul_div, Complex.conj_mul', ← ht]
      field_simp
  have hφ' : (starRingEnd ℂ) φ * φ = 1 := by rw [← Complex.star_def]; exact hφ
  have hφt' : (starRingEnd ℂ) φ * u z = (t : ℂ) := by rw [← Complex.star_def]; exact hφt
  set e : Fin m → ℂ := Pi.single z 1 with he
  set v : Fin m → ℂ := fun i => star φ * u i with hv
  have hee : star e ⬝ᵥ e = 1 := by simp [he, dotProduct, Pi.single_apply]
  have hvv : star v ⬝ᵥ v = 1 := by
    have : ∀ i, star (v i) * v i = ((‖u i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      simp only [hv, star_mul, star_star]
      calc star (u i) * φ * (star φ * u i) = (star φ * φ) * (star (u i) * u i) := by ring
        _ = _ := by rw [hφ, one_mul, Complex.star_def, Complex.conj_mul']; push_cast; ring
    simp only [dotProduct, Pi.star_apply, this]
    rw [← Complex.ofReal_sum, hn]; simp
  have hev : star e ⬝ᵥ v = (t : ℂ) := by
    simp [he, dotProduct, Pi.single_apply, hv, hφt, hφt']
  have hve : star v ⬝ᵥ e = (t : ℂ) := by
    simp only [he, dotProduct, Pi.star_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [hv]
    rw [hφt]; simp
  set c : ℂ := ((1 / (1 + t) : ℝ) : ℂ) with hcdef
  have hc : c * (1 + (t : ℂ)) = 1 := by
    have : (1 + t) ≠ 0 := by positivity
    have h2 : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast this
    simp only [hcdef]; push_cast; field_simp
  have hcs : star c = c := by simp [hcdef]
  set T : Matrix (Fin m) (Fin m) ℂ := 1 - c • vecMulVec (e + v) (star (e + v)) + (2 : ℂ) • vecMulVec v (star e) with hT
  have hTu : Tᴴ * T = 1 := reflectionBoost_matrix_conjTranspose_mul_self e v t c hee hvv hev hve hc hcs
  set d : Fin m → ℂ := fun i => if i = z then φ else 1 with hd
  set k : Matrix (Fin m) (Fin m) ℂ := T * diagonal d with hk
  have hdd : (diagonal d)ᴴ * diagonal d = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    by_cases h : i = z
    · simp [hd, h, hφ, hφ']
    · simp [hd, h]
  have hku : kᴴ * k = 1 := by
    rw [hk, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ, hTu, Matrix.one_mul, hdd]
  have hTe : ∀ i j, T i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j - c * ((e i + v i) * star (e j + v j)) + 2 * (v i * star (e j)) := by
    intro i j; simp [hT, vecMulVec_apply]
  have hvneg : ∀ i, ε i = false → v i = 0 := fun i hi => by simp [hv, hneg i hi]
  have heneg : ∀ i, ε i = false → e i = 0 := fun i hi => by
    have : i ≠ z := by rintro rfl; simp [hz] at hi
    simp [he, Pi.single_apply, this]
  have hT0 : ∀ i j, ε i ≠ ε j → T i j = 0 := by
    intro i j hij
    have hne : i ≠ j := by rintro rfl; exact hij rfl
    rw [hTe, one_apply_ne hne]
    cases hi : ε i <;> cases hj : ε j
    · simp [hi, hj] at hij
    · simp [hvneg i hi, heneg i hi]
    · simp [hvneg j hj, heneg j hj]
    · simp [hi, hj] at hij
  have hcomm : Jm ε * k = k * Jm ε := by
    ext i j
    simp only [hk, Jm, diagonal_mul, mul_diagonal]
    by_cases hij : ε i = ε j
    · rw [hij]; ring
    · rw [hT0 i j hij]; ring
  refine ⟨k, ?_, hku, ?_⟩
  · show Formalism.REAL.inUJ ε k
    unfold Formalism.REAL.inUJ
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hku, Matrix.one_mul]
  · intro i
    have hez : e z = 1 := by simp [he]
    have hvz : v z = (t : ℂ) := by simp [hv, hφt, hφt']
    have hTz : T i z = v i := by
      rw [hTe, hez, hvz]
      rw [show star ((1 : ℂ) + (t : ℂ)) = 1 + (t : ℂ) by simp, star_one, mul_one]
      have : c * ((e i + v i) * (1 + (t : ℂ))) = e i + v i := by rw [mul_comm (e i + v i), ← mul_assoc, hc, one_mul]
      rw [this]
      by_cases h : i = z
      · subst h; simp [he]; ring
      · simp [he, Pi.single_apply, h, one_apply_ne h]; ring
    simp only [hk, mul_diagonal, hTz, hd, if_true, hv]
    calc star φ * u i * φ = (star φ * φ) * u i := by ring
      _ = u i := by rw [hφ, one_mul]

end GlobalTheory.Twist.Boost

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FnShapeOfJointShape
section
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.ListShape

def posFn (x : List ℤ) (i : ℕ) : ℕ := (x.getD i 0).toNat

def negFn (y : List ℤ) (i : ℕ) : ℕ := posFn (y.reverse.map fun v => -v) i

theorem posFn_eq_zero {x : List ℤ} {i : ℕ} (h : x.length ≤ i) : posFn x i = 0 := by
  unfold posFn
  rw [List.getD_eq_default _ _ h]
  simp

theorem negFn_eq_zero {y : List ℤ} {i : ℕ} (h : y.length ≤ i) : negFn y i = 0 := by
  unfold negFn
  exact posFn_eq_zero (by simpa using h)

theorem posFn_antitone {x : List ℤ} (h : x.Pairwise (· ≥ ·)) : Antitone (posFn x) := by
  intro i j hij
  by_cases hj : j < x.length
  · have hi : i < x.length := lt_of_le_of_lt hij hj
    simp only [posFn, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    apply Int.toNat_le_toNat
    rcases hij.lt_or_eq with hlt | heq
    · exact List.pairwise_iff_getElem.mp h i j hi hj hlt
    · subst heq
      exact le_rfl
  · rw [posFn_eq_zero (not_lt.mp hj)]
    exact Nat.zero_le _

theorem negFn_antitone {y : List ℤ} (h : y.Pairwise (· ≥ ·)) : Antitone (negFn y) := by
  show Antitone (posFn (y.reverse.map fun v => -v))
  apply posFn_antitone
  rw [List.pairwise_map, List.pairwise_reverse]
  exact h.imp fun hab => neg_le_neg hab

theorem posFn_cast {x : List ℤ} (hx : ∀ v ∈ x, 0 < v) {i : ℕ} (hi : i < x.length) :
    (posFn x i : ℚ) = (x[i] : ℤ) := by
  have hp : 0 < x[i] := hx _ (List.getElem_mem hi)
  simp only [posFn, List.getD_eq_getElem _ _ hi]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hp.le]

theorem negFn_cast {y : List ℤ} (hy : ∀ v ∈ y, v < 0) {i : ℕ} (hi : i < y.length) :
    (negFn y i : ℚ) = -((y[y.length - 1 - i] : ℤ) : ℚ) := by
  have hl : i < (y.reverse.map fun v => -v).length := by simpa using hi
  have hk : y.length - 1 - i < y.length := by omega
  have hv : y[y.length - 1 - i] < 0 := hy _ (List.getElem_mem hk)
  simp only [negFn, posFn, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_reverse]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]

theorem disj {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) (i : Fin n) :
    posFn x i = 0 ∨ negFn y i.rev = 0 := by
  have hn := i.isLt
  by_cases hi : x.length ≤ (i : ℕ)
  · exact Or.inl (posFn_eq_zero hi)
  · right
    apply negFn_eq_zero
    rw [Fin.val_rev]
    omega

private lemma getD_map_intCast (l : List ℤ) (i : ℕ) :
    (l.map (fun v : ℤ => (v : ℚ))).getD i 0 = ((l.getD i 0 : ℤ) : ℚ) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem pad_getD {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) {n : ℕ}
    (h : x.length + y.length ≤ n) (i : Fin n) :
    (pad x (n - x.length - y.length) y).getD i 0 = (posFn x i : ℚ) - negFn y i.rev := by
  have hn := i.isLt
  unfold pad
  rw [getD_map_intCast, List.append_assoc, Fin.val_rev]
  by_cases h1 : (i : ℕ) < x.length
  · rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, posFn_cast hx h1,
      negFn_eq_zero (by omega)]
    simp
  · rw [List.getD_append_right _ _ _ _ (not_lt.mp h1), posFn_eq_zero (not_lt.mp h1)]
    by_cases h2 : (i : ℕ) - x.length < n - x.length - y.length
    · rw [List.getD_append _ _ _ _ (by simpa using h2), negFn_eq_zero (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, h2]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_replicate]
      have hj : n - ((i : ℕ) + 1) < y.length := by omega
      rw [negFn_cast hy hj]
      have e : (i : ℕ) - x.length - (n - x.length - y.length) = y.length - 1 - (n - ((i : ℕ) + 1)) := by
        omega
      rw [e, List.getD_eq_getElem _ _ (by omega)]
      simp

end GlobalTheory.JointHarm.ListShape

namespace GlobalTheory.JointHarm


open ListShape in
theorem fnShape_of_jointShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
    (h : JointShape p q r s μ μ') : FnShape p q r s μ μ' := by
  obtain ⟨a, b, c, d, ha, hc, hb, hd, ha', hb', hc', hd', hab, hcd, had, hcb, hμ, hμ'⟩ := h
  refine ⟨posFn a, negFn b, posFn c, negFn d, posFn_antitone ha', negFn_antitone hb',
    posFn_antitone hc', negFn_antitone hd', fun i hi => posFn_eq_zero (by omega),
    fun i hi => negFn_eq_zero (by omega), fun i hi => posFn_eq_zero (by omega),
    fun i hi => negFn_eq_zero (by omega), disj hab, disj hcd, disj had, disj hcb,
    fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hμ]
    exact pad_getD ha hb hab i
  · rw [hμ]
    exact pad_getD hc hd hcd i
  · rw [hμ']
    exact pad_getD ha hd had i
  · rw [hμ']
    exact pad_getD hc hb hcb i

end GlobalTheory.JointHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionFieldEmbeddingCompat
section
noncomputable section

namespace GlobalTheory.Proof.FractionFieldEmbeddingCompat

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

theorem fracExt_fracBase_algebraMap {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w)) :
    fracExt c w (fracBase D (c.twI w) (algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y)) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
          (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y))) := by
  rw [← IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)]
  simp [fracExt, fracBase, IsFractionRing.map]

theorem embW_eq_of_tie {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : D.LL0) :
    c.embW w (x : D.what₂.LL) = fracExt c w (fracBase D (c.twI w) (embSide D (c.twI w) (c.sd w) x)) := by
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w)) (embSide D (c.twI w) (c.sd w) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hz0
  have hmul : embSide D (c.twI w) (c.sd w) x * algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have e := h.embedding_baseField_condition w x y z hz0 hmul
  rw [← fracExt_fracBase_algebraMap, ← fracExt_fracBase_algebraMap, ← hmul, map_mul, map_mul] at e
  exact mul_right_cancel₀ ((map_ne_zero _).2 ((map_ne_zero _).2 hz1)) e

theorem embCompat : EmbCompat := by
  intro D c h K _ _ _ κ hκ w ιK hι
  subst hι
  ext x
  have e := embW_eq_of_tie h w (κ x)
  rw [hκ x] at e
  exact e

end GlobalTheory.Proof.FractionFieldEmbeddingCompat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpAddSmulDuhamel
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem hasDerivAt_exp_add_smul_duhamel (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X V : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (X + t • V))
      (∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • X)) 0 := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Continuous (NormedSpace.exp : A → A) := NormedSpace.exp_continuous
  set f : ℝ → ℝ → A := fun t s =>
    NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • (X + t • V)) with hf
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hf, Function.uncurry_def]
    exact ((hc.comp (by fun_prop)).mul continuous_const).mul (hc.comp (by fun_prop))
  set F : ℝ → A := fun t => ∫ s in (0 : ℝ)..1, f t s with hF
  have hFc : Continuous F :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hfc 0 1
  have key : ∀ t : ℝ, NormedSpace.exp (X + t • V) = NormedSpace.exp X + t • F t := by
    intro t
    have hd : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => NormedSpace.exp ((1 - s) • X) * NormedSpace.exp (s • (X + t • V)))
        (t • f t s) s := by
      intro s
      have h0 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
        simpa using (hasDerivAt_id s).const_sub 1
      have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (1 - s)).scomp s h0
      have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (X + t • V) s
      have h3 := h1.mul h2
      refine h3.congr_deriv ?_
      simp only [hf, Function.comp_apply, neg_smul, one_smul, add_mul, mul_add, mul_assoc,
        neg_mul, smul_mul_assoc, mul_smul_comm]
      abel
    have hi : IntervalIntegrable (fun s => t • f t s) volume 0 1 :=
      ((hfc.comp (Continuous.prodMk_right t)).const_smul t).intervalIntegrable 0 1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
    rw [intervalIntegral.integral_smul] at h
    simp only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, one_smul, sub_zero,
      mul_one] at h
    simp only [hF]
    rw [h]
    abel
  have hF0 : F 0 = ∫ s in (0 : ℝ)..1,
      NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • X) := by
    simp [hF, hf]
  rw [← hF0, hasDerivAt_iff_tendsto_slope_zero]
  have ht : Filter.Tendsto F (nhdsWithin 0 {0}ᶜ) (nhds (F 0)) :=
    hFc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  have ht0' : t ≠ 0 := ht0
  rw [key (0 + t), key 0]
  simp [smul_smul, inv_mul_cancel₀ ht0']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasFDerivAtOfCompImmersion
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem hasFDerivAt_of_comp_immersion : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (Φ : E → F) (ψ : E → E) (x : E) (A D : E →L[ℝ] F), HasStrictFDerivAt Φ A (ψ x) → Function.Injective A → ContinuousAt ψ x → HasFDerivAt (fun y => Φ (ψ y)) D x → ∃ P : E →L[ℝ] E, HasFDerivAt ψ P x ∧ A.comp P = D := by
  intro E F _ _ _ _ _ _ Φ ψ x A D hA hinj hψ hD

  obtain ⟨g, hg⟩ := (A : E →ₗ[ℝ] F).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  let L : F →L[ℝ] E := LinearMap.toContinuousLinearMap g
  have hLA : ∀ v, L (A v) = v := fun v => by
    have h := LinearMap.congr_fun hg v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe] at h
    first
      | exact h
      | simpa [L] using h
      | (rw [show (L : F → E) = g from LinearMap.coe_toContinuousLinearMap' g]; exact h)

  have hr : (fun y => Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)) =o[nhds x] (fun y => ψ y - ψ x) :=
    hA.hasFDerivAt.isLittleO.comp_tendsto hψ
  have hs : (fun y => Φ (ψ y) - Φ (ψ x) - D (y - x)) =o[nhds x] (fun y => y - x) :=
    hD.isLittleO
  have hLr : (fun y => L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x))) =o[nhds x] (fun y => ψ y - ψ x) :=
    (L.isBigO_comp _ _).trans_isLittleO hr

  have hu : (fun y => ψ y - ψ x) =O[nhds x] (fun y => y - x) := by
    have h1 := hLr.right_isBigO_add
    have hsum : (fun y => L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)) + (ψ y - ψ x))
        = fun y => L (Φ (ψ y) - Φ (ψ x)) := by
      funext y
      simp only [map_sub, hLA]
      abel
    rw [hsum] at h1
    exact h1.trans ((L.isBigO_comp _ _).trans hD.isBigO_sub)

  have hP : HasFDerivAt ψ (L.comp D) x := by
    rw [hasFDerivAt_iff_isLittleO]
    have hdiff : (fun y => L (Φ (ψ y) - Φ (ψ x) - D (y - x)) - L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)))
        = fun y => ψ y - ψ x - (L.comp D) (y - x) := by
      funext y
      simp only [map_sub, hLA, ContinuousLinearMap.comp_apply]
      abel
    rw [← hdiff]
    exact ((L.isBigO_comp _ _).trans_isLittleO hs).sub (hLr.trans_isBigO hu)
  refine ⟨L.comp D, hP, ?_⟩
  exact (hA.hasFDerivAt.comp x hP).unique hD

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasStrictFDerivAtExpTwoUpperRightBlockElementP
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

def twoPYLin (p q : ℕ) : (Fin p → Fin q → ℂ) →ₗ[ℝ] Mat p q where
  toFun C := pY C + pY C
  map_add' B C := by rw [pY_add]; abel
  map_smul' t B := by rw [pY_smul, smul_add]; rfl

def entryLin {p q : ℕ} (a b : Ix p q) : Mat p q →ₗ[ℝ] ℂ where
  toFun M := M a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Matrix.Norms.Operator in
theorem contDiff_exp_two_pY_entry (p q : ℕ) (a b : Ix p q) :
    ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => NormedSpace.exp (pY C + pY C) a b) := by
  have h1 : ContDiff ℝ 1 (NormedSpace.exp : Mat p q → Mat p q) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have h2 : ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => (pY C + pY C : Mat p q)) :=
    (LinearMap.toContinuousLinearMap (twoPYLin p q)).contDiff
  have h3 : ContDiff ℝ 1 (fun M : Mat p q => M a b) :=
    (LinearMap.toContinuousLinearMap (entryLin a b)).contDiff
  exact h3.comp (h1.comp h2)

theorem hasStrictFDerivAt_exp_two_pY : ∀ (p q : ℕ) (B : Fin p → Fin q → ℂ), (∀ (V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • V) a b) ((NormedSpace.exp (pY B) * sAd (pY B) V * NormedSpace.exp (pY B)) a b) 0) → ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B) := by
  intro p q B h
  have hc : ContDiff ℝ 1 (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) =>
      NormedSpace.exp (pY C + pY C) a b) :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => contDiff_exp_two_pY_entry p q a b
  have hs := hc.contDiffAt.hasStrictFDerivAt_fderiv (x := B) (by simp)
  refine ⟨_, hs, fun C => ?_⟩
  ext a b
  have hl : HasDerivAt (fun t : ℝ => B + t • C) C 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const C).const_add B
  have h1 := hs.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 a) b
  have h3 := h (pY C + pY C) a b
  have e : (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • (pY C + pY C)) a b) =
      fun t : ℝ => NormedSpace.exp (pY (B + t • C) + pY (B + t • C)) a b := by
    funext t
    have e' : pY B + pY B + t • (pY C + pY C) = pY (B + t • C) + pY (B + t • C) := by
      rw [pY_add, pY_smul, smul_add]; abel
    rw [e']
  rw [e] at h3
  exact h2.unique h3

end GlobalTheory.PolarU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormProportionalOfIrreducibleStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_eq_mul_of_finrank_hwSub_eq_one : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (H₁ H₂ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (E₁ : M.V →ₗ[ℂ] H₁) (E₂ : M.V →ₗ[ℂ] H₂), IrrGK M → Module.finrank ℂ ↥(hwSub M.act Λ) = 1 → Function.Injective E₁ → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₁ y) = inner ℂ (E₁ x) (E₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₂ (M.act Z x)) (E₂ y) = inner ℂ (E₂ x) (E₂ (M.act (adjZ Z) y))) → ∃ c : ℝ, ∀ y, ‖E₂ y‖ = c * ‖E₁ y‖ := by
  first | exact @GlobalTheory.FockTensor.norm_proportional_of_irreducible | exact GlobalTheory.FockTensor.norm_proportional_of_irreducible | (intros; apply GlobalTheory.FockTensor.norm_proportional_of_irreducible <;> assumption)
end

