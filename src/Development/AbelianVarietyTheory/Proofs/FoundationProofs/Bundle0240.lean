module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0211

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructure
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FourCopies

theorem exists_orthogonal_family {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : V → V →ₗ[K] K)
    (hsym : ∀ x y, h y x = 0 → h x y = 0) (hdef : ∀ x, h x x = 0 → x = 0) (s : Finset V) :
    ∃ (n : ℕ) (v : Fin n → V), (∀ i, v i ≠ 0) ∧ (∀ i j, i ≠ j → h (v j) (v i) = 0) ∧
      ∀ x ∈ s, x ∈ Submodule.span K (Set.range v) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | insert x s _ ih =>
    obtain ⟨n, v, h0, ho, hs⟩ := ih
    set p : V := ∑ i, (h (v i) x / h (v i) (v i)) • v i with hp
    have hpm : p ∈ Submodule.span K (Set.range v) :=
      sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hx : ∀ j, h (v j) (x - p) = 0 := by
      intro j
      have hj : h (v j) (v j) ≠ 0 := fun e => h0 j (hdef _ e)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hp, map_sum, Finset.sum_eq_single j]
      · rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hj, sub_self]
      · intro i _ hij
        rw [map_smul, ho i j hij, smul_zero]
      · simp
    by_cases hz : x - p = 0
    · refine ⟨n, v, h0, ho, fun y hy => ?_⟩
      rcases Finset.mem_insert.1 hy with rfl | hy
      · rw [sub_eq_zero.1 hz]; exact hpm
      · exact hs y hy
    · have hle : Submodule.span K (Set.range v) ≤
          Submodule.span K (Set.range (Fin.cons (x - p) v : Fin (n + 1) → V)) :=
        Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, by simp⟩)
      refine ⟨n + 1, Fin.cons (x - p) v, fun i => ?_, fun i j hij => ?_, fun y hy => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hz
        · simpa using h0 i
      · revert hij
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
        · exact absurd rfl hij
        · exact hx j
        · exact hsym _ _ (hx i)
        · exact ho i j (fun e => hij (by rw [e]))
      · rcases Finset.mem_insert.1 hy with rfl | hy
        · have := add_mem (Submodule.subset_span (Set.mem_range_self 0)) (hle hpm)
          rwa [Fin.cons_zero, sub_add_cancel] at this
        · exact hle (hs y hy)

theorem exists_similitude (a : ℚ) (ha : 0 < a) :
    ∃ A : Fin 4 → Fin 4 → ℚ, (∀ j j', a * ∑ k, A j k * A j' k = if j = j' then 1 else 0) ∧
      ∀ k k', a * ∑ j, A j k * A j k' = if k = k' then 1 else 0 := by
  obtain ⟨p, q, r, s, h⟩ := Nat.sum_four_squares (a.num.natAbs * a.den)
  have hn : (0 : ℚ) < a.num := by exact_mod_cast Rat.num_pos.2 ha
  have h1 : ((a.num.natAbs : ℕ) : ℚ) = a.num := by
    rw [Nat.cast_natAbs, abs_of_pos (Rat.num_pos.2 ha)]
  have h2 : (p : ℚ) ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = a.num * a.den := by
    rw [← h1]; exact_mod_cast h
  have h3 : a * a.den = a.num := Rat.mul_den_eq_num a
  obtain ⟨p, q, r, s, h⟩ : ∃ p q r s : ℚ, a * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) = 1 := by
    refine ⟨p / a.num, q / a.num, r / a.num, s / a.num, ?_⟩
    simp only [div_pow, ← add_div, h2]
    field_simp
    linear_combination h3
  refine ⟨![![p, q, r, s], ![-q, p, -s, r], ![-r, s, p, -q], ![-s, -r, q, p]], fun j j' => ?_, fun j j' => ?_⟩ <;>
    fin_cases j <;> fin_cases j' <;> simp [Fin.sum_univ_four] <;>
    first | linear_combination h | (right; ring)

variable (D : D7)

theorem exists_rat_of_real (x : D.host.K) (hx : (D.host.φ₀ (x : D.host.E)).im = 0) : ∃ a : ℚ, x = (a : D.host.K) :=
  by apply _root_.GlobalTheory.RationalOfReal.rat_of_real <;> assumption

theorem exists_rat_pos {N N' : ℕ} (x : Matrix (Fin N') (Fin N) D.host.E) (hx : x ≠ 0) :
    ∃ a : ℚ, 0 < a ∧ hYY D x x = (a : D.host.K) := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  have h : D.host.φ₀ ((hYY D x x : D.host.K) : D.host.E) =
      ((∑ τ, ∑ i, ∑ j, Complex.normSq (embT D τ (x i j)) : ℝ) : ℂ) := by
    unfold hYY
    rw [← (GlobalTheory.InducedType.induced_type D).1.2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hc, Complex.mul_conj]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := exists_rat_of_real D (hYY D x x) (by rw [h, Complex.ofReal_im])
  refine ⟨a, ?_, ha⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, x i j ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hx (Matrix.ext hh)
  have hpos : 0 < ∑ τ, ∑ i, ∑ j, Complex.normSq (embT D τ (x i j)) := by
    have nn := fun τ i j => Complex.normSq_nonneg (embT D τ (x i j))
    refine Finset.sum_pos' (fun τ _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => nn τ i j)
      ⟨D.eTau.symm 1, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => nn _ i j) ⟨i, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun j _ => nn _ i j) ⟨j, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.2 ((map_ne_zero _).2 hij)
  rw [ha] at h
  have h' : ((a : ℝ) : ℂ) = ((∑ τ, ∑ i, ∑ j, Complex.normSq (embT D τ (x i j)) : ℝ) : ℂ) := by
    rw [← h]; simp
  rw [← Complex.ofReal_injective h'] at hpos
  exact_mod_cast hpos

def cols (N : ℕ) : Fin (N + 3 * N) ≃ Fin 4 × Fin N :=
  (finCongr (by ring)).trans finProdFinEquiv.symm

def blocks {N N' : ℕ} (c : Fin 4 → ℚ) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] Matrix (Fin N') (Fin (N + 3 * N)) D.host.E where
  toFun v := fun i j => (c (cols N j).1 : D.host.E) * v i (cols N j).2
  map_add' v w := by
    funext i j
    exact mul_add _ _ _
  map_smul' a v := by
    funext i j
    exact mul_smul_comm a _ (v i (cols N j).2)

theorem blocks_apply {N N' : ℕ} (c : Fin 4 → ℚ) (v : Matrix (Fin N') (Fin N) D.host.E) (i j) :
    blocks D c v i j = (c (cols N j).1 : D.host.E) * v i (cols N j).2 := rfl

theorem hYY_blocks {N N' : ℕ} (c c' : Fin 4 → ℚ) (v w : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (blocks D c v) (blocks D c' w) = ((∑ k, c k * c' k : ℚ) : D.host.K) * hYY D v w := by
  unfold hYY
  rw [← smul_eq_mul ((∑ k, c k * c' k : ℚ) : D.host.K), ← map_smul, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (cols N).symm.sum_comp, Fintype.sum_prod_type, Algebra.smul_def, map_ratCast]
  simp only [blocks_apply, Equiv.apply_symm_apply, map_mul, map_ratCast]
  push_cast
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_onB_four : ∀ (D : D7) (N N' : ℕ), ∃ (m r : ℕ) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b := by
  intro D N N'
  obtain ⟨s, hs⟩ : (⊤ : Submodule D.host.K (Matrix (Fin N') (Fin N) D.host.E)).FG := Module.Finite.fg_top
  obtain ⟨n, v, h0, ho, hsp⟩ := exists_orthogonal_family (hYYLeft D (N := N) (N' := N'))
    (fun x y e => by
      have h1 := hYY_herm D (GlobalTheory.InducedType.induced_type D).1.2 x y
      change hYY D x y = 0 at e
      change hYY D y x = 0
      rw [e] at h1
      simpa using h1)
    (fun x e => by
      by_contra hx
      obtain ⟨a, ha, h1⟩ := exists_rat_pos D x hx
      change hYY D x x = 0 at e
      rw [e] at h1
      exact ha.ne' (by exact_mod_cast h1.symm)) s
  have htop : ∀ x, x ∈ Submodule.span D.host.K (Set.range v) := fun x =>
    (Submodule.span_le.2 (fun y hy => hsp y hy) : Submodule.span D.host.K (s : Set _) ≤ _) (by rw [hs]; trivial)
  choose a ha hav using fun i => exists_rat_pos D (v i) (h0 i)
  choose A hA hA' using fun i => exists_similitude (a i) (ha i)
  let e : Fin (n * 4) ≃ Fin n × Fin 4 := finProdFinEquiv.symm
  refine ⟨3 * N, n * 4, fun l => blocks D (A (e l).1 (e l).2) (v (e l).1), fun l l' => ?_, ?_⟩
  · rw [hYY_blocks]
    by_cases hi : (e l).1 = (e l').1
    · rw [← hi, hav, ← Rat.cast_mul, mul_comm, hA]
      have : (e l).2 = (e l').2 ↔ l = l' := ⟨fun h => e.injective (Prod.ext hi h), fun h => by rw [h]⟩
      simp only [this]
      split_ifs <;> simp
    · have : l ≠ l' := fun h => hi (by rw [h])
      rw [if_neg this, show hYY D (v (e l).1) (v (e l').1) = 0 from ho _ _ hi, mul_zero]
  · set W := Submodule.span D.host.K (Set.range fun l => blocks D (A (e l).1 (e l).2) (v (e l).1)) with hW
    have hb : ∀ i j, blocks D (A i j) (v i) ∈ W := fun i j =>
      Submodule.subset_span ⟨e.symm (i, j), by simp only [Equiv.apply_symm_apply]⟩
    have h1 : ∀ (k : Fin 4) i, blocks D (fun k' => if k = k' then 1 else 0) (v i) ∈ W := by
      intro k i
      have : blocks D (fun k' => if k = k' then 1 else 0) (v i) =
          ∑ j, ((a i * A i j k : ℚ) : D.host.K) • blocks D (A i j) (v i) := by
        funext s t
        simp only [Matrix.sum_apply, Matrix.smul_apply, blocks_apply, Algebra.smul_def, map_ratCast]
        rw [← hA' i]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      exact sum_mem fun j _ => W.smul_mem _ (hb i j)
    have h2 : ∀ (k : Fin 4) x, blocks D (fun k' => if k = k' then 1 else 0) x ∈ W := by
      intro k x
      have : Submodule.span D.host.K (Set.range v) ≤ W.comap (blocks D fun k' => if k = k' then 1 else 0) :=
        Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h1 k i)
      exact this (htop x)
    rw [eq_top_iff]
    intro x _
    have : x = ∑ k : Fin 4, blocks D (fun k' => if k = k' then 1 else 0)
        (Matrix.of fun i j => x i ((cols N).symm (k, j))) := by
      funext s t
      simp only [Matrix.sum_apply, blocks_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single (cols N t).1]
      · simp
      · intro k _ hk
        simp [hk]
      · simp
    rw [this]
    exact sum_mem fun k _ => h2 k _

end GlobalTheory.FourCopies
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCexpGaussianPlane
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem integral_cexp_gaussian_plane : ∀ l u v : ℂ, 0 < l.re → Integrable (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) ∧ ∫ z : ℂ, cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)) = l⁻¹ * cexp (π * (u * conj v) / l) := by
  intro l u v hl
  have hl0 : l ≠ 0 := by
    intro h
    simp [h] at hl
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (-(π : ℂ) * l).re < 0 := by
    have := mul_pos Real.pi_pos hl
    simpa using this
  set f : ℝ → ℂ := fun x => cexp ((-(π : ℂ) * l) * x ^ 2 + (π * (u + conj v)) * x + 0) with hf
  set g : ℝ → ℂ := fun y => cexp ((-(π : ℂ) * l) * y ^ 2 + (π * I * (conj v - u)) * y + 0) with hg
  have hfi : Integrable f := integrable_cexp_quadratic' hb _ _
  have hgi : Integrable g := integrable_cexp_quadratic' hb _ _
  have key : (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)))
      = (fun p : ℝ × ℝ => f p.1 * g p.2) ∘ Complex.measurableEquivRealProd := by
    funext z
    simp only [hf, hg, Function.comp, Complex.measurableEquivRealProd_apply, ← Complex.exp_add]
    congr 1
    have hz : z = z.re + z.im * I := (Complex.re_add_im z).symm
    have hc : conj z = z.re - z.im * I := by
      apply Complex.ext <;> simp
    rw [hc]
    generalize (z.re : ℂ) = a at hz ⊢
    generalize (z.im : ℂ) = b at hz ⊢
    subst hz
    linear_combination (π * l * b ^ 2) * Complex.I_sq
  have hmp := Complex.volume_preserving_equiv_real_prod
  refine ⟨?_, ?_⟩
  · rw [key, hmp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding]
    exact hfi.mul_prod hgi
  · rw [key]
    have h1 := hmp.integral_comp' (fun p : ℝ × ℝ => f p.1 * g p.2)
    simp only [Function.comp_def]
    rw [h1, Measure.volume_eq_prod, integral_prod_mul, hf, hg, integral_cexp_quadratic hb,
      integral_cexp_quadratic hb]
    have h2 : (π : ℂ) / -(-(π : ℂ) * l) = l⁻¹ := by field_simp
    have h3 : (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) * (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) = l⁻¹ := by
      rw [← Complex.cpow_add _ _ (inv_ne_zero hl0)]
      norm_num
    rw [h2, mul_mul_mul_comm, h3, ← Complex.exp_add]
    congr 2
    field_simp
    linear_combination (π * (conj v - u) ^ 2) * Complex.I_sq

end GlobalTheory.UnitaryTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralUnfoldFundamentalDomain
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory

theorem integral_unfold_fundamentalDomain : ∀ (V : Type) [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ g : V → ℂ, Integrable g μ → IntegrableOn (fun z => ∑' y : Λ, g (z + y)) Fd μ ∧ ∫ z in Fd, ∑' y : Λ, g (z + y) ∂μ = ∫ z, g z ∂μ := by
  intro V _ _ _ _ μ _ Λ _ Fd hFd g hg
  have hv : ∀ (y : Λ) (z : V), y +ᵥ z = z + y := fun y z => by
    rw [add_comm]; rfl
  have hm : ∀ y : Λ, AEStronglyMeasurable (fun z => g (z + y)) (μ.restrict Fd) := fun y => by
    have h := (hg.comp_add_left (y : V)).aestronglyMeasurable
    simp only [add_comm (y : V)] at h
    exact h.restrict
  have hfin : ∑' y : Λ, ∫⁻ z in Fd, ‖g (z + y)‖ₑ ∂μ ≠ ⊤ := by
    have h := hFd.lintegral_eq_tsum'' (fun z => ‖g z‖ₑ)
    simp only [hv] at h
    rw [← h]
    exact hg.2.ne
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : AEMeasurable (fun z => ∑' y : Λ, g (z + y)) (μ.restrict Fd) :=
      AEMeasurable.tsum fun y => (hm y).aemeasurable
    exact this.aestronglyMeasurable
  · refine lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun y => (hm y).enorm]
    exact hfin.lt_top
  · rw [integral_tsum hm hfin, hFd.integral_eq_tsum'' g hg]
    simp only [hv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleOfWeightLine
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockIrr

theorem act_diag_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} (h : v ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  have h1 := (Submodule.mem_iInf _).1 h a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
  exact sub_eq_zero.1 h1

theorem irreducible_of_weight_line : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  intro p q M H _ _ E hE hadj S hS μ v U hv hU hline N hNU hN
  by_cases hvN : v ∈ N
  · exact Or.inr (le_antisymm hNU (hU N hvN hN))
  left
  have horth : ∀ x ∈ N, inner ℂ (E x) (E v) = 0 := by
    intro x hx
    have hx' := _root_.GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub p q M.V M.act N (fun a => hN a a (hS.refl a)) x hx (M.wts x)
    clear hx
    induction hx' using Submodule.iSup_induction' with
    | mem ν y hy =>
      obtain ⟨hyN, hyν⟩ := hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, hc⟩ := hline y (hNU hyN) hyν
        by_cases hc0 : c = 0
        · simp [hc, hc0]
        · exfalso
          apply hvN
          have : v = c⁻¹ • y := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
          rw [this]
          exact N.smul_mem _ hyN
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h1 := hadj (Eab a a) y v
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_diag_of_mem_wtSub hyν, act_diag_of_mem_wtSub hv, map_smul, map_smul,
          inner_smul_left, inner_smul_right, map_ratCast] at h1
        have hne : ((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha
        have h2 : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) * inner ℂ (E y) (E v) = 0 := by
          rw [sub_mul, h1, sub_self]
        exact (mul_eq_zero.1 h2).resolve_left hne
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _), inner_add_left, hy, hz, add_zero]
  let U' : Submodule ℂ M.V :=
    { carrier := {y | ∀ x ∈ N, inner ℂ (E x) (E y) = 0}
      add_mem' := fun {y z} hy hz x hx => by
        rw [map_add (f := _), inner_add_right, hy x hx, hz x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun c y hy x hx => by
        rw [map_smul, inner_smul_right, hy x hx, mul_zero] }
  have hUU' : U ≤ U' := by
    refine hU U' horth ?_
    intro a b hab y hy x hx
    have h1 := hadj (adjZ (Eab a b)) x y
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at h1
    rw [← h1]
    apply hy
    rw [GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (hN b a (hS.symm hab) x hx)
  rw [eq_bot_iff]
  intro x hx
  have h0 : inner ℂ (E x) (E x) = 0 := hUU' (hNU hx) x hx
  rw [inner_self_eq_zero] at h0
  exact (Submodule.mem_bot ℂ).2 (hE (by rw [h0, map_zero]))

end GlobalTheory.FockIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeLeLogOfIntegralHermitianForm
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem muMaxDef_le_log_of_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → L ≠ ⊥ → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → Formalism.HN.muMaxDef (Pi.basisFun K (Fin d)) X L ≤ Real.log s := by
  intro K _ _ _ _ v₀ hv d H X hH s hs L hL hL0 hint
  have hX : ∀ v, IsUnit (X v).det := fun v => (hH.2 v).1
  refine Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le _ X hL0 fun Q hQ hQ0 => ?_
  have hQfg : Q.FG := Formalism.LFunctionChainParameters.slopeLatticeData.fg_of_le hL hQ
  have h := _root_.GlobalTheory.neg_rank_mul_log_le_lcv K v₀ hv d H X hH s hs Q hQfg fun x hx y hy => hint x (hQ hx) y (hQ hy)
  rw [Formalism.LFunctionChainParameters.slopeLatticeData.muDef_eq_log _ X hX hQfg hQ0]
  have hj : (0 : ℝ) < (Formalism.HN.rkK Q : ℝ) := by exact_mod_cast Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hQ0
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  unfold Formalism.DivisionValues.lcv at h
  have e : -(2 * Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X Q)) /
      ((Module.finrank ℚ K : ℝ) * (Formalism.HN.rkK Q : ℝ)) =
      -((2 / (Module.finrank ℚ K : ℝ)) * Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X Q)) /
        (Formalism.HN.rkK Q : ℝ) := by
    field_simp
  rw [e, div_le_iff₀ hj]
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NabIndepAndDelIndepLocalConditions
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.TestLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem isBasisAt_inv_mul (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (B B' : GL (Fin n) K)
    (h : IsBasisAt w M B) (h' : IsBasisAt w M B') : IsBasisAt w (colLat 1) (B'⁻¹ * B) := by
  rw [← isBasisAt_gLat w B', ← colLat_mul, mul_one, mul_inv_cancel_left]
  exact h'.symm.trans h

theorem indep_of_stable (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (T : Submodule (𝓞 K) (Pol K ι n))
    (hT : ∀ g : ι → GL (Fin n) K, (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ T, actP lam g F ∈ T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K)
    (h : ∀ τ, IsBasisAt w (M τ) (B τ)) (h' : ∀ τ, IsBasisAt w (M τ) (B' τ)) (F : Pol K ι n) :
    actP lam B⁻¹ F ∈ T ↔ actP lam B'⁻¹ F ∈ T := by
  constructor
  · intro hF
    have := hT (B'⁻¹ * B) (fun τ => isBasisAt_inv_mul w (M τ) (B τ) (B' τ) (h τ) (h' τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this
  · intro hF
    have := hT (B⁻¹ * B') (fun τ => isBasisAt_inv_mul w (M τ) (B' τ) (B τ) (h' τ) (h τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this

theorem nabIndep_and_delIndep : NabIndep ∧ DelIndep :=
  ⟨fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt K ι n lam w) M B B' h h' F,
    fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (_root_.GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd K ι n lam w) M B B' h h' F⟩

end GlobalTheory.TestLat
end

