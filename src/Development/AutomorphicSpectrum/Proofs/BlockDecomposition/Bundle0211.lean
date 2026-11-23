module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantElementsGlValued
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityExists
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem exists_mollifiers (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] :
    ∃ φ : ℕ → Mat n → ℝ, (∀ k, IsTest (φ k)) ∧ (∀ k y, 0 ≤ φ k y) ∧
      (∀ k, ∫ y : G n, φ k y.val ∂μ = 1) ∧
      ∀ N ∈ 𝓝 (1 : G n), ∀ᶠ k in atTop, ∀ y : G n, φ k y.val ≠ 0 → y ∈ N := by
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ _
  have hemb := GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n
  obtain ⟨r, hr0, hr⟩ : ∃ r > 0, Metric.closedBall (1 : Mat n) r ⊆ GLs n :=
    Metric.nhds_basis_closedBall.mem_iff.1 (isOpen_GLs.mem_nhds (one_mem_GLs n))
  have hrange : ∀ x ∈ GLs n, x ∈ Set.range (Units.val : G n → Mat n) := by
    intro x hx
    have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
    exact ⟨hu.unit, rfl⟩
  let b : ℕ → ContDiffBump (1 : Mat n) := fun k =>
    { rIn := r / (2 * ((k : ℝ) + 1))
      rOut := r / ((k : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        exact div_lt_div_of_pos_left hr0 this (by linarith) }
  have hbOut : ∀ k, (b k).rOut ≤ r := by
    intro k
    exact div_le_self hr0.le (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hcont : ∀ k, Continuous fun y : G n => b k y.val := fun k =>
    (b k).continuous.comp Units.continuous_val
  have hcomp : ∀ k, HasCompactSupport fun y : G n => b k y.val := by
    intro k
    have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' Metric.closedBall (1 : Mat n) r) :=
      (hemb.isInducing.isCompact_preimage_iff (fun x hx => hrange x (hr hx))).2
        (isCompact_closedBall _ _)
    refine HasCompactSupport.intro hK ?_
    intro y hy
    have : y.val ∉ Function.support (b k) := by
      rw [(b k).support_eq]
      intro h
      exact hy (Metric.closedBall_subset_closedBall (hbOut k) (Metric.ball_subset_closedBall h))
    simpa using this
  have hpos : ∀ k, 0 < ∫ y : G n, b k y.val ∂μ := by
    intro k
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : G n)) (hcont k)
      (hcomp k) (fun y => (b k).nonneg) ?_
    simpa using (b k).one_of_mem_closedBall (x := (1 : Mat n)) (by simp [(b k).rIn_pos.le]) |>.symm ▸ one_ne_zero
  refine ⟨fun k x => (∫ y : G n, b k y.val ∂μ)⁻¹ * b k x, ?_, ?_, ?_, ?_⟩
  · intro k
    have hts : tsupport (b k) ⊆ Metric.closedBall (1 : Mat n) r := by
      exact (b k).tsupport_eq.le.trans (Metric.closedBall_subset_closedBall (hbOut k))
    have hsub : tsupport (fun x => (∫ y : G n, b k y.val ∂μ)⁻¹ * b k x) ⊆ tsupport (b k) :=
      closure_mono fun x hx h => hx (by simp [h])
    refine ⟨contDiff_const.mul (b k).contDiff, ((b k).hasCompactSupport).mul_left, ?_⟩
    exact hsub.trans (hts.trans hr)
  · intro k y
    exact mul_nonneg (inv_nonneg.2 (hpos k).le) (b k).nonneg
  · intro k
    simp only []
    rw [integral_const_mul, inv_mul_cancel₀ (hpos k).ne']
  · intro N hN
    have himg : (Units.val : G n → Mat n) '' N ∈ 𝓝 (1 : Mat n) := by
      have := hemb.isOpenMap.image_mem_nhds hN
      simpa using this
    obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.1 himg
    obtain ⟨K, hK⟩ := exists_nat_gt (r / ε)
    filter_upwards [eventually_ge_atTop K] with k hk y hy
    have hne : b k y.val ≠ 0 := right_ne_zero_of_mul hy
    have hsupp : y.val ∈ Metric.ball (1 : Mat n) (b k).rOut := by
      rw [← (b k).support_eq]
      exact hne
    have hlt : (b k).rOut < ε := by
      have h1 : r / ε < (k : ℝ) + 1 := by
        have : (K : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have h2 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      show r / ((k : ℝ) + 1) < ε
      rw [div_lt_iff₀ h2]
      rw [div_lt_iff₀ hε0] at h1
      linarith
    obtain ⟨z, hz, e⟩ := hε (Metric.ball_subset_ball hlt.le hsupp)
    have : z = y := hemb.injective e
    exact this ▸ hz

end GlobalTheory.CompanionTheory.PresSobA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryRootMap
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapRoot

section Cont

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem continuous_of_v_eq (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) : Continuous σ := by
  refine continuous_of_continuousAt_zero σ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero L _).tendsto_iff (Valued.hasBasis_nhds_zero L _)]
  refine fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rwa [show Valued.v.restrict (σ x) = Valued.v.restrict x from (Valuation.restrict_inj _).2 (hv x)]

theorem continuous_nU_val : Continuous fun x : L => ((nU x : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact continuous_id | exact continuous_const

theorem continuous_nU_inv_val :
    Continuous fun x : L => (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU, Units.inv_mk] <;>
    first | exact continuous_id | exact continuous_const | exact continuous_neg

theorem continuous_partner_nU (σ : L →+* L) (hc : Continuous σ) :
    Continuous fun x : L => partner σ (nU x) := by
  unfold partner cT
  exact (continuous_const.matrix_mul
    (continuous_nU_inv_val.matrix_map hc).matrix_transpose).matrix_mul continuous_const

theorem continuous_uR_val (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ) (a : ℕ)
    (h : 2 * (a + 2) ≤ n) :
    Continuous fun x : L => (((uR σ hσ a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  simp only [uR, rootHom_val, blockM]
  exact (continuous_const.add (((continuous_const.matrix_mul
    (continuous_nU_val.sub continuous_const))).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul
    ((continuous_partner_nU σ hc).sub continuous_const)).matrix_mul continuous_const)

theorem uR_neg (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) :
    (uR σ hσ a h x)⁻¹ = uR σ hσ a h (-x) := by
  have h0 : uR σ hσ a h (0 : L) = 1 := by
    have e : nU (0 : L) = 1 := by
      ext p r; fin_cases p <;> fin_cases r <;> simp [nU]
    simp only [uR, e, map_one]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← uR_add, add_neg_cancel, h0]

theorem continuous_uR : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    Continuous (uR σ hU.1 a h : L → GU σ n) := by
  intro L _ _ ϖ σ q n hU a h
  have hc : Continuous σ := continuous_of_v_eq σ hU.2.1
  refine Continuous.subtype_mk (f := fun x => ((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)) ?_ _
  refine Units.continuous_iff.2 ⟨continuous_uR_val σ hU.1 hc a h, ?_⟩
  have e : ∀ x : L, ((((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((uR σ hU.1 a h (-x) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := fun x => by
    rw [← uR_neg, Subgroup.coe_inv]
  simp only [e]
  exact (continuous_uR_val σ hU.1 hc a h).comp continuous_neg

end Cont

end GlobalTheory.CompanionTheory.SwapRoot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContraction
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.DomGLVal
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.DomUnitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {σ : L →+* L}
variable (D : CassData (GU σ n))

theorem mem_J_iff (hJ : D.J = IwU σ n) (x : GU σ n) : x ∈ D.J ↔ (x : GL (Fin n) L) ∈ IwGL L n := by
  rw [hJ, IwU, Subgroup.mem_subgroupOf]

theorem upper_facts (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    {x : GU σ n} (hx : x ∈ D.J ⊓ D.N) :
    IsUniM (x : GL (Fin n) L) ∧ IsUniM (x : GL (Fin n) L)⁻¹ ∧ Integ (x : GL (Fin n) L) ∧
      Integ (x : GL (Fin n) L)⁻¹ := by
  have h := (mem_IwGL_iff _).1 ((mem_J_iff D hJ x).1 hx.1)
  exact ⟨(hN _).1 hx.2, (hN _).1 (inv_mem hx.2), h.1, h.2⟩

theorem lower_facts (hJ : D.J = IwU σ n) (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    {x : GU σ n} (hx : x ∈ D.J ⊓ D.Nm) :
    IsLowUniM (x : GL (Fin n) L) ∧ IsLowUniM (x : GL (Fin n) L)⁻¹ ∧ Integ (x : GL (Fin n) L) ∧
      Integ (x : GL (Fin n) L)⁻¹ := by
  have h := (mem_IwGL_iff _).1 ((mem_J_iff D hJ x).1 hx.1)
  exact ⟨(hNm _).1 hx.2, (hNm _).1 (inv_mem hx.2), h.1, h.2⟩

theorem dom_core (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    (hT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) (τ : GU σ n) (hτ : τ ∈ D.T)
    (hmono : ∀ i j : Fin n, i ≤ j → ordL (((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
      ordL (((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)) :
    (∀ x ∈ D.J ⊓ D.N, τ * x * τ⁻¹ ∈ D.J ⊓ D.N) ∧ (∀ x ∈ D.J ⊓ D.Nm, τ⁻¹ * x * τ ∈ D.J ⊓ D.Nm) ∧
      ∀ x ∈ D.J ⊓ D.T, τ * x * τ⁻¹ ∈ D.J ⊓ D.T ∧ τ⁻¹ * x * τ ∈ D.J ⊓ D.T := by
  obtain ⟨d, hd, hne, hdd⟩ : ∃ d : Fin n → L, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = d i :=
    ⟨_, (diag_data ((hT _).1 hτ)).1, (diag_data ((hT _).1 hτ)).2, fun _ => rfl⟩
  have hmono' : ∀ i j, i ≤ j → ordL (d j) ≤ ordL (d i) := by simpa only [hdd] using hmono
  have hle : ∀ i j, i ≤ j → Valued.v (d i) * Valued.v (d j)⁻¹ ≤ 1 := fun i j hij =>
    ratio_le (hne j) (v_le_of_ordL_le (hne j) (hne i) (hmono' i j hij))
  have hle' : ∀ i j, j ≤ i → Valued.v (d i)⁻¹ * Valued.v ((d j)⁻¹)⁻¹ ≤ 1 := fun i j hij => by
    rw [inv_inv, mul_comm]
    exact hle j i hij
  have hs' := val_inv_diag hne hd
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨u1, u2, i1, i2⟩ := upper_facts D hJ hN hx
    have := up_mem hne hd u1 u2 (fun i j hij => valuation_triple_mul_le (hle i j hij.le) (i1.1 i j))
      (fun i j hij => valuation_triple_mul_le (hle i j hij.le) (i2.1 i j))
    exact ⟨(mem_J_iff D hJ _).2 this.1, (hN _).2 this.2⟩
  · obtain ⟨l1, l2, i1, i2⟩ := lower_facts D hJ hNm hx
    have := low_mem (fun i => inv_ne_zero (hne i)) hs' l1 l2
      (fun i j hij => valuation_triple_mul_lt_one (hle' i j hij.le) (i1.2 i j hij))
      (fun i j hij => valuation_triple_mul_lt_one (hle' i j hij.le) (i2.2 i j hij))
    rw [inv_inv] at this
    exact ⟨(mem_J_iff D hJ _).2 this.1, (hNm _).2 this.2⟩
  · obtain ⟨hdx, -⟩ := diag_data ((hT _).1 hx.2)
    have hc : τ * x = x * τ := by
      apply Subtype.ext
      apply Units.ext
      show ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
      rw [hd, hdx, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have e1 : τ * x * τ⁻¹ = x := by rw [hc, mul_inv_cancel_right]
    have e2 : τ⁻¹ * x * τ = x := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    rw [e1, e2]
    exact ⟨hx, hx⟩

theorem strict_core (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    (hT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) (τ : GU σ n) (hτ : τ ∈ D.T)
    (hst : IsStrictDom (τ : GL (Fin n) L)) :
    (∀ x ∈ D.N, ∃ j : ℕ, τ ^ j * x * (τ ^ j)⁻¹ ∈ D.J ⊓ D.N) ∧
      ∀ U : Set (GU σ n), IsOpen U → (1 : GU σ n) ∈ U →
        ∃ j : ℕ, ∀ x ∈ D.J ⊓ D.Nm, (τ ^ j)⁻¹ * x * τ ^ j ∈ U := by
  obtain ⟨d, hd, hne, hdd⟩ : ∃ d : Fin n → L, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = d i :=
    ⟨_, (diag_data ((hT _).1 hτ)).1, (diag_data ((hT _).1 hτ)).2, fun _ => rfl⟩
  have hst' : ∀ i j, i < j → ordL (d j) < ordL (d i) := by
    intro i j hij
    have := hst i j hij
    rwa [hdd, hdd] at this
  have hr : ∀ i j, i < j → ∀ m : ℕ, Valued.v (d i ^ m) * Valued.v (d j ^ m)⁻¹ ≤ cc ^ m := fun i j hij m =>
    ratio_pow_le (hne j) (v_le_of_ordL_lt (hne j) (hne i) (hst' i j hij)) m
  have hpow : ∀ m : ℕ, (((τ ^ m : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => d i ^ m) := fun m => by
    rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hd, Matrix.diagonal_pow]
    rfl
  have hnep : ∀ m : ℕ, ∀ i, d i ^ m ≠ 0 := fun m i => pow_ne_zero _ (hne i)
  refine ⟨fun x hx => ?_, fun U hU h1 => ?_⟩
  · have u1 : IsUniM (x : GL (Fin n) L) := (hN _).1 hx
    have u2 : IsUniM (x : GL (Fin n) L)⁻¹ := (hN _).1 (inv_mem hx)
    choose f hf using fun p : Fin n × Fin n =>
      exists_pow_mul_le (Valued.v (((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.1 p.2))
    choose f' hf' using fun p : Fin n × Fin n =>
      exists_pow_mul_le (Valued.v ((((x : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.1 p.2))
    have hM : ∀ p, f p ≤ Finset.univ.sup f ⊔ Finset.univ.sup f' := fun p =>
      le_sup_of_le_left (Finset.le_sup (Finset.mem_univ p))
    have hM' : ∀ p, f' p ≤ Finset.univ.sup f ⊔ Finset.univ.sup f' := fun p =>
      le_sup_of_le_right (Finset.le_sup (Finset.mem_univ p))
    generalize Finset.univ.sup f ⊔ Finset.univ.sup f' = M at hM hM'
    have key : ∀ (y : L) (i j : Fin n), i < j → cc ^ M * Valued.v y ≤ 1 →
        Valued.v (d i ^ M * y * (d j ^ M)⁻¹) ≤ 1 := by
      intro y i j hij hy
      rw [map_mul, map_mul, mul_right_comm]
      have h2 := hr i j hij M
      calc Valued.v (d i ^ M) * Valued.v (d j ^ M)⁻¹ * Valued.v y ≤ cc ^ M * Valued.v y := by gcongr
        _ ≤ 1 := hy
    have := up_mem (hnep M) (hpow M) u1 u2
      (fun i j hij => key _ i j hij (hf (i, j) M (hM _)))
      (fun i j hij => key _ i j hij (hf' (i, j) M (hM' _)))
    exact ⟨M, (mem_J_iff D hJ _).2 this.1, (hN _).2 this.2⟩
  · obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
    obtain ⟨m, hm⟩ := open_shrink W hW h1
    refine ⟨m, fun x hx => ?_⟩
    obtain ⟨l1, l2, i1, i2⟩ := lower_facts D hJ hNm hx
    have hs := val_inv_diag (hnep m) (hpow m)
    have hes : ∀ i, (d i ^ m)⁻¹ ≠ 0 := fun i => inv_ne_zero (hnep m i)
    have hb : ∀ a b, b < a → Valued.v (d a ^ m)⁻¹ * Valued.v ((d b ^ m)⁻¹)⁻¹ ≤ cc ^ m := fun a b hab => by
      rw [inv_inv, mul_comm]
      exact hr b a hab m
    have c1 := low_close hes hs l1 (B := cc ^ m) (fun a b hab => valuation_triple_mul_le (hb a b hab) (i1.1 a b))
    have c2 := low_close hes hs l2 (B := cc ^ m) (fun a b hab => valuation_triple_mul_le (hb a b hab) (i2.1 a b))
    have := hm _ c1 (by rw [GlobalTheory.CompanionTheory.DomGLVal.conj_inv]; exact c2)
    rw [inv_inv] at this
    exact this

theorem domU : PositivityTheory.SphericalProduct.DomU := by
  intro L _ _ _ ϖ σ q _ n D hJ hN hNm hT t
  refine ⟨fun h => dom_core D hJ hN hNm hT t t.2 h, fun h => ⟨?_, strict_core D hJ hN hNm hT t t.2 h⟩⟩
  exact dom_core D hJ hN hNm hT t t.2 fun i j hij => by
    rcases hij.lt_or_eq with hij | rfl
    · exact (h i j hij).le
    · exact le_rfl

end GlobalTheory.CompanionTheory.DomUnitary
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvalueAdjointFacts
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem riesz_of_relation {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (S : Submodule ℂ H) (R : H → V → Prop) (C : ℝ)
    (hex : ∀ x ∈ closure (S : Set H), ∃ w, R x w ∧ ‖w‖ ≤ C * ‖x‖)
    (huniq : ∀ x w w', R x w → R x w' → w = w')
    (hlin : ∀ (a : ℂ) x y w w', R x w → R y w' → R (a • x + y) (a • w + w')) (v : V) :
    ∃ κ ∈ closure (S : Set H), ∀ x ∈ S, ∀ w, R x w → ⟪κ, x⟫_ℂ = ⟪v, w⟫_ℂ := by
  classical
  have hK : ∀ x : S.topologicalClosure, ∃ w, R (x : H) w ∧ ‖w‖ ≤ C * ‖(x : H)‖ := fun x =>
    hex x x.2
  choose l hl hb using hK
  have hl0 : l 0 = 0 := by
    have := hb 0
    simpa using this
  let L₀ : S.topologicalClosure →ₗ[ℂ] V :=
    { toFun := l
      map_add' := fun x y => by
        have := hlin 1 x y (l x) (l y) (hl x) (hl y)
        exact huniq _ _ _ (hl (x + y)) (by simpa using this)
      map_smul' := fun a x => by
        have := hlin a x 0 (l x) (l 0) (hl x) (hl 0)
        exact huniq _ _ _ (hl (a • x)) (by simpa [hl0] using this) }
  let L : S.topologicalClosure →L[ℂ] V := L₀.mkContinuous C (fun x => hb x)
  refine ⟨(ContinuousLinearMap.adjoint L v : S.topologicalClosure), ?_, ?_⟩
  · exact (ContinuousLinearMap.adjoint L v).2
  · intro x hx w hw
    have hxk : x ∈ S.topologicalClosure := S.le_topologicalClosure hx
    have hw' : w = l ⟨x, hxk⟩ := huniq x w _ hw (hl ⟨x, hxk⟩)
    have := ContinuousLinearMap.adjoint_inner_left L (⟨x, hxk⟩ : S.topologicalClosure) v
    rw [hw']
    exact this

theorem Rw_zero {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Bool × Fin n × Fin n)) : Rw w (0 : Mat n → V) = 0 := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    funext g
    simp [Rw, ih, Rd]

theorem sob_zero {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Sob μ (0 : Mat n → V) := by
  refine ⟨contDiffOn_const, fun w => ?_⟩
  rw [Rw_zero]
  exact MemLp.zero

theorem evAdj : EvAdj := by
  intro n _ _ μ _ E _ Ω T F c hS h hh v
  obtain ⟨hLg, hUn, hRC, hSob, hAlg, hWS, hWC, hCS, hSm, hPW, hM, hsym, hres, hinv, hOm, hbd⟩ := hS
  obtain ⟨C, hC⟩ := hSm n μ E Ω T F hLg hUn hRC hSob hAlg hCS hOm h hh
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  obtain ⟨hc1, hc2, -⟩ := hCl n μ E.V hUn
  have hmem : ∀ {f : Mat n → E.V}, Sob μ f → MemLp (fun y : G n => f y.val) 2 μ := fun hf => hf.2 []
  have hsum : ∀ (a : ℂ) (f f' : Mat n → E.V), Sob μ f → Sob μ f' → Sob μ (a • f + f') := fun a f f' hf hf' =>
    ((hOps n μ E.V hLg hUn hRC f hf).2.2.2.1 a f' hf').1
  have hsec : ∀ (a : ℂ) (f f' : Mat n → E.V), IsSec E f → IsSec E f' → IsSec E (a • f + f') := by
    intro a f f' hf hf' g hg k
    simp [hf g hg k, hf' g hg k]
  have h0 : cls μ (0 : Mat n → E.V) = 0 := by
    simpa using hc2 (-1) 0 0 (hmem (sob_zero μ E.V)) (hmem (sob_zero μ E.V))
  let S : Submodule ℂ (Lp E.V 2 μ) :=
    { carrier := secCls μ E
      zero_mem' := ⟨0, sob_zero μ E.V, fun g _ k => by simp, h0⟩
      add_mem' := by
        rintro _ _ ⟨f, hf, hs, rfl⟩ ⟨f', hf', hs', rfl⟩
        exact ⟨1 • f + f', hsum 1 f f' hf hf', hsec 1 f f' hs hs', by
          simpa using hc2 1 f f' (hmem hf) (hmem hf')⟩
      smul_mem' := by
        rintro a _ ⟨f, hf, hs, rfl⟩
        refine ⟨a • f + 0, hsum a f 0 hf (sob_zero μ E.V), hsec a f 0 hs (fun g _ k => by simp), ?_⟩
        have := hc2 a f 0 (hmem hf) (hmem (sob_zero μ E.V))
        simpa [h0] using this }
  let R : Lp E.V 2 μ → E.V → Prop := fun x w =>
    ∃ f', Sob μ f' ∧ IsSec E f' ∧ cls μ f' = F.Φ h x ∧ f' 1 = w
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  obtain ⟨κ, hκ, hrep⟩ := riesz_of_relation S R C
    (fun x hx => by
      obtain ⟨f', a, b, d, e⟩ := hC x hx
      exact ⟨f' 1, ⟨f', a, b, d, rfl⟩, e⟩)
    (by
      rintro x _ _ ⟨f, hf, -, hcf, rfl⟩ ⟨f', hf', -, hcf', rfl⟩
      exact hc1 f f' hf.1.continuousOn hf'.1.continuousOn (hmem hf) (hmem hf') (hcf.trans hcf'.symm) 1 h1)
    (by
      rintro a x y _ _ ⟨f, hf, hs, hcf, rfl⟩ ⟨f', hf', hs', hcf', rfl⟩
      refine ⟨a • f + f', hsum a f f' hf hf', hsec a f f' hs hs', ?_, rfl⟩
      rw [hc2 a f f' (hmem hf) (hmem hf'), hcf, hcf', map_add (f := _), map_smul]) v
  refine ⟨κ, hκ, fun φ f' hφ hφs hf' hf's hcl => ?_⟩
  exact hrep (cls μ φ) ⟨φ, hφ, hφs, rfl⟩ (f' 1) ⟨f', hf', hf's, hcl, rfl⟩

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensitySmoothStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.energy_density_smooth : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (u : ℝ → Mat n → W), Sm u → Sm (dens u) ∧ ∀ (X : Mat n) (v : ℝ → Mat n → W), Sm v → Sm fun s y => ⟪Rt X u s y, v s y⟫_ℝ := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | exact GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusOnSobolev
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

theorem phi_keeps_sections : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ) (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T),
      LgFacts → Unimod → RCalc → SobG → CalcSteps →
      (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) →
      ∀ (h : C₀(ℝ, ℂ)) (f : Mat n → E.V), Sob μ f → IsSec E f →
        ∃ f', Sob μ f' ∧ IsSec E f' ∧ cls μ f' = F.Φ h (cls μ f) := by
  intro n _ _ μ _ E
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hL hU hR hSG hCS hΩ h f hf hs
  obtain ⟨-, -, -, -, hC, hO, hCp, -, hP, hCT, -, hFr, hOF, hI, hD⟩ := hCS
  have hrep : ∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x :=
    (hCT n μ E.V hL hU hR hSG hP hFr hC hO hCp hOF hI hD).1
  obtain ⟨f', hf', hcl, -⟩ := GlobalTheory.CompanionTheory.WaveFc.Asm.pres hC hO hL hU hR hSG hP F hrep hΩ h hf
  exact ⟨f', hf', GlobalTheory.CompanionTheory.WaveFc.Asm.sec_pres E hC hO hL hU hR F hrep hΩ h hf hs hf' hcl, hcl⟩

end GlobalTheory.CompanionTheory.FcSmooth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValuePermInvariant
section
theorem GlobalTheory.CompanionTheory.ModelS.gelfVal_perm :
    ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ),
      GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k :=
  fun _ χ σ k => GlobalTheory.CompanionTheory.WaveMult.gelfVal_comp_perm χ σ k
end

