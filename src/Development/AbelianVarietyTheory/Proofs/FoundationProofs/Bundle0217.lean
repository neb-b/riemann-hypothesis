module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0211
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAtStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  first | exact @GlobalTheory.NabStab.polyAction_mem_locP_nabStd | exact GlobalTheory.NabStab.polyAction_mem_locP_nabStd | (intros; apply GlobalTheory.NabStab.polyAction_mem_locP_nabStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.Minor

open ReciprocityTheory.ChartRestriction.G Matrix

abbrev Incr (a d : ℕ) : Type := {s : Fin a → Fin d // StrictMono s}

noncomputable def toIncr {a d : ℕ} (S : Set.powersetCard (Fin d) a) : Incr a d :=
  ⟨GlobalTheory.subsetEnum S, (S.1.orderEmbOfFin S.2).strictMono⟩

theorem toIncr_bijective {a d : ℕ} : Function.Bijective (toIncr (a := a) (d := d)) := by
  constructor
  · intro S S' h
    have h1 : GlobalTheory.subsetEnum S = GlobalTheory.subsetEnum S' := congrArg Subtype.val h
    have h2 : (S.1 : Set (Fin d)) = S'.1 := by
      rw [← GlobalTheory.range_subsetEnum S, ← GlobalTheory.range_subsetEnum S', h1]
    exact Subtype.ext (Finset.coe_injective h2)
  · intro s
    have hc : (Finset.univ.image s.1).card = a := by
      rw [Finset.card_image_of_injective _ s.2.injective]; simp
    refine ⟨⟨Finset.univ.image s.1, hc⟩, Subtype.ext ?_⟩
    exact (Finset.orderEmbOfFin_unique hc (fun x => by simp) s.2).symm

theorem det_submatrix_mul {R l o : Type*} [CommRing R] {a d : ℕ}
    (A : Matrix l (Fin d) R) (B : Matrix (Fin d) o R) (r : Fin a → l) (c : Fin a → o) :
    ((A * B).submatrix r c).det = ∑ s : Incr a d, (A.submatrix r s.1).det * (B.submatrix s.1 c).det := by
  rw [GlobalTheory.det_submatrix_mul_eq_sum_minors]
  exact Fintype.sum_bijective toIncr toIncr_bijective _ _ fun S => rfl

theorem det_submatrix_one {a d : ℕ} (s s' : Incr a d) :
    ((1 : Matrix (Fin d) (Fin d) ℂ).submatrix s.1 s'.1).det = if s = s' then 1 else 0 := by
  obtain ⟨I, rfl⟩ := toIncr_bijective.2 s
  obtain ⟨J, rfl⟩ := toIncr_bijective.2 s'
  split_ifs with h
  · rw [← h, submatrix_one _ (toIncr I).2.injective, det_one]
  · have h' : I ≠ J := fun e => h (by rw [e])
    obtain ⟨x, hxI, hxJ⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne I J).mp h'
    have h1 : x ∈ Set.range (GlobalTheory.subsetEnum I) := by rw [GlobalTheory.range_subsetEnum]; exact hxI
    have h2 : x ∉ Set.range (GlobalTheory.subsetEnum J) := by rw [GlobalTheory.range_subsetEnum]; exact hxJ
    obtain ⟨i, rfl⟩ := h1
    exact det_eq_zero_of_row_eq_zero i fun j => one_apply_ne fun e => h2 ⟨j, e.symm⟩

theorem minors_orth {a d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (s' s'' : Incr a d) :
    ∑ s : Incr a d, (u.submatrix s'.1 s.1).det * star (u.submatrix s''.1 s.1).det = if s' = s'' then 1 else 0 := by
  rw [← det_submatrix_one, ← (Matrix.mem_unitaryGroup_iff.1 hu), det_submatrix_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← det_conjTranspose, conjTranspose_submatrix, star_eq_conjTranspose]

theorem sum_norm_sq_eq {ι : Type*} [Fintype ι] (K : ι → ι → ℂ)
    (hK : ∀ i j, ∑ t, K i t * star (K j t) = if i = j then 1 else 0) (v : ι → ℂ) :
    ∑ t, ‖∑ i, K i t * v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  have h (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_sum, h, star_sum, star_mul', Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ j, ∑ t, K i t * v i * (star (K j t) * star (v j)) = (if i = j then 1 else 0) * (v i * star (v j)) := by
    intro j
    rw [← hK, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem prod_prod_sum {R T S : Type*} [CommSemiring R] [Fintype T] [DecidableEq T] [Fintype S] (n : T → ℕ)
    (f : ∀ τ, Fin (n τ) → S → R) :
    ∏ τ, ∏ j, ∑ s, f τ j s = ∑ t : ∀ τ, Fin (n τ) → S, ∏ τ, ∏ j, f τ j (t τ j) := by
  simp only [Fintype.prod_sum]

theorem polyDeriv_subst {σ κ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [Fintype κ] {F : W → ℂ}
    (hF : ContDiff ℂ (⊤ : ℕ∞) F) (s : σ → κ → ℂ)
    (j : σ → κ → σ) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hΦ : ∀ l, Φ (MvPolynomial.X l) = ∑ k, MvPolynomial.C (s l k) * MvPolynomial.X (j l k))
    (u : σ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (Φ P) u F x = I2.polyDeriv P (fun l => ∑ k, s l k • u (j l k)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    have h : (MvPolynomial.C a : MvPolynomial σ ℂ) = a • MvPolynomial.monomial 0 1 := by
      simp [MvPolynomial.smul_eq_C_mul]
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, h]
    simp [I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
      -MvPolynomial.monomial_zero']
  | add P Q hP hQ => simp only [map_add (f := _), I2.polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hΦ, Finset.mul_sum, I2.jof_polyDeriv_sum, GlobalTheory.ThFr.polyDeriv_mul_X hF, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, MvPolynomial.C_mul', I2.polyDeriv_smul, GlobalTheory.ThFr.polyDeriv_mul_X hF, funext hP]
    simp

variable {D : D7} {a d : ℕ}

theorem applyAt0_eq (P : MvPolynomial (GL3Theta.Idx D a d) ℂ) (G : VC D a d → ℂ) :
    GL3Theta.applyAt0 D P G = I2.polyDeriv P (coordV D) G 0 := by
  unfold GL3Theta.applyAt0 I2.polyDeriv taylor
  refine Finset.sum_congr rfl fun α _ => ?_
  have h : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [mul_assoc, mul_div_cancel₀ _ h]
  rfl

theorem applyAt0_comp {κ : Type} [Fintype κ] {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (A : VC D a d →ₗ[ℂ] VC D a d) (s : GL3Theta.Idx D a d → κ → ℂ) (j : GL3Theta.Idx D a d → κ → GL3Theta.Idx D a d)
    (hA : ∀ l, A (coordV D l) = ∑ k, s l k • coordV D (j l k)) (P : MvPolynomial (GL3Theta.Idx D a d) ℂ) :
    GL3Theta.applyAt0 D P (fun z => G (A z)) = GL3Theta.applyAt0 D
      (MvPolynomial.aeval (fun l => ∑ k, MvPolynomial.C (s l k) * (MvPolynomial.X (j l k) : MvPolynomial _ ℂ)) P) G := by
  have hG' : ContDiff ℂ (⊤ : ℕ∞) G := contDiff_infty.2 fun k => I2.contDiff_of_differentiable_fd hG k
  rw [applyAt0_eq, applyAt0_eq, polyDeriv_subst hG' s j _ (fun l => MvPolynomial.aeval_X _ l)]
  have h := GlobalTheory.Jet.polyDeriv_comp_clm P (coordV D) hG (LinearMap.toContinuousLinearMap A) 0
  rw [map_zero] at h
  refine h.trans ?_
  congr 1
  funext l
  exact hA l

def mulR (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) : VC D a d →ₗ[ℂ] VC D a d where
  toFun z := fun τ i j => ∑ k, z τ i k * u τ k j
  map_add' x y := by
    funext τ i j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j
    simp [Finset.mul_sum, mul_assoc]

def mulL (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) : VC D a d →ₗ[ℂ] VC D a d where
  toFun z := fun τ i j => ∑ k, u τ i k * z τ k j
  map_add' x y := by
    funext τ i j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j
    simp [Finset.mul_sum, mul_left_comm]

theorem mulR_coordV (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (l : GL3Theta.Idx D a d) :
    mulR u (coordV D l) = ∑ k, u l.1 l.2.2 k • coordV D (l.1, l.2.1, k) := by
  obtain ⟨τ, i, j⟩ := l
  funext τ' i' j'
  by_cases h1 : τ' = τ <;> by_cases h2 : i' = i <;>
    simp [mulR, coordV, Finset.sum_apply, h1, h2]

theorem mulL_coordV (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (l : GL3Theta.Idx D a d) :
    mulL u (coordV D l) = ∑ k, u l.1 k l.2.1 • coordV D (l.1, k, l.2.2) := by
  obtain ⟨τ, i, j⟩ := l
  funext τ' i' j'
  by_cases h1 : τ' = τ <;> by_cases h2 : j' = j <;>
    simp [mulL, coordV, Finset.sum_apply, h1, h2]

theorem applyAt0_minorPol_mulR {n : D.what₂.Tau → ℕ} {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D t) (fun z => G (mulR u z)) =
      (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G := by
  rw [applyAt0_comp hG (mulR u) (fun l k => u l.1 l.2.2 k) (fun l k => (l.1, l.2.1, k)) (mulR_coordV u),
    applyAt0_eq, applyAt0_eq, ← I2.polyDeriv_smul]
  congr 1
  unfold minorPol
  rw [map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_pow, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [AlgHom.map_det, RingHom.map_det, mul_comm, ← det_transpose (RingHom.mapMatrix _ _), ← det_mul]
  congr 1
  ext1 i i'
  simp [Matrix.mul_apply, mul_comm]

theorem applyAt0_minorPol_mulL {n : D.what₂.Tau → ℕ} {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (t : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D t) (fun z => G (mulL u z)) =
      ∑ t' : Tup D a d n, (∏ τ, ∏ j, ((u τ).submatrix (t' τ j).1 (t τ j).1).det) *
        GL3Theta.applyAt0 D (minorPol D t') G := by
  rw [applyAt0_comp hG (mulL u) (fun l k => u l.1 k l.2.1) (fun l k => (l.1, k, l.2.2)) (mulL_coordV u)]
  simp only [applyAt0_eq, ← I2.polyDeriv_smul]
  rw [← I2.jof_polyDeriv_sum]
  congr 1
  unfold minorPol
  simp only [MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  rw [← prod_prod_sum n (fun τ j (s : Incr a d) => MvPolynomial.C ((u τ).submatrix s.1 (t τ j).1).det *
    (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s.1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det)]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  have h := det_submatrix_mul ((u τ)ᵀ.map (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ))
    (Matrix.of fun (i : Fin d) (i' : Fin a) => (MvPolynomial.X (τ, i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ))
    (t τ j).1 id
  rw [AlgHom.map_det]
  refine Eq.trans ?_ (h.trans (Finset.sum_congr rfl fun s _ => ?_))
  · congr 1
    ext1 i i'
    simp [Matrix.mul_apply]
  · rw [RingHom.map_det, ← det_transpose (RingHom.mapMatrix _ _)]
    rfl

end GlobalTheory.NormSum.Minor


open GlobalTheory.NormSum.Minor ReciprocityTheory.ChartRestriction.G in
theorem GlobalTheory.NormSum.applyAt0_minorPol_linear : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ), Differentiable ℂ G → (∀ (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n), GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (Matrix.of (z τ) * u τ : Matrix _ _ ℂ))) = (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G) ∧ (∀ (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ), (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ) → ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ)))‖ ^ 2 = ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) G‖ ^ 2) ∧ (∀ (c : ℂ) P, GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G) ∧ ∀ G' P, Differentiable ℂ G' → GL3Theta.applyAt0 D P (G + G') = GL3Theta.applyAt0 D P G + GL3Theta.applyAt0 D P G' := by
  intro D a d n G hG
  refine ⟨fun u t => applyAt0_minorPol_mulR hG u t, fun u hu => ?_, fun c P => ?_, fun G' P hG' => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) (sum_norm_sq_eq
      (fun t' t : Tup D a d n => ∏ τ, ∏ j, ((u τ).submatrix (t' τ j).1 (t τ j).1).det) (fun t' t'' => ?_) _)
    · rw [← applyAt0_minorPol_mulL hG u t]
      rfl
    · simp only [star_prod, ← Finset.prod_mul_distrib]
      rw [← prod_prod_sum n (fun τ j (s : Incr a d) => ((u τ).submatrix (t' τ j).1 s.1).det *
        star ((u τ).submatrix (t'' τ j).1 s.1).det)]
      simp only [fun τ => minors_orth (a := a) (hu τ)]
      split_ifs with h
      · simp [h]
      · obtain ⟨τ, hτ⟩ := Function.ne_iff.1 h
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hτ
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj))
  · rw [applyAt0_eq, applyAt0_eq, GlobalTheory.Jet.polyDeriv_smul_fun P _ hG]
  · rw [applyAt0_eq, applyAt0_eq, applyAt0_eq, GlobalTheory.Jet.polyDeriv_add_fun P _ hG hG']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AreaBoundedOfDiscrEqOne
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators UpperHalfPlane Real

namespace GlobalTheory.LatticeAreaBound

theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ}
    (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} fun w : ℂ => (w ^ (2 * k))⁻¹
  have h2 := tsum_subtype (L.lattice : Set ℂ) fun w : ℂ => (w ^ (2 * k))⁻¹
  simp only [eisG, PeriodPair.G, one_div]
  refine h1.trans (Eq.trans (tsum_congr fun w => ?_) h2.symm)
  rcases eq_or_ne w 0 with rfl | hw
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

theorem discr_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    TaylorLogMetric.discr Λ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_G L Λ h (by norm_num), eisG_eq_G L Λ h (by norm_num)]
  rfl

theorem area_eq {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    area Λ = ‖a‖ ^ 2 * τ.im := by
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  have hA : 0 < ‖a‖ ^ 2 * τ.im := by positivity
  have key : ∀ m n m' n' : ℤ,
      ((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im
        = ((n * m' - m * n' : ℤ) : ℝ) * (‖a‖ ^ 2 * τ.im) := fun m n m' n' => by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  refine IsLeast.csInf_eq ⟨⟨hA, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩, ?_⟩
  · rw [key, abs_of_nonneg (by simpa using hA.le)]
    simp
  · rintro b ⟨hb, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := (h _).1 h₁
    obtain ⟨m', n', rfl⟩ := (h _).1 h₂
    rw [key, abs_mul, abs_of_pos hA] at hb ⊢
    have h0 : n * m' - m * n' ≠ 0 := fun e => by simp [e] at hb
    have h1 : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs h0
    exact le_mul_of_one_le_left hA.le h1

theorem exists_bound_discriminant :
    ∃ C : ℝ, ∀ τ : ℍ, τ.im ^ 6 * ‖ModularForm.discriminant τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound CuspForm.discriminant
  refine ⟨C, fun τ => ?_⟩
  have h := hC τ
  have hy := τ.im_pos
  rw [CuspForm.coe_discriminant, show (((12 : ℤ) : ℝ) / 2 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, le_div_iff₀ (by positivity)] at h
  rwa [mul_comm]

theorem area_bounded_of_discr_eq_one : ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → 0 < area Λ ∧ area Λ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_discriminant
  refine ⟨max 1 ((2 * π) ^ 12 * C), lt_max_of_lt_left one_pos, ?_⟩
  rintro Λ ⟨w₁, w₂, hi, rfl⟩ hd
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ L.lattice := fun z => by
    rw [AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  rw [area_eq ha fun x => (hL x).trans (h x)]
  rw [discr_eq L _ hL, ← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h] at hd
  have e := congrArg norm hd
  rw [norm_mul, norm_pow, norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp [Real.pi_pos.le],
    norm_one, div_pow, div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity)] at e
  have hb : (‖a‖ ^ 2 * τ.im) ^ 6 ≤ (2 * π) ^ 12 * C := by
    calc (‖a‖ ^ 2 * τ.im) ^ 6 = ‖a‖ ^ 12 * τ.im ^ 6 := by ring
      _ = (2 * π) ^ 12 * (τ.im ^ 6 * ‖ModularForm.discriminant τ‖) := by rw [← e]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC τ) (by positivity)
  refine ⟨by positivity, ?_⟩
  rcases le_total (‖a‖ ^ 2 * τ.im) 1 with h1 | h1
  · exact le_max_of_le_left h1
  · exact le_max_of_le_right ((le_self_pow₀ h1 (by norm_num)).trans hb)

end GlobalTheory.LatticeAreaBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem branchesAlong_of_irreducible {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N) (lam : DomWeight N)
    (hirr : ∀ mu : DomWeight n, (smallRep ι mu).IsIrreducible)
    (hz : ∀ mu nu : DomWeight n, mu ≠ nu → ∀ φ : (smallRep ι mu).IntertwiningMap (smallRep ι nu), φ = 0) :
    BranchesAlong ι h lam := by
  classical
  have iso : Nonempty ((sumRep ι h lam).Equiv (resRep ι h lam)) := by
    refine GlobalTheory.nonempty_directSum_equiv_of_finrank_le ℂ H (Below h lam) _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1) _
      (fun mu => hirr mu.1) (fun i j hij => hz i.1 j.1 fun e => hij (Subtype.ext e)) (fun mu => ?_) (GlobalTheory.Branching.finrank_le_finrank_directSum_below n N h lam)
    obtain ⟨φ, hφ⟩ := GlobalTheory.Branching.exists_intertwining_ne_zero n N h lam mu.1 mu.2
    refine ⟨⟨φ.toLinearMap, fun y => φ.isIntertwining' (ι y)⟩, fun e => hφ ?_⟩
    have e' := congrArg Representation.IntertwiningMap.toLinearMap e
    exact Representation.IntertwiningMap.ext e'
  refine ⟨iso, fun mu => ?_⟩
  letI : Fintype (Below h lam) := Fintype.ofFinite _
  have hm := (GlobalTheory.IntertwinerSum.finrank_intertwiningMap_directSum ℂ H (Below h lam) _ _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1)
    (smallRep ι mu) (resRep ι h lam) iso).1
  have h0 : ∀ nu : DomWeight n, mu ≠ nu →
      Module.finrank ℂ ((smallRep ι mu).IntertwiningMap (smallRep ι nu)) = 0 := fun nu hne => by
    have : Subsingleton ((smallRep ι mu).IntertwiningMap (smallRep ι nu)) :=
      ⟨fun a b => (hz mu nu hne a).trans (hz mu nu hne b).symm⟩
    exact Module.finrank_zero_of_subsingleton
  refine ⟨fun hI => ?_, fun hI => ?_⟩
  · unfold mult
    rw [hm, Finset.sum_eq_single (⟨mu, hI⟩ : Below h lam)]
    · have := hirr mu
      exact Representation.IsIrreducible.finrank_intertwiningMap_self _
    · intro b _ hb
      exact h0 b.1 fun e => hb (Subtype.ext e.symm)
    · simp
  · unfold mult
    rw [hm]
    exact Finset.sum_eq_zero fun b _ => h0 b.1 fun e => hI (e ▸ b.2)

theorem intertwining_unitary_eq_zero (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (smallRep (unitaryIncl n) mu).IntertwiningMap (smallRep (unitaryIncl n) nu)) : φ = 0 := by
  have := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  obtain ⟨f, hf, h0⟩ := GlobalTheory.Branching.exists_ne_zero_map_eq_zero_of_weight_ne n mu nu hne
    ⟨φ.toLinearMap, fun g => LinearMap.ext fun f => GlobalTheory.Branching.intertwining_gl_of_unitary n mu nu φ g f⟩
  refine (Representation.IsIrreducible.injective_or_eq_zero φ).resolve_left fun hi => hf (hi ?_)
  rw [map_zero]; exact h0

theorem isIrreducible_smallRep_id (n : ℕ) (mu : DomWeight n) : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IsIrreducible := by
  have hU := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  let r : Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu) → Subrepresentation (smallRep (unitaryIncl n) mu) :=
    fun S => ⟨S.toSubmodule, fun u _ hv => S.apply_mem_toSubmodule (unitaryIncl n u) hv⟩
  have hnt : Nontrivial (Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (r S) with e | e
  · have e' := congrArg Subrepresentation.toSubmodule e
    exact Or.inl (Subrepresentation.ext e')
  · have e' := congrArg Subrepresentation.toSubmodule e
    exact Or.inr (Subrepresentation.ext e')

theorem intertwining_id_eq_zero (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IntertwiningMap (smallRep (MonoidHom.id (GL (Fin n) ℂ)) nu)) :
    φ = 0 := by
  have := intertwining_unitary_eq_zero n mu nu hne ⟨φ.toLinearMap, fun u => φ.isIntertwining' (unitaryIncl n u)⟩
  have e' := congrArg Representation.IntertwiningMap.toLinearMap this
  exact Representation.IntertwiningMap.ext e'

theorem branchesAlong_all (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) :
    BranchesAlong (MonoidHom.id (GL (Fin n) ℂ)) h lam ∧ BranchesAlong (unitaryIncl n) h lam :=
  ⟨branchesAlong_of_irreducible _ h lam (isIrreducible_smallRep_id n) (intertwining_id_eq_zero n),
    branchesAlong_of_irreducible _ h lam (isIrreducible_smallRep_unitary n) (intertwining_unitary_eq_zero n)⟩

theorem comult_of_irreducible {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N)
    (lam : DomWeight N) (hirr : ∀ mu : DomWeight n, (smallRep ι mu).IsIrreducible)
    (hz : ∀ mu nu : DomWeight n, mu ≠ nu → ∀ φ : (smallRep ι mu).IntertwiningMap (smallRep ι nu), φ = 0)
    (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep ι h lam).IntertwiningMap (smallRep ι mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep ι h lam).IntertwiningMap (smallRep ι mu)) = 0) := by
  classical
  have iso := (branchesAlong_of_irreducible ι h lam hirr hz).1
  letI : Fintype (Below h lam) := Fintype.ofFinite _
  have hm := (GlobalTheory.IntertwinerSum.finrank_intertwiningMap_directSum ℂ H (Below h lam) _ _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1)
    (smallRep ι mu) (resRep ι h lam) iso).2
  have h0 : ∀ nu : DomWeight n, nu ≠ mu →
      Module.finrank ℂ ((smallRep ι nu).IntertwiningMap (smallRep ι mu)) = 0 := fun nu hne => by
    have : Subsingleton ((smallRep ι nu).IntertwiningMap (smallRep ι mu)) :=
      ⟨fun a b => (hz nu mu hne a).trans (hz nu mu hne b).symm⟩
    exact Module.finrank_zero_of_subsingleton
  refine ⟨fun hI => ?_, fun hI => ?_⟩
  · rw [hm, Finset.sum_eq_single (⟨mu, hI⟩ : Below h lam)]
    · have := hirr mu
      exact Representation.IsIrreducible.finrank_intertwiningMap_self _
    · intro b _ hb
      exact h0 b.1 fun e => hb (Subtype.ext e)
    · simp
  · rw [hm]
    exact Finset.sum_eq_zero fun b _ => h0 b.1 fun e => hI (e ▸ b.2)

theorem comult_id (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
        (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
        (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) = 0) :=
  comult_of_irreducible _ h lam (isIrreducible_smallRep_id n) (intertwining_id_eq_zero n) mu

theorem comult_unitary (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep (unitaryIncl n) h lam).IntertwiningMap
        (smallRep (unitaryIncl n) mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep (unitaryIncl n) h lam).IntertwiningMap
        (smallRep (unitaryIncl n) mu)) = 0) :=
  comult_of_irreducible _ h lam (isIrreducible_smallRep_unitary n) (intertwining_unitary_eq_zero n) mu

end GlobalTheory.Branching

namespace GlobalTheory.Published

theorem weylBranching_holds : WeylBranching := fun n N h _ lam => GlobalTheory.Branching.branchesAlong_all n N h lam

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualFrLatticeHolds
section
namespace GlobalTheory

theorem dualFrLattice_holds : Formalism.L2.DIV.DualFrLattice :=
  GlobalTheory.DualLat.dualFr_lattice_and_hdual.1

end GlobalTheory
end

