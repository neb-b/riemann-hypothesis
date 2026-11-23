module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEqMulProdMinors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GardingVectorDerivativeEqGardingVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmVec

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

def fieldDeriv (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (P : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ) where
  toFun X g := fderiv ℝ φ g (-(P * X * P⁻¹) * g)
  map_add' X Y := by
    funext g
    simp only [Pi.add_apply, ← map_add (f := _), Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply, ← map_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]

theorem isTest_fderiv {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    IsTest fun g => fderiv ℝ φ g (Y * g) := by
  refine ⟨(hφ.1.fderiv_right (m := ∞) (le_of_eq rfl)).clm_apply (contDiff_const.mul contDiff_id), ?_⟩
  refine HasCompactSupport.intro hφ.2 fun g hg => ?_
  rw [fderiv_of_notMem_tsupport ℝ hg]; rfl

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem hasDerivAt_integral_translate (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}
    (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    HasDerivAt (fun t : ℝ => ∫ g : Formalism.REAL.UJ ε, φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
      ∂(Formalism.REAL.muG ε)) (gard ε σ (fun g => fderiv ℝ φ g (Y * g)) w) 0 := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := continuous_umat
  have hb := continuous_orbit hσ w
  have he : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) (Z * NormedSpace.exp (t • Z)) t :=
    fun Z t => hasDerivAt_exp_smul_const' Z t
  have hc : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • Z) :=
    fun Z => continuous_iff_continuousAt.2 fun t => (he Z t).continuousAt
  have hxy : ∀ t : ℝ, NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := fun t => by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_left.smul_left t).smul_right t), ← smul_add]
    simp
  have hC : IsCompact (Set.image2 (· * ·) ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1)
      (tsupport φ)) := ((isCompact_closedBall (0 : ℝ) 1).image (hc _)).mul hφ.2
  have hK := hemb.isCompact_preimage hC
  set K := (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹' (Set.image2 (· * ·)
    ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1) (tsupport φ)) with hKdef
  replace hK : IsCompact K := hK
  have hout : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, ∀ g ∉ K, NormedSpace.exp (t • Y) * umat g ∉ tsupport φ :=
    fun t ht g hg hm => hg ⟨_, ⟨t, ht, rfl⟩, _, hm, by
      show _ * (_ * _) = umat g
      rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]⟩
  set μ := Formalism.REAL.muG ε
  let F' : ℝ → Formalism.REAL.UJ ε → H := fun t g =>
    fderiv ℝ φ (NormedSpace.exp (t • Y) * umat g) (Y * NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
  have hF'c : Continuous fun p : ℝ × Formalism.REAL.UJ ε => F' p.1 p.2 := by
    have h1 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => NormedSpace.exp (p.1 • Y) := (hc Y).comp continuous_fst
    have h2 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => umat p.2 := hu.comp continuous_snd
    exact (((hφ.1.continuous_fderiv (by simp)).comp (h1.mul h2)).clm_apply
      ((continuous_const.mul h1).mul h2)).smul (hb.comp continuous_snd)
  obtain ⟨C, hCb⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hK).exists_bound_of_continuousOn hF'c.continuousOn
  have hint : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, Integrable
      (fun g : Formalism.REAL.UJ ε => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) μ := fun t ht =>
    Continuous.integrable_of_hasCompactSupport ((hφ.continuous.comp (continuous_const.mul hu)).smul hb)
      (HasCompactSupport.intro hK fun g hg => by
        rw [image_eq_zero_of_notMem_tsupport (hout t ht g hg), zero_smul])
  have e0 : F' 0 = fun g : Formalism.REAL.UJ ε => fderiv ℝ φ (umat g) (Y * umat g) • σ (umat g) w := by
    funext g; simp [F']
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun t g => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) (F' := F')
    (bound := K.indicator fun _ => C) (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    (by filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
        exact (hint t ht).aestronglyMeasurable)
    (hint 0 (Metric.mem_closedBall_self zero_le_one))
    (by rw [e0]; exact ((isTest_fderiv hφ Y).integrable hb).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g t ht => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg]; exact hCb (t, g) ⟨ht, hg⟩
      · rw [Set.indicator_of_notMem hg]
        simp [F', fderiv_of_notMem_tsupport ℝ (hout t ht g hg)])
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun g t _ =>
      (((hφ.1.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t ((he Y t).mul_const (umat g))).smul_const _)
  rw [e0] at key
  exact key.2

theorem dRep_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ φ, IsTest φ → ∃ ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ), ∀ X, IsTest (ψ X) ∧ (X ∈ lieG G → ∀ w, dRep (trRep σ P) X (gard ε σ φ w) = gard ε σ (ψ X) w) := by
  intro n ε H _ _ _ σ P G hP h hσ φ hφ
  refine ⟨fieldDeriv φ P, fun X => ⟨isTest_fderiv hφ _, fun hX w => ?_⟩⟩
  refine Eq.trans ?_ (hasDerivAt_integral_translate hσ hφ (-(P * X * P⁻¹)) w).deriv
  unfold dRep
  congr 1
  funext t
  rw [gard_eq hσ hφ]
  refine GlobalTheory.LowTypeRestriction.garding_translate hσ hφ.continuous hφ.2 w
    (conj_mem_UJ hP h (exp_mem_UH (gram_unit hP h) hX t)) ?_
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.exp_add_of_commute _ _ (((Commute.refl (P * X * P⁻¹)).neg_left.smul_left t).smul_right t), ← smul_add]
  simp

end GlobalTheory.SmVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointHighestProportional
section
noncomputable section

open MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm GlobalTheory.Harm.HighestUnique

namespace GlobalTheory.DefLift.Joint

theorem X_mul_pderiv_mem {σ : Type} (u v : σ) (N : ℕ) (Q : MvPolynomial σ ℂ)
    (hQ : Q ∈ restrictTotalDegree σ ℂ N) : X u * pderiv v Q ∈ restrictTotalDegree σ ℂ N := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_restrictTotalDegree] at hQ ⊢
  have hd : (m.sum fun _ e => e) ≤ N := (le_totalDegree hm).trans hQ
  rw [pderiv_monomial]
  by_cases h : m v = 0
  · simp [h]
  · rw [X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)
    have h1 : Finsupp.single v 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    have h2 : m = Finsupp.single v 1 + (m - Finsupp.single v 1) := (add_tsub_cancel_of_le h1).symm
    conv_rhs => rw [h2]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp
    rfl

theorem antitone_rowOp {σ J : Type} [Fintype σ] [Fintype J] {p : ℕ} (z : Fin p × J → σ)
    (hz : Function.Injective z) {P : MvPolynomial σ ℂ} (hP : P ≠ 0) (μ : Fin p → ℤ)
    (hup : ∀ a b, a < b → ∑ k, X (z (a, k)) * pderiv (z (b, k)) P = 0)
    (hwt : ∀ a, ∑ k, X (z (a, k)) * pderiv (z (a, k)) P = (μ a : ℂ) • P) : Antitone μ :=
  highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) (restrictTotalDegree σ ℂ P.totalDegree)
    (fun i j w hw => by
      rw [rowOp_apply]
      exact Submodule.sum_mem _ fun _ _ => X_mul_pderiv_mem _ _ _ _ hw)
    P ((mem_restrictTotalDegree _ _ _).2 le_rfl) hP μ
    (fun a b h => (rowOp_apply _ _ _ _).trans (hup a b h))
    (fun a => (rowOp_apply _ _ _ _).trans (hwt a))

theorem degree_of_mem_support {σ J : Type} [Fintype J] (z : J → σ) {P : MvPolynomial σ ℂ} {w : ℤ}
    (h : ∑ k, X (z k) * pderiv (z k) P = (w : ℂ) • P) {m : σ →₀ ℕ} (hm : m ∈ P.support) :
    ((∑ k, m (z k) : ℕ) : ℤ) = w := by
  have := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [coeff_sum, coeff_smul] at this
  simp only [coeff_X_mul_pderiv, ← Finset.sum_mul, smul_eq_mul] at this
  have h2 := mul_right_cancel₀ (mem_support_iff.1 hm) this
  exact_mod_cast h2

theorem exists_eq_smul_base {T : Type} [Fintype T] {p n : ℕ} (h : p + 0 ≤ n)
    {P : Poly ℂ T p 0 (Fin n)} (hP : P ≠ 0) (κ : T → Fin n → ℤ) (μ : T → Fin p → ℤ)
    (hup : ∀ t k l, k < l → ∑ a, X (xVar t a k) * pderiv (xVar t a l) P = 0)
    (hwt : ∀ t k, ∑ a, X (xVar t a k) * pderiv (xVar t a k) P = (κ t k : ℂ) • P)
    (hup' : ∀ t a b, a < b → ∑ k, X (xVar t a k) * pderiv (xVar t b k) P = 0)
    (hwt' : ∀ t a, ∑ k, X (xVar t a k) * pderiv (xVar t a k) P = (μ t a : ℂ) • P) :
    ∃ r : ℂ, P = r • basePoly ℂ h (fun t => diffOf fun a : Fin p => (κ t (Fin.castLE (n := p) h a)).toNat)
      (fun _ _ => 0) := by
  classical
  let z : T → Fin p × Fin n → Var T p 0 (Fin n) := fun t w => xVar t w.1 w.2
  let y : T → Fin 0 × Fin n → Var T p 0 (Fin n) := fun t w => yVar t w.1 w.2
  have hz : ∀ t, Function.Injective (z t) := fun t u w e => by simpa [z, Prod.ext_iff] using e
  have hy : ∀ t, Function.Injective (y t) := fun t u w e => u.1.elim0
  have hzy : ∀ t u w, z t u ≠ y t w := fun t u w => w.1.elim0
  have hμ : ∀ t, Antitone (μ t) := fun t => antitone_rowOp (z t) (hz t) hP _ (hup' t) (hwt' t)
  have hκ : ∀ t, Antitone (κ t) := fun t =>
    antitone_rowOp (fun w : Fin n × Fin p => z t w.swap) ((hz t).comp Prod.swap_injective) hP _
      (hup t) (hwt t)
  let a : T → Fin p → ℕ := fun t i => (μ t i).toNat
  have ha : ∀ t, Antitone (a t) := fun t i j hij => Int.toNat_le_toNat (hμ t hij)
  have hdeg : ∀ t i, ∀ m ∈ P.support, ∑ k, m (xVar t i k) = a t i := fun t i m hm => by
    have := degree_of_mem_support (fun k => xVar t i k) (hwt' t i) hm
    simp only [a]
    omega
  have hinv : ∀ t (i j : Fin p), i < j → ∀ s : ℂ,
      bind₁ (fun v => X v + ∑ k, if v = z t (j, k) then C s * X (z t (i, k)) else 0) P = P :=
    fun t i j hij => ((rowAdd_invariant_iff (fun k => z t (i, k)) (fun k => z t (j, k))
      (fun k l e => by simpa using hz t e)
      (fun k l e => hij.ne (congrArg Prod.fst (hz t e))) P).out 3 2).1 (hup' t i j hij)
  have hw : ∀ t, κ t = mixedWeight n (a t) (fun _ : Fin 0 => 0) := fun t =>
    weight_eq_mixedWeight h (z t) (hz t) (y t) (hy t) (hzy t) (a t) _ (ha t) (fun i => i.elim0)
      (hdeg t) (fun i => i.elim0) (hinv t) (fun i => i.elim0) (fun _ i => i.elim0) (κ t) (hκ t)
      (fun k l hkl => by rw [mixedOp_apply]; simpa using hup t k l hkl)
      (fun k => by rw [mixedOp_apply]; simpa using hwt t k) hP
  have e : (fun t => diffOf fun i : Fin p => (κ t (Fin.castLE (n := p) h i)).toNat) = fun t => diffOf (a t) := by
    funext t
    congr 1
    funext i
    rw [hw t, mixedWeight_apply]
    simp
  rw [e]
  refine exists_eq_smul_basePoly h _ _ ?_ κ hκ (fun t k l hkl => by simpa using hup t k l hkl)
    fun t k => by simpa using hwt t k
  refine mem_rowHighest_iff_of_charZero.2 ⟨fun _ _ b => b.elim0, fun t i m hm => ?_,
    fun _ b => b.elim0, fun t i j hij s => ?_, fun _ b => b.elim0⟩
  · rw [partOf_diffOf (ha t)]; exact hdeg t i m hm
  · rw [rowAddX_eq_bind₁]; exact hinv t i j hij s

end GlobalTheory.DefLift.Joint

namespace GlobalTheory.DefLift

theorem joint_highest_proportional (ι : Type) [Fintype ι] (m n : ℕ) (hnm : n ≤ m) (P Q : Pol ι m n)
    (κ : ι → Fin m → ℤ) (μ μ' : ι → Fin n → ℤ) (hP : P ≠ 0)
    (h1 : ∀ τ k l, k < l → rowLie n τ k l P = 0 ∧ rowLie n τ k l Q = 0)
    (h2 : ∀ τ k, rowLie n τ k k P = (κ τ k : ℂ) • P ∧ rowLie n τ k k Q = (κ τ k : ℂ) • Q)
    (h3 : ∀ τ k l, k < l → colLie m τ k l P = 0 ∧ colLie m τ k l Q = 0)
    (h4 : ∀ τ k, colLie m τ k k P = (μ τ k : ℂ) • P ∧ colLie m τ k k Q = (μ' τ k : ℂ) • Q) :
    ∃ r : ℂ, Q = r • P := by
  by_cases hQ : Q = 0
  · exact ⟨0, by simp [hQ]⟩
  let f : ι × Fin m × Fin n → Var ι n 0 (Fin m) := fun v => xVar v.1 v.2.2 v.2.1
  have hf : Function.Injective f := fun u w e => by
    simp only [f, Prod.ext_iff, Sum.inl.injEq] at e
    exact Prod.ext e.1 (Prod.ext e.2.2 e.2.1)
  have hr : ∀ τ k l (R : Pol ι m n), rename f (rowLie n τ k l R) =
      ∑ a, X (xVar τ a k) * pderiv (xVar τ a l) (rename f R) := fun τ k l R => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [rowLie_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, rename_X, ← pderiv_rename hf]
  have hc : ∀ τ k l (R : Pol ι m n), rename f (colLie m τ k l R) =
      ∑ a, X (xVar τ k a) * pderiv (xVar τ l a) (rename f R) := fun τ k l R => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [colLie_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, rename_X, ← pderiv_rename hf]
  have hi := rename_injective (R := ℂ) f hf
  obtain ⟨r, er⟩ := Joint.exists_eq_smul_base (show n + 0 ≤ m from hnm)
    ((map_ne_zero_iff _ hi).2 hP) κ μ
    (fun t k l h => by rw [← hr, (h1 t k l h).1, map_zero])
    (fun t k => by rw [← hr, (h2 t k).1, map_smul])
    (fun t k l h => by rw [← hc, (h3 t k l h).1, map_zero])
    (fun t k => by rw [← hc, (h4 t k).1, map_smul])
  obtain ⟨s, es⟩ := Joint.exists_eq_smul_base (show n + 0 ≤ m from hnm)
    ((map_ne_zero_iff _ hi).2 hQ) κ μ'
    (fun t k l h => by rw [← hr, (h1 t k l h).2, map_zero])
    (fun t k => by rw [← hr, (h2 t k).2, map_smul])
    (fun t k l h => by rw [← hc, (h3 t k l h).2, map_zero])
    (fun t k => by rw [← hc, (h4 t k).2, map_smul])
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hP (hi (by rw [er, zero_smul, map_zero]))
  refine ⟨s / r, hi ?_⟩
  rw [map_smul, er, es, smul_smul, div_mul_cancel₀ _ hr0]

end GlobalTheory.DefLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieWordCommutesOneParameterDerivative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmVecDeriv

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem contDiff_snoc {k : ℕ} :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using contDiff_snd
  · simp only [Fin.snoc_castSucc]
    fun_prop

theorem snoc_mem {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (i : Fin (k + 1)) :
    (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i ∈ lieG G := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hX
  · simpa using hXs j

theorem rep_snoc (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hXs : ∀ i, Xs i ∈ lieG G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (t : Fin k → ℝ) (s : ℝ) (u : H) :
    π (List.ofFn fun i => NormedSpace.exp ((Fin.snoc t s : Fin (k + 1) → ℝ) i •
        (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i)).prod u =
      π (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod (π (NormedSpace.exp (s • X)) u) := by
  rw [← rep_mul hπ (expProd_mem_UH hG hXs t) (exp_mem_UH hG hX s)]
  simp [List.ofFn_succ', -List.ofFn_succ]

theorem contDiff_word (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ Y ∈ l, Y ∈ lieG G) (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (hXs : ∀ i, Xs i ∈ lieG G) :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod
      (word π l (π (NormedSpace.exp (p.2 • X)) w)) := by
  induction l generalizing k with
  | nil =>
    have h1 := (hw (k + 1) (Fin.snoc Xs X) (snoc_mem hXs hX)).comp contDiff_snoc
    convert h1 using 2 with p
    exact (rep_snoc hG hπ hXs hX p.1 p.2 w).symm
  | cons Y l ih =>
    have hl' : ∀ Z ∈ l, Z ∈ lieG G := fun Z hZ => hl Z (by simp [hZ])
    have hY := hl Y (by simp)
    have h1 := ih hl' (k + 1) (Fin.snoc Xs Y) (snoc_mem hXs hY)
    have hs : ContDiff ℝ ∞ fun q : ((Fin k → ℝ) × ℝ) × ℝ =>
        (((Fin.snoc q.1.1 q.2 : Fin (k + 1) → ℝ), q.1.2) : (Fin (k + 1) → ℝ) × ℝ) :=
      (contDiff_snoc.comp (contDiff_fst.fst.prodMk contDiff_snd)).prodMk contDiff_fst.snd
    have h2 : ContDiff ℝ ∞ (Function.uncurry fun (p : (Fin k → ℝ) × ℝ) (r : ℝ) =>
        π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod (π (NormedSpace.exp (r • Y))
          (word π l (π (NormedSpace.exp (p.2 • X)) w)))) := by
      convert h1.comp hs using 1
      funext q
      exact (rep_snoc hG hπ hXs hY q.1.1 q.2 _).symm
    have h3 := (ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (g := fun _ : (Fin k → ℝ) × ℝ => (0 : ℝ)) h2
      contDiff_const (le_of_eq rfl)).clm_apply (contDiff_const (c := (1 : ℝ)))
    convert h3 using 2 with p
    have hu := word_mem hG hπ hl' (rep_mem hG hπ hw (exp_mem_UH hG hX p.2))
    have h4 := (((π _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dRep hu hY) :
      HasDerivAt (fun r : ℝ => π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod
        (π (NormedSpace.exp (r • Y)) (word π l (π (NormedSpace.exp (p.2 • X)) w)))) _ 0)
    exact h4.deriv.symm

theorem contDiff_word_curve (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ Y ∈ l, Y ∈ lieG G) :
    ContDiff ℝ ∞ fun s : ℝ => word π l (π (NormedSpace.exp (s • X)) w) := by
  have h1 := (contDiff_word hG hπ hw hX hl 0 Fin.elim0 (fun i => i.elim0)).comp
    ((contDiff_const (c := (0 : Fin 0 → ℝ))).prodMk (contDiff_id (E := ℝ)))
  simpa [Function.comp_def, rep_one hπ] using h1

theorem hasDerivAt_word : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), ∀ X ∈ lieG G, HasDerivAt (fun t : ℝ => word (trRep σ P) l ((trRep σ P) (NormedSpace.exp (t • X)) w)) (word (trRep σ P) l (dRep (trRep σ P) X w)) 0 := by
  intro n ε H _ _ _ σ P G hP h hσ l hl w hw X hX
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have h1 := ((contDiff_word_curve hG hπ hw hX hl).differentiable (by simp) 0).hasDerivAt
  convert h1 using 1
  refine ext_inner_smooth hP h hσ fun u hu => ?_
  obtain ⟨u', -, h2⟩ := word_adjoint hG hπ hl hu
  have h3 := (hasDerivAt_const (0 : ℝ) u).inner ℂ h1
  have h4 := (hasDerivAt_const (0 : ℝ) u').inner ℂ (hasDerivAt_dRep hw hX)
  simp only [h2 _ (rep_mem hG hπ hw (exp_mem_UH hG hX _)), inner_zero_left, add_zero] at h3 h4
  rw [h2 _ (dRep_mem hG hπ hw hX)]
  exact h4.unique h3

end GlobalTheory.SmVecDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.CharLoc

variable {F : Type} [Field F] [NumberField F]

theorem psiV_twist {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x))
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    psiV F ψ v y = psiV F ψ₀ v (algebraMap F (Fv F v) a * y) := by
  rw [psiV, psiV, h]
  refine congrArg ψ₀ (Prod.ext (mul_zero _) ?_)
  show algebraMap F (Af F) a * singleV F v y = singleV F v _
  rw [mul_comm, GlobalTheory.SnMass.Inhab.single_mul, mul_comm]
  rfl

theorem psiInf_twist {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x))
    (y : Ainf F) : psiInf F ψ y = psiInf F ψ₀ (algebraMap F (Ainf F) a * y) := by
  rw [psiInf, psiInf, h]
  exact congrArg ψ₀ (Prod.ext rfl (mul_zero _))

theorem eventually_integral (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) a).2

theorem ne_one_of_stdAt {v : HeightOneSpectrum (𝓞 F)} {χ : Fv F v → ℂ} (hs : GlobalTheory.SnMass.StdAt v χ) :
    ∃ y, χ y ≠ 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have h1 := (hs (z * (algebraMap F (Fv F v) (d : F))⁻¹)).1 (fun y _ => hn _) d hd
  rw [inv_mul_cancel_right₀ hd1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h1
  omega

theorem eq_zero_of_std {ψ : AddChar (AF F) ℂ} (h : GlobalTheory.SnMass.IsStdChar F ψ) (z : Ainf F)
    (hz : ∀ y, psiInf F ψ (z * y) = 1) : z = 0 := by
  classical
  funext w
  by_contra hw
  have hw' : z w ≠ 0 := hw
  let y : Ainf F := Pi.single w ((z w)⁻¹ * 2⁻¹)
  have h1 := hz y
  rw [h.2.1, Finset.sum_eq_single w] at h1
  · have e : (z * y) w = 2⁻¹ := by
      show z w * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) w = _
      rw [Pi.single_eq_same, mul_inv_cancel_left₀ hw']
    rw [e, map_inv₀, map_ofNat] at h1
    have e2 : 2 * Real.pi * Complex.I * (((2⁻¹ : ℂ).re : ℝ) : ℂ) = Real.pi * Complex.I := by
      have : (2⁻¹ : ℂ).re = 2⁻¹ := by simp
      rw [this]
      push_cast
      ring
    rw [e2, Complex.exp_pi_mul_I] at h1
    norm_num at h1
  · intro u _ hu
    have e : (z * y) u = 0 := by
      show z u * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) u = _
      rw [Pi.single_eq_of_ne hu, mul_zero]
    rw [e, map_zero, Complex.zero_re]
  · intro hn
    exact absurd (Finset.mem_univ w) hn

theorem char_local : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ y, psiV F ψ v y ≠ 1) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F) ∧ ∀ x : Ainf F, (∀ y, psiInf F ψ (x * y) = 1) → x = 0 := by
  intro F _ _ _ ψ hψ
  obtain ⟨ψ₀, h₀⟩ := GlobalTheory.SnMass.Inhab.exists_isStdChar F
  obtain ⟨a, ha, h⟩ := _root_.GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ₀ ψ h₀.1 hψ
  refine ⟨fun v => ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := ne_one_of_stdAt (h₀.2.2 v)
    refine ⟨algebraMap F (Fv F v) a⁻¹ * y, ?_⟩
    rwa [psiV_twist h, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  · obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
    have hd1 : (d : F) ≠ 0 := by exact_mod_cast hd0
    filter_upwards [eventually_integral a, eventually_integral (a * d)⁻¹] with v h1 h2 y
    simp only [psiV_twist h, ← mul_assoc]
    refine (h₀.2.2 v _).trans ⟨fun hy => ?_, fun hy d' _ => ?_⟩
    · have h3 := mul_mem (hy d hd) h2
      rwa [mul_right_comm _ y, ← map_mul, mul_right_comm, ← map_mul, mul_inv_cancel₀ (mul_ne_zero ha hd1),
        map_one, one_mul] at h3
    · exact mul_mem (mul_mem h1 hy) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v d')
  · have h1 := eq_zero_of_std h₀ (algebraMap F (Ainf F) a * x) fun y => by
      rw [mul_assoc, ← psiInf_twist h, hx]
    have h2 := congrArg (algebraMap F (Ainf F) a⁻¹ * ·) h1
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul, mul_zero] using h2

end GlobalTheory.GaugeEx.CharLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumUniqueAll
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem vacuum_unique_all : ∀ D : D7, VacUniqueO D :=
  fun D => GlobalTheory.VacUnique.vacUniqueO D

end GlobalTheory
end

