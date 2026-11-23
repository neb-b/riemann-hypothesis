module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantMultilinearMapsSmoothVectorsIntertwin
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.SmoothMultilinear

theorem conj_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Mt V.rank} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h1 := M.fr_gram τ
  have h2 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  show (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ)
  calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
        rw [h1, hg']
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h2]; simp

theorem rep_one {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

theorem rep_mul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {a b : Mt V.rank} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (a * b) = M.rep τ a * M.rep τ b := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  unfold DSModel.rep
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = (M.fr τ * a * (M.fr τ)⁻¹) * (M.fr τ * b * (M.fr τ)⁻¹) := by
    calc _ = M.fr τ * a * ((M.fr τ)⁻¹ * M.fr τ) * b * (M.fr τ)⁻¹ := by
          rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (conj_mem M τ ha) _ (conj_mem M τ hb)

theorem prod_mem {n : ℕ} (H : Mt n) (l : List (Mt n)) (hl : ∀ g ∈ l, g ∈ Formalism.QuantumDeterminants.UH H) :
    l.prod ∈ Formalism.QuantumDeterminants.UH H := by
  induction l with
  | nil => show (1 : Mt n)ᴴ * H * 1 = H; simp
  | cons a l ih =>
    rw [List.prod_cons]
    exact CCRuleCW.UH_mul _ _ _ (hl a (by simp)) (ih fun g hg => hl g (by simp [hg]))

theorem exp_mem {n : ℕ} (H X : Mt n) (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  apply CCRuleCW.exp_mem_UH
  have := CCRuleCW.lie_smul H X hX t
  rwa [Complex.coe_smul] at this

theorem smooth_of_span {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : v ∈ Submodule.span ℂ {w | SmoothVec L σ w}) :
    SmoothVec L σ v := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro k Xs _; simp only [map_zero]; exact contDiff_const
  | add x y _ _ hx hy => intro k Xs h; simp only [map_add (f := _)]; exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx => intro k Xs h; simp only [map_smul]; exact (hx k Xs h).const_smul c

theorem hasDerivAt_of_smooth {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : SmoothVec L σ v) (X : Mt n) (hX : X ∈ L) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0 := by
  have h := hv 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => (fun _ : Fin 1 => t)) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := h.comp h2
  have h4 : ContDiff ℝ ∞ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) := by
    convert h3 using 2
    simp
  exact (h4.differentiable (by simp) 0).hasDerivAt

theorem act_list {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K)
    (h : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y))
    (y : ∀ τ, M.H τ) (l : List (D.what₂.Tau × Mt V.rank))
    (hl : ∀ p ∈ l, p.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V p.1)) :
    ρ (l.map fun p => atTau θ V p.1 p.2).prod (Φ y) =
      Φ fun τ => M.rep τ (l.map fun p => if p.1 = τ then p.2 else 1).prod (y τ) := by
  induction l with
  | nil => simp [rep_one]
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V q.1) := fun q hq => hl q (by simp [hq])
    rw [List.map_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply, ih hl',
      ← h p.1 p.2 (hl p (by simp))]
    congr 1
    funext τ
    rw [List.map_cons, List.prod_cons]
    by_cases e : p.1 = τ
    · subst e
      rw [Function.update_self, if_pos rfl, rep_mul M _ (hl p (by simp)), ContinuousLinearMap.mul_apply]
      apply prod_mem
      intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
      split_ifs with e
      · exact e ▸ hl' q hq
      · exact prod_mem _ [] (by simp)
    · rw [Function.update_of_ne (Ne.symm e), if_neg e, one_mul]

theorem smooth_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K)) (Φ : ContinuousMultilinearMap ℂ M.H K), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) → ∀ v : M.Vec, IsSmoothVector' θ V ρ (Φ fun τ => (v τ : M.H τ)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) = Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))) := by
  intro D θ V _ S M K _ _ ρ Φ h v
  have hs : ∀ τ, SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) := fun τ => smooth_of_span _ _ _ (v τ).2
  refine ⟨?_, ?_⟩
  · intro k τs Xs hX
    have e : (fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod (Φ fun τ => (v τ : M.H τ))) =
        fun t : Fin k → ℝ => Φ fun τ => M.rep τ
          (List.ofFn fun i => NormedSpace.exp (t i • (if τs i = τ then Xs i else 0))).prod (v τ : M.H τ) := by
      funext t
      have := act_list θ M ρ Φ h (fun τ => (v τ : M.H τ))
        (List.ofFn fun i => (τs i, NormedSpace.exp (t i • Xs i))) (by
          intro p hp
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
          exact exp_mem _ _ (hX i) _)
      simp only [List.map_ofFn] at this
      refine this.trans ?_
      congr 1
      funext τ
      congr 4
      funext i
      dsimp only [Function.comp_apply, Prod.fst, Prod.snd]
      split_ifs <;> simp
    rw [e]
    have hΦ : ContDiff ℝ ∞ (Φ : (∀ τ, M.H τ) → K) := (Φ.contDiff (n := ∞)).restrict_scalars ℝ
    refine hΦ.comp (contDiff_pi.2 fun τ => ?_)
    refine hs τ k _ fun i => ?_
    split_ifs with e
    · exact e ▸ hX i
    · simp [lieAt]
  · intro τ X hX
    have e : (fun t : ℝ => ρ (oneP θ V τ X t) (Φ fun τ => (v τ : M.H τ))) =
        fun t : ℝ => (Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ)
          (M.rep τ (NormedSpace.exp (t • X)) (v τ)) := by
      funext t
      exact (h τ _ (exp_mem _ _ hX t) _).symm
    unfold dL2
    simp only
    rw [e]
    have h1 := hasDerivAt_of_smooth _ _ _ (hs τ) X hX
    exact (((Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1).deriv

end GlobalTheory.SmoothMultilinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerContractionChartForms
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.StabTheta

variable {K : Type} [Field K]

theorem smul_mem_spanForms (M M' : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) (c : K)
    (h : ∀ m ∈ M, c * m ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    c • η ∈ spanForms M' H a := by
  have key : spanForms M H a ≤
      (spanForms M' H a).comap (DistribSMul.toAddMonoidHom (abelian₂ K) c) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show c • (m • ExteriorAlgebra.ιMulti K a v) ∈ AddSubgroup.closure _
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨c * m, h m hm, v, hv, rfl⟩
  exact key hη

theorem iota_mul_mem_spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (q : ℕ) (w : Ω[K⁄ℤ]) (hw : w ∈ H)
    {η : abelian₂ K} (hη : η ∈ spanForms M H q) :
    ExteriorAlgebra.ι K w * η ∈ spanForms M H (q + 1) := by
  have key : spanForms M H q ≤
      (spanForms M H (q + 1)).comap (AddMonoidHom.mulLeft (ExteriorAlgebra.ι K w)) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show ExteriorAlgebra.ι K w * (m • ExteriorAlgebra.ιMulti K q v) ∈ AddSubgroup.closure _
    rw [mul_smul_comm]
    refine AddSubgroup.subset_closure ⟨m, hm, Fin.cons w v, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hw
      · simpa using hv k
    · rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp [Matrix.vecTail]
  exact key hη

theorem theta_dlog {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K)
    (hθ : IsEulerContraction x i θ) (j : Fin n) :
    θ (ExteriorAlgebra.ι K (dlog (x j))) = algebraMap K (abelian₂ K) (if j = i then 1 else 0) := by
  rw [hθ.2.2 j]
  split_ifs <;> simp

theorem theta_frame (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) (j : Fin n) :
    ∃ a ∈ A, θ (ExteriorAlgebra.ι K (frame x J j)) = algebraMap K (abelian₂ K) a := by
  have hif : (if j = i then (1 : K) else 0) ∈ A := by split_ifs <;> simp
  unfold frame
  split_ifs with hj
  · exact ⟨_, hif, theta_dlog x i θ hθ j⟩
  · have hd : dK (x j : K) = (x j : K) • dlog (x j) := by
      unfold dlog
      rw [smul_smul]
      simp
    refine ⟨(x j : K) * (if j = i then 1 else 0), A.mul_mem (hx j) hif, ?_⟩
    rw [hd, map_smul, map_smul, theta_dlog x i θ hθ j, Algebra.smul_def, ← map_mul]

theorem theta_iotaMulti (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) :
    ∀ (q : ℕ) (v : Fin (q + 1) → Ω[K⁄ℤ]), (∀ k, v k ∈ Set.range (frame x J)) →
      θ (ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms (A : Set K) (Set.range (frame x J)) q := by
  intro q
  induction q with
  | zero =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1, ExteriorAlgebra.ιMulti_zero_apply, hθ.1,
      mul_zero, sub_zero, mul_one]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    rw [← hj, he, Algebra.algebraMap_eq_smul_one]
    refine AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, fun k => k.elim0, ?_⟩
    rw [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    have htail : ∀ k, Matrix.vecTail v k ∈ Set.range (frame x J) := fun k => hv k.succ
    refine AddSubgroup.sub_mem _ ?_ ?_
    · rw [← hj, he, ← Algebra.smul_def]
      exact AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, htail, rfl⟩
    · exact iota_mul_mem_spanForms _ _ q _ (hv 0) (ih _ htail)

end GlobalTheory.LogDR.StabTheta

open GlobalTheory.LogDR.StabTheta in
theorem GlobalTheory.LogDR.chartForms_stable_euler :
    ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  intro K _ A n x J t i θ hx hθ
  constructor
  · intro q η hη
    have key : chartForms A x J t (q + 1) ≤ (chartForms A x J t q).comap θ.toAddMonoidHom := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show θ (c • ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms _ _ q
      rw [map_smul]
      refine smul_mem_spanForms (A : Set K) _ _ q c ?_ (theta_iotaMulti A x J i θ hx hθ q v hv)
      intro m hm
      show c * m * (t : K) ∈ A
      rw [mul_right_comm]
      exact A.mul_mem hc hm
    exact key hη
  · intro η hη
    have key : chartForms A x J t 0 ≤ θ.toAddMonoidHom.ker := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
      show θ (c • ExteriorAlgebra.ιMulti K 0 v) = 0
      rw [map_smul, ExteriorAlgebra.ιMulti_zero_apply, hθ.1, smul_zero]
    exact key hη
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjOfIntegralConjGenerator
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ConjInt

section Coords

variable (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type} (b : Module.Basis κ ℚ M)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_smul {a : v.adicCompletion ℚ} (ha : a ∈ v.adicCompletionIntegers ℚ)
    {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) : IsIntB v b (a • x) := fun i => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem ha (hx i)

theorem isIntB_sum {ι : Type} (s : Finset ι) (f : ι → v.adicCompletion ℚ ⊗[ℚ] M)
    (h : ∀ i ∈ s, IsIntB v b (f i)) : IsIntB v b (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isIntB_zero v b
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntB_add v b (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isIntB_tmul_iff (c : M) : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) ↔
    ∀ i, algebraMap ℚ (v.adicCompletion ℚ) (b.repr c i) ∈ v.adicCompletionIntegers ℚ := by
  unfold IsIntB
  simp only [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem eventually_isIntB_tmul [Finite κ] (c : M) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) := by
  have h : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ i,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr c i) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (b.repr c i)).2
  exact h.mono fun v hv => (isIntB_tmul_iff v b c).2 hv

theorem eq_sum_basis [Fintype κ] (x : v.adicCompletion ℚ ⊗[ℚ] M) :
    x = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr x i •
      ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b i) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr x]
  simp only [Algebra.TensorProduct.basis_apply]

end Coords

section Alg

variable (v : HeightOneSpectrum ℤ) {A : Type} [Ring A] [Algebra ℚ A] {κ : Type} (b : Module.Basis κ ℚ A)

theorem isIntB_mul [Finite κ] (hb : ∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j)))
    {x y : v.adicCompletion ℚ ⊗[ℚ] A} (hx : IsIntB v b x) (hy : IsIntB v b y) : IsIntB v b (x * y) := by
  haveI := Fintype.ofFinite κ
  rw [eq_sum_basis v b x, eq_sum_basis v b y, Finset.sum_mul]
  refine isIntB_sum v b _ _ fun i _ => ?_
  rw [Finset.mul_sum]
  refine isIntB_sum v b _ _ fun j _ => ?_
  rw [smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact isIntB_smul v b (mul_mem (hx i) (hy j)) (hb i j)

theorem isIntB_pow [Finite κ] (hb : ∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j)))
    (h1 : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : A)))
    {x : v.adicCompletion ℚ ⊗[ℚ] A} (hx : IsIntB v b x) (k : ℕ) : IsIntB v b (x ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact h1
  | succ k ih => rw [pow_succ]; exact isIntB_mul v b hb ih hx

theorem tmul_central_comm {R : Type} [CommRing R] [Algebra ℚ R] (z : A) (hz : ∀ c, z * c = c * z)
    (y : R ⊗[ℚ] A) : ((1 : R) ⊗ₜ[ℚ] z) * y = y * ((1 : R) ⊗ₜ[ℚ] z) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul, hz c]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end Alg

end GlobalTheory.ConjInt

namespace GlobalTheory.ConjInt

variable {p : ℕ} [Fact p.Prime]

theorem mem_adjoin_of_centralizer (G : HTGroup p) (γ : G.C) (hdeg : (minpoly G.F γ).natDegree = G.n)
    (L : Type) [Field L] (ι : L →+* G.C) (hι : Function.Injective ι)
    (hc : ∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) (w : L) :
    ι w ∈ Algebra.adjoin G.F ({γ} : Set G.C) := by
  set B := Algebra.adjoin G.F ({γ} : Set G.C) with hB
  have hBc : B ≤ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
    refine Algebra.adjoin_le ?_
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg; rw [Set.mem_singleton_iff] at hg; rw [hg]
  have hof : ∀ x : B, ∃ w, ι w = (x : G.C) := by
    intro x
    have hx := hBc x.2
    rw [Subalgebra.mem_centralizer_iff] at hx
    exact (hc x).1 (hx γ (Set.mem_singleton γ)).symm
  haveI : NoZeroDivisors B := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨wx, hwx⟩ := hof x
    obtain ⟨wy, hwy⟩ := hof y
    have h0 : ι (wx * wy) = 0 := by
      rw [map_mul, hwx, hwy]; exact congrArg Subtype.val hxy
    rcases mul_eq_zero.1 (hι (h0.trans (map_zero ι).symm)) with h | h
    · left; apply Subtype.ext; rw [← hwx, h, map_zero]; rfl
    · right; apply Subtype.ext; rw [← hwy, h, map_zero]; rfl
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  have hγB : γ ∈ B := Algebra.self_mem_adjoin_singleton G.F γ
  have hint : IsIntegral G.F (⟨γ, hγB⟩ : B) := Algebra.IsIntegral.isIntegral _
  have hirr : Irreducible (minpoly G.F γ) := by
    have e := minpoly.algHom_eq B.val Subtype.val_injective ⟨γ, hγB⟩
    rw [show B.val ⟨γ, hγB⟩ = γ from rfl] at e
    rw [e]; exact minpoly.irreducible hint
  have hcom : Commute (ι w) γ := (hc (ι w)).2 ⟨w, rfl⟩
  exact (GlobalTheory.CentIrr.commute_iff_mem_adjoin G.F G.C G.n G.n_pos G.rankC γ hirr hdeg (ι w)).1 hcom

end GlobalTheory.ConjInt

namespace GlobalTheory.ConjInt

variable {p : ℕ} [Fact p.Prime]

theorem conj_tmul_smul_pow (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (X : (R ⊗[ℚ] G.C)ˣ)
    (c : G.F) (γ : G.C) (k : ℕ) :
    (X : R ⊗[ℚ] G.C) * ((1 : R) ⊗ₜ[ℚ] (c • γ ^ k)) * ↑X⁻¹ =
      ((1 : R) ⊗ₜ[ℚ] algebraMap G.F G.C c) * (↑X * ((1 : R) ⊗ₜ[ℚ] γ) * ↑X⁻¹) ^ k := by
  have hz : ∀ y : G.C, algebraMap G.F G.C c * y = y * algebraMap G.F G.C c := fun y => Algebra.commutes c y
  rw [Units.conj_pow, Algebra.smul_def, ← one_mul (1 : R), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.tmul_pow, one_pow, ← mul_assoc, ← mul_assoc,
    ← tmul_central_comm _ hz (X : R ⊗[ℚ] G.C)]
  simp only [mul_assoc]

theorem isIntB_conj_map_of_isIntB_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C)
    (κ' : Type) (ℓ : Module.Basis κ' ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      ∀ ρ, IsIntB v ℓ ρ →
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ρ * ↑X⁻¹) := by
  intro p _ G γ hdeg L _ _ ι hι hc κ b κ' ℓ
  haveI : Finite κ := Module.Finite.finite_basis b
  haveI : Finite κ' := Module.Finite.finite_basis ℓ
  haveI := Fintype.ofFinite κ'
  have hq : ∀ a, ∃ q : Polynomial G.F, Polynomial.aeval (γ : G.C) q = ι (ℓ a) := by
    intro a
    have h := mem_adjoin_of_centralizer G (γ : G.C) hdeg L ι.toRingHom hι hc (ℓ a)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  choose q hq using hq
  have hev : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      (∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j))) ∧
      IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : G.C)) ∧
      ∀ a, ∀ k ∈ Finset.range ((q a).natDegree + 1),
        IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] algebraMap G.F G.C ((q a).coeff k)) :=
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_isIntB_tmul b _).and
      ((eventually_isIntB_tmul b _).and
        (Filter.eventually_all.2 fun a => (Filter.eventually_all_finset _).2 fun k _ =>
          eventually_isIntB_tmul b _))
  refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun v hv X hX ρ hρ => ?_⟩
  have hP := hv
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hP
  obtain ⟨hb, h1, hcoef⟩ := hP
  set ιv := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι
  have hmap : ∀ (r : v.adicCompletion ℚ) (m : L),
      ιv (r • ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] m)) = r • ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ι m) := by
    intro r m
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul']
    rfl
  have hterm : ∀ a, IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ι (ℓ a)) * ↑X⁻¹) := by
    intro a
    rw [← hq a, Polynomial.aeval_eq_sum_range, TensorProduct.tmul_sum, Finset.mul_sum, Finset.sum_mul]
    refine isIntB_sum v b _ _ fun k hk => ?_
    rw [conj_tmul_smul_pow]
    exact isIntB_mul v b hb (hcoef a k hk) (isIntB_pow v b hb h1 hX k)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_basis v ℓ ρ, map_sum, Finset.mul_sum, Finset.sum_mul]
  refine isIntB_sum v b _ _ fun a _ => ?_
  rw [hmap, mul_smul_comm, smul_mul_assoc]
  exact isIntB_smul v b (hρ a) (hterm a)

end GlobalTheory.ConjInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOneTmulAdicIntegralCoordsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_one_tmul_adic_integral_coords : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M) (x : M),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] x) := by
  first | (exact @GlobalTheory.AdicSpan.exists_finset_isIntB_one_tmul) | (exact GlobalTheory.AdicSpan.exists_finset_isIntB_one_tmul) | (intros; apply GlobalTheory.AdicSpan.exists_finset_isIntB_one_tmul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicGroupLawSplitByIdempotentStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logarithmic_group_law_split_by_idempotent : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d d' : ℕ) (G : LogFGL v d) (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C), (∀ a b, IsIntV v (I a b)) → (∀ a b, IsIntV v (P a b)) → P * I = 1 → (∃ φ, IsIntHom G G φ (I * P)) → (∃ ψ, IsIntHom G G ψ (1 - I * P)) → ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  first | exact @GlobalTheory.IdemImage.exists_image | exact GlobalTheory.IdemImage.exists_image | (intros; apply GlobalTheory.IdemImage.exists_image <;> assumption)
end

