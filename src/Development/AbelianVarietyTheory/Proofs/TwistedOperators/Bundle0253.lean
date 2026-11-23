module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantNeZeroOfMemMaxCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.FockOrbit

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.PointAtPlaceHom

section General

variable {G σ : Type} [TopologicalSpace G]

def CoefCont (F : G → MvPolynomial σ ℂ) : Prop := ∀ m, Continuous fun k => AddMonoidAlgebra.coeff (F k) m

theorem CoefCont.const (P : MvPolynomial σ ℂ) : CoefCont fun _ : G => P := fun _ => continuous_const

theorem CoefCont.add {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k + F' k := fun m => by
  simp only [MvPolynomial.coeff_add]
  exact (h m).add (h' m)

theorem CoefCont.mul {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k * F' k := fun m => by
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finsetSum _ fun p _ => (h _).mul (h' _)

theorem CoefCont.smul {s : G → ℂ} {F : G → MvPolynomial σ ℂ} (hs : Continuous s) (h : CoefCont F) :
    CoefCont fun k => s k • F k := fun m => by
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  exact hs.mul (h m)

theorem CoefCont.sum {ι : Type} [Fintype ι] {F : ι → G → MvPolynomial σ ℂ} (h : ∀ i, CoefCont (F i)) :
    CoefCont fun k => ∑ i, F i k := fun m => by
  simp only [MvPolynomial.coeff_sum]
  exact continuous_finsetSum _ fun i _ => h i m

theorem CoefCont.aeval {τ : Type} {g : G → τ → MvPolynomial σ ℂ} (h : ∀ v, CoefCont fun k => g k v)
    (P : MvPolynomial τ ℂ) : CoefCont fun k => MvPolynomial.aeval (g k) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using CoefCont.const _
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (h v)

theorem exists_monomials [Finite σ] (N : ℕ) : ∃ (n : ℕ) (e : Fin n → σ →₀ ℕ), ∀ P : MvPolynomial σ ℂ,
    P.totalDegree ≤ N → P = ∑ i, AddMonoidAlgebra.coeff P (e i) • MvPolynomial.monomial (e i) (1 : ℂ) := by
  let T := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset
  refine ⟨T.card, fun i => (T.equivFin.symm i : σ →₀ ℕ), fun P hP => ?_⟩
  rw [T.equivFin.symm.sum_comp (fun d : T => AddMonoidAlgebra.coeff P (d : σ →₀ ℕ) •
    MvPolynomial.monomial (d : σ →₀ ℕ) (1 : ℂ)),
    Finset.sum_coe_sort T fun d => AddMonoidAlgebra.coeff P d • MvPolynomial.monomial d (1 : ℂ)]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [P.as_sum]
  refine Finset.sum_subset (fun d hd => ?_) fun d _ hd => ?_
  · simp only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact (MvPolynomial.le_totalDegree hd).trans hP
  · rw [MvPolynomial.notMem_support_iff.1 hd, map_zero]

theorem exists_coefFam [Group G] [Finite σ] (ρ : G → Module.End ℂ (MvPolynomial σ ℂ))
    (hm : ∀ a b P, ρ (a * b) P = ρ a (ρ b P)) (hd : ∀ a P, (ρ a P).totalDegree ≤ P.totalDegree)
    (hc : ∀ P, CoefCont fun k => ρ k P) (φ : MvPolynomial σ ℂ) :
    ∃ (n : ℕ) (φs : Fin n → MvPolynomial σ ℂ) (c : Fin n → G → ℂ), IsCoefFam c ∧ ∀ k, ρ k φ = ∑ i, c i k • φs i := by
  obtain ⟨n, e, he⟩ := exists_monomials (σ := σ) φ.totalDegree
  refine ⟨n, fun i => MvPolynomial.monomial (e i) 1, fun i k => AddMonoidAlgebra.coeff (ρ k φ) (e i),
    ⟨fun i => hc φ _, fun k₀ i => ⟨fun j => AddMonoidAlgebra.coeff (ρ k₀ (MvPolynomial.monomial (e j) 1)) (e i),
      fun k => ?_⟩⟩, fun k => he _ (hd k φ)⟩
  beta_reduce
  rw [hm]
  conv_lhs => rw [he _ (hd k φ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end General

theorem signBlockDeterminant_ne_zero_of_mem_maxCompact {n : ℕ} {ε : Fin n → Bool} (e : Bool) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : signBlockDeterminant ε e k ≠ 0 := by
  have hd : k.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det k).1 (Unitary.isUnit_coe (U := ⟨k, hk.1⟩)) |>.ne_zero
  rw [Matrix.twoBlockTriangular_det k (fun i => ε i = e) (fun i hi j hj => by
    have h := congrFun (congrFun hk.2 i) j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases e <;> simp only [Bool.not_eq_true, Bool.not_eq_false] at hi <;> simp [hi, hj] at h <;>
      first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h)] at hd
  have := left_ne_zero_of_mul hd
  unfold signBlockDeterminant
  convert this
  rfl

theorem continuous_signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) : Continuous (signBlockDeterminant ε e) :=
  (continuous_id.matrix_submatrix _ _).matrix_det

theorem continuous_toMK {n : ℕ} (ε : Fin n → Bool) : Continuous fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

variable {D : D7}

theorem unframe_mem {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (τ : D.what₂.Tau)
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M'.ε τ)) :
    (M'.fr τ)⁻¹ * k * M'.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  have hJ : kᴴ * Formalism.REAL.Jm (M'.ε τ) * k = Formalism.REAL.Jm (M'.ε τ) := (Formalism.REAL.maximal_compact_facts _ _).1 k hk
  have hJ' : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ,
      kᴴ * (Formalism.REAL.Jm (M'.ε τ) * (k * A)) = Formalism.REAL.Jm (M'.ε τ) * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  have e1 : ((M'.fr τ)⁻¹)ᴴ * (M'.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd]; simp
  have e2 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, ((M'.fr τ)⁻¹)ᴴ * ((M'.fr τ)ᴴ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  change ((M'.fr τ)⁻¹ * k * M'.fr τ)ᴴ * gramAt D W τ * ((M'.fr τ)⁻¹ * k * M'.fr τ) = gramAt D W τ
  rw [← M'.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e2, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJ']

theorem elt_mul {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (τ : D.what₂.Tau) {a b : Matrix (Fin W.rank) (Fin W.rank) ℂ} (ha : a ∈ Formalism.REAL.Kset (M'.ε τ))
    (hb : b ∈ Formalism.REAL.Kset (M'.ε τ)) : elt θ M' τ (a * b) = elt θ M' τ a * elt θ M' τ b := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  rw [elt, elt, elt, ← atTau_mul hθ W τ (unframe_mem M' τ ha) (unframe_mem M' τ hb)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem elt_one' {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  rw [elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), atTau_one hθ]

theorem coefCont_subst {G : Type} [TopologicalSpace G] {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool)
    (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) {k : G → Matrix (Fin b) (Fin b) ℂ} (hk : Continuous k)
    (P : PolF D b a) : CoefCont fun x => subst τ ε ε' g (k x) P := by
  unfold subst
  refine CoefCont.aeval (fun v => ?_) P
  split_ifs
  all_goals first
    | exact CoefCont.const _
    | refine CoefCont.sum fun l => CoefCont.sum fun m => CoefCont.smul ?_ (CoefCont.const _)
  · exact (hk.matrix_elem _ _).mul continuous_const
  · exact ((hk.matrix_elem _ _).mul continuous_const).star

theorem fock_orbit_coefFam : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ), IsInfFam θ → Function.Injective (ptOf ψ θ M M' f) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → ∀ φ : PolF D W.rank V.rank, ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ), IsCoefFam c ∧ ∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f (∑ i, c i k • φs i) := by
  intro D V W S S' M M' θ ψ ω f τ aS aT hθ hpt hC φ
  obtain ⟨x, y, -, -, hc⟩ := hC
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hp : ptOf ψ θ M M' f = pt := rfl
  rw [hp] at hpt hc ⊢
  let s : Formalism.REAL.KG (M'.ε τ) → ℂ := fun k => signBlockDeterminant (M.ε τ) true 1 ^ x true * signBlockDeterminant (M.ε τ) false 1 ^ x false *
    (signBlockDeterminant (M'.ε τ) true (Formalism.REAL.toMK k) ^ y true * signBlockDeterminant (M'.ε τ) false (Formalism.REAL.toMK k) ^ y false)
  let ρ : Formalism.REAL.KG (M'.ε τ) → Module.End ℂ (PolF D W.rank V.rank) := fun k =>
    s k • (subst τ (M.ε τ) (M'.ε τ) ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ).map (starRingEnd ℂ))
      (Formalism.REAL.toMK k)).toLinearMap
  have key : ∀ k P, ω (1, elt θ M' τ (Formalism.REAL.toMK k)) (pt P) = pt (ρ k P) := fun k P => by
    have := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (Formalism.REAL.toMK k) k.2 P
    rw [elt_one' hθ, ← map_smul] at this
    exact this
  have hz : ∀ e, Continuous fun k : Formalism.REAL.KG (M'.ε τ) => signBlockDeterminant (M'.ε τ) e (Formalism.REAL.toMK k) ^ y e := fun e =>
    ((continuous_signBlockDeterminant _ e).comp (continuous_toMK _)).zpow₀ _ fun k => Or.inl (signBlockDeterminant_ne_zero_of_mem_maxCompact e k.2)
  have hs : Continuous s := continuous_const.mul ((hz true).mul (hz false))
  obtain ⟨n, φs, c, h1, h2⟩ := exists_coefFam ρ (fun a b P => hpt (by
      have e : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
      rw [← key, ← key, ← key, e, elt_mul hθ M' τ a.2 b.2, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk,
        mul_one]))
    (fun a P => (MvPolynomial.totalDegree_smul_le _ _).trans
      (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _))
    (fun P => CoefCont.smul hs (coefCont_subst τ _ _ _ (continuous_toMK _) P)) φ
  exact ⟨n, φs, c, h1, fun k => by rw [key, h2]⟩

end GlobalTheory.Chain.IoLift.FockOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCost
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped ENNReal

namespace GlobalTheory.Size.SupWord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OrientedHeis

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {f f' : WO V W → ℂ}
  {p : (WO V W → ℂ) → ℝ≥0∞}

theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool))
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    wordAct (heisDer ψ θ) l (f + f') = wordAct (heisDer ψ θ) l f + wordAct (heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, wordAct_cons, wordAct_cons, ih]
    exact dRho_add hψ hθ a.1 _ (theta_word hψ hθ l h) (theta_word hψ hθ l h')

theorem word_smul (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool)) (c : ℂ) (f : WO V W → ℂ) :
    wordAct (heisDer ψ θ) l (c • f) = c • wordAct (heisDer ψ θ) l f :=
  wordAct_rel (R := fun g g' => g = c • g') l (fun a _ _ _ e => e ▸ dRho_smul a.1 _ c _) rfl

theorem ws_add_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') (k : ℕ) :
    wordSum (heisDer ψ θ) p k (f + f') ≤ wordSum (heisDer ψ θ) p k f + wordSum (heisDer ψ θ) p k f' :=
  wordSum_le_add fun l => by rw [word_add hψ hθ l h h']; exact hp _ _

theorem ws_smul (hp : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) (k : ℕ) (c : ℂ) (f : WO V W → ℂ) :
    wordSum (heisDer ψ θ) p k (c • f) = ‖c‖ₑ * wordSum (heisDer ψ θ) p k f :=
  wordSum_eq_mul fun l => by rw [word_smul]; exact hp _ _

theorem ws_sum_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (hs : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ}
    (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) (k : ℕ) :
    wordSum (heisDer ψ θ) p k (∑ i ∈ s, g i) ≤ ∑ i ∈ s, wordSum (heisDer ψ θ) p k (g i) := by
  refine Finset.le_sum_of_subadditive_on_pred (wordSum (heisDer ψ θ) p k) (IsThetaFunO ψ V W) ?_
    (fun _ _ a b => ws_add_le hψ hθ hp a b k) (fun _ _ => theta_add) g hg
  have := ws_smul (ψ := ψ) (θ := θ) hs k 0 (0 : WO V W → ℂ)
  rw [zero_smul, enorm_zero, zero_mul] at this
  simp [this]

theorem ws_dRho_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (hs : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (k : ℕ) :
    wordSum (heisDer ψ θ) p k (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) ≤
      ENNReal.ofReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)) * wordSum (heisDer ψ θ) p (k + 1) f := by
  have ht : ∀ (c : ℂ) a, IsThetaFunO ψ V W (c • heisDer ψ θ a f) := fun c a =>
    theta_smul c (theta_dRho hθ hψ a.1 _ hf)
  have hb : ∀ (c : ℝ) a, wordSum (heisDer ψ θ) p k ((c : ℂ) • heisDer ψ θ a f) ≤
      ENNReal.ofReal |c| * wordSum (heisDer ψ θ) p (k + 1) f := fun c a => by
    rw [ws_smul hs, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact wordSum_letter_le k a f
  rw [dRho_eq_sum_heisDer hψ hθ hf, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (ws_sum_le hψ hθ hp hs _ (fun i _ => theta_finsetSum _ fun j _ => theta_add (ht _ _) (ht _ _)) k).trans
    (Finset.sum_le_sum fun i _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (ws_sum_le hψ hθ hp hs _ (fun j _ => theta_add (ht _ _) (ht _ _)) k).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), add_mul]
  exact (ws_add_le hψ hθ hp (ht _ _) (ht _ _) k).trans (add_le_add (hb _ _) (hb _ _))

theorem supN_add_le (g g' : WO V W → ℂ) : (⨆ w, ‖(g + g') w‖ₑ) ≤ (⨆ w, ‖g w‖ₑ) + ⨆ w, ‖g' w‖ₑ :=
  iSup_le fun w => (enorm_add_le (g w) (g' w)).trans (add_le_add (le_iSup (fun w => ‖g w‖ₑ) w)
    (le_iSup (fun w => ‖g' w‖ₑ) w))

theorem supN_smul (c : ℂ) (g : WO V W → ℂ) : (⨆ w, ‖(c • g) w‖ₑ) = ‖c‖ₑ * ⨆ w, ‖g w‖ₑ := by
  simp only [Pi.smul_apply, enorm_smul, ENNReal.mul_iSup]

theorem wordSum_sup_sub_and_derAlong :
    ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → (∀ (G H : WO V W → ℂ) (c : ℂ) (k : ℕ), IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (G - c • H) ≤ GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G + ‖c‖ₑ * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k H) ∧ ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E), ∃ c : ℝ, 0 ≤ c ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ k : ℕ, GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (derAlong ψ θ V W C x G) ≤ ENNReal.ofReal c * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (k + 1) G := by
  intro D V W ψ hψ θ hθ
  have ha : ∀ g g' : WO V W → ℂ, (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (g + g') ≤
      (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g + (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g' := supN_add_le
  have hs : ∀ (c : ℂ) (g : WO V W → ℂ), (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (c • g) =
      ‖c‖ₑ * (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g := supN_smul
  refine ⟨fun G H c k hG hH => ?_, fun r C x => ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul]
    refine (ws_add_le hψ hθ ha hG (theta_smul _ hH) k).trans ?_
    rw [ws_smul hs, enorm_neg]
  · refine ⟨∑ τ, ∑ i, ∑ j, (|(dirAt V W C τ (x.map (tauE D τ)) i j).re| +
      |(dirAt V W C τ (x.map (tauE D τ)) i j).im|), by positivity, fun G hG k => ?_⟩
    unfold derAlong
    refine (ws_sum_le hψ hθ ha hs _ (fun τ _ => theta_dRho hθ hψ τ _ hG) k).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun τ _ => by positivity), Finset.sum_mul]
    exact Finset.sum_le_sum fun τ _ => ws_dRho_le hψ hθ ha hs hG τ _ k

end GlobalTheory.Size.SupWord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.UnitaryDetAbs

open GlobalTheory.MixModel

theorem absE_det_matHom (D : D7) (W : HSp D) (h : GA D W) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 := by
  have hM := GlobalTheory.MixModel.mt_unitary W h
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hadj : (GlobalTheory.MixModel.adj (mt W h)).det = cA D (mt W h).det := by
    rw [GlobalTheory.MixModel.adj, Matrix.det_transpose, RingHom.map_det]; rfl
  have hG : IsUnit (GlobalTheory.MixModel.gA W).det := by
    have e : (GlobalTheory.MixModel.gA W).det = incA D W.gram.det := by
      rw [GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat, RingHom.map_det]; rfl
    rw [e]
    exact (GlobalTheory.MixModel.gram_isUnit_det W).map _
  rw [hadj] at hdet
  have key : cA D (mt W h).det * (mt W h).det = 1 := by
    have e2 : cA D (mt W h).det * (mt W h).det * (GlobalTheory.MixModel.gA W).det = 1 * (GlobalTheory.MixModel.gA W).det := by
      rw [one_mul]; nth_rewrite 2 [← hdet]; ring
    exact hG.mul_right_cancel e2
  have hu : GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom W h)) *
      Matrix.GeneralLinearGroup.det (matHom W h) = 1 := by
    ext
    exact key
  have h2 := congrArg (GlobalTheory.Doubling.absE D.host.F D.host.E) hu
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

end GlobalTheory.UnitaryDetAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionPeriodicNormFiniteSqIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSqInt

theorem thetaO_norm_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → (∀ γ ∈ ratL T S, ∀ w, ‖F (γ + w)‖ = ‖F w‖) ∧ ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≠ ⊤ ∧ ∫ x in 𝓕, F x * starRingEnd ℂ (F x) ∂μ = (((∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  intro D ψ hψ S T μ 𝓕 hC F hF
  haveI hB : BorelSpace (WO S T) := ⟨rfl⟩
  haveI hO : OpensMeasurableSpace (WO S T) := BorelSpace.opensMeasurable
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ w
    obtain ⟨ξ, rfl⟩ := hγ
    have hq := hF.quasi ξ w
    have e : ((incA D).toAddMonoidHom.mapMatrix ξ : WO S T) = ratW T S ξ := rfl
    rw [e, hq, norm_mul, hn, one_mul]
  · obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hF
    have hle : ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≤ ∫⁻ _x in 𝓕, ENNReal.ofReal M ^ 2 ∂μ := by
      refine lintegral_mono fun x => ?_
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM x)
    rw [setLIntegral_const, hC.2.2, mul_one] at hle
    exact ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hle
  · have h1 : ∀ x, F x * starRingEnd ℂ (F x) = (((‖F x‖ ^ 2 : ℝ)) : ℂ) := fun x => by
      rw [Complex.mul_conj']; push_cast; rfl
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg ‖F x‖)
      ((hF.cont.norm.pow 2).measurable.aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

end GlobalTheory.ThetaSqInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessCharacterTrivial
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffVanish

theorem matrixCoeff_eq_zero : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν →
    ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
    ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ ∀ ξ : WO V W, ∀ u ∈ U, u.map (infPart D) = 0 →
      ψ (symplO V W ξ u) ≠ 1 → ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
  intro D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'

  obtain ⟨U₁, hU₁, hGfix⟩ := hG.level
  obtain ⟨U₂, hU₂, hG'fix⟩ := hG'.level
  refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact hU₁.inter hU₂
  intro ξ u hu hfin hψu
  obtain ⟨hcomp, -, hkeep, hunit, -⟩ := GlobalTheory.ThetaSquare.heisUnitary (V := V) (W := W) hψ
  have hGu : heisO ψ V W u G = G := hGfix u hu.1 hfin
  have hG'u : heisO ψ V W u G' = G' := hG'fix u hu.2 hfin

  have hswap : symplOH V W u ξ = -symplOH V W ξ u := GlobalTheory.MixModel.symplOH_skew V W ξ u
  have hmove : heisO ψ V W u (heisO ψ V W ξ G) = ψ (-symplO V W ξ u) • heisO ψ V W ξ G := by
    have hξG : heisO ψ V W ξ G = ψ (symplOH V W ξ u) • heisO ψ V W (ξ + u) G := by
      have h := hcomp ξ u G
      rwa [hGu] at h
    rw [hcomp u ξ G, add_comm u ξ, hξG, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hswap, GlobalTheory.ThetaSquare.symplO_eq]
    ring

  set c : ℂ := ψ (-symplO V W ξ u) with hc
  have hI := hunit ν 𝓕 hν h𝓕 u (heisO ψ V W ξ G) G' (hkeep ξ G hG) hG'
  rw [hmove, hG'u] at hI
  unfold GlobalTheory.Ker.ipO at hI
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, starRingEnd_apply] at hI
  rw [MeasureTheory.integral_const_mul] at hI
  have hc1 : c ≠ 1 := by
    intro h1
    apply hψu
    have hprod : ψ (symplO V W ξ u) * c = 1 := by
      rw [hc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rwa [h1, mul_one] at hprod
  have hsub : (c - 1) * ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · exact h

end GlobalTheory.CoeffVanish

end
end

