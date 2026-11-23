module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceInnerMul
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Unip

variable {D : D7} {n : ℕ}

theorem halfTr_add' (a c : AE D) : halfTr (a + c) = halfTr a + halfTr c := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_add (f := _), mul_add]

theorem halfTr_add_cA (s : AE D) : halfTr s + halfTr (cA D s) = trA s := by
  have hinv : Function.Involutive (cA D) := by
    intro a
    have h := congrArg (fun N => N 0 0)
      (GlobalTheory.MixModel.adj_adj (D := D) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => a))
    simpa [GlobalTheory.MixModel.adj] using h
  have hcomm : ∀ r : AF D.host.F, cA D (algebraMap (AF D.host.F) (AE D) r) =
      algebraMap (AF D.host.F) (AE D) r := by
    intro r
    simp [Formalism.L2.Theta.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]
  let e : AE D ≃ₐ[AF D.host.F] AE D :=
    AlgEquiv.ofBijective { cA D with commutes' := hcomm } hinv.bijective
  have htr : trA (cA D s) = trA s := Algebra.trace_eq_of_algEquiv e s
  simp only [GlobalTheory.StdUnn.halfTr]
  rw [htr, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem inner_add_add (V : HSp D) (z x : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (z + x) (z + x) = GlobalTheory.StdUnn.inner V z z + GlobalTheory.StdUnn.inner V z x + GlobalTheory.StdUnn.inner V x z +
      GlobalTheory.StdUnn.inner V x x := by
  simp only [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj_add, Matrix.mul_add, Matrix.add_mul]
  abel

theorem adj_inner (V : HSp D) (z x : Mx D V.rank n) :
    adj (GlobalTheory.StdUnn.inner V z x) = GlobalTheory.StdUnn.inner V x z := by
  simp only [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA,
    Matrix.mul_assoc]

theorem trace_inner_mul (V : HSp D) (b : Mx D n n) (z x : Mx D V.rank n) :
    Matrix.trace (GlobalTheory.StdUnn.inner V z (x ⬝ b)) = Matrix.trace (b * GlobalTheory.StdUnn.inner V z x) := by
  rw [Matrix.trace_mul_comm b]
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]

theorem trace_swap (V : HSp D) {b : Mx D n n} (hb : adj b = b) (z x : Mx D V.rank n) :
    Matrix.trace (b * GlobalTheory.StdUnn.inner V x z) = cA D (Matrix.trace (b * GlobalTheory.StdUnn.inner V z x)) := by
  rw [← GlobalTheory.MixModel.trace_adj, GlobalTheory.MixModel.adj_mul, GlobalTheory.CompanionTheory.EisCovar.Unip.adj_inner, hb,
    Matrix.trace_mul_comm]

theorem quad_shift (V : HSp D) {b : Mx D n n} (hb : adj b = b) (z x : Mx D V.rank n) :
    halfTr (Matrix.trace (b * GlobalTheory.StdUnn.inner V (z + x) (z + x))) =
      halfTr (Matrix.trace (b * GlobalTheory.StdUnn.inner V z z)) + trA (Matrix.trace (GlobalTheory.StdUnn.inner V z (x ⬝ b))) +
        halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V x (x ⬝ b))) := by
  rw [GlobalTheory.CompanionTheory.EisCovar.Unip.inner_add_add, GlobalTheory.CompanionTheory.EisCovar.Unip.trace_inner_mul,
    GlobalTheory.CompanionTheory.EisCovar.Unip.trace_inner_mul]
  simp only [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.EisCovar.Unip.halfTr_add']
  rw [GlobalTheory.CompanionTheory.EisCovar.Unip.trace_swap V hb z x,
    ← GlobalTheory.CompanionTheory.EisCovar.Unip.halfTr_add_cA (Matrix.trace (b * GlobalTheory.StdUnn.inner V z x))]
  abel

theorem mat_inv_unip {g : G D n} {b : Mx D n n} (hg : mat g = blk4 1 b 0 1) : mat g⁻¹ = blk4 1 (-b) 0 1 := by
  have h1 : GlobalTheory.StdUnn.mat g * GlobalTheory.StdUnn.blk4 1 (-b) 0 1 = 1 := by
    rw [hg, GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      neg_add_cancel, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]
  calc GlobalTheory.StdUnn.mat g⁻¹ = GlobalTheory.StdUnn.mat g⁻¹ * (GlobalTheory.StdUnn.mat g * GlobalTheory.StdUnn.blk4 1 (-b) 0 1) := by
        rw [h1, Matrix.mul_one]
    _ = GlobalTheory.StdUnn.blk4 1 (-b) 0 1 := by
        rw [← Matrix.mul_assoc, GlobalTheory.CompanionTheory.EisCovar.mat_inv_mul', Matrix.one_mul]

end GlobalTheory.CompanionTheory.EisCovar.Unip

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covAt_unip : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (g : G D n) (b : Mx D n n), adj b = b → mat g = blk4 1 b 0 1 → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hW g b hb hg
  unfold GlobalTheory.CompanionTheory.EisCovar.CovAt
  intro v Φ Ψ hΨ
  have hinv := GlobalTheory.CompanionTheory.EisCovar.Unip.mat_inv_unip hg
  funext z
  rw [hinv, hW.unip g b hg Ψ z, hΨ]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [GlobalTheory.CompanionTheory.EisCovar.x_part_mul_block, GlobalTheory.CompanionTheory.EisCovar.y_part_mul_block]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.mul_neg]
  rw [hW.unip g b hg Φ, GlobalTheory.CompanionTheory.EisCovar.Unip.quad_shift V hb z (xPart v)]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.mul_neg,
    Matrix.trace_add, Matrix.trace_neg, map_add, map_neg]
  ring

end GlobalTheory.CompanionTheory.EisCovar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSum
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliTrace

open Polynomial Formalism.REAL GroundTheory.BlockD.FourierDecayAlt.GaugeExists

theorem coeff_prod_lin {A : Type} [Ring A] (l : List A) (k : ℕ) (hk : k + 1 = l.length) :
    ((l.map fun b => (X + C b : A[X])).prod).coeff k = l.sum := by
  have h := prod_linear l.length (fun i => l.get i)
  have e : (List.ofFn fun i : Fin l.length => (X + C (l.get i) : A[X])) = l.map fun b => (X + C b : A[X]) := by
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  rw [e] at h
  rw [h.2.2 k hk]
  conv_rhs => rw [← List.ofFn_get l, List.sum_ofFn]

theorem coeff_eq_zero_of_forall {V : Type} [AddCommGroup V] [Module ℂ V] (N : ℕ) (w : ℕ → V)
    (h : ∀ u : ℂ, ∑ j ∈ Finset.range N, u ^ j • w j = 0) (i : ℕ) (hi : i < N) : w i = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  have hP : (∑ j ∈ Finset.range N, C (f (w j)) * X ^ j : ℂ[X]) = 0 := by
    refine Polynomial.funext fun u => ?_
    have := congrArg f (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p : ℂ[X] => p.coeff i) hP
  rw [finsetSum_coeff, Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hji
    simp [coeff_C_mul_X_pow, Ne.symm hji]
  · simp [hi]

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem evU_prod_lin (l : List ℂ) (c v : ℂ) :
    evU v (((l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c)).map fun b => (X + C b)).prod) =
      algebraMap ℂ (Module.End ℂ V) (l.map (v - c + ·)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih]
    congr 1
    simp only [evU_apply, eval₂_add, eval₂_X, eval₂_C, RingHom.id_apply, ← map_add (f := _)]
    congr 1
    ring

theorem sum_map_lin (l : List ℂ) (c : ℂ) :
    (l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c)).sum =
      algebraMap ℂ (Module.End ℂ V) (l.sum - l.length * c) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, ← map_add (f := _)]
    congr 1
    push_cast
    ring

theorem trace_of_qdet {n : ℕ} (Eo : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (l : List ℂ)
    (hl : l.length = n + 1) (φ : V)
    (h : ∀ v : ℂ, qdet Eo v φ = (l.map (v - (n : ℂ) / 2 + ·)).prod • φ) :
    (∑ i, Eo i i) φ = l.sum • φ := by
  set c : ℂ := (n : ℂ) / 2 with hc
  set L : List (Module.End ℂ V) := l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c) with hL
  set R : (Module.End ℂ V)[X] := (L.map fun b => (X + C b)).prod with hR
  set D : (Module.End ℂ V)[X] := qdetPoly Eo - R with hD
  have hev : ∀ v, (evU v D) φ = 0 := fun v => by
    rw [hD, map_sub, evU_qdetPoly, hR, hL, evU_prod_lin, LinearMap.sub_apply, h, Module.algebraMap_end_apply,
      sub_self]
  have hsum : ∀ v : ℂ, ∑ j ∈ Finset.range (D.natDegree + 1 + (n + 1)), v ^ j • (D.coeff j) φ = 0 := fun v => by
    have := hev v
    rw [evU_apply, eval₂_eq_sum_range' _ (show D.natDegree < D.natDegree + 1 + (n + 1) by omega),
      LinearMap.sum_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_pow, RingHom.id_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
  have h0 := coeff_eq_zero_of_forall _ (fun j => (D.coeff j) φ) hsum n (by omega)
  have hq : (qdetPoly Eo).coeff n = ∑ k, Eo k k - algebraMap ℂ _ (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_qdetPoly_top Eo n (by omega), (prod_linear (n + 1) _).2.2 n rfl, Finset.sum_sub_distrib, ← map_sum,
      sum_fin_cast]
  have hr : R.coeff n = algebraMap ℂ _ (l.sum - l.length * c) := by
    rw [hR, coeff_prod_lin L n (by simp [hL, hl]), hL, sum_map_lin]
  simp only [hD, coeff_sub, hq, hr] at h0
  have hs : (∑ k, Eo k k) - algebraMap ℂ (Module.End ℂ V) (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) -
      algebraMap ℂ _ (l.sum - l.length * c) = (∑ k, Eo k k) - algebraMap ℂ _ l.sum := by
    rw [sub_sub, ← map_add (f := _)]
    congr 2
    rw [hl, hc]
    push_cast
    ring
  rw [hs, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h0
  exact h0

end Gen

theorem trace_Eop_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  intro E _ _ _ a π τ m hm φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases a with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end GlobalTheory.CompanionTheory.CapelliTrace

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSchwartzFunctionIntegrable
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Phase

def flat (S : Type) [AddCommGroup S] [TopologicalSpace S] (n M : ℕ) :
    (Fin n → Fin M → S) ≃ₜ+ (Fin 1 → Fin (n * M) → S) where
  toFun X _ p := X (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  invFun Y a i := Y 0 (finProdFinEquiv (a, i))
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext a p
    rw [Subsingleton.elim a 0]
    exact congrArg (Y 0) (finProdFinEquiv.apply_symm_apply p)
  map_add' X Y := by
    funext a p
    rfl
  continuous_toFun := continuous_pi fun _ => continuous_pi fun p =>
    (continuous_apply _).comp (continuous_apply _)
  continuous_invFun := continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_apply _).comp (continuous_apply _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem projInf_flat_symm {n M : ℕ} (Y : Fin 1 → Fin (n * M) → AF F ⊗[F] E) :
    projInf ((flat _ n M).symm Y) = (flat _ n M).symm (projInf Y) := rfl

theorem projFin_flat_symm {n M : ℕ} (Y : Fin 1 → Fin (n * M) → AF F ⊗[F] E) :
    projFin ((flat _ n M).symm Y) = (flat _ n M).symm (projFin Y) := rfl

theorem isSchwartzBruhat_flat {n M : ℕ} {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ}
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ ∘ (flat _ n M).symm) := by
  obtain ⟨k, P, Q, hP, hQ, hs⟩ := hΦ
  refine ⟨k, fun i => P i ∘ (flat _ n M).symm, fun i => Q i ∘ (flat _ n M).symm, fun i => ?_,
    fun i => ⟨(hQ i).1.comp_continuous (flat _ n M).symm.continuous,
      (hQ i).2.comp_homeomorph (flat _ n M).symm.toHomeomorph⟩, fun Y => ?_⟩
  · obtain ⟨N, e, c1, c2, f, hf⟩ := hP i
    refine ⟨N, (flat (Ainf F ⊗[F] E) n M).symm.toAddEquiv.trans e, c1.comp (flat _ n M).symm.continuous,
      (flat _ n M).continuous.comp c2, f, fun X => ?_⟩
    exact hf _
  · simp only [Function.comp_apply, hs, projInf_flat_symm, projFin_flat_symm]

theorem continuous_integrable [NumberField E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {n M : ℕ}
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : dx.IsAddHaarMeasure)
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ} (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    Continuous Φ ∧ Integrable Φ dx := by
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor n M
  haveI := hBor 1 (n * M)
  let e := flat (AF F ⊗[F] E) n M
  haveI : (dx.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map _ e.toAddEquiv.toAddMonoidHom e.continuous e.surjective
      e.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  obtain ⟨c, hi⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt.continuous_integrable_of_isSchwartzBruhat F E σ hCM (n * M)
    (dx.map e) inferInstance _ (isSchwartzBruhat_flat hΦ)
  have hcomp : (Φ ∘ e.symm) ∘ e = Φ := by
    funext X
    simp
  refine ⟨hcomp ▸ c.comp e.continuous, ?_⟩
  have := (e.toHomeomorph.measurableEmbedding.integrable_map_iff).1 hi
  rwa [show (Φ ∘ (flat _ n M).symm) ∘ e.toHomeomorph = Φ from hcomp] at this

theorem integrable_mul_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), dx.IsAddHaarMeasure →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ b : HermR (AF F) σ n, Integrable (fun X => Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)))) dx := by
  intro F E _ _ _ _ _ σ hCM M J n ψ hψ dx hdx Φ hΦ b
  obtain ⟨h1, -, -, -, -, htr, -, hBor, -, hgram⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor n M
  obtain ⟨hc, hi⟩ := continuous_integrable σ hCM dx hdx hΦ
  have hph : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
      ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) := by
    refine hψ.1.comp (continuous_const.mul (htr.comp ?_))
    exact (continuous_const.matrix_mul (hgram n M J)).matrix_trace
  refine hi.mono (hc.mul hph).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
  rw [norm_mul, hψ.2.1, mul_one]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Phase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentNongenericQuotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg.TwoSeg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem range_le_comap (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (g : GL (Fin N) k) :
    LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (π g) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨σ g w, Representation.IntertwiningMap.isIntertwining _ _ f g w⟩

def quotRep (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) : Representation ℂ (GL (Fin N) k) (V ⧸ LinearMap.range f.toLinearMap) where
  toFun g := (LinearMap.range f.toLinearMap).mapQ _ (π g) (range_le_comap π σ f g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

theorem mkQ_mem_twKer (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (U : Subgroup (GL (Fin N) k)) (θ : U →* ℂˣ) {v : V} (hv : v ∈ twKer π U θ) :
    (LinearMap.range f.toLinearMap).mkQ v ∈ twKer (quotRep π σ f) U θ := by
  have hle : twKer π U θ ≤ (twKer (quotRep π σ f) U θ).comap (LinearMap.range f.toLinearMap).mkQ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, u, rfl⟩
    refine Submodule.subset_span ⟨n, (LinearMap.range f.toLinearMap).mkQ u, ?_⟩
    simp only [LinearMap.map_sub, LinearMap.map_smul]
    rfl
  exact hle hv

theorem isSmooth_of_injective (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (hπ : IsSmooth π) : IsSmooth σ := by
  intro w
  have : {g : GL (Fin N) k | σ g w = w} = {g | π g (f w) = f w} := by
    ext g
    simp only [Set.mem_setOf_eq]
    rw [← Representation.IntertwiningMap.isIntertwining _ _ f g w, hf.eq_iff]
  rw [this]
  exact hπ _

theorem not_isGeneric_quotRep {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (hπ : IsSmooth π)
    (hr : Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1) (hσ : IsGeneric σ) :
    ¬ IsGeneric (quotRep π σ f) := by
  rw [isGeneric_iff_isGenericFor hψ h1] at hσ ⊢
  have hσs := isSmooth_of_injective π σ f hf hπ
  unfold IsGenericFor at hσ ⊢
  rw [not_nontrivial_iff_subsingleton]

  obtain ⟨q, hq⟩ := exists_ne (0 : TwJacquet σ (unipB k (Fin N)) (whitChar ψ N))
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hw : w ∉ twKer σ (unipB k (Fin N)) (whitChar ψ N) := fun h => hq ((Submodule.Quotient.mk_eq_zero _).2 h)
  have hfw : f w ∉ twKer π (unipB k (Fin N)) (whitChar ψ N) := fun h =>
    hw (GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N σ π hσs hπ f.toLinearMap hf
      (fun g v => Representation.IntertwiningMap.isIntertwining _ _ f g v) w h)
  obtain ⟨e, he⟩ := rank_le_one_iff.1 hr
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  obtain ⟨a, ha⟩ := he (Submodule.Quotient.mk (f w))
  obtain ⟨b, hb⟩ := he (Submodule.Quotient.mk v)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hfw ((Submodule.Quotient.mk_eq_zero _).1 (by rw [← ha, zero_smul]))
  have hk : v - (b / a) • f w ∈ twKer π (unipB k (Fin N)) (whitChar ψ N) := by
    refine (Submodule.Quotient.mk_eq_zero _).1 ?_
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← ha, ← hb, smul_smul,
      div_mul_cancel₀ _ ha0, sub_self]
  have h2 := mkQ_mem_twKer π σ f _ _ hk
  have h3 : (LinearMap.range f.toLinearMap).mkQ (f w) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  rw [map_sub, map_smul, h3, smul_zero, sub_zero] at h2
  exact h2

end GlobalTheory.CompanionTheory.BZSeg.TwoSeg

namespace GlobalTheory.CompanionTheory.BZSeg

open GlobalTheory.CompanionTheory.BZSeg.TwoSeg


end GlobalTheory.CompanionTheory.BZSeg
end
end

