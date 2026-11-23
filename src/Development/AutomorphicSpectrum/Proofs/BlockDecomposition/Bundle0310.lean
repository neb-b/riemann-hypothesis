module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0299
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSequenceOperatorSequence
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

theorem π_cokOps {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)}
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k) (e : ℕ) :
    cokernel.π (T (Fin.last k) e) ≫ cokOps hc i e =
      T i.castSucc (e + 1) ≫ cokernel.π (T (Fin.last k) (e + 1)) := by
  exact cokernel.π_desc _ _ _

theorem app_comp_apply {X : Scheme.{0}} {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens)
    (x : Γ(A, U)) : g.app U (f.app U x) = (f ≫ g).app U x := by
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

theorem app_apply_eq_of_comp_eq {X : Scheme.{0}} {A B B' C : X.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ B') (g' : B' ⟶ C) (h : f ≫ g = f' ≫ g') (U : X.Opens) (x : Γ(A, U)) :
    g.app U (f.app U x) = g'.app U (f'.app U x) := by
  rw [app_comp_apply, app_comp_apply, h]

theorem cokOpSeq {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : OpSeq (k + 1) M T d) :
    OpSeq k (cokSeq M T) (cokOps hM.comm) d := by
  refine ⟨?_, cokOps_comm hM.comm, ?_⟩
  · intro e
    have := (hM.coherent e).1
    exact isCoherent_cokernel (T (Fin.last k) e) (hM.coherent (e + 1))
  · intro e he U
    have := (hM.coherent (e + 1)).1
    have := (hM.coherent (e + 1 + 1)).1
    rw [eq_top_iff]
    rintro y -
    obtain ⟨z, rfl⟩ := surjective_cokernel_π_app (T (Fin.last k) (e + 1)) U.2 y
    have hz : z ∈ Submodule.span Γ(X, U) (⋃ i, Set.range ((T i (e + 1)).app U)) := by
      rw [hM.gen (e + 1) (by omega) U]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hz
      induction i using Fin.lastCases with
      | last =>
        have h0 : T (Fin.last k) (e + 1) ≫ cokernel.π (T (Fin.last k) (e + 1)) = 0 :=
          cokernel.condition _
        rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, h0,
          Scheme.Modules.Hom.zero_app]
        exact Submodule.zero_mem _
      | cast i =>
        refine Submodule.subset_span (Set.mem_iUnion.2 ⟨i, (cokernel.π (T (Fin.last k) e)).app U x, ?_⟩)
        exact app_apply_eq_of_comp_eq (B := cokSeq M T e) (C := cokSeq M T (e + 1))
          (cokernel.π (T (Fin.last k) e)) (cokOps hM.comm i e) (T i.castSucc (e + 1))
          (cokernel.π (T (Fin.last k) (e + 1))) (π_cokOps hM.comm i e) U.1 x
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Scheme.Modules.Hom.app_smul]
      exact Submodule.smul_mem _ _ ha

end GlobalTheory.CompanionTheory.GE.UV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSupportedInPreimage
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.PSupp

theorem cokernel_supportedIn_preimage : ∀ {X : Scheme.{0}} (O : X.Opens) {P : X.Modules} {E : (O : Scheme.{0}).Modules}, P.IsQuasicoherent → E.IsQuasicoherent → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ Bb : Subobject P, ∀ B : Subobject E, (B : (O : Scheme.{0}).Modules).IsQuasicoherent → (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → ∀ (C : Set X), (∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) C → secs Bb U = Set.univ) → Scheme.Modules.SupportedIn (cokernel B.arrow) (O.ι.base ⁻¹' C) := by
  intro X O P E hP hE f hf Bb B hB hsec C hC
  haveI : P.IsQuasicoherent := hP
  haveI : E.IsQuasicoherent := hE
  haveI : Epi f := hf
  refine GlobalTheory.CompanionTheory.GE.Comb.supportedIn_of_secs_eq_univ hE hB fun W hW hd => ?_
  have hWi : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
  have hdis : Disjoint ((O.ι ''ᵁ W : X.Opens) : Set X) C := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ hyC
    exact Set.disjoint_left.1 hd hy hyC
  rw [hsec W hW, hC _ hWi hdis, Set.image_univ]
  refine Function.Surjective.range_eq fun y => ?_
  obtain ⟨z, rfl⟩ := surjective_app_of_epi f hW y
  refine ⟨(P.restrictAppIso O.ι W).hom z, ?_⟩
  simp

end GlobalTheory.CompanionTheory.GE.PSupp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLogSizeM
section
noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GlobalTheory.CompanionTheory.Size

namespace GlobalTheory.CompanionTheory.SizeCont

theorem continuous_iSup_fin {X ι : Type} [TopologicalSpace X] [Fintype ι] (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) : Continuous fun x => ⨆ i, f i x := by
  rcases isEmpty_or_nonempty ι with h | h
  · simpa [Real.iSup_of_isEmpty] using continuous_const
  · have : (fun x => ⨆ i, f i x) = fun x => Finset.univ.sup' Finset.univ_nonempty fun i => f i x := by
      funext x
      rw [Finset.sup'_univ_eq_ciSup]
    rw [this]
    exact Continuous.finset_sup'_apply _ fun i _ => hf i

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem continuous_cW (w : HeightOneSpectrum (𝓞 E)) : Continuous (cW w : Ad E → w.adicCompletion E) :=
  (RestrictedProduct.continuous_eval w).comp continuous_snd

theorem continuous_elem (p : Fin n × Fin n) :
    Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => A p.1 p.2 :=
  continuous_id.matrix_elem p.1 p.2

theorem continuous_inf (v : InfinitePlace E) : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
    Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) :=
  Real.continuous_posLog.comp (continuous_iSup_fin _ fun p =>
    (((continuous_cV v).comp (continuous_elem p)).norm).pow 2)

theorem continuous_fin (w : HeightOneSpectrum (𝓞 E)) : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
    Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) :=
  Real.continuous_posLog.comp (continuous_iSup_fin _ fun p =>
    ((continuous_cW w).comp (continuous_elem p)).norm)

theorem eventually_finsum (hS : SzFin) (A₀ : Matrix (Fin n) (Fin n) (Ad E)) :
    ∀ᶠ A in 𝓝 A₀, ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) =
      ∑ w ∈ (hS E (Fin n) (Fin n) A₀).toFinset,
        Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) := by
  have hev : ∀ p : Fin n × Fin n, ∀ᶠ A : Matrix (Fin n) (Fin n) (Ad E) in 𝓝 A₀,
      ∀ w, ‖cW w (A p.1 p.2)‖ ≤ max ‖cW w (A₀ p.1 p.2)‖ 1 := fun p =>
    (continuous_elem p).continuousAt.eventually (eventually_fin (A₀ p.1 p.2))
  filter_upwards [Filter.eventually_all.2 hev] with A hA
  refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  by_contra hn
  have h0 : sz (A₀.map (cW w)) ≤ 1 := not_lt.1 hn
  refine hw ((Real.posLog_eq_zero_iff _).2 ?_)
  have h1 : 0 ≤ ⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  rw [abs_of_nonneg h1]
  refine Real.iSup_le (fun p => (hA p w).trans (max_le ?_ le_rfl)) zero_le_one
  exact (le_sup (fun q : Fin n × Fin n => ‖cW w (A₀ q.1 q.2)‖) p).trans h0

theorem continuous_logSizeM (hS : SzFin) :
    Continuous (logSizeM : Matrix (Fin n) (Fin n) (Ad E) → ℝ) := by
  refine continuous_iff_continuousAt.2 fun A₀ => ?_
  have hc : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
      ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) +
        ∑ w ∈ (hS E (Fin n) (Fin n) A₀).toFinset,
          Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) :=
    (continuous_finsetSum _ fun v _ => continuous_inf v).add
      (continuous_finsetSum _ fun w _ => continuous_fin w)
  refine hc.continuousAt.congr ?_
  filter_upwards [eventually_finsum hS A₀] with A hA
  rw [logSizeM, hA]

theorem sizeCont : SzFin → SizeCont := by
  intro hS E _ _ _ n
  have h := continuous_logSizeM (E := E) (n := n) hS
  exact (h.comp Units.continuous_val).add (h.comp Units.continuous_coe_inv)

end GlobalTheory.CompanionTheory.SizeCont

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnFderivApply
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.RCalc.ByParts

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_deriv_eq_zero {Γ V : Type*} [TopologicalSpace Γ] [SecondCountableTopology Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] {μ : Measure Γ} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F F' : ℝ → Γ → V} {K : Set Γ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) (C : ℝ)
    (hc : ∀ t ∈ Metric.ball (0 : ℝ) ε, Continuous (F t)) (hc' : Continuous (F' 0))
    (hd : ∀ y, ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivAt (fun s => F s y) (F' t y) t)
    (hz : ∀ y, y ∉ K → F 0 y = 0)
    (hz' : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y, y ∉ K → F' t y = 0)
    (hb : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y ∈ K, ‖F' t y‖ ≤ C)
    (hconst : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∫ y, F t y ∂μ = ∫ y, F 0 y ∂μ) :
    ∫ y, F' 0 y ∂μ = 0 := by
  have hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ :=
    eventually_of_mem hs fun t ht => (hc t ht).aestronglyMeasurable
  have hint : Integrable (F 0) μ :=
    (hc 0 (Metric.mem_ball_self hε)).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hz)
  have hbi : Integrable (K.indicator fun _ => C) μ :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖F' t y‖ ≤ K.indicator (fun _ => C) y :=
    ae_of_all _ fun y t ht => by
      by_cases hy : y ∈ K
      · simpa [hy] using hb t ht y hy
      · simp [hy, hz' t ht y hy]
  have h1 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hint hc'.aestronglyMeasurable hbound hbi
    (ae_of_all _ hd)).2
  have h2 : HasDerivAt (fun t => ∫ y, F t y ∂μ) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (∫ y, F 0 y ∂μ)).congr_of_eventuallyEq ?_
    exact eventually_of_mem hs hconst
  exact h1.unique h2

theorem continuousOn_fderiv_apply {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace P] {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {S : Set P} {A B : P → E} (hA : ContinuousOn A S) (hB : ContinuousOn B S) (hm : MapsTo A S U) :
    ContinuousOn (fun p => fderiv ℝ f (A p) (B p)) S := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.continuousOn.comp hA hm).clm_apply hB

theorem hasDerivAt_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (g v : E) (t : ℝ) (hf : DifferentiableAt ℝ f (g + t • v)) :
    HasDerivAt (fun s : ℝ => f (g + s • v)) (fderiv ℝ f (g + t • v) v) t := by
  have h2 : HasDerivAt (fun s : ℝ => g + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add g
  exact hf.hasFDerivAt.comp_hasDerivAt t h2

variable {n : ℕ}

def c (X : Mat n) (t : ℝ) : Mat n := 1 + t • X

theorem continuous_c (X : Mat n) : Continuous (c X) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem c_zero (X : Mat n) : c X 0 = 1 := by simp [c]

theorem mul_c (y X : Mat n) (t : ℝ) : y * c X t = y + t • (y * X) := by
  simp [c, mul_add]

theorem exists_eps (X : Mat n) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, c X t ∈ GLs n := by
  have h : IsOpen (c X ⁻¹' GLs n) := isOpen_GLs.preimage (continuous_c X)
  have h0 : (0 : ℝ) ∈ c X ⁻¹' GLs n := by simp [c_zero, GLs]
  obtain ⟨ε, hε, h'⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.mem_nhds h0)
  exact ⟨ε, hε, h'⟩

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem mul_mem_GLs' {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  have h : x.det ≠ 0 := hx
  simp [GLs, Matrix.det_nonsing_inv, h]

def toG {x : Mat n} (hx : x ∈ GLs n) : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx

theorem secondCountable_G : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem lg_le_lg_mul (hL : LgFacts) (y : G n) {x : Mat n} (hx : x ∈ GLs n) : lg y.val ≤ lg (y.val * x) + lg x := by
  obtain ⟨hsub, hinv, -⟩ := hL n
  have hdet : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have e : y.val = (y.val * x) * x⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  calc lg y.val = lg ((y.val * x) * x⁻¹) := by rw [← e]
    _ ≤ lg (y.val * x) + lg x⁻¹ := hsub _ (mul_mem_GLs' (val_mem_GLs y) hx) _ (inv_mem_GLs hx)
    _ = lg (y.val * x) + lg x := by rw [hinv x hx]

theorem fderiv_eq_zero_far (hL : LgFacts) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V} {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → f y = 0) {x : Mat n} (hx : x ∈ GLs n) (hlg : R < lg x) : fderiv ℝ f x = 0 := by
  obtain ⟨-, -, -, hsm, -⟩ := hL n
  have ho : IsOpen (GLs n ∩ lg ⁻¹' Ioi R) := hsm.continuousOn.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have he : f =ᶠ[𝓝 x] fun _ => (0 : V) :=
    eventually_of_mem (ho.mem_nhds ⟨hx, hlg⟩) fun y hy => hR y hy.1 hy.2
  rw [he.fderiv_eq]
  simp

theorem ibp_of (hL : LgFacts) (hU : Unimod) : IBP := by
  intro n _ _ μ _ V _ _ _ f hf hC X
  obtain ⟨R, hR⟩ := hC
  obtain ⟨-, -, -, hsm, hcpt, -⟩ := hL n
  haveI := (hU n μ).1
  haveI : SecondCountableTopology (G n) := secondCountable_G
  obtain ⟨ε, hε, hcε⟩ := exists_eps X
  have hball : ∀ t ∈ Metric.ball (0 : ℝ) ε, c X t ∈ GLs n := fun t ht => hcε t (Metric.ball_subset_closedBall ht)
  have hmem : ∀ (y : G n), ∀ t ∈ Metric.closedBall (0 : ℝ) ε, y.val * c X t ∈ GLs n :=
    fun y t ht => mul_mem_GLs' (val_mem_GLs y) (hcε t ht)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, lg (c X t) ≤ C₀ := by
    have hcont : ContinuousOn (fun t => lg (c X t)) (Metric.closedBall (0 : ℝ) ε) :=
      hsm.continuousOn.comp (continuous_c X).continuousOn hcε
    obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℝ) ε).bddAbove_image hcont
    exact ⟨C₀, fun t ht => hC₀ (mem_image_of_mem _ ht)⟩
  set K : Set (G n) := {y : G n | lg y.val ≤ R + C₀} with hKdef
  have hK : IsCompact K := hcpt (R + C₀)
  have hfar : ∀ (y : G n), y ∉ K → ∀ t ∈ Metric.closedBall (0 : ℝ) ε, R < lg (y.val * c X t) := by
    intro y hy t ht
    have h1 : R + C₀ < lg y.val := not_le.1 hy
    have h2 := lg_le_lg_mul hL y (hcε t ht)
    have h3 := hC₀ t ht
    linarith
  have hvalc : Continuous fun y : G n => y.val := Units.continuous_val
  obtain ⟨C, hCb⟩ : ∃ C, ∀ p ∈ K ×ˢ Metric.closedBall (0 : ℝ) ε,
      ‖fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X)‖ ≤ C := by
    have hcont : ContinuousOn (fun p : G n × ℝ => fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X))
        (K ×ˢ Metric.closedBall (0 : ℝ) ε) := by
      refine continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_
      · exact ((hvalc.comp continuous_fst).mul ((continuous_c X).comp continuous_snd)).continuousOn
      · exact ((hvalc.comp continuous_fst).mul continuous_const).continuousOn
      · exact fun p hp => hmem p.1 p.2 hp.2
    exact (hK.prod (isCompact_closedBall (0 : ℝ) ε)).exists_bound_of_continuousOn hcont
  have key := integral_deriv_eq_zero (μ := μ) (F := fun t (y : G n) => f (y.val * c X t))
    (F' := fun t (y : G n) => fderiv ℝ f (y.val * c X t) (y.val * X)) hK hε C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [c_zero, Rd] using key
  · intro t ht
    exact hf.continuousOn.comp_continuous (hvalc.mul continuous_const)
      fun y => hmem y t (Metric.ball_subset_closedBall ht)
  · refine continuousOn_univ.1 (continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_)
    · exact (hvalc.mul continuous_const).continuousOn
    · exact (hvalc.mul continuous_const).continuousOn
    · exact fun y _ => hmem y 0 (Metric.mem_closedBall_self hε.le)
  · intro y t ht
    have hd : DifferentiableAt ℝ f (y.val + t • (y.val * X)) := by
      rw [← mul_c]
      exact differentiableAt_of_smooth hf (hmem y t (Metric.ball_subset_closedBall ht))
    have := hasDerivAt_line (y.val) (y.val * X) t hd
    have e1 : (fun s : ℝ => f (y.val * c X s)) = fun s : ℝ => f (y.val + s • (y.val * X)) := by
      funext s; rw [mul_c]
    show HasDerivAt (fun s : ℝ => f (y.val * c X s)) (fderiv ℝ f (y.val * c X t) (y.val * X)) t
    rw [e1, mul_c]
    exact this
  · intro y hy
    exact hR _ (hmem y 0 (Metric.mem_closedBall_self hε.le)) (hfar y hy 0 (Metric.mem_closedBall_self hε.le))
  · intro t ht y hy
    have ht' := Metric.ball_subset_closedBall ht
    simp only [fderiv_eq_zero_far hL hR (hmem y t ht') (hfar y hy t ht'), ContinuousLinearMap.zero_apply]
  · intro t ht y hy
    exact hCb (y, t) ⟨hy, Metric.ball_subset_closedBall ht⟩
  · intro t ht
    have h0 := integral_mul_right_eq_self (μ := μ) (fun y : G n => f y.val) (toG (hball t ht))
    simpa [toG, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible, c_zero] using h0

end GlobalTheory.CompanionTheory.RCalc.ByParts

theorem GlobalTheory.CompanionTheory.RCalc.ibp : GlobalTheory.CompanionTheory.RCalc.IBP :=
  GlobalTheory.CompanionTheory.RCalc.ByParts.ibp_of _root_.GlobalTheory.CompanionTheory.LengthGL.lgFacts _root_.GlobalTheory.CompanionTheory.GLUnimod.unimod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatThickeningQuotientStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_thickening_quotient : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))), FlatT T → FlatT (qT hn T) := by
  first | exact @GlobalTheory.CompanionTheory.FlatThick.flatT_qT | exact GlobalTheory.CompanionTheory.FlatThick.flatT_qT | (intros; apply GlobalTheory.CompanionTheory.FlatThick.flatT_qT <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameRight
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GlobalTheory.CompanionTheory.DegMoveProof

namespace GlobalTheory.CompanionTheory.DegRightProof

theorem frame_right {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n k : ℕ} (x h : GA E n)
    (M : Matrix (Fin n) (Fin k) (Ad E)) :
    h.val * (((x * h)⁻¹ : GA E n).val * M) = (x⁻¹ : GA E n).val * M := by
  rw [← Matrix.mul_assoc, ← Units.val_mul, _root_.mul_inv_rev, mul_inv_cancel_left]

theorem degRight_of : MulF → MulI → SzFin → FinSupp → DegRight := by
  intro hF hI hSz hFS E _ _ _ n
  have hb : (0 : ℝ) ≤ (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) :=
    mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨n * (1 + (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)), by positivity,
    fun x h W => ?_⟩
  obtain ⟨hLI, -⟩ := lin_basisMat W
  have hkn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
  obtain ⟨N, hN⟩ := exists_left_inv (basisMat W) hLI
  have hY : (N.map (algebraMap E (Ad E)) * (x * h : GA E n).val) *
      (((x * h)⁻¹ : GA E n).val * (basisMat W).map (algebraMap E (Ad E))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (x * h : GA E n).val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc := core hF hI hSz hFS hkn h _ _ hY
  rw [frame_right] at hc
  have e1 : deg (x * h) W = degG (x * h) (basisMat W) := rfl
  have e2 : deg x W = degG x (basisMat W) := rfl
  rw [e1, e2]
  simp only [degG]
  have hS := logSizeM_nonneg h.val
  have hS' := logSizeM_nonneg (h⁻¹ : GA E n).val
  have hsz : logSize h = logSizeM h.val + logSizeM (h⁻¹ : GA E n).val := rfl
  rw [hsz]
  generalize logSizeM h.val = S at *
  generalize logSizeM (h⁻¹ : GA E n).val = S' at *
  generalize (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) = b at *
  have hpos : 0 ≤ (n : ℝ) * (S' + b * S + b * S') := by positivity
  nlinarith [hc, hpos]

end GlobalTheory.CompanionTheory.DegRightProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafQuasicoherent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem isQuasicoherent_imageSubobject {X : Scheme.{0}} {A B : X.Modules}
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) (f : A ⟶ B) :
    (imageSubobject f : X.Modules).IsQuasicoherent := by
  haveI := hA
  haveI := hB
  have hK : (kernel (cokernel.π f)).IsQuasicoherent := inferInstance
  exact GlobalTheory.QCoh.isQuasicoherent_of_iso
    (Abelian.imageIsoImage f ≪≫ (imageSubobjectIso f).symm)

theorem isQuasicoherent_genSub : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)),
    (genSub hH n b : X.Modules).IsQuasicoherent := by
  intro X H hH P hP n b
  have hO : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := inferInstance
  have hS : (GlobalTheory.twistZ (SheafOfModules.unit X.ringCatSheaf) H (-n)).IsQuasicoherent :=
    GlobalTheory.Twist.isQuasicoherent_twist (F := SheafOfModules.unit X.ringCatSheaf)
      (GlobalTheory.Twist.isLB_lbZPow hH (-n))
  exact isQuasicoherent_imageSubobject hS hP _

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

