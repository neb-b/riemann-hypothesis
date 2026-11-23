module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
section
open Set Filter GlobalTheory.AdelicU NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology ComplexConjugate ContDiff Matrix

noncomputable section

namespace GlobalTheory.Orb

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def IsSmoothRealFam (u : P → GAd σ J) : Prop :=
  (∀ t, projFin σ J (u t) = 1) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j, ContDiff ℝ ∞ fun t => archMat σ J τ (projArch σ J w (u t)) i j


omit [NumberField E] in
theorem isSmoothRealFam_one : IsSmoothRealFam fun _ : P => (1 : GAd σ J) :=
  ⟨fun _ => map_one _, fun _ _ _ _ => contDiff_const⟩


omit [NumberField E] in
theorem IsSmoothRealFam.mul {u v : P → GAd σ J} (hu : IsSmoothRealFam u) (hv : IsSmoothRealFam v) :
    IsSmoothRealFam fun t => u t * v t := by
  refine ⟨fun t => by rw [map_mul, hu.1, hv.1, one_mul], fun w τ i j => ?_⟩
  simp only [map_mul, Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hu.2 w τ i k).mul (hv.2 w τ k j)


omit [NumberField E] in
theorem IsSmoothRealFam.comp {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {u : P → GAd σ J}
    (hu : IsSmoothRealFam u) {p : Q → P} (hp : ContDiff ℝ ∞ p) : IsSmoothRealFam fun t => u (p t) :=
  ⟨fun _ => hu.1 _, fun w τ i j => (hu.2 w τ i j).comp hp⟩


omit [NumberField E] in
theorem isSmoothRealFam_prod {k : ℕ} {u : Fin k → P → GAd σ J} (hu : ∀ i, IsSmoothRealFam (u i)) :
    IsSmoothRealFam fun t => (List.ofFn fun i => u i t).prod := by
  induction k with
  | zero => simpa using isSmoothRealFam_one
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hu 0).mul (ih fun i => hu i.succ)


omit [NumberField E] in
theorem infCoord_mul (x : GInf σ J) (y : GAd σ J) : infCoord σ J (x * projInf σ J y) =
    fun w τ i j => ∑ k, infCoord σ J x w τ i k * archMat σ J τ (projArch σ J w y) k j := by
  funext w τ i j
  simp only [infCoord, archCoord, matCoord, map_mul, Matrix.mul_apply, projInfArch_projInf]

theorem IsSmoothRealFam.contDiff {u : P → GAd σ J} (hu : IsSmoothRealFam u) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J)
    (g : GAd σ J) : ContDiff ℝ ∞ fun t => f (g * u t) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨-, Φ, hΦ, e⟩, b, -, rfl⟩ := hf
    simp only [infFin, map_mul, hu.1, mul_one, e, infCoord_mul]
    refine (hΦ.comp (contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => contDiff_const.mul (hu.2 w τ k j))).mul contDiff_const
  | zero => exact contDiff_const
  | add f f' _ _ h h' => exact h.add h'
  | smul a f _ h => exact h.const_smul a

theorem IsSmoothRealFam.deriv_mem_ccInf {u : ℝ → GAd σ J} (hu : IsSmoothRealFam u) (hc : Continuous u)
    (h0 : u 0 = 1) {a : GInf σ J → ℂ} (ha : a ∈ CcInf σ J) :
    (fun x => deriv (fun t => a (x * projInf σ J (u t))) 0) ∈ CcInf σ J := by
  obtain ⟨hs, Φ, hΦ, e⟩ := ha
  refine ⟨.intro hs fun x hx => ?_, fun y => fderiv ℝ Φ y fun w τ i j =>
    ∑ k, y w τ i k * deriv (fun t => archMat σ J τ (projArch σ J w (u t)) k j) 0, ?_, fun x => ?_⟩
  · have h1 : Tendsto (fun t => x * projInf σ J (u t)) (𝓝 0) (𝓝 x) := by
      simpa [h0] using (continuous_const.mul ((continuous_projInf σ J).comp hc)).tendsto (f := fun t => x * projInf σ J (u t)) 0
    rw [EventuallyEq.deriv_eq (f := fun _ => (0 : ℂ)) (h1.eventually (notMem_tsupport_iff_eventuallyEq.1 hx)),
      deriv_const]
  · refine (hΦ.fderiv_right (m := ∞) le_rfl).clm_apply ?_
    exact contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) τ) i) k).mul
        contDiff_const
  · have h1 : HasDerivAt (fun t => infCoord σ J (x * projInf σ J (u t))) (fun w τ i j =>
        ∑ k, infCoord σ J x w τ i k * deriv (fun t => archMat σ J τ (projArch σ J w (u t)) k j) 0) 0 := by
      simp only [infCoord_mul]
      exact hasDerivAt_pi.2 fun w => hasDerivAt_pi.2 fun τ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j =>
        HasDerivAt.fun_sum fun k _ => ((hu.2 w τ k j).differentiable (by simp) 0).hasDerivAt.const_mul _
    have h2 := (hΦ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 h1
    simp only [h0, map_one, mul_one] at h2
    simp only [e]
    exact h2.deriv

theorem IsSmoothRealFam.deriv_mem_ccAd {u : ℝ → GAd σ J} (hu : IsSmoothRealFam u) (hc : Continuous u)
    (h0 : u 0 = 1) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    (fun g => deriv (fun t => f (g * u t)) 0) ∈ CcAd σ J := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    convert infFin_mem_ccAd (hu.deriv_mem_ccInf hc h0 ha) hb using 1
    funext g
    simp only [infFin, map_mul, hu.1, mul_one, deriv_mul_const_field]
  | zero =>
    simp only [Pi.zero_apply, deriv_const]
    exact (CcAd σ J).zero_mem
  | add f f' hf hf' h h' =>
    convert (CcAd σ J).add_mem h h' using 1
    funext g
    exact deriv_fun_add ((hu.contDiff hf g).differentiable (by simp) 0) ((hu.contDiff hf' g).differentiable (by simp) 0)
  | smul c f _ h =>
    convert (CcAd σ J).smul_mem c h using 1
    funext g
    exact deriv_fun_const_smul_field c _

theorem isSmoothRealFam_embArch (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {x : P → GArch σ J w}
    (hx : ∀ i j, ContDiff ℝ ∞ fun t => archMat σ J τ (x t) i j) :
    IsSmoothRealFam (fun t => embArch σ J w (x t)) ∧ Continuous fun t => embArch σ J w (x t) := by
  refine ⟨⟨fun t => projFin_embArch σ J w _, fun w' τ' i j => ?_⟩, (continuous_embArch σ J w).comp
    ((isEmbedding_archMat J h τ).continuous_iff.2 (continuous_pi fun i => continuous_pi fun j => (hx i j).continuous))⟩
  by_cases e : w' = w
  · subst e
    simp only [projArch_embArch_self]
    rcases infEmb_eq_or_conj h τ τ' with e | e
    · simpa only [archMat_apply, e] using hx i j
    · simp only [archMat_apply, e]
      exact Complex.conjCLE.contDiff.comp (hx i j)
  · simp only [projArch_embArch_ne σ J e]
    exact contDiff_const

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_exp_smul_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • X) : Matrix (Fin n) (Fin n) ℂ) i j := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
    contDiff_iff_contDiffAt.2 fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).contDiffAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp
    (h.comp (contDiff_id.smul contDiff_const))

end

end General

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem isSmoothRealFam_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) :
    IsSmoothRealFam (oneP θ V τ X) ∧ Continuous (oneP θ V τ X) ∧ oneP θ V τ X 0 = 1 := by
  choose x hx using fun t : ℝ => exists_archEquiv_eq V (embOverOf D τ) rfl
    (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t)
  have e : oneP θ V τ X = fun t => embArch _ _ _ (x t) := funext fun t => by
    rw [oneP, ← hx, atTau_archEquiv hθ V _ rfl]
  have h := isSmoothRealFam_embArch (isCMExt_host D) (embOverOf D τ) (x := x) fun i j => by
    simp only [archMat_eq_archEquiv _ (isCMExt_host D), hx]
    exact contDiff_exp_smul_entry X i j
  refine ⟨e ▸ h.1, e ▸ h.2, ?_⟩
  have h1 := atTau_archEquiv hθ V (embOverOf D τ) rfl 1
  rw [map_one, map_one] at h1
  rw [oneP, zero_smul, NormedSpace.exp_zero]
  exact h1

theorem ccGA_smooth_and_Rder_mem (D : D7) (V : HSp D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (f : GA D V → ℂ)
    (hf : f ∈ CcGA V) :
    (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ∧
    ∀ τ, ∀ X ∈ lieAt V τ, Rder θ V τ X f ∈ CcGA V :=
  ⟨fun _ _ _ hX g => (isSmoothRealFam_prod fun i => (isSmoothRealFam_oneP hθ (hX i)).1.comp
      (contDiff_apply ℝ (fun _ => ℝ) i)).contDiff hf g,
    fun _ _ hX => have h := isSmoothRealFam_oneP hθ hX; h.1.deriv_mem_ccAd h.2.1 h.2.2 hf⟩

end Record

end GlobalTheory.Orb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZero
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis.Conv.Discr

open Filter Topology

section Abstract

variable {A E : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Field E]
  (ι : E →+* A)

theorem finite_of_isCompact (h : ∃ U ∈ 𝓝 (0 : A), ∀ x : E, ι x ∈ U → x = 0) {Ω : Set A}
    (hΩ : IsCompact Ω) : {x : E | ι x ∈ Ω}.Finite := by
  obtain ⟨U, hU, hx⟩ := h
  refine hΩ.induction_on (p := fun s => {x : E | ι x ∈ s}.Finite) (by simp)
    (fun s t hst ht => ht.subset fun x hx => hst hx)
    (fun s t hs ht => (hs.union ht).subset fun x hx => hx) fun a _ => ?_
  have hc : ContinuousAt (fun p : A × A => p.1 - p.2) (a, a) := by fun_prop
  have h1 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 (a, a) :=
    hc.preimage_mem_nhds (by simpa using hU)
  rw [nhds_prod_eq, Filter.mem_prod_self_iff] at h1
  obtain ⟨V, hV, hVU⟩ := h1
  refine ⟨V, mem_nhdsWithin_of_mem_nhds hV, Set.Subsingleton.finite fun x hx' y hy => ?_⟩
  refine sub_eq_zero.1 (hx _ ?_)
  rw [map_sub]
  exact hVU (Set.mk_mem_prod hx' hy)

theorem eventually_eq_zero [T2Space A] (h : ∃ U ∈ 𝓝 (0 : A), ∀ x : E, ι x ∈ U → x = 0)
    {Ω : Set A} (hΩ : IsCompact Ω) {s ε : A} (hs : Tendsto (fun m : ℕ => s ^ m) atTop (𝓝 ε))
    (hε : ¬ IsUnit ε) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, ι x = s ^ m * ω → x = 0 := by
  have hK : IsCompact ((fun p : A × A => p.1 * p.2) ''
      (insert ε (Set.range fun m : ℕ => s ^ m) ×ˢ Ω)) :=
    (hs.isCompact_insert_range.prod hΩ).image (by fun_prop)
  have hfin := finite_of_isCompact ι h hK
  have hev : ∀ x : E, ∀ᶠ m : ℕ in atTop, ∀ ω ∈ Ω, ι x = s ^ m * ω → x = 0 := by
    intro x
    by_cases hx : x = 0
    · exact Eventually.of_forall fun _ _ _ _ => hx
    have h1 : ∀ᶠ t in 𝓝 ε, ∀ ω ∈ Ω, ι x ≠ t * ω := by
      refine hΩ.eventually_forall_of_forall_eventually (P := fun t ω => ι x ≠ t * ω)
        fun ω _ => ?_
      have ho : IsOpen {p : A × A | ι x ≠ p.1 * p.2} :=
        isOpen_ne_fun continuous_const (by fun_prop)
      refine ho.mem_nhds fun he => hε ?_
      have hu : IsUnit (ε * ω) := by
        have := (IsUnit.mk0 x hx).map ι
        rwa [he] at this
      exact isUnit_of_mul_isUnit_left hu
    filter_upwards [hs.eventually h1] with m hm ω hω he
    exact absurd he (hm ω hω)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 ((eventually_all_finite hfin).2 fun x _ => hev x)
  refine ⟨m₀, fun m hm ω hω x hx => hm₀ m hm x ?_ ω hω hx⟩
  exact ⟨(s ^ m, ω), ⟨Or.inr ⟨m, rfl⟩, hω⟩, hx.symm⟩

end Abstract

theorem tendsto_halfInf_pow (F : Type) [Field F] [NumberField F] :
    Tendsto (fun m : ℕ => (halfInf F).1 ^ m) atTop (𝓝 ((0, 1) : AF F)) := by
  have h1 : Tendsto (fun m : ℕ => (algebraMap F (Ainf F) 2⁻¹) ^ m) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => ?_
    have h : ‖algebraMap F (Ainf F) 2⁻¹ v‖ < 1 := by
      rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
      change v (2⁻¹ : F) < 1
      rw [← InfinitePlace.norm_embedding_eq, map_inv₀, map_ofNat, norm_inv]
      norm_num
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one h
  have h2 : Tendsto (fun m : ℕ => (1 : FiniteAdeleRing (𝓞 F) F) ^ m) atTop (𝓝 1) := by
    simp only [one_pow]
    exact tendsto_const_nhds
  exact h1.prodMk_nhds h2

theorem finite_and_eventually_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Ω : Set (AF F ⊗[F] E)), IsCompact Ω → {x : E | inclR (F := F) (AF F) x ∈ Ω}.Finite ∧ ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, inclR (F := F) (AF F) x = (halfE F E).1 ^ m * ω → x = 0 := by
  intro F E _ _ _ _ _ Ω hΩ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have h := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
  refine ⟨finite_of_isCompact _ h hΩ, eventually_eq_zero _ h hΩ
    (ε := algebraMap (AF F) (AF F ⊗[F] E) (0, 1)) ?_ fun hu => ?_⟩
  · have hc : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
    have := (hc.tendsto _).comp (tendsto_halfInf_pow F)
    refine this.congr fun m => ?_
    exact map_pow (algebraMap (AF F) (AF F ⊗[F] E)) _ m
  · have h0 : algebraMap (AF F) (AF F ⊗[F] E) (0, 1) * algebraMap (AF F) (AF F ⊗[F] E) (1, 0) = 0 := by
      refine (map_mul (algebraMap (AF F) (AF F ⊗[F] E)) _ _).symm.trans ?_
      refine (congrArg (algebraMap (AF F) (AF F ⊗[F] E)) ?_).trans (map_zero _)
      exact Prod.ext (zero_mul _) (mul_zero _)
    have h1 := hu.mul_right_eq_zero.1 h0
    have hinj : Function.Injective (algebraMap (AF F) (AF F ⊗[F] E)) :=
      Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
    have h2 : ((1, 0) : AF F) = 0 := hinj (h1.trans (map_zero _).symm)
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h3 : (1 : v.Completion) = 0 := congrFun (congrArg Prod.fst h2) v
    exact one_ne_zero h3

end GlobalTheory.Eis.Conv.Discr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdeleCoverModFieldShrunkCompact
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis.ConvCover

theorem exists_int_near {F : Type} [Field F] {w : InfinitePlace F} (hw : w.IsReal)
    (N : ℕ) (t : w.Completion) (ht : ‖t‖ ≤ N) :
    ∃ n ∈ Finset.Icc (-(N : ℤ)) N, ‖t - (n : w.Completion)‖ ≤ 1 := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw
  set e := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw with he
  have hn : ∀ s, ‖e s‖ = ‖s‖ := fun s => hi.norm_map_of_map_zero (map_zero e) s
  rw [← hn, Real.norm_eq_abs, abs_le] at ht
  refine ⟨⌊e t⌋, Finset.mem_Icc.2 ⟨?_, ?_⟩, ?_⟩
  · rw [Int.le_floor]; push_cast; exact ht.1
  · have : (⌊e t⌋ : ℝ) ≤ ((N : ℤ) : ℝ) := by
      push_cast; exact (Int.floor_le _).trans ht.2
    exact_mod_cast this
  · rw [← hn, map_sub, map_intCast, Real.norm_eq_abs, abs_le]
    have h1 := Int.floor_le (e t)
    have h2 := Int.lt_floor_add_one (e t)
    constructor <;> linarith

theorem norm_two_pow_le {F : Type} [Field F] (w : InfinitePlace F) (m : ℕ) :
    ‖(2 : w.Completion) ^ m‖ ≤ 2 ^ m := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  rw [← hi.norm_map_of_map_zero (map_zero _), map_pow, map_ofNat, norm_pow]
  simp

theorem exists_cover : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ (Ω : Set (AF F)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C * ((2 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω := by
  intro F _ _ _
  classical
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have := GlobalTheory.AdeleCocompact.properSpace_completion F
  have hb : ∃ R : ℕ, ∀ k ∈ K, ∀ w : InfinitePlace F, ‖k.1 w‖ ≤ R := by
    have hc : Continuous fun k : AdeleRing (𝓞 F) F => ∑ w : InfinitePlace F, ‖k.1 w‖ :=
      continuous_finsetSum _ fun w _ => ((continuous_apply w).comp continuous_fst).norm
    obtain ⟨B, hB⟩ := (hK.image hc).bddAbove
    refine ⟨⌈B⌉₊, fun k hk w => ?_⟩
    refine le_trans ?_ ((hB ⟨k, hk, rfl⟩).trans (Nat.le_ceil B))
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => ‖k.1 w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  obtain ⟨R, hR⟩ := hb
  let h : InfiniteAdeleRing F := algebraMap F (InfiniteAdeleRing F) 2⁻¹
  have h2 : h * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (InfiniteAdeleRing F)) 2, ← map_mul,
      inv_mul_cancel₀ two_ne_zero, map_one]
  let ι : (InfinitePlace F → ℤ) → InfiniteAdeleRing F := fun n w => (n w : w.Completion)
  refine ⟨((Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1 :
      Set (InfiniteAdeleRing F)) ×ˢ (Prod.snd '' K) :
        Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)),
    (2 * R + 1 : ℝ) ^ Fintype.card (InfinitePlace F),
    (isCompact_univ_pi fun v => isCompact_closedBall _ _).prod (hK.image continuous_snd),
    fun m => ?_⟩
  refine ⟨(Fintype.piFinset fun _ : InfinitePlace F =>
      Finset.Icc (-((2 ^ m * R : ℕ) : ℤ)) ((2 ^ m * R : ℕ) : ℤ)).image
      fun n => ((h ^ m * ι n, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F), ?_, fun a => ?_⟩
  · refine le_trans (Nat.cast_le.2 Finset.card_image_le) ?_
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm _ m,
      pow_mul, ← mul_pow, Nat.cast_pow]
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
    have hc : (Finset.Icc (-((2 ^ m * R : ℕ) : ℤ)) ((2 ^ m * R : ℕ) : ℤ)).card
        = 2 * (2 ^ m * R) + 1 := by
      rw [Int.card_Icc]; omega
    rw [hc]
    push_cast
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ one_le_two
    nlinarith
  · obtain ⟨x, hx⟩ := hKx a
    set k := a - algebraMap F (AdeleRing (𝓞 F) F) x with hk
    have hn : ∀ w : InfinitePlace F, ∃ n ∈ Finset.Icc (-((2 ^ m * R : ℕ) : ℤ)) ((2 ^ m * R : ℕ) : ℤ),
        ‖(2 : w.Completion) ^ m * k.1 w - (n : w.Completion)‖ ≤ 1 := fun w => by
      refine exists_int_near (IsTotallyReal.isReal w) _ _ ((norm_mul_le _ _).trans ?_)
      push_cast
      exact mul_le_mul (norm_two_pow_le w m) (hR k hx w) (norm_nonneg _) (by positivity)
    choose n hn1 hn2 using hn
    refine ⟨x, _, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hn1),
      ((2 ^ m * k.1 - ι n, k.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F),
      ⟨fun w _ => ?_, ⟨k, hx, rfl⟩⟩, ?_⟩
    · exact mem_closedBall_zero_iff.2 (hn2 w)
    · have ha : a = algebraMap F (AdeleRing (𝓞 F) F) x + k := by rw [hk]; ring
      refine ha.trans (Eq.trans (congrArg (algebraMap F (AF F) x + ·) ?_) (add_assoc (G := AF F) _ _ _).symm)
      refine Prod.ext ?_ ?_
      · change k.1 = h ^ m * ι n + h ^ m * (2 ^ m * k.1 - ι n)
        rw [← mul_add, add_sub_cancel, ← mul_assoc, ← mul_pow, h2, one_pow, one_mul]
      · change k.2 = 0 + 1 ^ m * k.2
        rw [one_pow, one_mul, zero_add]

end GlobalTheory.Eis.ConvCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmAdeleSplitComplexFiniteAdeles
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis.Conv.AdeleCMSplit


open scoped TensorProduct NNReal Matrix in
open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∃ e : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) ≃+* (InfinitePlace E → ℂ) × FiniteAdeleRing (𝓞 E) E,
      Continuous e.symm ∧
      (∀ x : E, e (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) =
        (fun w : InfinitePlace E => w.embedding x, algebraMap E (FiniteAdeleRing (𝓞 E) E) x)) ∧
      e (_root_.GlobalTheory.Eis.Conv.halfE F E).1 = (fun _ => 2⁻¹, 1) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨e₁, he₁, -, he₁s⟩ := _root_.GlobalTheory.AdSplit.exists_adele_equiv F E
  choose θ hθ using fun τ => (_root_.GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E σ hσ τ).exists
  have hcm : _root_.GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace E => w.embedding) := by
    unfold _root_.GlobalTheory.Mem.Vol.IsCMFam
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  obtain ⟨e₂, he₂, -, he₂s, -⟩ := _root_.GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ
    (InfinitePlace E) (fun w => w.embedding) (fun w => θ w.embedding) hσ hcm (fun w => hθ _)
  obtain ⟨ι, hι1, hι2, -⟩ := _root_.GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  have hιs := _root_.GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2
  refine ⟨e₁.trans (RingEquiv.prodCongr e₂ ι), ?_, ?_, ?_⟩
  · exact he₁s.comp ((he₂s.comp continuous_fst).prodMk (hιs.comp continuous_snd))
  · intro x
    have h1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x = (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] x := rfl
    have h2 : e₁ ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] x) =
        ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x, (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) := by
      refine Prod.ext ?_ ?_
      · rw [(he₁ _).1]; exact Algebra.TensorProduct.map_tmul _ _ _ _
      · rw [(he₁ _).2]; exact Algebra.TensorProduct.map_tmul _ _ _ _
    rw [h1, RingEquiv.trans_apply, h2]
    refine Prod.ext ?_ ?_
    · funext w
      exact (he₂ _ w).trans ((hθ _).1 x)
    · exact hι1 x
  · have h0 : ((_root_.GlobalTheory.Eis.Conv.halfE F E).1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) =
        ((algebraMap F (InfiniteAdeleRing F) 2⁻¹, (1 : FiniteAdeleRing (𝓞 F) F)) : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
          ⊗ₜ[F] (1 : E) := rfl
    have h2 : e₁ (((algebraMap F (InfiniteAdeleRing F) 2⁻¹, (1 : FiniteAdeleRing (𝓞 F) F)) :
        _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] (1 : E)) = ((1 : InfiniteAdeleRing F) ⊗ₜ[F] algebraMap F E 2⁻¹, 1) := by
      refine Prod.ext ?_ ?_
      · rw [(he₁ _).1]
        refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
        show algebraMap F (InfiniteAdeleRing F) 2⁻¹ ⊗ₜ[F] (1 : E) = _
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
      · rw [(he₁ _).2]; exact (Algebra.TensorProduct.map_tmul _ _ _ _).trans (by rfl)
    rw [h0]
    refine (congrArg (RingEquiv.prodCongr e₂ ι) h2).trans ?_
    refine Prod.ext ?_ ?_
    · funext w
      refine ((he₂ ((1 : InfiniteAdeleRing F) ⊗ₜ[F] algebraMap F E 2⁻¹) w).trans
        ((hθ _).1 _)).trans ?_
      simp only [map_inv₀, map_ofNat]
    · exact map_one ι

end GlobalTheory.Eis.Conv.AdeleCMSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvaluesStatement
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues : ∀ (G V W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (ρ : Representation ℂ G W) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K → GlobalTheory.LGrp.IsIrrSmooth π → IsSmooth ρ → ∀ x ∈ fixed π K, x ≠ 0 → ∀ y ∈ fixed ρ K, y ≠ 0 → (∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec π K h x = c • x ∧ heckeVec ρ K h y = c • y) → GlobalTheory.LGrp.IsSubquot π ρ := by
  first | exact @GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | exact GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | (intros; apply GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues <;> assumption)
end

