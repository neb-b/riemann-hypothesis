module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparison
public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportDescendedFunction
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.descFn_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  intro F E _ _ _ _ _ A r M Ax j lam α hαl hαc f hf

  have hstar : Continuous (star : E → E) := by
    have : Isometry (starAddEquiv : E ≃+ E) :=
      (AddMonoidHomClass.isometry_iff_norm (starAddEquiv : E ≃+ E)).2 (fun x => Unram.norm_star F x)
    exact this.continuous
  haveI : ContinuousStar E := ⟨hstar⟩
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjs : Continuous j.symm :=
    LinearMap.continuous_of_finiteDimensional ((j.symm : (Fin r → E) →ₗ[E] A.L).restrictScalars F)

  have hact : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (actU p.2 (Ax, j p.1, lam) : Hn r F E)) := by
    have hg : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (p.2 : Matrix (Fin r) (Fin r) E)) :=
      continuous_subtype_val.comp continuous_snd
    have c1 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) * Ax.1 * star (p.2 : Matrix (Fin r) (Fin r) E)) :=
      (hg.mul continuous_const).mul hg.star
    have c2 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) *ᵥ j p.1) :=
      Continuous.matrix_mulVec hg (hj.comp continuous_fst)
    exact Continuous.prodMk (Continuous.subtype_mk c1 _) (Continuous.prodMk c2 continuous_const)
  set Φ : A.L × Matrix.unitaryGroup (Fin r) E → ℂ := fun p => f (actU p.2 (Ax, j p.1, lam)) * (α p.2 : ℂ) with hΦ
  have hΦl : IsLocallyConstant Φ := by
    refine IsLocallyConstant.mul (hf.1.comp_continuous hact) ?_
    exact (hαl.comp_continuous continuous_snd).comp (fun x : ℝ => (x : ℂ))
  have hdesc : ∀ y, A.descFn M Ax j lam α f y = (letI := M.mU; ∫ g, Φ (y, g) ∂M.μU) := fun y => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y0
    have key : ∀ᶠ y in 𝓝 y0, ∀ g ∈ tsupport α, Φ (y, g) = Φ (y0, g) := by
      refine hαc.isCompact.eventually_forall_of_forall_eventually ?_
      intro g _
      have h1 := (IsLocallyConstant.iff_eventually_eq Φ).1 hΦl (y0, g)
      have h2 : ∀ᶠ z : A.L × Matrix.unitaryGroup (Fin r) E in 𝓝 (y0, g), Φ (y0, z.2) = Φ (y0, g) := by
        have h3 : Tendsto (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) (𝓝 (y0, g)) (𝓝 (y0, g)) := by
          have : Continuous (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) :=
            continuous_const.prodMk continuous_snd
          simpa using this.tendsto (y0, g)
        exact h3.eventually h1
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    rw [hdesc, hdesc]
    congr 1
    funext g
    by_cases hg : g ∈ tsupport α
    · exact hy g hg
    · have : α g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [hΦ, this]
  · let S : Set (Fin r → E) := Prod.fst '' (Prod.snd '' tsupport f)
    let Kset : Set A.L := (fun p : Matrix.unitaryGroup (Fin r) E × (Fin r → E) => j.symm (star (p.1 : Matrix (Fin r) (Fin r) E) *ᵥ p.2)) '' (tsupport α ×ˢ S)
    have hS : IsCompact S :=
      (hf.2.isCompact.image continuous_snd).image continuous_fst
    have hK : IsCompact Kset := by
      refine (hαc.isCompact.prod hS).image ?_
      refine hjs.comp ?_
      exact Continuous.matrix_mulVec ((continuous_subtype_val.comp continuous_fst).star) continuous_snd
    have hKc : IsClosed Kset := by
      have h1 : IsClosed (j '' Kset) := (hK.image hj).isClosed
      have h2 : Kset = j ⁻¹' (j '' Kset) := (Set.preimage_image_eq _ j.injective).symm
      rw [h2]
      exact h1.preimage hj
    refine HasCompactSupport.intro' hK hKc ?_
    intro y hy
    by_contra hne
    rw [hdesc] at hne
    have : ∃ g, Φ (y, g) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      have : (fun g => Φ (y, g)) = fun _ => 0 := funext hall
      rw [this]
      simp
    obtain ⟨g, hg⟩ := this
    have hfg : f (actU g (Ax, j y, lam)) ≠ 0 := left_ne_zero_of_mul hg
    have hαg : (α g : ℂ) ≠ 0 := right_ne_zero_of_mul hg
    have hαg' : α g ≠ 0 := by exact_mod_cast hαg
    apply hy
    refine ⟨(g, g.1 *ᵥ j y), ⟨subset_tsupport _ hαg', ?_⟩, ?_⟩
    · exact ⟨(actU g (Ax, j y, lam)).2, ⟨actU g (Ax, j y, lam), subset_tsupport _ hfg, rfl⟩, rfl⟩
    · simp only [Matrix.mulVec_mulVec]
      have hu : star (g.1 : Matrix (Fin r) (Fin r) E) * g.1 = 1 := Matrix.UnitaryGroup.star_mul_self g
      rw [hu, Matrix.one_mulVec, LinearEquiv.symm_apply_apply]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportIdempotentCoordin
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem isTest_coord : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by
  intro F E _ _ _ _ _ A e h1 h2
  let ι : A.K →ₗ[F] A.L := (Algebra.linearMap A.K A.L).restrictScalars F
  let f : (A.K × A.K) →ₗ[F] A.L :=
    LinearMap.mulRight F e ∘ₗ ι ∘ₗ LinearMap.fst F A.K A.K +
      LinearMap.mulRight F (1 - e) ∘ₗ ι ∘ₗ LinearMap.snd F A.K A.K
  let tr : A.L →ₗ[F] A.K := (Algebra.trace A.K A.L).restrictScalars F
  let g : A.L →ₗ[F] A.K × A.K :=
    LinearMap.prod (tr ∘ₗ LinearMap.mulRight F e) (tr ∘ₗ LinearMap.mulRight F (1 - e))
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  have hf : ∀ p, f p = cc A e p := fun p => rfl
  have hg : ∀ y, g y = ci A e y := fun y => rfl
  have cf : Continuous (cc A e) := by
    have := IsModuleTopology.continuous_of_linearMap f
    simpa [funext hf] using this
  have cg : Continuous (ci A e) := by
    have := IsModuleTopology.continuous_of_linearMap g
    simpa [funext hg] using this
  let H : (A.K × A.K) ≃ₜ A.L :=
    { toFun := cc A e, invFun := ci A e, left_inv := h1, right_inv := h2,
      continuous_toFun := cf, continuous_invFun := cg }
  refine ⟨fun φ hφ => ⟨hφ.1.comp_continuous cf, hφ.2.comp_homeomorph H⟩,
    fun Φ hΦ => ⟨hΦ.1.comp_continuous cg, hΦ.2.comp_homeomorph H.symm⟩⟩

end GlobalTheory.JR.Hyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportMixedModelPartial
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

theorem psi_isLocallyConstant {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  have h1 : ψ (y - x) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
  calc ψ y = ψ (x + (y - x)) := by rw [add_sub_cancel]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, h1, mul_one]

theorem isOpen_setOf_eq_of_isLocallyConstant {Y : Type} [TopologicalSpace Y] {g h : Y → ℂ}
    (hg : IsLocallyConstant g) (hh : IsLocallyConstant h) : IsOpen {p | g p = h p} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  filter_upwards [(IsLocallyConstant.iff_eventually_eq g).1 hg p,
    (IsLocallyConstant.iff_eventually_eq h).1 hh p] with q h1 h2
  show g q = h q
  rw [h1, h2]; exact hp

theorem isTest_partialFourier {X F : Type} [TopologicalSpace X] [T2Space X] [NontriviallyNormedField F]
    [ProperSpace F] {r : ℕ} [MeasurableSpace (Fin r → F)] (μ : Measure (Fin r → F))
    (hμ : ∀ (g : (Fin r → F) → ℂ) (w : Fin r → F), ∫ b, g (b + w) ∂μ = ∫ b, g b ∂μ)
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f : X × (Fin r → F) → ℂ) (hf : IsTest f) :
    IsTest (fun p : X × (Fin r → F) => ∫ b, f (p.1, b) * ψ (b ⬝ᵥ p.2) ∂μ) := by
  obtain ⟨hfl, hfc⟩ := hf
  have hK : IsCompact (tsupport f) := hfc
  have hψl := psi_isLocallyConstant ψ hψ

  have hn1 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) | f (q.1.1, q.1.2 + q.2) = f q.1} :=
    isOpen_setOf_eq_of_isLocallyConstant (hfl.comp_continuous (by fun_prop))
      (hfl.comp_continuous continuous_fst)
  obtain ⟨u1, v1, -, hv1, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (0 : Fin r → F))) hn1 (by
      rintro ⟨p, w⟩ ⟨-, hw⟩
      simp only [Set.mem_singleton_iff] at hw
      subst hw
      simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hv1 0 (h0v rfl)
  have inv1 : ∀ x b (w : Fin r → F), ‖w‖ < δ → f (x, b + w) = f (x, b) := by
    intro x b w hw
    have hwv : w ∈ v1 := hball (by simpa using hw)
    by_cases hxb : (x, b) ∈ tsupport f
    · exact huv (⟨hKu hxb, hwv⟩ : ((x, b), w) ∈ u1 ×ˢ v1)
    · by_cases hxbw : (x, b + w) ∈ tsupport f
      · have hmw : -w ∈ v1 := hball (by simpa using hw)
        have := huv (⟨hKu hxbw, hmw⟩ : ((x, b + w), -w) ∈ u1 ×ˢ v1)
        simp only [Set.mem_setOf_eq, add_neg_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hxb, image_eq_zero_of_notMem_tsupport hxbw]
  have hzero : ∀ x b, b ∉ Prod.snd '' tsupport f → f (x, b) = 0 := fun x b hb =>
    image_eq_zero_of_notMem_tsupport (fun h => hb ⟨_, h, rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨x0, u0⟩
    have hdot : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ q.1.2 := by
      unfold dotProduct; fun_prop
    have hdot0 : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ u0 := by
      unfold dotProduct; fun_prop
    have hn2 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) |
        f (q.1.1, q.2) * ψ (q.2 ⬝ᵥ q.1.2) = f (x0, q.2) * ψ (q.2 ⬝ᵥ u0)} :=
      isOpen_setOf_eq_of_isLocallyConstant
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot) (· * ·))
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot0) (· * ·))
    obtain ⟨u2, v2, hu2, -, hxu, hKv, hu2n⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := (x0, u0))) (hK.image continuous_snd) hn2 (by
        rintro ⟨p, b⟩ ⟨hp, -⟩
        simp only [Set.mem_singleton_iff] at hp
        subst hp
        simp)
    filter_upwards [hu2.mem_nhds (hxu rfl)] with p hp
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    by_cases hb : b ∈ Prod.snd '' tsupport f
    · exact hu2n (⟨hp, hKv hb⟩ : (p, b) ∈ u2 ×ˢ v2)
    · simp only [hzero _ _ hb, zero_mul]
  · obtain ⟨a, ha, -⟩ := hψ.2
    refine HasCompactSupport.intro
      ((hK.image continuous_fst).prod (isCompact_closedBall (0 : Fin r → F) (‖a‖ / δ))) ?_
    rintro ⟨x, u⟩ hxu
    rw [Set.mem_prod, not_and_or] at hxu
    rcases hxu with hx | hu
    · have h0 : ∀ b, f (x, b) = 0 := fun b =>
        image_eq_zero_of_notMem_tsupport (fun h => hx ⟨_, h, rfl⟩)
      simp [h0]
    · rw [mem_closedBall_zero_iff, not_le] at hu
      obtain ⟨i, hi⟩ : ∃ i, ‖a‖ / δ < ‖u i‖ := by
        by_contra h
        push_neg at h
        exact (not_le.2 hu) ((pi_norm_le_iff_of_nonneg (by positivity)).2 h)
      have hui : u i ≠ 0 := by
        intro h
        rw [h, norm_zero] at hi
        exact (not_lt.2 (by positivity)) hi
      classical
      have hw : ‖(Pi.single i (a / u i) : Fin r → F)‖ < δ := by
        rw [Pi.norm_single, norm_div, div_lt_iff₀ (norm_pos_iff.2 hui)]
        rw [div_lt_iff₀ hδ] at hi
        linarith
      have hwu : (Pi.single i (a / u i) : Fin r → F) ⬝ᵥ u = a := by
        rw [single_dotProduct]; field_simp
      have key := hμ (fun b => f (x, b) * ψ (b ⬝ᵥ u)) (Pi.single i (a / u i))
      have hsh : ∀ b, f (x, b + Pi.single i (a / u i)) * ψ ((b + Pi.single i (a / u i)) ⬝ᵥ u) =
          (f (x, b) * ψ (b ⬝ᵥ u)) * ψ a := by
        intro b
        rw [inv1 x b _ hw, add_dotProduct, AddChar.map_add_eq_mul, hwu]
        ring
      simp only [hsh, integral_mul_const] at key
      show ∫ b, f (x, b) * ψ (b ⬝ᵥ u) ∂μ = 0
      by_contra hI
      exact ha (mul_left_cancel₀ hI (key.trans (mul_one _).symm))

end GlobalTheory.JR.WeilMix

namespace GlobalTheory.JR.WeilMix

theorem ptrB_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ,
    IsTest f → IsTest (WeilMix.ptrB M ψ f) := by
  intro F E _ _ _ _ hU r M ψ hψ f hf
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let eH : Gl r F ≃ₜ (Matrix (Fin r) (Fin r) F × (Fin r → F) × F) × (Fin r → F) :=
    { toFun := fun Y => ((Y.1, Y.2.2.1, Y.2.2.2), Y.2.1)
      invFun := fun p => (p.1.1, p.2, p.1.2.1, p.1.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hμ : ∀ (g : (Fin r → F) → ℂ) (w : Fin r → F),
      ∫ b, g (b + w) ∂(Measure.pi fun _ : Fin r => M.μF) = ∫ b, g b ∂(Measure.pi fun _ : Fin r => M.μF) :=
    fun g w => integral_add_right_eq_self g w
  have hg : IsTest (f ∘ eH.symm) := ⟨hf.1.comp_continuous eH.symm.continuous, hf.2.comp_homeomorph eH.symm⟩
  have h1 := isTest_partialFourier (Measure.pi fun _ : Fin r => M.μF) hμ ψ hψ (f ∘ eH.symm) hg
  exact ⟨h1.1.comp_continuous eH.continuous, h1.2.comp_homeomorph eH⟩

end GlobalTheory.JR.WeilMix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportPartialFourierGLB
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem exists_nhds_zero_add_invariant_of_isTest {X : Type} [UniformSpace X] [AddCommGroup X] [IsUniformAddGroup X] {f : X → ℂ}
    (hf : IsTest f) : ∃ U ∈ 𝓝 (0 : X), ∀ Y : X, ∀ u ∈ U, f (Y + u) = f Y := by
  obtain ⟨hlc, hcs⟩ := hf

  have hK : IsCompact (tsupport f) := hcs
  haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
  have hfin0 : (Set.range fun x : tsupport f => f x).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  have hT : (Set.range f).Finite := by
    refine (hfin0.insert 0).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ tsupport f
    · exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
    · exact Set.mem_insert_iff.2 (Or.inl (image_eq_zero_of_notMem_tsupport hx))

  set D : Set ℂ := (Set.image2 (fun a b => a - b) (Set.range f) (Set.range f)) \ {0} with hD
  have hDfin : D.Finite := (hT.image2 _ hT).diff
  have hDo : Dᶜ ∈ 𝓝 (0 : ℂ) := hDfin.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hDo
  have huc := hcs.uniformContinuous_of_continuous hlc.continuous (Metric.dist_mem_uniformity hε)
  rw [uniformity_eq_comap_nhds_zero X, Filter.mem_map, Filter.mem_comap] at huc
  obtain ⟨V, hV, hVs⟩ := huc
  refine ⟨V, hV, fun Y u hu => ?_⟩
  have h1 : ((Y, Y + u) : X × X) ∈ (fun p : X × X => p.2 - p.1) ⁻¹' V := by
    simpa [add_sub_cancel_left] using hu
  have h1' := hVs h1
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at h1'
  have h2 : f (Y + u) - f Y ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]; exact h1'
  have h3 := hball h2
  by_contra hne
  exact h3 ⟨⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩, fun h => hne (sub_eq_zero.1 h)⟩

theorem fourG_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ f' : Gl r F → ℂ, IsTest f' → IsTest (fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f' hf
  have hU : ∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y := by
    exact exists_nhds_zero_add_invariant_of_isTest (X := Gl r F) (f := f') (by exact hf)
  exact ⟨fourG_isLocallyConstant_of_invariant F E r M ψ hψ f' hf hU,
    fourG_hasCompactSupport F E r M ψ hψ f' hf hU⟩

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantEtaleTraceAddCharHermitianKerne
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem isLocallyConstant_of_isStdChar {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) : IsLocallyConstant (fun t : F => ψ t) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have hs : ‖y - x‖ ≤ 1 := by simpa [dist_eq_norm] using hy
  have : y = x + (y - x) := by abel
  rw [this, AddChar.map_add_eq_mul, hψ.1 _ hs, mul_one]

def kerLinF {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    (A : Et F E) (x : A.K) (y' : A.L) : A.L →ₗ[F] F where
  toFun y := Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y * y'))
  map_add' a b := by simp [star_add, add_mul, mul_add, map_add (f := _)]
  map_smul' c a := by
    have hc : star (algebraMap F A.L c) = algebraMap F A.L c := by
      rw [IsScalarTower.algebraMap_apply F A.K A.L]; exact A.star_K _
    have h1 : star (c • a) * y' = (algebraMap F A.K c) • (star a * y') := by
      rw [Algebra.smul_def, star_mul, hc, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]; ring
    rw [h1, map_smul, smul_eq_mul, ← mul_assoc, mul_comm x, mul_assoc, ← Algebra.smul_def, map_smul]
    rfl

theorem isLocallyConstant_psiK_kerL (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  have hl := isLocallyConstant_of_isStdChar ψ hψ
  refine ⟨?_, fun x y' => ?_⟩
  · have hc : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hl.comp_continuous hc
  · have hc : Continuous (kerLinF A x y') := IsModuleTopology.continuous_of_linearMap _
    exact hl.comp_continuous hc

end GlobalTheory.JR.Hyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpoly
section
namespace GlobalTheory.UnitLemma

open Polynomial

theorem InvAlg.isReduced_of_separable_P : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  intro K B h
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B h
  have h2 : minpoly K.E (LinearMap.mulLeft K.E B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  have hms : (minpoly K.E B.g).Separable :=
    h.of_dvd (h2 ▸ LinearMap.minpoly_dvd_charpoly (LinearMap.mulLeft K.E B.g))
  have hsurj : ∀ a : B.A, ∃ q : K.E[X], aeval B.g q = a := by
    intro a
    have hle : Submodule.span K.E (Set.range e) ≤
        Subalgebra.toSubmodule (Algebra.adjoin K.E ({B.g} : Set B.A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact Subalgebra.pow_mem (Algebra.adjoin K.E ({B.g} : Set B.A))
        (Algebra.subset_adjoin (Set.mem_singleton B.g)) _
    have ha : a ∈ Algebra.adjoin K.E ({B.g} : Set B.A) := hle (e.span_eq ▸ Submodule.mem_top)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, hq⟩
  refine ⟨fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := hn
  obtain ⟨q, rfl⟩ := hsurj n
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    rw [pow_zero] at hk
    haveI := subsingleton_of_zero_eq_one hk.symm
    exact Subsingleton.elim _ _
  have hdk : minpoly K.E B.g ∣ q ^ k := minpoly.dvd _ _ (by rw [map_pow, hk])
  obtain ⟨r, hr⟩ := (hms.squarefree.dvd_pow_iff_dvd h0.ne').1 hdk
  rw [hr, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorGlBorderedConjugation
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OmegaInv

theorem norm_det_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hA _ _)

theorem eta_congr {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have hiff : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  unfold eta
  split_ifs <;> tauto

theorem omega_act (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ)
    (k : GL (Fin n) F) (hk : k ∈ glO n F) (Y : Gl n F) : omega (act k Y) = omega Y := by
  unfold omega
  apply eta_congr
  have h1 := (GlobalTheory.JR.transfer_factor_lemma F n).1
  have h2 := (GlobalTheory.JR.transfer_factor_lemma F n).2
  have hl : lastDet (act k Y) = lastDet Y * ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
    rw [h1, h1, h2, Matrix.det_mul, mul_assoc]
  have ha := norm_det_le_one _ (fun i j => (hk i j).1)
  have hb := norm_det_le_one _ (fun i j => (hk i j).2)
  have hprod : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
  have hkinv : ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    apply le_antisymm hb
    by_contra hlt
    push_neg at hlt
    have : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) hlt
    linarith
  rw [hl, norm_mul, hkinv, mul_one]

end GlobalTheory.JR.OmegaInv

theorem GlobalTheory.JR.omega_act_glO : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y :=
  fun F _ _ n k hk Y => GlobalTheory.JR.OmegaInv.omega_act F n k hk Y
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparisonStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_data_comparison : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Module.Basis (Fin n) Qp V) (W W' : Matrix (Fin n) (Fin n) BdR), W * W' = 1 → (∀ i j, W i j ∈ PD.Fil 0) → (∀ i j, W' i j ∈ PD.Fil 0) → (∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) * W.map (PD.actdR g) = W) → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a → a = 0 := by
  first | exact @GlobalTheory.SplitJump.jump_eq_zero | exact GlobalTheory.SplitJump.jump_eq_zero | (intros; apply GlobalTheory.SplitJump.jump_eq_zero <;> assumption)
end

