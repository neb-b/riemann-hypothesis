module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigAdm
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

private theorem prj_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) {f : H} (hf : f ∈ V) : prj V f = f := by
  have h : f ∈ V.topologicalClosure := V.le_topologicalClosure hf
  exact (Submodule.starProjection_eq_self_iff).2 h

private theorem comp_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (v : Pl K)
    (y : AdelicGLn.FiniteAdelicGL K n) :
    finAt v (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y v := by
  show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).2) v = _
  rw [prodEquiv_finEmb]


open scoped Classical in
private theorem levOn_inter {K : Type} [Field K] [NumberField K] {n : ℕ} (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)) :
    (levOn P (fun v => U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n) :
        Set (AdelicGLn.FiniteAdelicGL K n)) =
      (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
        ⋂ v ∈ P, (fun h : AdelicGLn.FiniteAdelicGL K n => finAt v (finEmb K n h)) ⁻¹' (U v : Set (Gw n v)) := by
  ext h
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · intro hh
    have hh' : ∀ v, finAt v (finEmb K n h) ∈ (if v ∈ P then U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n
        else GLnLocal.integralGL (v.adicCompletion K) n) := hh
    refine ⟨(AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, fun v hv => ?_⟩
    · rw [← comp_eq]
      have := hh' v
      split_ifs at this
      · exact this.2
      · exact this
    · have := hh' v
      rw [if_pos hv] at this
      exact this.1
  · rintro ⟨h1, h2⟩
    have h1' := (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 h1
    show ∀ v, finAt v (finEmb K n h) ∈ (if v ∈ P then U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n
        else GLnLocal.integralGL (v.adicCompletion K) n)
    intro v
    have h3 := h1' v
    rw [← comp_eq] at h3
    split_ifs with hv
    · exact ⟨h2 v hv, h3⟩
    · exact h3

private theorem fixL_anti {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n)))
    [μ.IsHaarMeasure] (v : Pl K) {J J' : Subgroup (Gw n v)} (h : J' ≤ J) : fixL μ v J ≤ fixL μ v J' := by
  intro f hf
  simp only [fixL, fixF, Submodule.mem_iInf] at hf ⊢
  exact fun u hu => hf u (Subgroup.map_mono h hu)

private theorem fin_of_compact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W E : Submodule ℂ H) (T : H →L[ℂ] H) {c : ℂ} (hc : c ≠ 0) (hT : IsCompactOperator (T ∘L prj W))
    (h : ∀ f ∈ E, f ∈ W ∧ T f = c • f) : FiniteDimensional ℂ E := by
  haveI := ContinuousLinearMap.finite_dimensional_eigenspace hT c hc
  refine Submodule.finiteDimensional_of_le (S₂ := Module.End.eigenspace (T ∘L prj W).toLinearMap c) ?_
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  rw [Module.End.mem_eigenspace_iff]
  show T (prj W f) = c • f
  rw [prj_self W h1, h2]

set_option maxHeartbeats 2000000 in
theorem UpperTheory.ConvolutionTheory.C.eigAdm :
    UpperTheory.ConvolutionTheory.C.EigAdm := by
  intro K _ _ n hn μ _ ν _ a x hx P U hU
  obtain ⟨m, _, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  let U' : ∀ v : Pl K, Subgroup (Gw n v) := fun v => U v ⊓ GLnLocal.integralGL (v.adicCompletion K) n
  have hcomp : ∀ v : Pl K, Continuous fun h : AdelicGLn.FiniteAdelicGL K n => finAt v (finEmb K n h) :=
    fun v => (continuous_finAt v).comp continuous_finEmb
  have hO : IsOpen (levOn P U' : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    rw [levOn_inter]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).inter
      (P.finite_toSet.isOpen_biInter fun v hv => (hU v hv).2.preimage (hcomp v))
  have hK : IsCompact (levOn P U' : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    rw [levOn_inter]
    refine (AdelicGLn.isCompact_integralFiniteGL K n).inter_right
      (isClosed_biInter fun v hv => ?_)
    exact (Subgroup.isClosed_of_isOpen (U v) (hU v hv).2).preimage (hcomp v)
  obtain ⟨e, -, he⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m (levOn P U') hO hK
  have hfix := UpperTheory.ConvolutionTheory.C.fixLev K n μ P U'
  have hB := (UpperTheory.ConvolutionTheory.C.opBasics K n μ (tens a e)).2.2
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  refine fin_of_compact (cuspidalL2 μ) _ (RR μ (tens a e)) hx' hB fun f hf => ?_
  rw [Submodule.mem_inf, Submodule.mem_inf] at hf
  obtain ⟨⟨he1, hs⟩, hl⟩ := hf
  obtain ⟨hc, he2⟩ := Submodule.mem_inf.1 he1
  have hfF : f ∈ fixF μ (levOn P U') := by
    rw [hfix, Submodule.mem_inf]
    refine ⟨hs, ?_⟩
    simp only [Submodule.mem_iInf] at hl ⊢
    exact fun v hv => fixL_anti μ v inf_le_left (hl v hv)
  have h1 : Ofin μ m e f = f := by rw [he]; exact prj_self _ hfF
  have h2 : Oinf μ ν a f = (x : ℂ) • f := Module.End.mem_eigenspace_iff.1 he2
  refine ⟨hc, ?_⟩
  rw [UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ ν m hC a e, ContinuousLinearMap.comp_apply, h1, h2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistFactor
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory.L1
open scoped Classical

namespace UpperTheory.ConvolutionTheory.C

def HasTwTrace {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (m : Measure G) (τ : SmIrr G)
    (I : τ.V ≃ₗ[ℂ] τ.V) (φ : G → ℂ) (t : ℂ) : Prop :=
  ∃ B : τ.V →ₗ[ℂ] τ.V, IsIntegralOp m τ.ρ φ B ∧ HasFinTrace (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V)) t

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsLocGal (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (s : Gw n w.1 →* Gw n w.1) : Prop :=
  ∀ g : GL (Fin n) (CompletionsOver E v), GM.cmp w (mapGL n (galFin σ v) g) = s (GM.cmp w g)

structure FitsV {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q} (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀)
    (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ) : Prop where
  S_eq : L.S = T.S
  test : ∀ v ∈ T.S, Test (ψ v)
  inv : ∀ v ∈ T.sp, ∀ u ∈ T.J (T.mk' v).1, ∀ g, ψ v (u * g) = ψ v g ∧ ψ v (g * u) = ψ v g
  split : ∀ v ∈ T.sp, L.φ v = GM.prodFn (Function.update
      (fun u : PlacesOver E v => ((T.J u.1 : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (T.mk' v) (ψ v)) ∧
    ∀ g, g ∈ L.UE v ↔ ∀ u, GM.cmp u g ∈ T.J u.1
  nonsplit : ∀ v ∈ T.S, ¬ GM.Split E v → ∀ g, L.φ v g = ψ v (GM.cmp (T.mk' v) g)

end

def TwistFactor : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V Z : Submodule ℂ (LL μ))
    (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
    (τ : ∀ i, SmIrr (Gw n (w i))) (s : ∀ i, Gw n (w i) ≃ₜ* Gw n (w i)) (I : ∀ i, (τ i).V ≃ₗ[ℂ] (τ i).V) (R : LL μ →L[ℂ] LL μ),
    IsSummand μ V → Function.Injective w → (∀ i, Occurs μ V (w i) (τ i)) →
    Z ≤ V → IsClosed (Z : Set (LL μ)) → (∀ i g, ∀ v ∈ Z, rhoL μ (w i) g v ∈ Z) →
    (∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixL μ (w i) (U i))) →
    (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (rhoL μ (w i) g v) = rhoL μ (w i) (s i g) (R v)) →
    (∀ i g x, I i ((τ i).ρ g x) = (τ i).ρ (s i g) (I i x)) →
    ∃ c : ℂ, ∀ (U : ∀ i, Subgroup (Gw n (w i))) (m : ∀ i, Measure (Gw n (w i))) (φ : ∀ i, Gw n (w i) → ℂ)
      (T : Fin r → LL μ →L[ℂ] LL μ) (t : Fin r → ℂ), (∀ i, CO (U i)) → (∀ i, (m i).IsHaarMeasure) → (∀ i, Test (φ i)) →
      (∀ i, ∀ u ∈ U i, ∀ g, φ i (u * g) = φ i g) → (∀ i, IsOloc μ (w i) (m i) (φ i) (T i)) →
      (∀ i, HasTwTrace (m i) (τ i) (I i) (φ i) (t i)) →
      trOn (Z ⊓ ⨅ i, fixL μ (w i) (U i)) ((List.ofFn T).prod ∘L R) = c * ∏ i, t i

def LocGalEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (Module.finrank F E).Prime → ∀ (n : ℕ) (v : Pl F) (w : PlacesOver E v), ¬ GM.Split E v →
    (∀ u : PlacesOver E v, u = w) ∧ ∃ s : Gw n w.1 ≃ₜ* Gw n w.1, IsLocGal σ w (s : Gw n w.1 →* Gw n w.1) ∧
      ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        (∀ g x, θ.U (rhoL μ w.1 g x) = rhoL μ w.1 (s g) (θ.U x)) ∧
        ∀ (V : Submodule ℂ (LL μ)) (τ : SmIrr (Gw n w.1)), IsSummand μ V → V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
          Occurs μ V w.1 τ → ∃ I : τ.V ≃ₗ[ℂ] τ.V, ∀ g x, I (τ.ρ g x) = τ.ρ (s g) (I x)

def TermEV : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ k n : ℕ, Module.finrank F E = k + 1 → (k + 1).Prime → 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    ∀ (D : InfD σ k) (s : Fin (k + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
      (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (m : ∀ u : Pl E, Measure (Gw n u)),
      (∀ u, (m u).IsHaarMeasure) →
    ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
      V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
      (∀ v ∈ T.S, ¬ GM.Split E v → ∀ u : PlacesOver E v,
        RankOne μ V u.1 (T.J u.1) (T.χ u.1) ∧ V ⊓ eigL μ u.1 (T.J u.1) (T.χ u.1) ≠ ⊥) →
    ∀ (τ₀ : SmIrr (Gw n w₀.1)) (τ : ∀ v : Pl F, SmIrr (Gw n (T.mk' v).1)) (g : ∀ v : Pl F, Gw n (T.mk' v).1 →* Gw n (T.mk' v).1)
      (I : ∀ v : Pl F, (τ v).V ≃ₗ[ℂ] (τ v).V), Occurs μ V w₀.1 τ₀ → (∀ v ∈ T.S, Occurs μ V (T.mk' v).1 (τ v)) →
      (∀ v ∈ T.S, ¬ GM.Split E v → IsLocGal σ (T.mk' v) (g v) ∧ ∀ x y, I v ((τ v).ρ x y) = (τ v).ρ (g v x) (I v y)) →
      ∀ y : ℝ, 0 < y →
      ∃ c : ℂ, (T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ → c ≠ 0) ∧
        ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), FitsV T L ψ →
        ∀ (e : Fin n → ℤ) (l : ℕ) (𝔢 : Side θ l), Antitone e → GM.IsSideE L νE aE e 𝔢 →
        ∀ (j : ℕ) (sq : ℂ) (t : Pl F → ℂ), HasTrace (m w₀.1) τ₀.ρ ((GM.iwCoset w₀.1 (j • e)).indicator 1) sq →
          (∀ v ∈ T.sp, HasTrace (m (T.mk' v).1) (τ v).ρ (ψ v) (t v)) →
          (∀ v ∈ T.S, ¬ GM.Split E v → HasTwTrace (m (T.mk' v).1) (τ v) (I v) (ψ v) (t v)) →
          trOn (eigIn V 𝔢.toAmp.A (y ^ (k + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) = c * sq * ∏ v ∈ T.S, t v

end UpperTheory.ConvolutionTheory.C
end
end

