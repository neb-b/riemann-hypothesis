module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistY
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HasFinTraceSmul
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.AtDown
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FdFixed
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

private theorem fd_fixed {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    (m : Measure G) (ρ : Representation ℂ G V) (J : Subgroup G) (hJ : MeasurableSet (J : Set G))
    (h1 : m (J : Set G) = 1) (A : V →ₗ[ℂ] V) (hA : IsIntegralOp m ρ ((J : Set G).indicator 1) A)
    (hf : FiniteDimensional ℂ (LinearMap.range A)) : FiniteDimensional ℂ (fixedVectors ρ J) := by
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range A) fun x hx => ?_
  have hAx : A x = x := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA x l).2, sub_eq_zero]
    have e : (fun g => ((J : Set G).indicator (1 : G → ℂ)) g * l (ρ g x)) =
        (J : Set G).indicator fun _ => l x := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · have hgx : ρ g x = x := hx g hg
        simp [Set.indicator_of_mem hg, hgx]
      · simp [Set.indicator_of_notMem hg]
    rw [e, integral_indicator hJ]
    simp [Measure.real, h1]
  exact ⟨x, hAx⟩

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

theorem UpperTheory.ConvolutionTheory.T.termE :
    UpperTheory.ConvolutionTheory.T.TermE := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn m hm μ _ θ hθ D s hs hsl νE _ νF _ b a aE aF hAS q w₀ hq T V hV hVθ hR hne _ _ mm hmm
    τ hocc ν hν
  obtain ⟨y, hy, hY⟩ := (UpperTheory.ConvolutionTheory.L1.twistY F E σ hσ m n hm hn μ θ hθ D s hs hsl νE νF b a aE aF hAS q w₀ hq T V hV hVθ hR).1 hne
  have hJ : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
  have hcoI : CO (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := hJ ▸ T.co w₀.1
  haveI := hmm w₀.1
  have h0 : mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) ≠ 0 :=
    hcoI.2.measure_ne_zero _ ⟨1, one_mem _⟩
  have hT : mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) ≠ ⊤ :=
    hcoI.1.measure_lt_top.ne
  obtain ⟨m₀, hm₀, hm₀1⟩ : ∃ m₀ : Measure (Gw n w₀.1), m₀.IsHaarMeasure ∧
      m₀ (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) = 1 := by
    refine ⟨(mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)))⁻¹ • mm w₀.1,
      Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT) (ENNReal.inv_ne_top.2 h0), ?_⟩
    simp [ENNReal.inv_mul_cancel h0 hT]
  haveI := hm₀
  have hmm' : ∀ u, (Function.update mm w₀.1 m₀ u).IsHaarMeasure := by
    intro u
    by_cases h : u = w₀.1
    · subst h
      simpa using hm₀
    · simpa [Function.update_of_ne h] using hmm u
  obtain ⟨c, hc, hmain⟩ := UpperTheory.ConvolutionTheory.C.termE F E σ hσ m n hm hn μ θ hθ D s hs hsl νE νF b a aE aF hAS
    (Function.update mm w₀.1 m₀) hmm' q w₀ hq T V hV hVθ hR (τ w₀.1) (fun v => τ (T.mk' v).1) (hocc _) (fun v _ => hocc _) y hy
  have hYZ : T.Y μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≤ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y := by
    unfold Ty.Y Ty.Z Ty.typed
    exact inf_le_inf_left _ (le_iInf₂ fun w _ => iInf_le _ w)
  have hZne : T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ := fun h => hY (le_bot_iff.1 (h ▸ hYZ))
  have hfix : V ⊓ fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) ≠ ⊥ := by
    intro h
    refine hY (le_bot_iff.1 (h ▸ le_inf ?_ ?_))
    · exact inf_le_left.trans inf_le_left
    · have heig := (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w₀.1 (T.J w₀.1) (T.χ w₀.1) (T.co _) (T.chr _)).2.1
      have hχ : T.χ w₀.1 = 1 := T.triv q hq w₀
      rw [← hJ, ← heig, ← hχ]
      exact inf_le_right.trans (iInf_le _ w₀.1)
  obtain ⟨hfx, -, -, s₀, -, A, hA, hfin, -⟩ :=
    UpperTheory.ConvolutionTheory.T.unitTrace E n μ V hV w₀.1 m₀ hm₀ (τ w₀.1) _ (hocc _) hcoI hfix
  have fd := fd_fixed m₀ (τ w₀.1).ρ _ hcoI.2.measurableSet hm₀1 A hA hfin
  obtain ⟨Z, hZ0, hcard, hZ⟩ := UpperTheory.ConvolutionTheory.C.iwPow E n w₀.1 m₀ hm₀1 (τ w₀.1) ν hν fd
  refine ⟨y ^ (m + 1), c, Z, pow_pos hy _, hc hZne, ?_, hZ0, ?_⟩
  · rintro rfl
    exact hfx (Submodule.finrank_eq_zero.1 (by simpa using hcard.symm))
  · intro L ψ hF l 𝔢 hS sv hsv j
    refine hmain L ψ hF ν l 𝔢 hν hS j _ sv ?_ ?_
    · rw [Function.update_self]
      exact hZ j
    · intro v hv
      have hne' : (T.mk' v).1 ≠ w₀.1 := by
        intro h
        have hvq : v = q := by rw [← under_eq (T.mk' v), h, under_eq w₀]
        exact T.q_not (hvq ▸ (Finset.mem_filter.1 hv).1)
      rw [Function.update_of_ne hne']
      exact hsv v hv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.InertData
section
open MeasureTheory NumberField IsDedekindDomain ValuativeRel Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc GlobalTheory.SplitWeil
open Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped ComplexConjugate

private theorem lc_ind {G : Type} [TopologicalSpace G] {U : Set G} (hU : IsClopen U) {h : G → ℂ}
    (hh : IsLocallyConstant h) : IsLocallyConstant (U.indicator h) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx, hh.eventually_eq x] with y hy e
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, e]
  · filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem td_gl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    TotallyDisconnectedSpace (GL (Fin n) k) := by
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem cmp_homeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) {v : HeightOneSpectrum (𝓞 F)}
    (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) :
    ∃ e : GL (Fin n) (CompletionsOver E v) ≃ₜ GL (Fin n) (w.1.adicCompletion E), ∀ g, e g = UpperTheory.ConvolutionTheory.GM.cmp w g := by
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let r : CompletionsOver E v ≃+* w.1.adicCompletion E :=
    RingEquiv.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)
  have hr : Continuous r := continuous_apply _
  have hs : Continuous r.symm :=
    (Homeomorph.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)).symm.continuous
  refine ⟨{ toEquiv := (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin n) r).toMulEquiv).toEquiv
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun g => ?_⟩
  · exact Continuous.units_map _ (continuous_id.matrix_map hr)
  · exact Continuous.units_map _ (continuous_id.matrix_map hs)
  · exact Units.ext (Matrix.ext fun i j => rfl)

theorem UpperTheory.ConvolutionTheory.T.inertData :
    UpperTheory.ConvolutionTheory.T.InertData := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hns
  obtain ⟨-, -, hne, huniq, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨w⟩ := hne v
  have hw : ∀ w' : PlacesOver E v, w' = w := huniq v hns w
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  obtain ⟨ρ, hρ, hdown⟩ := UpperTheory.ConvolutionTheory.Loc.atDown F E σ hσ v w hw n
  have hN : ball n ρ ∈ nhds (1 : Gw n w.1) :=
    (UpperTheory.ConvolutionTheory.Loc.BallG.isOpen_ball hρ.ne').mem_nhds (fun i j => by simp)
  obtain ⟨J, χ, hCO, hchr, hJN, hrank, hne0, hst⟩ := UpperTheory.ConvolutionTheory.T.howeType F E σ hσ hp n hn μ V hV v w hw _ hN
  haveI : T2Space (Gw n w.1) := (UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n).2.2.1
  haveI : T2Space (Gw n v) := (UpperTheory.V.Z.Tf.Orb.gLTop (v.adicCompletion F) n).2.2.1
  have hJc : IsClopen (J : Set (Gw n w.1)) := ⟨hCO.1.isClosed, hCO.2⟩
  let φ : Gw n w.1 → ℂ := (J : Set (Gw n w.1)).indicator fun x => conj (χ x)
  have hφl : IsLocallyConstant φ := lc_ind hJc (hchr.1.comp fun z => conj z)
  have hφc : HasCompactSupport φ := HasCompactSupport.intro hCO.1 fun x hx => Set.indicator_of_notMem hx _
  have hφS : φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)) := ⟨hφl, hφc⟩
  have hsupp : Function.support φ ⊆ ball n ρ := fun x hx => hJN (Set.mem_of_indicator_ne_zero hx)
  obtain ⟨f, hfS, hmatch⟩ := hdown φ hφS hsupp
  obtain ⟨e, he⟩ := cmp_homeo (F := F) n w hw
  have hec : (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) = φ ∘ e := funext fun g => by simp [he]
  have hTE : Test (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) := by
    rw [hec]
    exact ⟨hφl.comp_continuous e.continuous, hφc.comp_homeomorph e⟩
  have hTF : Test f := hfS
  obtain ⟨U₁, hU₁o, hU₁K, hU₁⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n w.1) φ hφS (GLnLocal.integralGL (w.1.adicCompletion E) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  obtain ⟨U₂, hU₂o, hU₂K, hU₂⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n v) f hfS (GLnLocal.integralGL (v.adicCompletion F) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  let J' : ∀ u : PlacesOver E v, Subgroup (Gw n u.1) := fun u => (hw u).symm ▸ J
  let χ' : ∀ u : PlacesOver E v, Gw n u.1 → ℂ := fun u => (hw u).symm ▸ χ
  have all : ∀ P : PlacesOver E v → Prop, P w → ∀ u, P u := fun P h u => (hw u).symm ▸ h
  have hprod : (UpperTheory.ConvolutionTheory.GM.prodFn fun u : PlacesOver E v => (J' u : Set (Gw n u.1)).indicator fun x => conj (χ' u x)) =
      fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g) := funext fun g => by
    unfold UpperTheory.ConvolutionTheory.GM.prodFn
    exact finprod_unique (fun u : PlacesOver E v =>
      (J' u : Set (Gw n u.1)).indicator (fun x => conj (χ' u x)) (UpperTheory.ConvolutionTheory.GM.cmp u g))
  refine ⟨J', χ', f, U₁.comap (UpperTheory.ConvolutionTheory.GM.cmp w), U₂, ?_, ?_, by rw [hprod]; exact hmatch, by rw [hprod]; exact hTE, hTF, ?_, ?_, hU₂o, hU₂K, ?_, ?_⟩
  · exact all _ ⟨hCO, hchr, hrank, hne0⟩
  · intro x hx
    have hxw : UpperTheory.ConvolutionTheory.GM.cmp w x ∈ J := hx w
    obtain ⟨h1, h2⟩ := hst x hxw
    refine ⟨all _ h1, ?_⟩
    rw [finprod_unique, finprod_unique]
    exact h2
  · have : (UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) = e := funext fun g => (he g).symm
    change IsOpen ((UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) ⁻¹' (U₁ : Set (Gw n w.1)))
    rw [this]
    exact hU₁o.preimage e.continuous
  · intro g hg u
    have hu := hw u
    subst hu
    exact hU₁K hg
  · intro y hy g
    rw [hprod]
    change φ (UpperTheory.ConvolutionTheory.GM.cmp w (y * g)) = φ (UpperTheory.ConvolutionTheory.GM.cmp w g)
    rw [map_mul]
    exact (hU₁ _ hy _).1
  · intro y hy g
    exact (hU₂ y hy g).1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PickS
section
open NumberField IsDedekindDomain Filter

theorem UpperTheory.ConvolutionTheory.T.pickS :
    UpperTheory.ConvolutionTheory.T.PickS := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V Λ t hV hAt v
  obtain ⟨hInf, hUnr, hNe, -, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨S₀, hS₀, hA⟩ := hAt
  obtain ⟨-, -, h0⟩ := UpperTheory.ConvolutionTheory.Dp.parEx E n hn μ V hV
  have hU := Filter.eventually_cofinite.1 hUnr
  have hfin := ((hS₀.image (fun w => w.under (𝓞 F))).union hU).union (Set.finite_singleton v)
  obtain ⟨q, hq, hqS⟩ := (hInf.diff hfin).nonempty
  have hsub : ∀ w, w.under (𝓞 F) ∉ hfin.toFinset → w ∉ S₀ := fun w hw hw0 =>
    hw (hfin.mem_toFinset.2 (Or.inl (Or.inl ⟨w, hw0, rfl⟩)))
  refine ⟨hfin.toFinset, q, (hNe q).some, hfin.mem_toFinset.2 (Or.inr rfl),
    fun h => hqS (hfin.mem_toFinset.1 h), hq, fun u hu => ?_, fun w hw => ?_, fun S' hS' => ?_⟩
  · by_contra h
    exact hu (hfin.mem_toFinset.2 (Or.inl (Or.inr h)))
  · exact (hA.2 w (hsub w hw)).2.1
  · have hS : ∀ w, w ∉ S' → w ∉ S₀ := fun w hw => hsub w fun h => hw ((hS' w).2 (Or.inl h))
    exact ⟨⟨hA.1, fun w hw => hA.2 w (hS w hw)⟩, fun τ => (hA.1 τ).1,
      fun w hw => ⟨(hA.2 w (hS w hw)).1, h0 w _ (hA.2 w (hS w hw))⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PosSide
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical NNReal

section Abs

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem trace_congr {p p' : Submodule ℂ V} (h : p = p') (A : V →ₗ[ℂ] V) (h1 : ∀ v ∈ p, A v ∈ p) (h2 : ∀ v ∈ p', A v ∈ p') :
    LinearMap.trace ℂ p (A.restrict h1) = LinearMap.trace ℂ p' (A.restrict h2) := by
  subst h
  rfl

private theorem hasTrace_smul [MeasurableSpace G] {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} (c : ℝ≥0)
    (hc : c ≠ 0) (h : HasTrace m ρ f s) : HasTrace (c • m) ρ f (((c : ℝ) : ℂ) * s) := by
  obtain ⟨A, hA, hfin, rfl⟩ := h
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hr : LinearMap.range (((c : ℝ) : ℂ) • A) = LinearMap.range A := LinearMap.range_smul _ _ hc'
  refine ⟨((c : ℝ) : ℂ) • A, fun v l => ⟨(hA v l).1.smul_measure_nnreal, ?_⟩, hr ▸ hfin, ?_⟩
  · rw [integral_smul_nnreal_measure, ← (hA v l).2, LinearMap.smul_apply, map_smul]
    rfl
  · rw [trace_congr hr _ _ (fun v _ => Submodule.smul_mem _ _ (LinearMap.mem_range_self A v)), ← smul_eq_mul, ← map_smul]
    rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem vol_pos (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hU : CO U) : 0 < m.real U :=
  ENNReal.toReal_pos (hU.2.measure_pos m ⟨1, one_mem U⟩).ne' hU.1.measure_lt_top.ne

private theorem trace_ind (m : Measure G) [m.IsHaarMeasure] {ρ : Representation ℂ G V} {U : Subgroup G} (hU : CO U) {s : ℂ}
    (h : HasTrace m ρ ((U : Set G).indicator 1) s) :
    FiniteDimensional ℂ (fixedVectors ρ U) ∧ s = (m.real U : ℂ) * Module.finrank ℂ (fixedVectors ρ U) := by
  obtain ⟨A, hA, hfin, rfl⟩ := h
  have hm : MeasurableSet (U : Set G) := hU.2.measurableSet
  have hc : (m.real U : ℂ) ≠ 0 := by exact_mod_cast (vol_pos m hU).ne'
  have h1 : ∀ v, A v ∈ fixedVectors ρ U := fun v => mem_fixedVectors.2 fun a ha => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2]
    refine (hA v (l ∘ₗ ρ a)).2.trans ?_
    rw [← integral_mul_left_eq_self (fun g => (U : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) a]
    congr 1
    funext g
    by_cases h : g ∈ U
    · simp [h, mul_mem ha h]
    · have : a * g ∉ U := fun h' => h (by simpa using mul_mem (inv_mem ha) h')
      simp [h, this]
  have h2 : ∀ v ∈ fixedVectors ρ U, A v = (m.real U : ℂ) • v := fun v hv => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2, map_smul]
    have : (fun g => (U : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) = (U : Set G).indicator fun _ => l v := by
      funext g
      by_cases h : g ∈ U
      · simp [h, mem_fixedVectors.1 hv g h]
      · simp [h]
    rw [this, integral_indicator_const _ hm]
    rfl
  have hr : LinearMap.range A = fixedVectors ρ U := by
    refine le_antisymm (by rintro _ ⟨v, rfl⟩; exact h1 v) fun v hv => ⟨(m.real U : ℂ)⁻¹ • v, ?_⟩
    rw [map_smul, h2 v hv, smul_smul, inv_mul_cancel₀ hc, one_smul]
  haveI : FiniteDimensional ℂ (fixedVectors ρ U) := hr ▸ hfin
  refine ⟨this, ?_⟩
  rw [trace_congr hr _ _ (fun v _ => h1 v)]
  have : A.restrict (p := fixedVectors ρ U) (q := fixedVectors ρ U) (fun v _ => h1 v) = (m.real U : ℂ) • LinearMap.id :=
    LinearMap.ext fun v => Subtype.ext (h2 v v.2)
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul]

private theorem ex_haar [LocallyCompactSpace G] {U : Subgroup G} (hU : CO U) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m U = 1 := by
  obtain ⟨P, hP⟩ : ∃ P : TopologicalSpace.PositiveCompacts G, (P : Set G) = U :=
    ⟨⟨⟨U, hU.1⟩, by
      change (interior (U : Set G)).Nonempty
      rw [hU.2.interior_eq]
      exact ⟨1, one_mem U⟩⟩, rfl⟩
  exact ⟨Measure.haarMeasure P, inferInstance, hP ▸ Measure.haarMeasure_self⟩

private theorem ex_norm (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hU : CO U) :
    ∃ (c : ℝ≥0) (m' : Measure G), c ≠ 0 ∧ m'.IsHaarMeasure ∧ m' U = 1 ∧ m = c • m' := by
  have h0 : m U ≠ 0 := (hU.2.measure_pos m ⟨1, one_mem U⟩).ne'
  have h1 : m U ≠ ⊤ := hU.1.measure_lt_top.ne
  have hc : (m U).toNNReal ≠ 0 := ENNReal.toNNReal_ne_zero.2 ⟨h0, h1⟩
  refine ⟨(m U).toNNReal, (m U).toNNReal⁻¹ • m, hc, Measure.IsHaarMeasure.nnreal_smul m (inv_ne_zero hc), ?_, ?_⟩
  · rw [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_inv hc, ENNReal.coe_toNNReal h1, smul_eq_mul,
      ENNReal.inv_mul_cancel h0 h1]
  · rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

end Abs

private theorem amp_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (h1 : 𝔞.ν = ν) :
    𝔞.A = Oinf μ ν 𝔞.a₀ ∘L prj (fixF μ 𝔞.U) := by
  subst h1
  rfl

private theorem term {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F]
    {σ : E ≃ₐ[F] E} {n : ℕ} (hn : 0 < n) {μ : Measure (normOneGL (K := F) (n := n))} [μ.IsHaarMeasure] {q : Pl F}
    {w₀ : GroundTheory.Global.SemiLocal.PlacesOver E q} {ν : Measure (archGroup F n)} [ν.IsHaarMeasure] {a : TI F n} {L : Loc σ n q w₀}
    {e : Fin n → ℤ} {l : ℕ} {𝔣 : Side (Twist.id μ) l} (he : Antitone e) (hF : IsSideF L ν a e 𝔣)
    (hf : ∀ v ∈ L.S, L.f v = (L.UF v : Set (Gw n v)).indicator 1) {x : ℝ} (hx : 0 < x) (V : Submodule ℂ (LL μ))
    (hV : IsSummand μ V) (hne : eigIn V 𝔣.toAmp.A x ≠ ⊥) :
    ∃ (c : ℝ) (Z : Multiset ℂ), 0 < c ∧ 0 ∉ Z ∧ Z ≠ 0 ∧ ∀ j : ℕ,
      trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) = c * (Z.map (· ^ j)).sum := by
  letI : ∀ v : Pl F, MeasurableSpace (Gw n v) := fun v => borel _
  haveI : ∀ v : Pl F, BorelSpace (Gw n v) := fun v => ⟨rfl⟩
  have hK : ∀ v : Pl F, CO (GLnLocal.integralGL (v.adicCompletion F) n) := fun v =>
    (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n v).2.1 _ (GLnLocal.isOpen_integralGL _ _) le_rfl
  choose m hm using fun v : Pl F => ex_haar (hK v)
  haveI := fun v => (hm v).1
  obtain ⟨κ, hκ, H⟩ := UpperTheory.ConvolutionTheory.C.termF F E σ n l hn μ ν m hm
  choose τ hτ using fun v : Pl F => (occursBasics F n μ V v (m v) hV).1
  obtain ⟨N, hN, H⟩ := H a q w₀ L.S V τ x hV hx fun v _ => hτ v
  have hlev : levF L.UF = levOn (insert q L.S) L.UF := by
    unfold levOn
    congr 1
    funext v
    split_ifs with h
    · rfl
    · rw [Finset.mem_insert, not_or] at h
      exact (L.off v h.2 h.1).2.2.2
  have hne' := hne
  rw [amp_eq 𝔣.toAmp ν hF.1, hF.2.1, hF.2.2.2.1, hlev, UpperTheory.eigenspace_comp_levelProjection_eq_inf_fixed F n hn μ ν V a x _ L.UF hx.ne'] at hne'
  have hN0 : 0 < N := hN.2 (ne_bot_of_le_ne_bot hne' inf_le_left)
  have hCO : ∀ v ∈ insert q L.S, CO (L.UF v) := fun v hv => by
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [L.at_q.2.2.2]
      exact (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n v).1
    · exact (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n v).2.1 _ (L.lev v hv).2.2.1 (L.lev v hv).2.2.2
  have hpos : ∀ v ∈ insert q L.S, FiniteDimensional ℂ (fixedVectors (τ v).ρ (L.UF v)) ∧
      0 < Module.finrank ℂ (fixedVectors (τ v).ρ (L.UF v)) ∧ HasTrace (m v) (τ v).ρ ((L.UF v : Set (Gw n v)).indicator 1)
        ((((m v).real (L.UF v) * Module.finrank ℂ (fixedVectors (τ v).ρ (L.UF v)) : ℝ)) : ℂ) := fun v hv => by
    obtain ⟨-, -, -, s, hs0, hs⟩ := T.unitTrace F n μ V hV v (m v) inferInstance (τ v) (L.UF v) (hτ v) (hCO v hv)
      (ne_bot_of_le_ne_bot hne' (inf_le_inf (inf_le_left.trans inf_le_left) (iInf₂_le v hv)))
    obtain ⟨h1, h2⟩ := trace_ind (m v) (hCO v hv) hs
    refine ⟨h1, Nat.pos_of_ne_zero fun h => hs0 (by rw [h2, h]; simp), ?_⟩
    push_cast
    exact h2 ▸ hs
  obtain ⟨hq1, hq2, -⟩ := hpos q (Finset.mem_insert_self _ _)
  rw [L.at_q.2.2.2] at hq1 hq2
  obtain ⟨c, m', hc, hm', hm1, hme⟩ := ex_norm (m q) (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n q).1
  obtain ⟨Z, hZ0, hZc, hZ⟩ := iwPow F n q m' hm1 (τ q) e he hq1
  let s : Pl F → ℝ := fun v => (m v).real (L.UF v) * Module.finrank ℂ (fixedVectors (τ v).ρ (L.UF v))
  have hs : ∀ v ∈ L.S, 0 < s v := fun v hv =>
    mul_pos (vol_pos _ (hCO v (Finset.mem_insert_of_mem hv))) (Nat.cast_pos.2 (hpos v (Finset.mem_insert_of_mem hv)).2.1)
  refine ⟨κ * x * N * c * ∏ v ∈ L.S, s v, Z, ?_, hZ0, ?_, fun j => ?_⟩
  · have h1 : (0 : ℝ) < c := by exact_mod_cast hc.bot_lt
    have h2 : (0 : ℝ) < N := Nat.cast_pos.2 hN0
    have h3 := Finset.prod_pos hs
    positivity
  · rintro rfl
    rw [← hZc] at hq2
    exact lt_irrefl _ hq2
  · have h1 := hasTrace_smul c hc (hZ j)
    rw [← hme] at h1
    rw [H L e 𝔣 rfl he hF j _ (fun v => (s v : ℂ)) h1 fun v hv => by
      rw [hf v hv]
      exact (hpos v (Finset.mem_insert_of_mem hv)).2.2]
    push_cast
    ring

theorem UpperTheory.ConvolutionTheory.T.posSide :
    UpperTheory.ConvolutionTheory.T.PosSide := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n hn μ _ q w₀ ν _ a L e l 𝔣 he hF hf p V x hV hpV hx hne
  have hfin : {W : Submodule ℂ (LL μ) | (IsSummand μ W ∧ eigIn W 𝔣.toAmp.A x ≠ ⊥) ∧ p W}.Finite :=
    ((T.ampFin F n hn μ 𝔣.toAmp).1 x hx).subset fun W hW => hW.1
  let ι := {W : Submodule ℂ (LL μ) | (IsSummand μ W ∧ eigIn W 𝔣.toAmp.A x ≠ ⊥) ∧ p W}
  haveI : Fintype ι := hfin.fintype
  choose c Z hc hZ0 hZ hT using fun W : ι => term hn he hF hf hx W.1 W.2.1.1 W.2.1.2
  have htr : ∀ j, 𝔣.tr p x j = ∑ W : ι, (c W : ℂ) * ((Z W).map (· ^ j)).sum := fun j => by
    simp only [← hT]
    rw [Side.tr, ← finsum_eq_sum_of_fintype, finsum_set_coe_eq_finsum_mem (s := ι)
      (f := fun W => trOn (eigIn W 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U))]
    refine finsum_mem_inter_support_eq' _ _ _ fun W hW => ⟨fun h => ⟨⟨h.1, fun hb => hW ?_⟩, h.2.2⟩, fun h => ⟨h.1.1, ?_, h.2⟩⟩
    · beta_reduce
      rw [hb]
      simpa using UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace (LL μ) ⊥ ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) 0 0 inferInstance fun v hv => by
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
    · exact Submodule.map_id W
  intro h
  let V₀ : ι := ⟨V, ⟨hV, hne⟩, hpV⟩
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero (hZ V₀)
  have h0 := powIndep ι (fun W => (c W : ℂ)) Z hZ0 (h.mono fun j hj => by rw [← htr]; exact not_not.1 hj) ζ
  have h1 : ∑ W : ι, c W * ((Multiset.filter (· = ζ) (Z W)).card : ℝ) = 0 := by exact_mod_cast h0
  refine (Finset.sum_pos' (fun W _ => mul_nonneg (hc W).le (Nat.cast_nonneg _)) ⟨V₀, Finset.mem_univ _, mul_pos (hc _) ?_⟩).ne' h1
  exact Nat.cast_pos.2 (Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩)
end

