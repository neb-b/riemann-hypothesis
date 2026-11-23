module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
public import GroundTheory.GlobalFields.KummerTheory.Splitting

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PullBack
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep GlobalTheory.CuspRep

namespace UpperTheory.ConvolutionTheory.T

section Rep
variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

private def pull (e : G ≃ₜ* H) (τ : SmIrr H) : SmIrr G where
  V := τ.V
  ρ := τ.ρ.comp (e : G →* H)
  smooth := fun x => (τ.smooth x).preimage e.continuous
  irred := by
    refine (OrderIso.isSimpleOrder_iff (β := Subrepresentation τ.ρ)
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => ?_⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (e g) hv⟩
        left_inv := fun S => rfl
        right_inv := fun S => rfl
        map_rel_iff' := Iff.rfl }).2 τ.irred
    have := S.apply_mem_toSubmodule (e.symm g) hv
    simpa using this

end Rep

section Trace
variable {G H V : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] [AddCommGroup V] [Module ℂ V]

private theorem hasFinTrace_smul {A : V →ₗ[ℂ] V} {c s : ℂ} (hc : c ≠ 0) (h : HasFinTrace A s) :
    HasFinTrace (c • A) (c * s) := by
  obtain ⟨hf, rfl⟩ := h
  have hR : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul A c hc
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (c • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((c • A).restrict h1) =
        c * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    rintro _ rfl h1 h2
    have : (c • A).restrict h1 = c • A.restrict h2 := by
      ext x
      simp
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hR ▸ hf, key _ hR _ _⟩

private theorem hasTrace_map (e : G ≃ₜ* H) (mF : Measure G) (mE : Measure H) (c : NNReal) (hc : c ≠ 0)
    (h : mE = c • mF.map e) (π : Representation ℂ H V) (ψ : H → ℂ) (s : ℂ)
    (hs : HasTrace mF (π.comp (e : G →* H)) (fun g => ψ (e g)) s) : HasTrace mE π ψ ((c : ℂ) * s) := by
  obtain ⟨A, hA, hf⟩ := hs
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  refine ⟨(c : ℂ) • A, fun x l => ?_, hasFinTrace_smul hc' hf⟩
  obtain ⟨hi, hl⟩ := hA x l
  have hi' : Integrable (fun y => ψ y * l (π y x)) (mF.map e) := hme.integrable_map_iff.2 hi
  subst h
  refine ⟨hi'.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, hme.integral_map, LinearMap.smul_apply, map_smul, hl]
  simp [NNReal.smul_def]

end Trace

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.pullBack :
    UpperTheory.ConvolutionTheory.T.PullBack := by
  intro F E _ _ _ _ _ n v w hs _ _ _ _ mF mE hF hE τ'
  obtain ⟨⟨e, he⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n
  have hmap : (mF.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map mF e
  have hscal := Measure.isMulLeftInvariant_eq_smul mE (mF.map e)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure mE (mF.map e)
  have hc0 : mE.haarScalarFactor (mF.map e) ≠ 0 := hpos.ne'
  refine ⟨pull e τ', ((mE.haarScalarFactor (mF.map e) : NNReal) : ℂ), by exact_mod_cast hc0, ?_, ?_, ?_⟩
  · rintro τ₁ ⟨E₁⟩
    refine ⟨E₁.toLinearEquiv, fun g x => ?_⟩
    rw [← he g]
    exact LinearMap.congr_fun (E₁.toIntertwiningMap.isIntertwining' g) x
  · intro ψ s h
    refine hasTrace_map e mF mE _ hc0 hscal τ'.ρ ψ s ?_
    have hfun : (fun g => ψ (e g)) = fun g => ψ (mapGL n (completionMap v w.1) g) :=
      funext fun g => by rw [he g]
    rw [hfun]
    exact h
  · intro J U hJ hU
    have hU' : ∀ g, g ∈ U ↔ e g ∈ J := fun g => by rw [he g]; exact hU g
    have hset : (U : Set (Gw n v)) = e ⁻¹' (J : Set (Gw n w.1)) := Set.ext hU'
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hset]
      exact e.toHomeomorph.isCompact_preimage.2 hJ.1
    · rw [hset]
      exact hJ.2.preimage e.continuous
    · intro h h0
      refine h (eq_bot_iff.2 fun x hx => ?_)
      have hx' : x ∈ fixedVectors (pull e τ').ρ U := fun u hu => hx _ ((hU' u).1 hu)
      rw [h0] at hx'
      exact hx'
    · intro φ hφ hinv
      refine ⟨fun y => φ (e.symm y), ⟨hφ.1.comp_continuous e.symm.continuous,
        hφ.2.comp_homeomorph e.symm.toHomeomorph⟩, fun u hu g => ?_, ?_⟩
      · have hu' : e.symm u ∈ U := (hU' _).2 (by simpa using hu)
        simpa [map_mul] using hinv _ hu' (e.symm g)
      · funext g
        rw [← he g]
        simp
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SideSum
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

private theorem trace_range_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c s : ℂ} (hc : c ≠ 0)
    (h : HasFinTrace A s) : HasFinTrace (c • A) (c * s) := by
  obtain ⟨hfd, rfl⟩ := h
  have hr : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul _ _ hc
  have key : ∀ W : Submodule ℂ V, W = LinearMap.range A → ∀ h' : ∀ v ∈ W, (c • A) v ∈ W,
      LinearMap.trace ℂ W ((c • A).restrict h') = c * LinearMap.trace ℂ (LinearMap.range A)
        (A.restrict (p := LinearMap.range A) (q := LinearMap.range A) fun v _ => LinearMap.mem_range_self A v) := by
    rintro W rfl h'
    have : (c • A).restrict h' = c • A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
        (fun v _ => LinearMap.mem_range_self A v) := by
      ext v
      rfl
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hr ▸ hfd, key _ hr _⟩

private theorem hasTrace_of_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} {d : ENNReal} (h0 : d ≠ 0) (ht : d ≠ ⊤)
    (h : HasTrace (d • m) ρ f s) : HasTrace m ρ f (((d.toReal : ℂ))⁻¹ * s) := by
  obtain ⟨A, hA, hT⟩ := h
  have hr : (d.toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  refine ⟨((d.toReal : ℂ))⁻¹ • A, fun v l => ?_, trace_range_smul A (inv_ne_zero hr) hT⟩
  obtain ⟨h1, h2⟩ := hA v l
  refine ⟨(integrable_smul_measure h0 ht).1 h1, ?_⟩
  rw [LinearMap.smul_apply, map_smul, h2, integral_smul_measure, smul_eq_mul, Complex.real_smul, inv_mul_cancel_left₀ hr]

private theorem fd_of_trace {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {I : Subgroup G} {s : ℂ} (hIm : MeasurableSet (I : Set G))
    (h0 : m I ≠ 0) (ht : m I ≠ ⊤) (h : HasTrace m ρ ((I : Set G).indicator 1) s) :
    FiniteDimensional ℂ (fixedVectors ρ I) := by
  obtain ⟨A, hA, hfd, -⟩ := h
  have hr : ((m (I : Set G)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  have hfix : ∀ v ∈ fixedVectors ρ I, A v = ((m (I : Set G)).toReal : ℂ) • v := by
    intro v hv
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2, map_smul, smul_eq_mul]
    have e : (fun g => (I : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) = (I : Set G).indicator fun _ => l v := by
      funext g
      by_cases hg : g ∈ (I : Set G)
      · have : ρ g v = v := hv g hg
        simp [hg, this]
      · simp [hg]
    rw [e, integral_indicator hIm, setIntegral_const, measureReal_def, Complex.real_smul]
  have hle : fixedVectors ρ I ≤ LinearMap.range A := by
    intro v hv
    refine ⟨((m (I : Set G)).toReal : ℂ)⁻¹ • v, ?_⟩
    rw [map_smul, hfix v hv, smul_smul, inv_mul_cancel₀ hr, one_smul]
  exact Submodule.finiteDimensional_of_le hle

private theorem test_ind {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) :
    Test (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hcl : IsClosed ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)) :=
    Subgroup.isClosed_of_isOpen _ ho
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w))
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem iw_pow_at {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) [MeasurableSpace (Gw n w)]
    [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure] (σ : SmIrr (Gw n w)) (ν : Fin n → ℤ) (hν : Antitone ν)
    {s₀ : ℂ} (h₀ : HasTrace m σ.ρ (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator 1) s₀) :
    ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ, HasTrace m σ.ρ ((GM.iwCoset w (j • ν)).indicator 1) (c * (Z.map (· ^ j)).sum) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hpos : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ 0 :=
    (ho.measure_pos m ⟨1, one_mem _⟩).ne'
  have htop : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ ⊤ := hc.measure_lt_top.ne
  have hfd := fd_of_trace ho.measurableSet hpos htop h₀
  set d : ENNReal := (m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)))⁻¹ with hd
  have hd0 : d ≠ 0 := ENNReal.inv_ne_zero.2 htop
  have hdt : d ≠ ⊤ := ENNReal.inv_ne_top.2 hpos
  haveI : (d • m).IsHaarMeasure := Measure.IsHaarMeasure.smul m hd0 hdt
  have h1 : (d • m) (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, hd, ENNReal.inv_mul_cancel hpos htop]
  obtain ⟨Z, hZ0, -, hZ⟩ := UpperTheory.ConvolutionTheory.C.iwPow K n w (d • m) h1 σ ν hν hfd
  exact ⟨_, Z, hZ0, fun j => hasTrace_of_smul hd0 hdt (hZ j)⟩

private theorem amp_A_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n)
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (h1 : 𝔞.ν = ν) (h2 : 𝔞.a₀ = a) (h3 : 𝔞.U = U) :
    𝔞.A = Oinf μ ν a ∘L prj (fixF μ U) := by
  subst h2 h3
  have : ∀ (ν' : Measure (archGroup K n)) (_ : ν'.IsHaarMeasure) (_ : ν' = ν) , Oinf μ ν' 𝔞.a₀ = Oinf μ ν 𝔞.a₀ := by
    intro ν' _ h; subst h; rfl
  exact congrArg (· ∘L prj (fixF μ 𝔞.U)) (this 𝔞.ν 𝔞.haar h1)

private theorem trOn_bot' {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (B : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) B = 0 := by
  have := UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace H ⊥ B B 0 inferInstance (fun v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv]; simp)
  simpa using this

theorem UpperTheory.ConvolutionTheory.T.sideSum :
    UpperTheory.ConvolutionTheory.T.SideSum := by
  intro F E _ _ _ _ _ _ σ n l hn μ _ ν _ _ _ m hm a q w₀ S UF e he p x hx
  haveI hmH : ∀ v, (m v).IsHaarMeasure := fun v => (hm v).1
  by_cases hex : ∃ (L : GM.Loc σ n q w₀) (𝔣 : Side (Twist.id μ) l), L.S = S ∧ (∀ v ∈ S, L.UF v = UF v) ∧ GM.IsSideF L ν a e 𝔣
  swap
  · refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
    intro L 𝔣 h1 h2 h3
    exact absurd ⟨L, 𝔣, h1, h2, h3⟩ hex
  obtain ⟨L₀, 𝔣₀, hS₀, hU₀, hF₀⟩ := hex
  obtain ⟨κ, -, hT⟩ := UpperTheory.ConvolutionTheory.C.termF F E σ n l hn μ ν m hm
  have hfin := (UpperTheory.ConvolutionTheory.T.ampFin F n hn μ 𝔣₀.toAmp).1 x hx
  set P : Set (Submodule ℂ (LL μ)) := {V | IsSummand μ V ∧ eigIn V 𝔣₀.toAmp.A x ≠ ⊥ ∧ p V} with hP
  have hPfin : P.Finite := hfin.subset fun V h => ⟨h.1, h.2.1⟩
  have hτ : ∀ V : P, ∃ τ : ∀ v : Pl F, SmIrr (Gw n v), ∀ v, Occurs μ V.1 v (τ v) := fun V => by
    have := fun v => (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 v (m v) V.2.1).1
    choose τ hτ using this
    exact ⟨τ, hτ⟩
  choose τ hτ using hτ
  have hZ : ∀ V : P, ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ,
      HasTrace (m q) (τ V q).ρ ((GM.iwCoset q (j • e)).indicator 1) (c * (Z.map (· ^ j)).sum) := fun V => by
    obtain ⟨s₀, hs₀⟩ := (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 q (m q) V.2.1).2.2 (τ V q) (hτ V q) _ (test_ind q)
    exact iw_pow_at q (m q) (τ V q) e he hs₀
  choose c Z hZ0 hZ using hZ
  have hN := fun V : P => hT a q w₀ S V.1 (τ V) x V.2.1 hx (fun v _ => hτ V v)
  choose N hN using hN
  letI : Fintype P := hPfin.fintype
  refine ⟨P, inferInstance, fun V => V.1, τ, fun V => κ * x * N V * c V, Z, fun V => ⟨V.2.1, V.2.2.2, hZ0 V, hτ V⟩, ?_⟩
  intro L 𝔣 hS hU hF s hs j
  have hUF : L.UF = L₀.UF := by
    funext v
    by_cases hv : v ∈ S
    · rw [hU v hv, hU₀ v hv]
    by_cases hq : v = q
    · subst hq
      rw [L.at_q.2.2.2, L₀.at_q.2.2.2]
    · rw [(L.off v (hS ▸ hv) hq).2.2.2, (L₀.off v (hS₀ ▸ hv) hq).2.2.2]
  have hA : 𝔣.toAmp.A = 𝔣₀.toAmp.A := by
    obtain ⟨h1, h2, -, h3, -, -⟩ := hF
    obtain ⟨h1', h2', -, h3', -, -⟩ := hF₀
    rw [amp_A_eq 𝔣.toAmp ν a _ h1 h2 h3, amp_A_eq 𝔣₀.toAmp ν a _ h1' h2' h3', hUF]
  have hid : ∀ V : Submodule ℂ (LL μ), V.map ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = V := fun V => by
    have : ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = LinearMap.id := LinearMap.ext fun _ => rfl
    rw [this, Submodule.map_id]
  have hsum : 𝔣.tr p x j = ∑ᶠ V ∈ P, trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) := by
    unfold Side.tr
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext V
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, hP]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      refine ⟨⟨h1, fun h => h4 ?_, h3⟩, h4⟩
      rw [hA, h, trOn_bot']
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      exact ⟨⟨h1, hid V, h3⟩, h4⟩
  rw [hsum, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [(hN V).2 L e 𝔣 hS he hF j _ (s V) (hZ V j) (hs V)]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

private theorem mem_fixL' {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (Gw n w)) (x : LL μ) (h : ∀ g ∈ J, rhoL μ w g x = x) : x ∈ fixL μ w J := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]
  rintro _ ⟨g, hg, rfl⟩
  exact h g hg

private theorem exists_fixed {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) :
    ∃ (S : Subgroup (Gw n w)) (x : LL μ), IsOpen (S : Set (Gw n w)) ∧ x ∈ V ∧ x ≠ 0 ∧ ∀ g ∈ S, rhoL μ w g x = x := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  obtain ⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w (Measure.haar) hV
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (LinearMap.ext hc)
  refine ⟨{ carrier := {g | σ.ρ g x = x}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq] at ha hb ⊢
              rw [map_mul, Module.End.mul_apply, hb, ha]
            one_mem' := by simp
            inv_mem' := fun {a} ha => by
              simp only [Set.mem_setOf_eq] at ha ⊢
              conv_lhs => rw [← ha]
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] },
    f x, σ.smooth x, hfV x, hx, fun g hg => ?_⟩
  rw [← hfe g x]
  exact congrArg f hg

theorem splitLev : SplitLev := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hv
  choose S x hSo hxV hx0 hxS using fun u : PlacesOver E v => exists_fixed μ V hV u.1
  have hsp := fun u : PlacesOver E v => (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hv u) n).1
  choose e he using hsp
  let U : Subgroup (Gw n v) := GLnLocal.integralGL (v.adicCompletion F) n ⊓
    ⨅ u : PlacesOver E v, (S u).comap (mapGL n (completionMap v u.1))
  have hUo : IsOpen (U : Set (Gw n v)) := by
    have h2 : IsOpen (⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1))) := by
      refine isOpen_iInter_of_finite fun u => ?_
      have : (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) = (e u) ⁻¹' (S u : Set (Gw n u.1)) := by
        ext g; simp only [Set.mem_preimage, he]
      rw [this]
      exact (hSo u).preimage (e u).continuous
    have h3 : (U : Set (Gw n v)) = (GLnLocal.integralGL (v.adicCompletion F) n : Set (Gw n v)) ∩
        ⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) := by
      ext g
      simp [U, Subgroup.mem_inf, Subgroup.mem_iInf]
    rw [h3]
    exact (GLnLocal.isOpen_integralGL _ n).inter h2
  have hUle : U ≤ GLnLocal.integralGL (v.adicCompletion F) n := inf_le_left
  have hUc : IsCompact (U : Set (Gw n v)) :=
    (GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo) hUle
  have hinj : ∀ u : PlacesOver E v, Function.Injective (mapGL n (completionMap v u.1)) := fun u a b h =>
    (e u).injective (by rw [he, he, h])
  refine ⟨U, fun u => U.map (mapGL n (completionMap v u.1)), ⟨hUc, hUo⟩, hUle, fun u => ?_⟩
  have himg : ((U.map (mapGL n (completionMap v u.1)) : Subgroup (Gw n u.1)) : Set (Gw n u.1)) = (e u) '' (U : Set (Gw n v)) := by
    ext y
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, he]
  refine ⟨⟨?_, ?_⟩, fun g => ?_, ?_⟩
  · rw [himg]
    exact hUc.image (e u).continuous
  · rw [himg]
    exact (e u).toHomeomorph.isOpenMap _ hUo
  · exact (Subgroup.mem_map_iff_mem (hinj u)).symm
  · intro hbot
    have hmem : x u ∈ V ⊓ fixL μ u.1 (U.map (mapGL n (completionMap v u.1))) := by
      refine ⟨hxV u, mem_fixL' μ u.1 _ _ ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      exact hxS u _ ((Subgroup.mem_iInf.1 hg.2) u)
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx0 u hmem

end UpperTheory.ConvolutionTheory.T
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStableAlt
section
open NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1

private theorem cmp_continuous {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} {v : Pl F} (u : PlacesOver E v) :
    Continuous (GM.cmp (n := n) u : GL (Fin n) (CompletionsOver E v) → GL (Fin n) (u.1.adicCompletion E)) :=
  Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map (continuous_apply u),
      Units.continuous_coe_inv.matrix_map (continuous_apply u)⟩

theorem UpperTheory.ConvolutionTheory.T.splitStable :
    UpperTheory.ConvolutionTheory.T.SplitStable := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v hs U J hJ
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm⟩
  obtain ⟨w₀⟩ := nonempty_placesOver E (v := v)
  obtain ⟨D, w, -, hw⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ m hm v w₀ hs
  have hc : ∀ (x : GL (Fin n) (CompletionsOver E v)) (i : Fin (m + 1)),
      GM.cmp (w i) x = mapGL n (completionMap v (w i).1) (D.comp n i x) := fun x i =>
    Units.ext (Matrix.ext fun a b => (hw _ i).symm)
  have hshift : ∀ (x : GL (Fin n) (CompletionsOver E v)) (i : Fin (m + 1)),
      D.comp n i (mapGL n (galFin σ v) x) = D.comp n (i + 1) x := fun x i =>
    Units.ext (Matrix.ext fun a b => D.map_shift _ i)
  refine ⟨fun x hx u => ?_, fun hCO hle => ?_⟩
  · obtain ⟨i, rfl⟩ := w.surjective u
    rw [hc]
    refine (hJ (w i) _).1 ?_
    rw [hshift, hJ (w (i + 1)), ← hc]
    exact hx _
  · have hJo : ∀ u, IsOpen (J u : Set (GL (Fin n) (u.1.adicCompletion E))) := fun u => by
      obtain ⟨e, he⟩ := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).1
      have h : (J u : Set (GL (Fin n) (u.1.adicCompletion E))) = e.symm ⁻¹' (U : Set (GL (Fin n) (v.adicCompletion F))) := by
        ext y
        have h1 := hJ u (e.symm y)
        rw [← he, e.apply_symm_apply] at h1
        exact h1.symm
      rw [h]
      exact hCO.2.preimage e.symm.continuous
    refine ⟨⨅ u, (J u).comap (GM.cmp u), fun g => by simp [Subgroup.mem_iInf], ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun u => (hJo u).preimage (cmp_continuous u)
    · intro g hg u
      have hgu : GM.cmp u g ∈ J u := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hg u)
      obtain ⟨e, he⟩ := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).1
      have h2 : e.symm (GM.cmp u g) ∈ U := by
        rw [hJ u, ← he, e.apply_symm_apply]
        exact hgu
      have h3 := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).2.1 _ |>.2 (hle h2)
      rw [← he, e.apply_symm_apply] at h3
      exact h3
end

