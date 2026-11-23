module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0033
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceActionDeterminant
section
noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise Kronecker

namespace GlobalTheory.CompanionTheory.ConeLin

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hOf_add (v w : Fin n × Fin n → ℝ) : hOf (v + w) = hOf v + hOf w := by
  simp only [hOf, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem hOf_smul (c : ℝ) (v : Fin n × Fin n → ℝ) : hOf (c • v) = (c : ℂ) • hOf v := by
  simp only [hOf, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

theorem hOf_single (q : Fin n × Fin n) : hOf (Pi.single q (1 : ℝ)) = hb q := by
  classical
  simp [hOf, Pi.single_apply, ite_smul]

theorem hOf_herm (v : Fin n × Fin n → ℝ) : (hOf v)ᴴ = hOf v := by
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

theorem re_trace (P : Mat n) (hP : Pᴴ = P) (p : Fin n × Fin n) :
    (((P * hb p).trace).re : ℂ) = (P * hb p).trace := by
  apply Complex.conj_eq_iff_re.1
  have h1 : star (P * hb p).trace = (P * hb p).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hP, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose,
      Matrix.trace_mul_comm]
  exact h1

theorem hOf_re (P : Mat n) (hP : Pᴴ = P) : hOf (fun p => ((P * hb p).trace).re) = P := by
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr P
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, re_trace P hP]

theorem conj_herm (g P : Mat n) (hP : Pᴴ = P) : (g * P * gᴴ)ᴴ = g * P * gᴴ := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

def realMap (g : Mat n) : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) where
  toFun v p := ((g * hOf v * gᴴ * hb p).trace).re
  map_add' v w := by
    funext p
    simp [hOf_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' c v := by
    funext p
    simp [hOf_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

def cplxMap (g : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun X := g * X * gᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxMap_apply (g X : Mat n) : cplxMap g X = g * X * gᴴ := rfl

theorem hOf_realMap (g : Mat n) (v : Fin n × Fin n → ℝ) : hOf (realMap g v) = g * hOf v * gᴴ :=
  hOf_re _ (conj_herm g _ (hOf_herm v))

theorem det_realMap (g : Mat n) : ((LinearMap.det (realMap g) : ℝ) : ℂ) = LinearMap.det (cplxMap g) := by
  rw [← LinearMap.det_toMatrix' (realMap g), ← GlobalTheory.CompanionTheory.TopClass.det_of_trace (cplxMap g),
    ← Matrix.det_transpose (Matrix.of _)]
  have h : ((LinearMap.toMatrix' (realMap g)).det : ℂ) =
      Complex.ofRealHom (LinearMap.toMatrix' (realMap g)).det := rfl
  rw [h, RingHom.map_det]
  congr 1
  ext p q
  have hh : (g * hb q * gᴴ)ᴴ = g * hb q * gᴴ := conj_herm g _ (GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose q)
  have := re_trace _ hh p
  simpa [LinearMap.toMatrix'_apply, realMap, hOf_single, cplxMap_apply, Pi.single_apply] using this

theorem det_cplxMap (g : Mat n) : LinearMap.det (cplxMap g) = (g.det * star g.det) ^ n := by
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)) (Matrix.stdBasis ℂ (Fin n) (Fin n)) (cplxMap g) =
      g ⊗ₖ g.map star := by
    ext ⟨i, j⟩ ⟨k, l⟩
    have hr : ∀ X : Mat n, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr X (i, j) = X i j := by
      intro X
      simp [Matrix.stdBasis]
    rw [LinearMap.toMatrix_apply, hr]
    simp [cplxMap_apply, Matrix.stdBasis_eq_single, Matrix.mul_apply, Matrix.single_apply, ite_and]
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)), h, Matrix.det_kronecker]
  have h2 : (g.map star).det = star g.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
    rfl
  rw [h2, Fintype.card_fin, mul_pow]

theorem cone_lin (n : ℕ) (g : Mat n) (_hg : g.det ≠ 0) :
    ∃ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ),
      (∀ v, hOf (T v) = g * hOf v * gᴴ) ∧ LinearMap.det T = ‖g.det‖ ^ (2 * n) := by
  refine ⟨realMap g, hOf_realMap g, ?_⟩
  apply Complex.ofReal_injective
  rw [det_realMap, det_cplxMap]
  have : g.det * star g.det = ((‖g.det‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.mul_conj' g.det
  rw [this, pow_mul]
  simp

end GlobalTheory.CompanionTheory.ConeLin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermKFiniteCoefficient
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.KType

theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finsetSum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    LinearMap.pi fun k => LinearMap.applyₗ (ρ k)
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ.comp (LinearMap.applyₗ w), rfl⟩
  exact Submodule.finiteDimensional_of_le this

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem eventually_eq_chart (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a)
    (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, φ.1 (unip x * g) =
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hlev.mem_nhds h1)] with x hx
  have hx' : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) φ = φ := hx
  rw [chart_val, JointCont.unip_mul_eq, ← mul_inv_cancel_left (JointCont.finPart g x₀) (JointCont.finPart g x),
    map_mul, mul_assoc, ← infGL_comm, ← mul_assoc]
  exact congrArg (fun ψ : Sm E a => ψ.1 (finGL E a (JointCont.finPart g x₀) * infGL E a (JointCont.infPart g x))) hx'

theorem continuous_unip_mul (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hf₀ : ContDiffOn ℝ ∞ (chart φ.1 (finGL E a (JointCont.finPart g x₀))) (invSet E a) := φ.2 _
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E =>
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a (JointCont.finPart g x₀)))
      (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  have hE : (fun x : BlockIx a r → Ad E => φ.1 (unip x * g)) =ᶠ[𝓝 x₀]
      fun x => chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) :=
    eventually_eq_chart φ hlev g x₀
  exact hA.congr hE.symm

theorem exists_bound_unip_mul (φ : Sm E a) (hleft : ∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hCm : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hCm.exists_bound_of_continuousOn (continuous_unip_mul (r := r) φ hlev g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Set.univ.pi fun _ : BlockIx a r => K,
      x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  rw [unip_add, unip_algebraMap, mul_assoc, hleft]
  exact hC x' hx'm

theorem ct_mem_coeffSpan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  intro E _ _ _ a r φ hleft hlev W _ _ _ ρ hρ _ _ μ 𝓕 hμ hF g
  haveI := hμ
  haveI := finiteDimensional_coeffSpan ρ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine integral_mem (μ.restrict 𝓕) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun x k => φ.1 (unip x * (g * infGL E a (Unitary.toUnits k)))) (fun x => ?_) (fun k => ?_)
  · have e : ∀ k : Kinf E a, (cptRep E a k φ).1 (unip x * g) = φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) :=
      fun k => by rw [← mul_assoc]; rfl
    have := hρ (unip x * g)
    simp only [e] at this
    exact this
  · obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) φ hleft hlev (g * infGL E a (Unitary.toUnits k))
    exact Integrable.of_bound (continuous_unip_mul φ hlev _).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)

end GlobalTheory.CompanionTheory.CTFin.KType

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermTranslateFormula
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

theorem constTerm_unip_left : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
      (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
    ∀ (y : BlockIx a r → Ad E) (g : GA E a),
      ∫ x in 𝓕, φ.1 (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  intro E _ _ _ a r φ hl _ _ _ μ 𝓕 hμ h𝓕 y g
  haveI := countable_ratN (E := E) (a := a) r
  have hper : ∀ n ∈ ratN E a r, ∀ x, φ.1 (unip (n + x) * g) = φ.1 (unip x * g) := by
    rintro _ ⟨q, rfl⟩ x
    rw [unip_add, mul_assoc]
    exact (congrArg (fun u => φ.1 (u * _)) (unip_algebraMap q)).trans (hl _ _)
  have h := Formalism.IndefR.Tow.fd_setIntegral_add h𝓕 (f := fun x => φ.1 (unip x * g)) hper y
  simpa only [unip_add, mul_assoc] using h

end GlobalTheory.CompanionTheory.CTFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionFixed
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepTensor

theorem extTensor_left {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (k : G) :
    extTensor ρ σ (k, 1) = TensorProduct.map (ρ k) LinearMap.id :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem extTensor_right {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (h : H) :
    extTensor ρ σ (1, h) = TensorProduct.map LinearMap.id (σ h) :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem contr_left {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Module.End ℂ V) (l : Module.Dual ℂ W) (v : V ⊗[ℂ] W) :
    A (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
      TensorProduct.rid ℂ V (LinearMap.lTensor V l (TensorProduct.map A LinearMap.id v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem contr_right {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (B : Module.End ℂ W) (l : Module.Dual ℂ V) (v : V ⊗[ℂ] W) :
    B (TensorProduct.lid ℂ W (LinearMap.rTensor W l v)) =
      TensorProduct.lid ℂ W (LinearMap.rTensor W l (TensorProduct.map LinearMap.id B v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa using this
  · intro h k
    have := h k k.2
    show ρ (k : G) v = ((1 : K →* ℂˣ) k : ℂ) • v
    simpa using this

theorem contrFix : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  intro G H V W _ _ _ _ _ _ ρ σ K L v hv
  have hv' := mem_fixed_iff'.1 hv
  refine ⟨fun l => mem_fixed_iff'.2 fun k hk => ?_, fun l => mem_fixed_iff'.2 fun h hh => ?_⟩
  · have h1 := hv' (k, 1) ⟨hk, L.one_mem⟩
    rw [extTensor_left] at h1
    rw [contr_left, h1]
  · have h1 := hv' (1, h) ⟨K.one_mem, hh⟩
    rw [extTensor_right] at h1
    rw [contr_right, h1]

end GlobalTheory.CompanionTheory.RepTensor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTail
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.IwahoriTraceProof

namespace GlobalTheory.CompanionTheory.IwahoriCount

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_cosets {I : Subgroup G} (ho : IsOpen (I : Set G)) {D : Set G} (hD : IsCompact D) :
    {q : G ⧸ I | q.out ∈ D}.Finite := by
  haveI : DiscreteTopology (G ⧸ I) := QuotientGroup.discreteTopology ho
  have h : IsCompact ((QuotientGroup.mk : G → G ⧸ I) '' D) := hD.image QuotientGroup.continuous_mk
  exact h.finite_of_discrete.subset fun q hq => ⟨q.out, hq, QuotientGroup.out_eq' q⟩

theorem measure_eq_card_mul [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {I : Subgroup G} (ho : IsOpen (I : Set G)) {D : Set G} (hD : ∀ g ∈ D, ∀ i ∈ I, g * i ∈ D)
    (S : Finset (G ⧸ I)) (hS : ∀ q, q ∈ S ↔ q.out ∈ D) : μ D = S.card * μ I :=
  _root_.UpperTheory.Reformulated.B.Yla7.main μ ho hD S hS

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem iwahoriCoset_mul {t : Fin n → kˣ} {g i : GL (Fin n) k} (hg : g ∈ iwahoriCoset t)
    (hi : i ∈ iwahori k (Fin n)) : g * i ∈ iwahoriCoset t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  exact ⟨a, ha, b * i, mul_mem hb hi, by simp only [mul_assoc]⟩

theorem mk_act {t : Fin n → kˣ} (ht : Contracts t) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) {v : V} (hv : v ∈ fixed π (iwahori k (Fin n)))
    {g : GL (Fin n) k} (hg : g ∈ iwahoriCoset t) :
    (Submodule.Quotient.mk (π g v) : Jacquet π (unipB k (Fin n))) = jacBU π t (Submodule.Quotient.mk v) := by
  obtain ⟨u, hu, -, i, hi, rfl⟩ := (mem_iwahoriCoset ht g).1 hg
  rw [jacBU_mk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, IwahoriInj.mem_fixed.1 hv i hi]
  exact (Submodule.Quotient.eq _).2 (IwahoriInj.sub_mem_twKer hu _)

theorem card_cosets {t : Fin n → kˣ} (ht : Contracts t) (S : Finset (GL (Fin n) k ⧸ iwahori k (Fin n)))
    (hS : ∀ q, q ∈ S ↔ q.out ∈ iwahoriCoset t) : (S.card : ℝ) = (deltaB t)⁻¹ := by
  have ho := IwahoriOnto.isOpen_iwahori k (Fin n)
  have hc := IwahoriOnto.isCompact_iwahori k (Fin n)
  letI : MeasurableSpace (GL (Fin n) k) := _root_.borel _
  haveI : BorelSpace (GL (Fin n) k) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin n) k) :=
    hc.locallyCompactSpace_of_mem_nhds_of_group (ho.mem_nhds (one_mem _))
  let μ : Measure (GL (Fin n) k) := Measure.haar
  have h1 := measure_iwahoriCoset μ ht
  have h2 := measure_eq_card_mul μ ho (fun g hg i hi => iwahoriCoset_mul hg hi) S hS
  have h3 : μ.real (iwahoriCoset t) = S.card * μ.real (iwahori k (Fin n) : Set (GL (Fin n) k)) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have h4 : μ.real (iwahori k (Fin n) : Set (GL (Fin n) k)) ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos (ho.measure_pos μ ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne).ne'
  rw [h3, mul_comm] at h1
  exact mul_left_cancel₀ h4 h1

theorem cosetCount : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  intro k _ _ _ _ n t ht
  have hset : {q : GL (Fin n) k ⧸ iwahori k (Fin n) | cosetInd t q.out ≠ 0} =
      {q | q.out ∈ iwahoriCoset t} := by
    ext q
    simp [cosetInd]
  have hfin : {q : GL (Fin n) k ⧸ iwahori k (Fin n) | q.out ∈ iwahoriCoset t}.Finite :=
    finite_cosets (IwahoriOnto.isOpen_iwahori k (Fin n)) (isCompact_iwahoriCoset t)
  refine ⟨hset ▸ hfin, fun V _ _ π v hv => ?_⟩
  have hcard := card_cosets ht hfin.toFinset fun q => hfin.mem_toFinset
  have hsum : PositivityTheory.Rg.BcB.F.Tail.PExp.hkS π (iwahori k (Fin n)) (cosetInd t) v =
      ∑ q ∈ hfin.toFinset, cosetInd t q.out • π q.out v := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    rw [Set.Finite.coe_toFinset]
    by_contra h
    apply hq
    have h0 : cosetInd t q.out = 0 := by
      by_contra h'
      exact h (hset ▸ h')
    simp [h0]
  rw [hsum]
  have hterm : ∀ q ∈ hfin.toFinset, (Submodule.Quotient.mk (cosetInd t q.out • π q.out v) :
      Jacquet π (unipB k (Fin n))) = jacBU π t (Submodule.Quotient.mk v) := by
    intro q hq
    have hq' : q.out ∈ iwahoriCoset t := hfin.mem_toFinset.1 hq
    have h1 : cosetInd t q.out = 1 := by simp [cosetInd, hq']
    rw [h1, one_smul]
    exact mk_act ht π hv hq'
  have hmk : (Submodule.Quotient.mk (∑ q ∈ hfin.toFinset, cosetInd t q.out • π q.out v) :
      Jacquet π (unipB k (Fin n))) = ∑ q ∈ hfin.toFinset,
        (Submodule.Quotient.mk (cosetInd t q.out • π q.out v) : Jacquet π (unipB k (Fin n))) :=
    map_sum (Submodule.mkQ _) _ _
  rw [hmk, Finset.sum_congr rfl hterm, Finset.sum_const, ← hcard, Complex.ofReal_natCast,
    Nat.cast_smul_eq_nsmul]

end GlobalTheory.CompanionTheory.IwahoriCount

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DropHom
section
noncomputable section

open GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.FineProd

variable {k : Type} [Field k]

def dropHom {r r' : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r) :
    Levi k (fun j => Fin (d j)) →* Levi k (fun a => Fin (d (o a))) where
  toFun g a := g (o a)
  map_one' := rfl
  map_mul' _ _ := rfl

end GlobalTheory.CompanionTheory.FineProd

end
end

