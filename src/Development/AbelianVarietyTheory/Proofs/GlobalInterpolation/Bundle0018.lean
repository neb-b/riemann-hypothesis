module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AveragedFibreMeasureComplFibreEqZero
section
open MeasureTheory Topology

namespace GlobalTheory.QuadFibre

theorem fibOf_compl_fibre : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ t : K, GlobalTheory.QuadFibre.fibOf μ ν q U s t (q ⁻¹' {t})ᶜ = 0 := by
  intro K V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ q hq hh U s hs t
  obtain ⟨hUo, hUc, h1, hmul, hinv, hn, hsc, hsq⟩ := hs
  by_cases ht : t = 0
  · subst ht; rw [fibOf_zero]; rfl
  have hm : Measurable (fun x : V => s (t / q x) • x) := by
    have h1 : Measurable (fun x : V => s (t / q x)) :=
      hsc.measurable.comp (measurable_const.div hq.measurable)
    exact h1.smul measurable_id
  have hA : MeasurableSet (q ⁻¹' {t})ᶜ :=
    ((isClosed_singleton.preimage hq).measurableSet).compl
  rw [fibOf_ne _ _ _ _ _ ht, Measure.smul_apply, Measure.map_apply hm hA,
    Measure.restrict_apply (hm hA)]
  convert smul_zero _
  convert measure_empty (μ := μ)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, u, hu, hx2⟩
  apply hx1
  have hu0 : u ≠ 0 := by
    intro h
    have := hn u hu
    rw [h] at this
    simp at this
  have hx2' : q x = t * u := by simpa using hx2.symm
  have h3 : t / q x = u⁻¹ := by rw [hx2']; field_simp
  show q (s (t / q x) • x) = t
  rw [hh, h3, hsq _ (hinv u hu), hx2']
  field_simp

end GlobalTheory.QuadFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
section
noncomputable section

namespace GlobalTheory.CompactDualQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal

variable {P Q P' Q' : ℕ}

def sg {P Q : ℕ} : Fin P ⊕ Fin Q → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

def SignCompat (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Prop :=
  ∀ i, sg (e (some i)) = sg i

def l1 (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : ℝ := ∑ i, ∑ j, ‖Z i j‖

def gauge (g : UpqT P Q) : ℝ := l1 (UpqT.mat g - 1)

def baseVec (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Sp P Q := Pi.single (e none) 1

def ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ + 2 * ∑ i, ‖y (e (some i))‖

def tanGauge (t : ℝ × Sp P' Q') : ℝ := |t.1| + 2 * ∑ i, ‖t.2 i‖

def polarPt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') : Sp P Q :=
  fun i => (e.symm i).elim
    ((Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I)) t.2

def IsBlockEmb (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q) : Prop :=
  ∀ g, UpqT.mat (j g) (e none) (e none) = 1 ∧ (∀ b, UpqT.mat (j g) (e none) (e (some b)) = 0) ∧
    (∀ a, UpqT.mat (j g) (e (some a)) (e none) = 0) ∧
    ∀ a b, UpqT.mat (j g) (e (some a)) (e (some b)) = UpqT.mat g a b

def expBall (P Q : ℕ) (r : ℝ) : Set (UpqT P Q) :=
  {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
    NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}

theorem sg_eq (i : Fin P ⊕ Fin Q) : sg i = 1 ∨ sg i = -1 := by
  rcases i with i | i <;> simp [sg]

theorem sg_ne_zero (i : Fin P ⊕ Fin Q) : sg i ≠ 0 := by
  rcases sg_eq i with h | h <;> rw [h] <;> norm_num

theorem qf_eq_sum (x : Sp P Q) : qf x = ∑ i, sg i * Complex.normSq (x i) := by
  simp [qf, sg, Fintype.sum_sum_type, sub_eq_add_neg]

theorem qf_baseVec (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    qf (baseVec e) = sg (e none) := by
  rw [qf_eq_sum, Finset.sum_eq_single (e none)]
  · simp [baseVec]
  · intro b _ hb; simp [baseVec, hb]
  · simp

theorem card_eq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : P + Q = P' + Q' + 1 := by
  simpa using (Fintype.card_congr e).symm

theorem polarPt_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') :
    polarPt e t (e none) =
      (Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I) := by
  simp [polarPt]

theorem polarPt_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q')
    (i : Fin P' ⊕ Fin Q') : polarPt e t (e (some i)) = t.2 i := by
  simp [polarPt]

theorem weightAbsEntrySum_nonneg (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : 0 ≤ l1 Z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem continuous_matrixEntryAbsSum : Continuous (l1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → ℝ) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm

theorem continuous_gauge : Continuous (gauge : UpqT P Q → ℝ) :=
  continuous_matrixEntryAbsSum.comp
    ((Units.continuous_val.comp continuous_subtype_val : Continuous UpqT.mat).sub continuous_const)

theorem ptGauge_nonneg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) :
    0 ≤ ptGauge e y := by
  unfold ptGauge; positivity

theorem continuous_ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (ptGauge e) := by
  unfold ptGauge; fun_prop

theorem tanGauge_nonneg (t : ℝ × Sp P' Q') : 0 ≤ tanGauge t := by
  unfold tanGauge; positivity

theorem continuous_tanGauge : Continuous (tanGauge : ℝ × Sp P' Q' → ℝ) := by
  unfold tanGauge; fun_prop

theorem tendsto_div_of_squeeze {F V A : ℝ → ℝ≥0∞} {n : ℕ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hV : ∀ t r : ℝ, 0 < t → 0 < r → V (t * r) = ENNReal.ofReal (t ^ n) * V r)
    (hF : Tendsto (fun r => F r / V r) (𝓝[>] 0) (𝓝 c))
    (hA : ∀ t : ℝ, 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), F (t⁻¹ * r) ≤ A r ∧ A r ≤ F (t * r)) :
    Tendsto (fun r => A r / V r) (𝓝[>] 0) (𝓝 c) := by
  have key : ∀ t : ℝ, 0 < t →
      Tendsto (fun r => F (t * r) / V r) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (t ^ n) * c)) := by
    intro t ht
    have h1 : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos ht hr
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (t ^ n)) (hF.comp h1)
      (Or.inr ENNReal.ofReal_ne_top)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have h0 : ENNReal.ofReal (t ^ n) ≠ 0 := by simpa using pow_pos ht n
    simp only [Function.comp, hV t r ht hr]
    rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ h0 ENNReal.ofReal_ne_top]
  have lim : ∀ u : ℝ → ℝ, ContinuousAt u 1 → u 1 = 1 →
      Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n) * c) (𝓝[>] 1) (𝓝 c) := by
    intro u hu h1
    have h3 : Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n)) (𝓝 1) (𝓝 1) := by
      have := (ENNReal.continuous_ofReal.continuousAt.comp (hu.pow n)).tendsto
      simp only [Function.comp, Pi.pow_apply, h1, one_pow, ENNReal.ofReal_one] at this
      exact this
    have := ENNReal.Tendsto.mul_const (b := c) h3 (Or.inr hc)
    rw [one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t⁻¹) (continuousAt_inv₀ one_ne_zero) inv_one).eventually
      (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t⁻¹ (inv_pos.2 (by linarith))).eventually (lt_mem_nhds h1), hA t ht]
      with r h3 h4 using h3.trans_le (ENNReal.div_le_div_right h4.1 _)
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t) continuousAt_id rfl).eventually
      (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t (by linarith)).eventually (gt_mem_nhds h1), hA t ht]
      with r h3 h4 using (ENNReal.div_le_div_right h4.2 _).trans_lt h3

end GlobalTheory.CompactDualQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SelfDualLatticeCompare

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_of_conj_eq (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h0
  · have : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := he
    rw [h0, Algebra.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h0 ▸ Algebra.mem_top
    have hx' : σ x = x := hx
    have := h.2.2.2 τ x
    rw [hx'] at this
    exact this.symm

theorem trace_field (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  have hσ := conj_conj h
  obtain ⟨a, ha⟩ := exists_of_conj_eq h (e + σ e) (by rw [map_add (f := _), hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h.2.2.1, map_add (f := _), h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

variable (R : Type) [CommRing R] [Algebra F R]

theorem trace_tensor (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) =
        a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj h]

theorem hR_self (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (x : Fin M → R ⊗[F] E) : hR R σ J x x = algebraMap R (R ⊗[F] E) (qR R σ J x) := by
  have hJ' : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  have hs : sigR R σ (hR R σ J x x) = hR R σ J x x := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R h]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ']
    ring
  have h2 : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1 := by
    rw [← IsScalarTower.algebraMap_apply, ← map_ofNat (algebraMap F (R ⊗[F] E)) 2, ← map_mul,
      show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  rw [qR, map_mul, trace_tensor R h, hs, ← two_mul, ← mul_assoc, h2, one_mul]

theorem hR_smul_right {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E)
    (c : R ⊗[F] E) : hR R σ J x (c • y) = c * hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Field

section Clauses

open GlobalTheory.IndefiniteRowSideFullHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem unram_iff : UnitaryLatticeOrthogonal.UnramAt F E v ↔ SelfDualLatticeActions.UnramifiedOrSplit E v := by
  refine forall_congr' fun w => forall_congr' fun hw => ?_
  haveI := w.isPrime
  haveI := w.isMaximal
  exact Ideal.ramificationIdx_eq_one_iff

theorem isSDLat_iff (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.IsSDLat σ J v L ↔ SelfDualLatticeActions.IsSelfDualLat v σ J L := Iff.rfl

theorem hasONB_iff (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.HasONB σ J v L ↔ SelfDualLatticeActions.HasOrthonormalBasis v σ J L := by
  refine exists_congr fun b => ?_
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.one_apply]
  exact Iff.rfl

theorem disjoint_span_perpLat (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (x : SelfDualLatticeActions.Wv E v M)
    (hx : IsUnit (qR (Fv F v) σ J x)) :
    Disjoint (Submodule.span (SelfDualLatticeActions.OEv E v) {x}) (SelfDualLatticeActions.perpLat v σ J x L) := by
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have h0 : hR (Fv F v) σ J x ((c : SelfDualLatticeActions.Ev E v) • x) = 0 := hy'.1
  rw [hR_smul_right, hR_self _ h hJ, (hx.map _).mul_left_eq_zero] at h0
  show (c : SelfDualLatticeActions.Ev E v) • x = 0
  rw [h0, zero_smul]

theorem unitVectors_iff (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (β : Fv F v) (hβ : IsUnit β) :
    UnitaryLatticeOrthogonal.UnitVectors σ J v L β ↔ SelfDualLatticeActions.UnitVectorClaims v σ J L β := by
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  refine forall_congr' fun x => forall_congr' fun hx => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, disjoint_span_perpLat σ J v h hJ L x (hx.2 ▸ hβ), h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1.symm, h2⟩

theorem conclusion_iff (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    (UnitaryLatticeOrthogonal.HasONB σ J v L ∧
      (∀ L₁ : Submodule (UnitaryLatticeOrthogonal.OEv F E v) (Fin M → UnitaryLatticeOrthogonal.Ev F E v), UnitaryLatticeOrthogonal.IsSDLat σ J v L₁ →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ UnitaryLatticeOrthogonal.act σ J v g y ∈ L₁) ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        UnitaryLatticeOrthogonal.UnitVectors σ J v L ((β : v.adicCompletionIntegers F) : Fv F v)) ↔
    (SelfDualLatticeActions.HasOrthonormalBasis v σ J L ∧
      (∀ L' : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M), SelfDualLatticeActions.IsSelfDualLat v σ J L' →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ SelfDualLatticeActions.act v σ J g y ∈ L') ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        SelfDualLatticeActions.UnitVectorClaims v σ J L ((β : v.adicCompletionIntegers F) : Fv F v)) :=
  and_congr (hasONB_iff σ J v L) (and_congr Iff.rfl (forall_congr' fun β =>
    unitVectors_iff σ J v h hJ L _ (β.isUnit.map (v.adicCompletionIntegers F).subtype)))

end Clauses

theorem selfDualLattices_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.SelfDualLattices ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas := by
  refine forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun σ => forall_congr' fun h => forall_congr' fun M => forall_congr' fun J => ?_
  rw [imp.swap]
  refine forall_congr' fun _ => forall_congr' fun hJ => forall_congr' fun v => ?_
  refine imp_congr (unram_iff v) (forall_congr' fun L => ?_)
  exact imp_congr (isSDLat_iff σ J v L) (conclusion_iff σ J v h hJ L)

end GlobalTheory.SelfDualLatticeCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbeddingStatement
section
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bruhatFunction_of_closedEmbedding : ∀ (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T'] (j : T' →* T), IsClosedEmbedding j → ∀ (m' : Measure T') [m'.IsHaarMeasure] [m'.IsInvInvariant], ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  first | exact @GlobalTheory.exists_bruhat_function_closedEmbedding | exact GlobalTheory.exists_bruhat_function_closedEmbedding | (intros; apply GlobalTheory.exists_bruhat_function_closedEmbedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCompactOpenUnitsSubgroupContinuousSqrt
section
open MeasureTheory Topology

namespace GlobalTheory.QuadFibre

theorem exists_local_sqrt_near_one (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : ∃ (N : Set K) (g : K → K), IsOpen N ∧ (1 : K) ∈ N ∧ ContinuousOn g N ∧
      ∀ u ∈ N, g u ^ 2 = u := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  have hf := hd.hasStrictFDerivAt_equiv h2
  let e := hf.toOpenPartialHomeomorph _
  have he : (e : K → K) = fun x => x ^ 2 := hf.toOpenPartialHomeomorph_coe
  refine ⟨e.target, e.symm, e.open_target, ?_, e.continuousOn_symm, fun u hu => ?_⟩
  · simpa using hf.image_mem_toOpenPartialHomeomorph_target
  · have := e.right_inv hu
    rwa [he] at this

theorem exists_isSqrtOn (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] (h2 : (2 : K) ≠ 0) : ∃ (U : Set K) (s : K → K), IsSqrtOn U s := by
  classical
  obtain ⟨N, g, hN, h1, hg, hsq⟩ := exists_local_sqrt_near_one K h2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hN 1 h1
  set r : ℝ := min (ε / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsub : Metric.closedBall (1 : K) r ⊆ N :=
    (Metric.closedBall_subset_ball hrε).trans hball
  have hopen : IsOpen (Metric.closedBall (1 : K) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr0.ne'
  have hclopen : IsClopen (Metric.closedBall (1 : K) r) := ⟨Metric.isClosed_closedBall, hopen⟩
  have hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1 := by
    intro a ha
    rw [mem_closedBall_iff_norm] at ha
    have hlt : ‖a - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; linarith
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, norm_one] at this
    exact this
  refine ⟨Metric.closedBall 1 r, (Metric.closedBall (1 : K) r).piecewise g (fun _ => 1), hopen,
    isCompact_closedBall _ _, Metric.mem_closedBall_self hr0.le, ?_, ?_, hnorm, ?_, ?_⟩
  · intro a ha b hb
    have hna := hnorm a ha
    rw [mem_closedBall_iff_norm] at ha hb ⊢
    have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
    rwa [norm_mul, hna, one_mul]
  · intro a ha
    have hna := hnorm a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hna
    rw [mem_closedBall_iff_norm] at ha ⊢
    have : a⁻¹ - 1 = -(a⁻¹ * (a - 1)) := by field_simp; ring
    rwa [this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul]
  · refine continuous_piecewise ?_ ?_ continuousOn_const
    · simp [hclopen.frontier_eq]
    · rw [Metric.isClosed_closedBall.closure_eq]
      exact hg.mono hsub
  · intro a ha
    rw [Set.piecewise_eq_of_mem _ _ _ ha]
    exact hsq a (hsub ha)

end GlobalTheory.QuadFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExtStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_finite_zeros_on_line_cmExt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ y : Fin M → K ⊗[F] E, ∀ x : Fin M → K ⊗[F] E, {t : K | qR K σ J (x + t • y) = 0}.Finite := by
  first | exact @GlobalTheory.HermLineZeros.finite_zeros_on_line | exact GlobalTheory.HermLineZeros.finite_zeros_on_line | (intros; apply GlobalTheory.HermLineZeros.finite_zeros_on_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPointStatement
section
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreFamily_eq_at_continuity_point : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℝ) (O U U' : Set V) (B B' : Set ℝ) (fib fib' : ℝ → Measure V) (β : ℝ), Measurable f → IsOpen O → O ⊆ U → O ⊆ U' → f ⁻¹' {β} ⊆ O → IsOpen B → IsOpen B' → β ∈ B → β ∈ B' → IsFibreFamily μ f id U (volume : Measure ℝ) B fib → IsFibreFamily μ f id U' (volume : Measure ℝ) B' fib' → fib β = fib' β := by
  first | exact @GlobalTheory.IsFibreFamily_eq_at | exact GlobalTheory.IsFibreFamily_eq_at | (intros; apply GlobalTheory.IsFibreFamily_eq_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyUnivOfNullConeStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreFamily_univ_of_null_cone' : ∀ (K V : Type) [NormedField K] [IsUltrametricDist K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) (q : V → K), Continuous q → μ {x | q x = 0} = 0 → ∀ (U : Set V) (B : Set K) (fib : K → Measure V), {x | q x ≠ 0} ⊆ U → {t | t ≠ 0} ⊆ B → IsFibreFamily μ q id U ν B fib → IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by
  first | exact @GlobalTheory.isFibreFamily_univ_of_null_cone | exact GlobalTheory.isFibreFamily_univ_of_null_cone | (intros; apply GlobalTheory.isFibreFamily_univ_of_null_cone <;> assumption)
end

