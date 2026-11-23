module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0119
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0039
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeTranslationOperatorEqPhaseMulNegComp
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0121

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetIsometryEqOne
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.KapVal

open IsDedekindDomain

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [NumberField K] (j : K →+* ℂ_[q])
    (y : 𝓞 K) : ‖j (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by
    convert map_isIntegral_int j (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

theorem norm_natCast_lt_one (q : ℕ) [Fact q.Prime] : ‖((q : ℕ) : ℂ_[q])‖ < 1 := by
  have e : ((q : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by
    simp
  rw [e, PadicComplex.norm_extends']
  exact Padic.norm_p_lt_one

end GlobalTheory.KapVal

namespace GlobalTheory.KapVal

open IsDedekindDomain

variable {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [NumberField K]

theorem exists_place (j : K →+* ℂ_[q]) :
    ∃ w : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ w.asIdeal ∧ ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1 := by
  let P : Ideal (𝓞 K) :=
    { carrier := {x | ‖j (x : K)‖ < 1}
      add_mem' := fun {x y} hx hy => by
        show ‖j ((x : K) + (y : K))‖ < 1
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      zero_mem' := by
        show ‖j (0 : K)‖ < 1
        simp
      smul_mem' := fun r x hx => by
        show ‖j ((r : K) * (x : K))‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one_of_int j r) (norm_nonneg _) hx }
  have hP : ∀ x : 𝓞 K, x ∈ P ↔ ‖j (x : K)‖ < 1 := fun _ => Iff.rfl
  have hl : ((q : ℕ) : 𝓞 K) ∈ P := by
    rw [hP]
    have e : j (((q : ℕ) : 𝓞 K) : K) = ((q : ℕ) : ℂ_[q]) := by simp
    rw [e]
    exact norm_natCast_lt_one q
  have hprime : P.IsPrime := by
    refine ⟨?_, fun {x y} hxy => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]
      simp
    · rw [hP] at hxy
      have e : j ((x * y : 𝓞 K) : K) = j (x : K) * j (y : K) := by simp
      rw [e, norm_mul] at hxy
      rw [hP, hP]
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hxy)
  refine ⟨⟨P, hprime, ?_⟩, hl, hP⟩
  intro h0
  rw [h0, Ideal.mem_bot] at hl
  exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast hl)

theorem norm_le_one_of_val (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (x : K) (hx : w.valuation K x ≤ 1) :
    ‖j x‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hd : 1 ≤ ‖j ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have h2 : ‖j x‖ * ‖j ((d : 𝓞 K) : K)‖ = ‖j (n : K)‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun z => ‖j z‖) h
  have h3 := norm_le_one_of_int j n
  nlinarith [norm_nonneg (j x)]

theorem norm_eq_one_of_val (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (x : K) (hx : w.valuation K x = 1) :
    ‖j x‖ = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 := norm_le_one_of_val j w hw x hx.le
  have h2 := norm_le_one_of_val j w hw x⁻¹ (by rw [map_inv₀, hx, inv_one])
  have h3 : ‖j x‖ * ‖j x⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
  nlinarith [norm_nonneg (j x), norm_nonneg (j x⁻¹)]

theorem norm_pow_eq (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (n : ℕ) (π : 𝓞 K)
    (hπ : w.valuation K (π : K) = WithZero.exp (-(n : ℤ))) (x : K) (hx : x ≠ 0) :
    ‖j x‖ ^ n = ‖j (π : K)‖ ^ (-WithZero.log (w.valuation K x)) := by
  set y := -WithZero.log (w.valuation K x) with hy
  have hv0 : w.valuation K x ≠ 0 := by simpa using hx
  have hvx : w.valuation K x = WithZero.exp (-y) := by
    rw [hy, neg_neg, WithZero.exp_log hv0]
  have hπ0 : (π : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hz : w.valuation K (x ^ n * (π : K) ^ (-y)) = 1 := by
    rw [map_mul, map_pow, map_zpow₀, hvx, hπ, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  have h1 := norm_eq_one_of_val j w hw _ hz
  rw [map_mul, map_pow, map_zpow₀, norm_mul, norm_pow, norm_zpow] at h1
  have hjπ : ‖j (π : K)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero j).2 hπ0
  have h2 : ‖j (π : K)‖ ^ (-y) * ‖j (π : K)‖ ^ y = 1 := by
    rw [← zpow_add₀ hjπ, neg_add_cancel, zpow_zero]
  calc ‖j x‖ ^ n = ‖j x‖ ^ n * (‖j (π : K)‖ ^ (-y) * ‖j (π : K)‖ ^ y) := by rw [h2, mul_one]
    _ = (‖j x‖ ^ n * ‖j (π : K)‖ ^ (-y)) * ‖j (π : K)‖ ^ y := by ring
    _ = ‖j (π : K)‖ ^ y := by rw [h1, one_mul]

end GlobalTheory.KapVal

namespace GlobalTheory.KapVal

open IsDedekindDomain

theorem norm_kappa_sq_mul_det : ∀ (D : D7) (γ₀ γ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], q ≠ 2 →
    jacobiSym (-(D.host.d : ℤ)) q = 1 → γ.AtP q → ∀ ι : ℂ ≃+* ℂ_[q],
    ‖ι k.kappa‖ ^ 2 * ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = 1 := by
  intro D γ₀ γ k q _ hq2 hj hat ι
  have hqp : q.Prime := Fact.out
  have hs : SplitK D q := Or.inr hj
  let jK : D.host.K →+* ℂ_[q] := ι.toRingHom.comp (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
  let jK' : D.host.K →+* ℂ_[q] := ι.toRingHom.comp (D.host.φ₀.comp
    ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E)))
  have ejK : ∀ z : D.host.K, jK z = ι (D.host.φ₀ (z : D.host.E)) := fun z => rfl
  have ejK' : ∀ z : D.host.K, jK' z = ι (D.host.φ₀ (D.host.conj (z : D.host.E))) := fun z => rfl
  have hU := _root_.GlobalTheory.detRel_mul_conj_eq_one D γ₀ γ
  set x : D.host.K := γ.detRel γ₀ with hxdef
  set h : ℕ := classNumber D.host.K with hh
  have hy : ordK (k.pp q) x = k.yP q :=
    yIndep D γ₀ q (k.pp q) γ (k.gaP q) hqp hs (k.pp_over q hqp hs) hat (k.gaP_at q hqp hs)
  have hπv : (k.pp q).valuation D.host.K ((k.pi q : 𝓞 D.host.K) : D.host.K) = WithZero.exp (-(h : ℤ)) :=
    GlobalTheory.T.valuation_eq_exp_neg_of_pow_eq_span_singleton D.host.K (k.pp q) h (k.pi q) (k.pi_gen q hqp hs)
  have hkap := _root_.GlobalTheory.KapSplitNorm.norm_kappa_split D γ₀ k q hs ι
  have hrt := k.rt_pow q hqp hs
  have hrt0 := k.rt_ne_zero q hqp hs
  set y : ℤ := k.yP q with hydef
  set 𝔭 := k.pp q with h𝔭
  set π : 𝓞 D.host.K := k.pi q with hπdef
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hU
    simp at hU
  have hxx : ‖jK x‖ * ‖jK' x‖ = 1 := by
    rw [← norm_mul, ejK, ejK', ← map_mul, ← map_mul, hU, map_one, map_one, norm_one]
  obtain ⟨w, hqw, hw⟩ := exists_place jK
  obtain ⟨w', hqw', hw'⟩ := exists_place jK'
  have hne : w ≠ w' := by
    intro heq
    obtain ⟨y0, h1, h2⟩ := _root_.GlobalTheory.ConjPlace.conj_place_ne D q hq2 hj ι
    have a1 : y0 ∈ w.asIdeal := (hw y0).2 (by rw [ejK]; exact h1)
    rw [heq, hw', ejK'] at a1
    exact absurd a1 (not_lt.2 h2)
  have hq𝔭 : ((q : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal := k.pp_over q hqp hs
  have hnot : ∀ v : HeightOneSpectrum (𝓞 D.host.K), v ≠ 𝔭 → π ∉ v.asIdeal := by
    intro v hv hπ
    apply hv
    have h1 : 𝔭.asIdeal ^ h ≤ v.asIdeal := by
      rw [hh, k.pi_gen q hqp hs, Ideal.span_singleton_le_iff_mem]
      exact hπ
    have h2 : 𝔭.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le h1
    have h3 : 𝔭.asIdeal = v.asIdeal := 𝔭.isMaximal.eq_of_le v.isPrime.ne_top h2
    exact (HeightOneSpectrum.ext h3).symm
  have hone : ∀ (j : D.host.K →+* ℂ_[q]) (v : HeightOneSpectrum (𝓞 D.host.K)),
      (∀ z : 𝓞 D.host.K, z ∈ v.asIdeal ↔ ‖j (z : D.host.K)‖ < 1) → v ≠ 𝔭 → ‖j (π : D.host.K)‖ = 1 := by
    intro j v hv hv𝔭
    exact le_antisymm (norm_le_one_of_int j π) (not_lt.1 fun hlt => hnot v hv𝔭 ((hv π).2 hlt))
  have key : ‖jK x‖ ^ h = (‖jK (π : D.host.K)‖ / ‖jK' (π : D.host.K)‖) ^ y := by
    rcases GlobalTheory.T.quadratic_field_at_most_two_primes_over_prime D.host.K (kQuad D) q hqp 𝔭 w w' hq𝔭 hqw hqw' with e | e | e
    · have h1 := norm_pow_eq jK w hw h π (by rw [← e]; exact hπv) x hx0
      have h2 : -WithZero.log (w.valuation D.host.K x) = y := by rw [← e]; exact hy
      rw [h2] at h1
      rw [h1, hone jK' w' hw' (fun e' => hne (e.symm.trans e'.symm)), div_one]
    · have h1 := norm_pow_eq jK' w' hw' h π (by rw [← e]; exact hπv) x hx0
      have h2 : -WithZero.log (w'.valuation D.host.K x) = y := by rw [← e]; exact hy
      rw [h2] at h1
      rw [hone jK w hw (fun e' => hne (e'.trans e)), one_div, inv_zpow', zpow_neg, ← h1]
      have hx' : ‖jK x‖ = ‖jK' x‖⁻¹ := eq_inv_of_mul_eq_one_left hxx
      rw [hx', inv_pow]
    · exact absurd e hne
  have hjx : ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = ‖jK x‖ := rfl
  rw [hjx, hkap]
  rw [← hh] at hrt
  have hr0 : 0 < ‖ι (k.rt q)‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hrt0)
  have hratio : ‖jK (π : D.host.K)‖ / ‖jK' (π : D.host.K)‖ = ‖ι (k.rt q)‖ ^ (2 * h) := by
    rw [ejK, ejK', ← norm_div, ← map_div₀, ← hrt, map_pow, norm_pow]
  rw [hratio] at key
  have hh0 : h ≠ 0 := by rw [hh]; exact (NumberField.classNumber_pos D.host.K).ne'
  have hxr : ‖jK x‖ = ‖ι (k.rt q)‖ ^ (2 * y) := by
    have e : (‖ι (k.rt q)‖ ^ (2 * h)) ^ y = (‖ι (k.rt q)‖ ^ (2 * y)) ^ h := by
      rw [← zpow_natCast, ← zpow_natCast (‖ι (k.rt q)‖ ^ (2 * y)), ← zpow_mul, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e] at key
    exact (pow_left_inj₀ (norm_nonneg _) (zpow_nonneg hr0.le _) hh0).1 key
  rw [hxr, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hr0.ne']
  rw [show -y * ((2 : ℕ) : ℤ) + 2 * y = 0 by push_cast; ring, zpow_zero]

end GlobalTheory.KapVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.QuotDiscrete


open MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  have h1 : μ.inv = Measure.haarScalarFactor μ.inv μ • μ :=
    Measure.isMulLeftInvariant_eq_smul μ.inv μ
  set c := Measure.haarScalarFactor μ.inv μ with hc
  have h2 : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [← h1]
      _ = c • μ.inv := by
          ext s _
          simp [Measure.inv_apply]
      _ = (c * c) • μ := by rw [h1, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK1
  have hfin : μ K < ∞ := hK.measure_lt_top
  have h3 : ((c * c : NNReal) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]
    conv_rhs => rw [h2]
    rfl
  have h4 : ((c * c : NNReal) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h3
  have h5 : ((c : ℝ) * c) = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  exact ⟨by rw [h1, h6, one_smul]⟩


open MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.QuotDiscrete.existsUnique_subgroupOf {G : Type} [Group G] {Γ H : Subgroup G} (hΓ : Γ ≤ H) {F : Set G}
    (hF : ∀ x : G, ∃! γ : Γ, γ • x ∈ F) (g : G) (h : H) :
    ∃! γ : Γ.subgroupOf H, γ • h ∈ {h : H | (h : G) * g ∈ F} := by
  obtain ⟨γ, hγ, huniq⟩ := hF (h * g)
  refine ⟨⟨⟨γ, hΓ γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at hγ ⊢
    simpa [mul_assoc] using hγ
  · intro δ hδ
    have hδ' : (⟨((δ : H) : G), Subgroup.mem_subgroupOf.1 δ.2⟩ : Γ) • ((h : G) * g) ∈ F := by
      simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at hδ ⊢
      simpa [mul_assoc] using hδ
    have := huniq _ hδ'
    have h2 : ((δ : H) : G) = (γ : G) := congrArg Subtype.val this
    exact Subtype.ext (Subtype.ext h2)


open MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.QuotDiscrete.discreteClause : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.DiscreteClause := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.DiscreteClause
  intro G _ _ _ _ _ _ _ _ H _ _ _ _ hH hG hHu dg _ ν _ μ hμ hQ Γ hΓ hd
  haveI : Countable Γ := (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  haveI : Countable (Γ.subgroupOf H) :=
    Countable.of_equiv _ (Subgroup.subgroupOfEquivOfLe hΓ).toEquiv.symm
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ν.IsMulRightInvariant := hHu ν inferInstance
  haveI : ν.IsInvInvariant := _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant ν
  haveI : dg.IsMulRightInvariant := hG dg inferInstance
  haveI : dg.IsInvInvariant := _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant dg
  obtain ⟨F, hFm, hF⟩ := _root_.GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have hFg : ∀ g : G, MeasurableSet {h : H | (h : G) * g ∈ F} := fun g =>
    hFm.preimage (measurable_subtype_coe.mul_const g)
  have hFD : IsFundamentalDomain Γ F dg := IsFundamentalDomain.mk' hFm.nullMeasurableSet hF
  have hFD' : ∀ g : G, IsFundamentalDomain (Γ.subgroupOf H) {h : H | (h : G) * g ∈ F} ν :=
    fun g => IsFundamentalDomain.mk' (hFg g).nullMeasurableSet
      (_root_.GlobalTheory.QuotDiscrete.existsUnique_subgroupOf hΓ hF g)
  refine ⟨⟨F, hFm, hFD⟩, ⟨_, hFg 1, hFD' 1⟩, ?_⟩
  intro D D' hD hD' f hf hinv
  have hFi : Measurable (F.indicator f) := hf.indicator hFm
  have hK : Measurable (fun x : G => F.indicator f x⁻¹) := hFi.comp measurable_inv
  obtain ⟨hcm, hcint⟩ := hQ _ hK
  have he : Continuous (QuotientGroup.quotientRightRelEquivQuotientLeftRel H) := by
    refine (Topology.IsQuotientMap.continuous_iff isQuotientMap_quotient_mk').2 ?_
    have hc : Continuous fun g : G => ((g⁻¹ : G) : G ⧸ H) :=
      continuous_quotient_mk'.comp continuous_inv
    exact hc
  refine ⟨fun q => _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H q), hcm.comp he.measurable, ?_, ?_⟩
  · intro g
    show _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹) ((g⁻¹ : G) : G ⧸ H) = _
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk]
    calc ∫⁻ h : H, F.indicator f (g⁻¹ * (h : G))⁻¹ ∂ν = ∫⁻ h : H, F.indicator f ((h : G) * g) ∂ν := by
          rw [← lintegral_inv_eq_self (μ := ν) (fun h : H => F.indicator f ((h : G) * g))]
          congr 1
          funext h
          simp [mul_inv_rev]
      _ = ∫⁻ h in {h : H | (h : G) * g ∈ F}, f ((h : G) * g) ∂ν := by
          rw [← lintegral_indicator (hFg g)]
          congr 1
      _ = ∫⁻ h in D', f ((h : G) * g) ∂ν := by
          refine (hFD' g).setLIntegral_eq hD' (fun h : H => f ((h : G) * g)) (fun γ h => ?_)
          simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
          exact hinv _ (Subgroup.mem_subgroupOf.1 γ.2) _
  · unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.rightMeasure
    calc ∫⁻ x in D, f x ∂dg = ∫⁻ x in F, f x ∂dg :=
          hD.setLIntegral_eq hFD f (fun γ x => hinv _ γ.2 x)
      _ = ∫⁻ x, F.indicator f x ∂dg := (lintegral_indicator hFm f).symm
      _ = ∫⁻ x, F.indicator f x⁻¹ ∂dg := (lintegral_inv_eq_self (μ := dg) (F.indicator f)).symm
      _ = ∫⁻ q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹) q ∂μ := hcint
      _ = ∫⁻ q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹)
            (QuotientGroup.quotientRightRelEquivQuotientLeftRel H (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H q)) ∂μ := by
          congr 1
          funext q
          rw [show _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H q =
            (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm q from rfl,
            Equiv.apply_symm_apply]
      _ = _ := (lintegral_map (hcm.comp he.measurable)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.continuous_invCoset H).measurable).symm

end GlobalTheory.QuotDiscrete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeDensity
section
namespace GlobalTheory.LatticeDensityClosed

theorem selfDualLatticeDensity : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.SelfDualLatticeDensity :=
  GlobalTheory.LocalDensityCompare.localDensity_iff.1
    (GlobalTheory.LatticeDensity.localDensity_of_selfDualLatticeLemmas
      GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas)

end GlobalTheory.LatticeDensityClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslatePrimeToOrderPreservesThetaIntegrality
section
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

noncomputable section
namespace GlobalTheory.MomTrans

variable {g : ℕ}

theorem ok_natCast_mul {d : ℕ} (n : ℕ) {z : ℂ} (h : z ∈ OK d) : (n : ℂ) * z ∈ OK d := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

theorem nnBasis_of_frame (q : ℕ) (S : Setup g) (hO : S.Ok) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ)
    (hx : ∀ i, x i ∈ S.La) (hb : ∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    (ha : ∀ i, 0 < a i ∧ Nat.Coprime (a i) q) : S.NNBasis q x := by
  classical
  have key : ∀ (c : Fin g → ℂ) (j : Fin g), beta S.d S.Hm (∑ i, c i • x i) (x j) = c j * a j := by
    intro c j
    rw [GlobalTheory.MomOne.Translates.beta_sum_left]
    simp [hb]
  have hli : LinearIndependent ℂ x := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := key c j
    rw [hc] at h
    have h0 : beta S.d S.Hm 0 (x j) = 0 := by simp [beta, hf]
    rw [h0] at h
    have : (a j : ℂ) ≠ 0 := by exact_mod_cast (ha j).1.ne'
    exact (mul_eq_zero.1 h.symm).resolve_right this
  let B := Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (by simp)).ge
  have hB : ∀ i, B i = x i := fun i => by simp [B]
  refine ⟨hx, fun y hy => ?_, fun c _ hc i => ?_⟩
  · have hy' : y = ∑ i, B.repr y i • x i := by
      conv_lhs => rw [← B.sum_repr y]
      simp only [hB]
    have hr : ∀ i, beta S.d S.Hm y (x i) = B.repr y i * a i := by
      intro i; conv_lhs => rw [hy']
      exact key _ i
    refine ⟨∏ i, a i, Nat.Coprime.prod_left fun i _ => (ha i).2,
      fun i => ((∏ j ∈ Finset.univ.erase i, a j : ℕ) : ℂ) * beta S.d S.Hm y (x i), fun i => ?_, ?_⟩
    · exact ok_natCast_mul _ (hO.2.2.2.2.2.2.1 y hy (x i) (hx i))
    · conv_lhs => rw [hy']
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [smul_smul, hr i, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      push_cast
      congr 1
      ring
  · exact (Fintype.linearIndependent_iff.1 hli) c hc i

theorem latInt_translate : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), Per S.d ι δ₀ θ Ω → S.Ok → GlobalTheory.MomOne.Split S.d q → S.IsTheta e → S.AlgJets δ₀ e → S.PrimeTo q t → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup e → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup (opU S.Hm t e) := by
  intro q _ ι δ₀ θ Ω g S e t hPer hO hS hth halg ht hLe
  obtain ⟨hIsTh, -, hδ, hall, hΩ, hLaws, -⟩ := hPer
  have hp : S.d.Prime := hO.1
  have h7 : S.d % 16 = 7 := hO.2.1
  have hq : q.Prime := Fact.out
  let lam : Qbar →+* ℂ_[q] := (ι : ℂ →+* ℂ_[q]).comp (algebraMap Qbar ℂ)
  have hlam : ∀ z : Qbar, ι (z : ℂ) = lam z := fun z => rfl
  have hqd : ¬ q ∣ S.d := (GlobalTheory.MomOne.okArith S.d q ι hp h7 hS).2.2.2.2.2.2
  obtain ⟨x, a, hx, hb, ha⟩ := GlobalTheory.MomOne.exists_orthFrame q g S hq hO hqd
  have hNN := nnBasis_of_frame q S hO x a hx hb ha
  obtain ⟨N, hN⟩ := GlobalTheory.MomOne.Translates.moments_of_translates S.d q lam δ₀ θ ι Ω hp h7 hS hIsTh hδ hall hlam hΩ
    hLaws g S rfl hO g x hNN e hth halg
  have h0 : S.PrimeTo q 0 := ⟨1, one_pos, Nat.coprime_one_left q, by simp [S.La.zero_mem]⟩
  obtain ⟨μ0, hμ0, hM0⟩ := hN 0 h0
  obtain ⟨μt, hμt, hMt⟩ := hN t ht
  have hU0 : opU S.Hm 0 e = e := by funext z; simp [opU, hf]
  have b0 := _root_.GlobalTheory.MomN.norm_le_one_iff_latInt q ι lam δ₀ Ω g S g x 0 (opU S.Hm 0 e) μ0 hlam hδ hΩ hO hS hNN h0
    (GlobalTheory.MomOne.Translates.contDiff_opU S.Hm 0 hth.1) hM0
  have bt := _root_.GlobalTheory.MomN.norm_le_one_iff_latInt q ι lam δ₀ Ω g S g x t (opU S.Hm t e) μt hlam hδ hΩ hO hS hNN ht
    (GlobalTheory.MomOne.Translates.contDiff_opU S.Hm t hth.1) hMt
  rw [hU0] at b0
  have hN1 : N ≤ 1 := hμ0 ▸ b0.2 hLe
  exact bt.1 (hμt ▸ hN1)

end GlobalTheory.MomTrans
end
end

