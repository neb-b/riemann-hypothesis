module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLZerosEqPrimitiveCharacterZeros
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin


open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
theorem _root_.GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
      (LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0) ∧
        _root_.GlobalTheory.Lin.ord χ s = _root_.GlobalTheory.Lin.ord χ.primitiveCharacter s := by
  intro q _ χ s hs hχs
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set E : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z))
    with hE
  have hform : ∀ z, (χ.primitiveCharacter ≠ 1 ∨ z ≠ 1) →
      LFunction χ z = LFunction χ.primitiveCharacter z * E z := by
    intro z hz
    have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hz
    rwa [changeLevel_primitiveCharacter] at h
  have hprim : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with h | h
    · left
      intro h1
      apply h
      calc χ = changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
            (changeLevel_primitiveCharacter χ).symm
        _ = 1 := by rw [h1, map_one]
    · exact Or.inr h
  have hEne : E s ≠ 0 := by
    rw [hE]
    refine Finset.prod_ne_zero_iff.2 (fun p hp => ?_)
    have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
    have hlt : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
      calc _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (norm_le_one _ _) (by positivity)
        _ < 1 := by
            rw [one_mul]
            exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)
    intro h0
    rw [sub_eq_zero] at h0
    rw [← h0, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hEd : Differentiable ℂ E := by
    have h : Differentiable ℂ (∏ p ∈ q.primeFactors,
        fun z : ℂ => 1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z)) :=
      Differentiable.finsetProd (fun p hp => by
        have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
        fun_prop (disch := exact Or.inl hp0))
    rw [hE]
    convert h using 1
    ext z
    simp [Finset.prod_apply]
  have hEa : AnalyticAt ℂ E s := hEd.analyticAt s
  have hLa : AnalyticAt ℂ (LFunction χ.primitiveCharacter) s := by
    by_cases h1 : χ.primitiveCharacter = 1
    · have hs1 : s ≠ 1 := hprim.resolve_left (not_not.2 h1)
      exact DifferentiableOn.analyticAt (s := {z | z ≠ 1})
        (fun z hz => (differentiableAt_LFunction _ z (Or.inl hz)).differentiableWithinAt)
        (isOpen_ne.mem_nhds hs1)
    · exact (differentiable_LFunction h1).analyticAt s
  have hev : LFunction χ =ᶠ[𝓝 s] LFunction χ.primitiveCharacter * E := by
    rcases hprim with h1 | h1
    · exact Eventually.of_forall (fun z => hform z (Or.inl h1))
    · filter_upwards [isOpen_ne.mem_nhds h1] with z hz using hform z (Or.inr hz)
  refine ⟨?_, ?_⟩
  · rw [hform s hprim, mul_eq_zero]
    simp [hEne]
  · show (analyticOrderAt _ s).toNat = (analyticOrderAt _ s).toNat
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hLa hEa,
      analyticOrderAt_eq_zero.2 (Or.inr hEne), add_zero]

end GlobalTheory.Lin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqIdOfIsUnramifiedAt
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.UnramifiedDiscriminant

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private lemma isCMExt_conj_ne_id (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  obtain ⟨-, hE, -, hτ⟩ := h
  intro hσ
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  have hc := hE.isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx := hτ τ x
  rw [hσ, AlgHom.id_apply] at hx
  exact hx.symm

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private lemma isCMExt_mem_range_of_conj_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hprime : (Module.finrank F E).Prime := by rw [h.2.2.1]; exact Nat.prime_two
  haveI := Subalgebra.isSimpleOrder_of_finrank_prime F E hprime
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h1
  · have hmem : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
    rw [h0] at hmem
    exact Algebra.mem_bot.mp hmem
  · exfalso
    apply isCMExt_conj_ne_id h
    ext y
    have hmem : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := h1 ▸ Algebra.mem_top
    exact hmem


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (a : 𝓞 E) (ha : σ a = a) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) t = a := by
  obtain ⟨f, hf⟩ := isCMExt_mem_range_of_conj_fixed h ha
  have hint : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (B := E), hf]
    exact RingOfIntegers.isIntegral_coe a
  refine ⟨⟨f, hint⟩, ?_⟩
  ext
  exact hf

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private lemma isCMExt_conj_conj (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v) :
    ∃ (w : E) (t n : 𝓞 F), w + σ w = algebraMap F E (t : F) ∧ w * σ w = algebraMap F E (n : F) ∧
      t ^ 2 - 4 * n ∉ v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨P, -, hPp, hPv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  have hPne : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hPv, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
  haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 F) P := hv ⟨P, hPp, hPne⟩ ⟨hPv.symm⟩
  let σ' : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Function.Involutive.bijective (isCMExt_conj_conj h))
  haveI : IsGalois F E := by
    refine IsGalois.of_fixedField_eq_bot F E (eq_bot_iff.mpr fun x hx => ?_)
    exact IntermediateField.mem_bot.mpr (isCMExt_mem_range_of_conj_fixed h
      ((IntermediateField.mem_fixedField_iff _ _).mp hx σ' (Subgroup.mem_top _)))
  have hcard : Nat.card (P.inertia (E ≃ₐ[F] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal P,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, σ' • x - x ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hmem : σ' ∈ P.inertia (E ≃ₐ[F] E) := hcon
    haveI := (Nat.card_eq_one_iff_unique.mp hcard).1
    have h1 : σ' = 1 := congrArg Subtype.val (Subsingleton.elim (⟨σ', hmem⟩ : P.inertia _) 1)
    apply isCMExt_conj_ne_id h
    ext z
    exact DFunLike.congr_fun h1 z
  set y : 𝓞 E := σ' • x
  have hy : (y : E) = σ x := rfl
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x + y) (by
    show σ ((x : E) + σ x) = (x : E) + σ x
    rw [map_add (f := _), isCMExt_conj_conj h, add_comm])
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x * y) (by
    show σ ((x : E) * σ x) = (x : E) * σ x
    rw [map_mul, isCMExt_conj_conj h, mul_comm])
  refine ⟨x, t, n, ?_, ?_, ?_⟩
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) ht).symm
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) hn).symm
  · intro hmem
    have hP : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) ∈ P := by
      rw [← hPv] at hmem
      exact Ideal.mem_comap.mp hmem
    have heq : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (y - x) ^ 2 := by
      rw [map_sub, map_pow, map_mul, ht, hn, map_ofNat]
      ring
    rw [heq] at hP
    exact hx (hPp.mem_of_pow_mem 2 hP)

end GlobalTheory.UnramifiedDiscriminant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCompactOpenUnitsSubgroupContinuousSqrtStatement
section
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_open_units_subgroup_continuous_sqrt : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K], (2 : K) ≠ 0 → ∃ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s := by
  first | exact @GlobalTheory.QuadFibre.exists_isSqrtOn | exact GlobalTheory.QuadFibre.exists_isSqrtOn | (intros; apply GlobalTheory.QuadFibre.exists_isSqrtOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsOrthogonalComplementIsometryEmbeddingTra
section
noncomputable section

namespace GlobalTheory.PerpFrameTranslate

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

variable {P Q P' Q' : ℕ}

theorem act_mul (g h : UpqT P Q) (x : Sp P Q) : act (g * h) x = act g (act h x) := by
  unfold act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : Sp P Q) : act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem act_inv_act (g : UpqT P Q) (x : Sp P Q) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : UpqT P Q) (x : Sp P Q) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem herm_eq_dot (x y : Sp P Q) : herm x y = star y ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ x) := by
  rw [herm_eq_hform]
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]
  rfl

theorem herm_act (g : UpqT P Q) (x y : Sp P Q) : herm (act g x) (act g y) = herm x y := by
  have hu : (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := g.2
  rw [herm_eq_dot, herm_eq_dot, act, act, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu]

theorem herm_eq_sum (x y : Sp P Q) : herm x y = ∑ i, (sg i : ℂ) * (x i * star (y i)) := by
  simp [herm, sg, Fintype.sum_sum_type, sub_eq_add_neg]

def incl (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ :=
  Matrix.of fun i b => if i = e (some b) then 1 else 0

theorem incl_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (u : Sp P' Q') :
    (incl e *ᵥ u) (e none) = 0 := by
  simp [incl, Matrix.mulVec, dotProduct]

theorem incl_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (u : Sp P' Q')
    (b : Fin P' ⊕ Fin Q') : (incl e *ᵥ u) (e (some b)) = u b := by
  simp [incl, Matrix.mulVec, dotProduct]

theorem ext_coord (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) {x y : Sp P Q}
    (h0 : x (e none) = y (e none)) (h1 : ∀ b, x (e (some b)) = y (e (some b))) : x = y := by
  funext i
  obtain ⟨i, rfl⟩ := e.surjective i
  rcases i with _ | b
  · exact h0
  · exact h1 b

theorem isPerpEmb_base (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e)
    (j₀ : UpqT P' Q' → UpqT P Q) (hj : IsBlockEmb e j₀) :
    IsPerpEmb (baseVec e) (incl e) j₀ := by
  refine ⟨fun u v => ?_, fun y => ?_, fun g => ⟨?_, fun u => ?_⟩⟩
  · rw [herm_eq_sum, herm_eq_sum, ← e.sum_comp, Fintype.sum_option]
    simp only [incl_none, incl_some, he _, zero_mul, mul_zero, zero_add]
  · have h1 : herm y (baseVec e) = (sg (e none) : ℂ) * y (e none) := by
      rw [herm_eq_sum, ← e.sum_comp, Fintype.sum_option]
      simp [baseVec]
    have h2 : (sg (e none) : ℂ) ≠ 0 := by exact_mod_cast sg_ne_zero _
    rw [h1, mul_eq_zero, or_iff_right h2]
    constructor
    · intro h
      exact ⟨fun b => y (e (some b)), ext_coord e (by rw [incl_none, h]) fun b => incl_some e _ b⟩
    · rintro ⟨u, rfl⟩
      exact incl_none e u
  · obtain ⟨h1, -, h3, -⟩ := hj g
    refine ext_coord e ?_ fun b => ?_
    · simp [act, baseVec, h1]
    · simp [act, baseVec, h3]
  · obtain ⟨-, h2, -, h4⟩ := hj g
    have key : ∀ i, act (j₀ g) (incl e *ᵥ u) i =
        ∑ b, UpqT.mat (j₀ g) i (e (some b)) * u b := fun i => by
      change ∑ k, UpqT.mat (j₀ g) i k * (incl e *ᵥ u) k = _
      rw [← e.sum_comp, Fintype.sum_option]
      simp only [incl_none, incl_some, mul_zero, zero_add]
    refine ext_coord e ?_ fun b => ?_
    · rw [key, incl_none]; simp [h2]
    · rw [key, incl_some]; simp only [h4]; rfl

theorem isPerpEmb_translate {x₀ : Sp P Q} {A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    {j : UpqT P' Q' → UpqT P Q} (h : IsPerpEmb x₀ A j) (g₀ : UpqT P Q) :
    IsPerpEmb (act g₀ x₀) (UpqT.mat g₀ * A) (fun g => g₀ * j g * g₀⁻¹) := by
  have hA : ∀ u, (UpqT.mat g₀ * A) *ᵥ u = act g₀ (A *ᵥ u) := fun u => by
    rw [act, Matrix.mulVec_mulVec]
  refine ⟨fun u v => ?_, fun y => ?_, fun g => ⟨?_, fun u => ?_⟩⟩
  · rw [hA, hA, herm_act, h.1]
  · rw [← act_act_inv g₀ y, herm_act, h.2.1]
    refine exists_congr fun u => ?_
    rw [hA]
    constructor
    · intro hu; rw [hu]
    · intro hu; rw [← act_inv_act g₀ (A *ᵥ u), hu, act_inv_act]
  · simp only [act_mul, act_inv_act, (h.2.2 g).1]
  · simp only [hA, act_mul, act_inv_act, (h.2.2 g).2]

theorem exists_isPerpEmb : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    SignCompat e → ∀ j₀ : UpqT P' Q' → UpqT P Q, IsBlockEmb e j₀ → ∀ g₀ : UpqT P Q,
    ∃ A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ,
      IsPerpEmb (act g₀ (baseVec e)) A (fun g => g₀ * j₀ g * g₀⁻¹) :=
  fun _ _ _ _ e he j₀ hj g₀ => ⟨_, isPerpEmb_translate (isPerpEmb_base e he j₀ hj) g₀⟩

end GlobalTheory.PerpFrameTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTsumVonMangoldtDivRpowLeDiv
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin


open ArithmeticFunction.vonMangoldt (residueClass LFunctionResidueClassAux LFunctionResidueClassAux_real
  eqOn_LFunctionResidueClassAux residueClass_apply_zero continuousOn_LFunctionResidueClassAux
  abscissaOfAbsConv_residueClass_le_one) in
theorem exists_tsum_vonMangoldt_div_rpow_le_div :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      Summable (fun n : ℕ => Λ n / (n : ℝ) ^ (1 + s)) ∧
        ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + s) ≤ C / s := by
  have ha : IsUnit (1 : ZMod 1) := isUnit_one
  have hres : ∀ n : ℕ, ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n = Λ n := fun n =>
    Set.indicator_of_mem (s := {n : ℕ | (n : ZMod 1) = 1}) (Subsingleton.elim (α := ZMod 1) _ _) _
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n / (n : ℝ) ^ x =
        (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) x).re
          + ((Nat.totient 1 : ℕ) : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux_real ha hx,
      ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, LSeries.term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, ArithmeticFunction.vonMangoldt.residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have hc : ContinuousOn (fun x : ℝ ↦ (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) x).re)
      (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ)
      (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux (1 : ZMod 1))
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x (hx : x ∈ Set.Icc (1 : ℝ) 2) ↦ by
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
  obtain ⟨B, hB⟩ := bddAbove_def.mp <| IsCompact.bddAbove_image isCompact_Icc hc
  refine ⟨|B| + 1, by linarith [abs_nonneg B], fun s hs hs1 => ⟨?_, ?_⟩⟩
  · have : Summable fun n : ℕ => ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n / (n : ℝ) ^ (1 + s) :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one (1 : ZMod 1)).trans_lt <| by
          have : (1 : ℝ) < 1 + s := by linarith
          exact_mod_cast this
    simpa only [hres] using this
  · have h1 := H (x := 1 + s) (by linarith)
    have h2 := hB _ (Set.mem_image_of_mem
      (fun x : ℝ ↦ (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) x).re)
      (show 1 + s ∈ Set.Icc (1 : ℝ) 2 from ⟨by linarith, by linarith⟩))
    simp only [hres, Nat.totient_one, Nat.cast_one, inv_one, add_sub_cancel_left] at h1
    rw [h1, add_div]
    have h3 : |B| ≤ |B| / s := by
      rw [le_div_iff₀ hs]
      exact mul_le_of_le_one_right (abs_nonneg B) hs1
    have h4 := le_abs_self B
    linarith

end GlobalTheory.Lin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HaarDisintegrationAveragedFibreMeasuresStatement
section
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_disintegration_averagedFibreMeasures : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → (∀ c : K, ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ) → μ {x | q x = 0} = 0 → ∀ φ : V → ENNReal, Measurable φ → ∫⁻ x, φ x ∂μ = ∫⁻ t, ∫⁻ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t) ∂ν := by
  first | exact @GlobalTheory.QuadFibre.disintegration | exact GlobalTheory.QuadFibre.disintegration | (intros; apply GlobalTheory.QuadFibre.disintegration <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsRest
section
open IsLocalRing Matrix

namespace GlobalTheory.DualNumberLocal

theorem main : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], ∃ _ : IsLocalRing (DualNumber O), IsNoetherianRing (DualNumber O) ∧ IsAdicComplete (maximalIdeal (DualNumber O)) (DualNumber O) ∧ IsLocalHom (algebraMap O (DualNumber O)) ∧ Function.Surjective (fun x : O => residue (DualNumber O) (algebraMap O (DualNumber O) x)) ∧ ∀ z : DualNumber O, z ∈ maximalIdeal (DualNumber O) ↔ z.fst ∈ maximalIdeal O := by
  intro O _ _ _ _
  haveI hloc : IsLocalRing (DualNumber O) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
      exact isUnit_or_isUnit_one_sub_self _
  haveI : Module.Finite O (DualNumber O) := inferInstanceAs (Module.Finite O (O × O))
  have hmem : ∀ z : DualNumber O, z ∈ maximalIdeal (DualNumber O) ↔ z.fst ∈ maximalIdeal O := by
    intro z
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  refine ⟨hloc, IsNoetherianRing.of_finite O (DualNumber O),
    GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (DualNumber O), ?_, ?_, hmem⟩
  · refine ⟨fun a h => ?_⟩
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.isUnit_iff_isUnit_fst,
      TrivSqZeroExt.fst_inl] at h
    exact h
  · intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨z.fst, ?_⟩
    show residue (DualNumber O) (algebraMap O (DualNumber O) z.fst) = residue (DualNumber O) z
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmem,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, sub_self]
    exact Ideal.zero_mem _

end GlobalTheory.DualNumberLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegrableContinuousOnAveragedFibreIntegralStatement
section
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_continuousOn_averagedFibreIntegral : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → (∀ t : K, t ≠ 0 → Integrable φ (GlobalTheory.QuadFibre.fibOf μ ν q U s t)) ∧ ContinuousOn (fun t => ∫ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t)) {t : K | t ≠ 0} := by
  first | exact @GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | exact GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | (intros; apply GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsPadicIntMatrixChangeStatement
section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_padicInt_matrix_change : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ κ' : Type) [Fintype κ] [Fintype κ'] (v : κ → V) (w : κ' → V) (c : κ' → κ → ℂ) (a : κ' → κ → ℤ_[q]) (G : V → ℂ), (∀ i j, ι (c i j) = zc (a i j)) → (∀ i, w i = ∑ j, c i j • v j) → MomInt ι v G → MomInt ι w G := by
  first | exact @GlobalTheory.MomN.momInt_push | exact GlobalTheory.MomN.momInt_push | (intros; apply GlobalTheory.MomN.momInt_push <;> assumption)
end

