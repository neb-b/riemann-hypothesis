module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0092
public import ReciprocityTheory.GaloisValuations.Global
public import ReciprocityTheory.NeutralLocalFields.Bundle0001
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierEtaleKEqIntegralPartialFourier
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.FourKFub

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem secondCountableK [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

theorem stdChar_continuous (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : ψ y = ψ x * ψ (y - x) := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
  rw [this, hψ.1 (y - x) (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy), mul_one]

theorem psiK_continuous (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous (A.psiK ψ) :=
  (stdChar_continuous ψ hψ).comp (IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K))

theorem psiK_add (A : Et F E) (ψ : AddChar F ℂ) (x y : A.K) : A.psiK ψ (x + y) = A.psiK ψ x * A.psiK ψ y := by
  simp only [Et.psiK, map_add (f := _), AddChar.map_add_eq_mul]

theorem fourK_eq_fourB_tilde : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → ∀ b c : A.K, A.fourK μK ψ φ' (b, c) = fourB μK (A.kerK ψ) (fun c' => A.tilde μK ψ φ' c' c) b := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ b c
  haveI := secondCountableK A
  have hc := psiK_continuous A ψ hψ
  let f : A.K × A.K → ℂ := fun p => φ' p * A.psiK ψ (b * p.2 + p.1 * c)
  have hf : Integrable f (μK.prod μK) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hφ.1.continuous.mul (hc.comp (by fun_prop))
    · exact hφ.2.mul_right
  simp only [Et.fourK, fourB, Et.tilde, Et.kerK]
  rw [integral_integral_swap (f := fun b' c' => φ' (b', c') * A.psiK ψ (b * c' + b' * c)) hf]
  refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
  simp only
  rw [psiK_add, mul_comm b c', mul_comm b' c]
  ring

end GlobalTheory.FourKFub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierIndicatorHermitianIntegralLattice
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourB_indicator_intLattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  intro F E _ _ _ _ hU A ψ hψ r j B hB hO _hC μ hμ y
  haveI := hU.ultraE
  set Λ : Set A.L := {y : A.L | ∀ i, ‖j y i‖ ≤ 1} with hΛ
  have key : ∀ z : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * z)) = 1) ↔ ‖z‖ ≤ 1 :=
    ((_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).2.2.2
  have hmem_add : ∀ a x, a ∈ Λ → (a + x ∈ Λ ↔ x ∈ Λ) := by
    intro a x ha
    constructor
    · intro h i
      have e1 : j x i = j (a + x) i + -(j a i) := by simp
      rw [e1]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i) (by rw [norm_neg]; exact ha i))
    · intro h i
      rw [map_add (f := _), Pi.add_apply]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (h i))
  have hBadd : ∀ a x, B (a + x) y = B a y * B x y := by
    intro a x
    rw [hB, hB, hB, map_add (f := _), star_add, add_dotProduct, map_add (f := _), AddChar.map_add_eq_mul]
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  unfold fourB
  by_cases hy : y ∈ Λ
  · have h1 : ∀ x, Set.indicator Λ 1 x * B x y = Set.indicator Λ (fun _ => (1:ℂ)) x := by
      intro x
      by_cases hx : x ∈ Λ
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, hB]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [dotProduct, Pi.star_apply, map_sum]
        refine Finset.sum_induction _ (fun t => ψ t = 1) (fun u v hu hv => by
          rw [AddChar.map_add_eq_mul, hu, hv, one_mul]) (AddChar.map_zero_eq_one ψ) fun i _ => ?_
        exact (key (j y i)).2 (hy i) _ (by rw [hU.norm_star]; exact hx i)
      · simp [hx]
    simp_rw [h1]
    rw [integral_indicator_const _ hO.measurableSet, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    simp [Measure.real]
  · obtain ⟨i, hi⟩ : ∃ i, ¬ ‖j y i‖ ≤ 1 := by
      by_contra h
      push_neg at h
      exact hy h
    obtain ⟨e, he, hne⟩ : ∃ e : E, ‖e‖ ≤ 1 ∧ ψ (Algebra.trace F E (e * j y i)) ≠ 1 := by
      by_contra h
      push_neg at h
      exact hi ((key _).1 h)
    set a := j.symm (Pi.single i (star e)) with ha_def
    have hja : j a = Pi.single i (star e) := by simp [ha_def]
    have ha : a ∈ Λ := by
      intro k
      rw [hja]
      by_cases hk : k = i
      · subst hk; simp [hU.norm_star, he]
      · simp [Pi.single_eq_of_ne hk]
    have hst : star (Pi.single i (star e) : Fin r → E) = Pi.single i e := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    have hBa : B a y = ψ (Algebra.trace F E (e * j y i)) := by
      rw [hB, hja, hst, single_dotProduct]
    have hint : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = B a y * ∫ x, Set.indicator Λ 1 x * B x y ∂μ := by
      rw [← integral_const_mul]
      calc ∫ x, Set.indicator Λ 1 x * B x y ∂μ
          = ∫ x, Set.indicator Λ 1 (a + x) * B (a + x) y ∂μ :=
            (integral_add_left_eq_self (fun x => Set.indicator Λ 1 x * B x y) a).symm
        _ = ∫ x, B a y * (Set.indicator Λ 1 x * B x y) ∂μ := by
            congr 1; ext x
            rw [hBadd]
            by_cases hx : x ∈ Λ
            · rw [Set.indicator_of_mem ((hmem_add a x ha).2 hx), Set.indicator_of_mem hx, Pi.one_apply, Pi.one_apply]; ring
            · have hx' : a + x ∉ Λ := fun h => hx ((hmem_add a x ha).1 h)
              simp [hx, hx']
    have h0 : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
      have : (1 - B a y) * ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← hint, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by rw [hBa] at h; exact (sub_eq_zero.1 h).symm) hne
      · exact h
    rw [h0]
    simp [hy]

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSubOneBij
section
noncomputable section
namespace GlobalTheory.PhiGam.TrivCocycle
open scoped LaurentSeries PowerSeries

theorem frob_sub_one_bij {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] (R : RingPG k l) {n : ℕ} [NeZero n] :
    (∀ s : ZMod n → k⟦X⟧, ∃ m : ZMod n → k⟦X⟧,
      ∀ i, R.φ (vv k * (m (i - 1) : k⸨X⸩)) - vv k * (m i : k⸨X⸩) = vv k * (s i : k⸨X⸩)) ∧
    ∀ m : ZMod n → k⟦X⟧, (∀ i, R.φ (vv k * (m (i - 1) : k⸨X⸩)) = vv k * (m i : k⸨X⸩)) → m = 0 := by
  have inj : Function.Injective (fun a : k⟦X⟧ => (a : k⸨X⸩)) := HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  have hX := vv_eq_coe_X k
  have hv := vv_ne_zero k
  choose f hf using R.φ_int
  obtain ⟨u, hu⟩ := R.φ_v
  obtain ⟨l', hl'⟩ := Nat.exists_eq_add_of_le hl.out.two_le
  let T : (ZMod n → k⟦X⟧) →+ (ZMod n → k⟦X⟧) :=
    { toFun := fun m i => (u : k⟦X⟧) * PowerSeries.X ^ (l' + 1) * f (m (i - 1))
      map_zero' := by
        funext i
        apply inj
        simp [← hf]
      map_add' := by
        intro a b
        funext i
        apply inj
        simp only [Pi.add_apply, map_add (f := _), map_mul, ← hf, mul_add] }
  have hT : ∀ m i, T m i = (u : k⟦X⟧) * PowerSeries.X ^ (l' + 1) * f (m (i - 1)) := fun _ _ => rfl
  have hT' : ∀ m i, vv k * (T m i : k⸨X⸩) = R.φ (vv k * (m (i - 1) : k⸨X⸩)) := by
    intro m i
    rw [hT, map_mul R.φ, hu, hf, map_mul, map_mul, map_pow, ← hX, hl']
    ring
  haveI : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (ZMod n → k⟦X⟧) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _
  haveI : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (ZMod n → k⟦X⟧) := by
    rw [← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have key := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T
    (contracting_of_semi PowerSeries.X ((u : k⟦X⟧) * PowerSeries.X ^ (l' + 1)) T ?_ ?_)
  · constructor
    · intro s
      obtain ⟨m, hm⟩ := key.1 s
      refine ⟨m, fun i => ?_⟩
      rw [← hT', ← hm, Pi.sub_apply, map_sub, mul_sub]
    · intro m h
      refine key.2 m ?_
      funext i
      apply inj
      apply mul_left_cancel₀ hv
      rw [hT', h]
  · intro m
    funext i
    apply inj
    simp only [hT, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hf, ← hX, hu, hl']
    ring
  · intro m
    refine ⟨fun i => (u : k⟦X⟧) * PowerSeries.X ^ l' * f (m (i - 1)), ?_⟩
    funext i
    simp only [hT, Pi.smul_apply, smul_eq_mul]
    ring

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] (b g : ZMod n → k⟦X⟧), (∀ i, PowerSeries.constantCoeff (g i) = 0) → (∀ i, R.γ (b i : k⸨X⸩) - (b i : k⸨X⸩) = R.φ (g (i - 1) : k⸨X⸩) - (g i : k⸨X⸩)) → ∃ (m : ZMod n → k⟦X⟧) (c : ZMod n → k), ∀ i, (b i : k⸨X⸩) = R.φ (m (i - 1) : k⸨X⸩) - (m i : k⸨X⸩) + algebraMap k k⸨X⸩ (c i) ∧ (g i : k⸨X⸩) = R.γ (m i : k⸨X⸩) - (m i : k⸨X⸩) := by
  intro k _ l _ _ R n _ b g hg hc
  have hX := vv_eq_coe_X k
  obtain ⟨h1, h2⟩ := frob_sub_one_bij R (n := n)
  choose g' hg' using fun i => PowerSeries.X_dvd_iff.2 (hg i)
  let s : ZMod n → k⟦X⟧ := fun i => PowerSeries.mk fun j => PowerSeries.coeff (j + 1) (b i)
  have hb : ∀ i, (b i : k⸨X⸩) =
      vv k * (s i : k⸨X⸩) + algebraMap k k⸨X⸩ (PowerSeries.constantCoeff (b i)) := by
    intro i
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (b i), map_add (f := _), map_mul, ← vv_eq_coe_X]
    rfl
  obtain ⟨m, hm⟩ := h1 s
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  choose t ht using R.γ_int
  have hd : ∀ i, vv k * ((g' i - ((1 - κ * PowerSeries.X) * t (m i) - m i) : k⟦X⟧) : k⸨X⸩) =
      (g i : k⸨X⸩) - (R.γ (vv k * (m i : k⸨X⸩)) - vv k * (m i : k⸨X⸩)) := by
    intro i
    rw [hg' i, map_mul R.γ, hκ, ht]
    simp only [map_sub, map_mul, map_one, ← hX]
    ring
  have h0 := h2 (fun i => g' i - ((1 - κ * PowerSeries.X) * t (m i) - m i)) (by
    intro i
    rw [hd, hd, map_sub, map_sub, R.comm]
    have e := hc i
    rw [hb i, ← hm i, map_add R.γ, map_sub R.γ, AlgHom.commutes] at e
    linear_combination -e)
  refine ⟨fun i => PowerSeries.X * m i, fun i => PowerSeries.constantCoeff (b i), fun i => ?_⟩
  have e1 : ∀ j, ((PowerSeries.X * m j : k⟦X⟧) : k⸨X⸩) = vv k * (m j : k⸨X⸩) := fun j => by
    rw [map_mul, ← hX]
  simp only [e1]
  refine ⟨by rw [hm, ← hb], ?_⟩
  have e := hd i
  rw [congrFun h0 i, Pi.zero_apply, map_zero, mul_zero] at e
  exact sub_eq_zero.1 e.symm

end GlobalTheory.PhiGam.TrivCocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisAddHomVanishesComplexConjugation
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField

namespace GlobalTheory

theorem complexConjugation_mul_self {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (c : Ω ≃ₐ[E] Ω) (hc : IsComplexConjugation c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  ext x
  apply j.injective
  show j (c (c x)) = j x
  rw [hj, hj, Complex.conj_conj]

theorem not_isComplexConjugation_of_nrRealPlaces_eq_zero {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (hE : InfinitePlace.nrRealPlaces E = 0)
    (c : Ω ≃ₐ[E] Ω) : ¬ IsComplexConjugation c := by
  rintro ⟨j, hj⟩
  let φ : E →+* ℂ := j.comp (algebraMap E Ω)
  have hφ : ComplexEmbedding.IsReal φ := by
    ext x
    show starRingEnd ℂ (j (algebraMap E Ω x)) = j (algebraMap E Ω x)
    rw [← hj, AlgEquiv.commutes]
  have hw : (InfinitePlace.mk φ).IsReal := InfinitePlace.isReal_mk_iff.mpr hφ
  have : IsEmpty {w : InfinitePlace E // w.IsReal} := by
    classical
    rw [InfinitePlace.nrRealPlaces] at hE
    exact Fintype.card_eq_zero_iff.mp (by convert hE)
  exact this.false ⟨_, hw⟩

theorem addHom_complexConjugation_eq_zero : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    ∀ (c : Ω ≃ₐ[E] Ω), IsComplexConjugation c → z c = 0 := by
  intro E Ω _ _ _ _ l _ O _ _ hl M _ _ z hz c hc
  rcases hl with hl | hE
  · have h1 : z 1 = 0 := by
      have := hz 1 1
      simp only [mul_one] at this
      simpa using this
    have h2 : z c + z c = 0 := by
      rw [← hz, show (c * c : G E Ω) = 1 from complexConjugation_mul_self c hc, h1]
    have hu : IsUnit (2 : ℤ_[l]) := by
      have := (PadicInt.norm_natCast_eq_one_iff (p := l) (n := 2)).mpr
        ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl)
      rw [PadicInt.isUnit_iff]; exact_mod_cast this
    have hu' : IsUnit (2 : O) := by
      have := hu.map (algebraMap ℤ_[l] O)
      rwa [map_ofNat] at this
    have h3 : (2 : O) • z c = 0 := by rw [two_smul]; exact h2
    exact (hu'.smul_left_cancel).mp (h3.trans (smul_zero _).symm)
  · exact absurd hc (not_isComplexConjugation_of_nrRealPlaces_eq_zero hE c)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityLaurentShiftEqSumSen
section
noncomputable section
namespace GlobalTheory.PhiGam.Range
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem finite_map_trans {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P Q S : Submodule k U}
    (hSQ : S ≤ Q) (h1 : FiniteDimensional k (P.map Q.mkQ)) (h2 : FiniteDimensional k (Q.map S.mkQ)) :
    FiniteDimensional k (P.map S.mkQ) := by
  refine Module.Finite.iff_fg.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor hSQ) ?_ ?_)
  · rw [← Submodule.map_comp, Submodule.factor_comp_mk]
    exact Module.Finite.iff_fg.mp h1
  · have hle : P.map S.mkQ ⊓ LinearMap.ker (Submodule.factor hSQ) ≤ Q.map S.mkQ := by
      rintro _ ⟨⟨p, -, rfl⟩, hp⟩
      exact ⟨p, (Submodule.Quotient.mk_eq_zero Q).mp hp, rfl⟩
    exact Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hle)

theorem finite_quot_of_map {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P S : Submodule k U}
    (h : FiniteDimensional k (P.map S.mkQ)) : FiniteDimensional k (↥P ⧸ S.submoduleOf P) := by
  have hker : LinearMap.ker (S.mkQ ∘ₗ P.subtype) = S.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hr : LinearMap.range (S.mkQ ∘ₗ P.subtype) = P.map S.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  haveI : FiniteDimensional k (LinearMap.range (S.mkQ ∘ₗ P.subtype)) := by rw [hr]; exact h
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_self {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  set P' := P ⊓ ⨆ m : ℕ, P.comap ((T - algebraMap k (Module.End k U) x) ^ m)
  have h : P.submoduleOf P' = ⊤ := eq_top_iff.mpr fun y _ => y.2.1
  haveI : Subsingleton (↥P' ⧸ P.submoduleOf P') := Submodule.Quotient.subsingleton_iff.mpr h
  exact Module.finrank_zero_of_subsingleton

theorem finite_sh {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    {N : Submodule k⟦X⟧ V} (hN : IsLat N) (a : ℤ) (m : ℕ) :
    FiniteDimensional k (((sh a N).restrictScalars k).map ((sh (a + m) N).restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Submodule.mkQ_map_self]
    infer_instance
  | succ m ih =>
    have h := Window.finite_quot (hN.shift (a + m)).1
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h
    rw [Nat.cast_succ, ← add_assoc]
    exact finite_map_trans (fun y hy => Window.sh_succ_le _ _ hy) ih h

theorem qmult_sh_range : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ) (x : k), qmult g (sh a N) (sh (a + m) N) x = ∑ j ∈ Finset.range m, sen g N (x + (a + j : ℤ)) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m x
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Finset.sum_range_zero]
    exact gmult_self _ _ _
  | succ m ih =>
    have hf := finite_quot_of_map (finite_sh hN a (m + 1))
    rw [Finset.sum_range_succ, ← ih, ← _root_.GlobalTheory.PhiGam.SenShift.sen_sh R g hg N hN hC (a + m) x, sen, sh_sh_eq,
      add_comm (1 : ℤ)]
    rw [Nat.cast_succ, ← add_assoc] at hf ⊢
    exact _root_.GlobalTheory.PhiGam.GmultAdd.main (nab g) _ _ _ (fun y hy => Window.sh_succ_le _ _ hy)
      (fun y hy => Window.sh_add_le a m N hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy)
      (fun y hy => Window.nab_mem_sh R hg hC _ hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy) hf x

end GlobalTheory.PhiGam.Range
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportJacquetRallisOrbitalIntegrand
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.GLCompact

theorem Bm_act {k : Type} [CommRing k] {r : ℕ} (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by
  have hcol : ∀ j : ℕ, ((act g Y).1 ^ j) *ᵥ (act g Y).2.1 =
      (g : Matrix (Fin r) (Fin r) k) *ᵥ ((Y.1 ^ j) *ᵥ Y.2.1) := by
    intro j
    simp only [act]
    rw [Units.conj_pow, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  ext i j
  simp only [Bm, Matrix.of_apply, Matrix.mul_apply, hcol]
  simp [Matrix.mulVec, dotProduct]

theorem continuous_Bm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Bm Y) := by
  refine continuous_matrix fun i j => ?_
  simp only [Bm, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((continuous_fst.pow (j : ℕ)).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem continuous_Cm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Cm Y) := by
  refine continuous_matrix fun i j => ?_
  simp only [Cm, Matrix.of_apply]
  exact (continuous_apply j).comp
    (((continuous_fst.comp (continuous_snd.comp continuous_snd))).matrix_vecMul
      (continuous_fst.pow (i : ℕ)))

end GlobalTheory.JR.GLCompact

private theorem isCompact_unit_box (F : Type) [NontriviallyNormedField F] [ProperSpace F] (n : ℕ) :
    IsCompact {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} := by
  have hv : IsCompact (Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hm : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} := by
    have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} =
        Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1 := by
      ext A
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ i) j (Set.mem_univ j)⟩
    rw [h]
    exact isCompact_univ_pi fun _ => hv
  have h : {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} = {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ
        ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ
          ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ Metric.closedBall (0 : F) 1)) := by
    ext Z; simp
  rw [h]
  exact hm.prod (hv.prod (hv.prod (isCompact_closedBall 0 1)))

theorem GlobalTheory.JR.orbG_integrand_hasCompactSupport : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (n : ℕ) (Y : Gl n F), Delta (inv Y) ≠ 0 → HasCompactSupport (fun g : GL (Fin n) F => unitG n F (act g Y) * omega (act g Y)) := by
  intro F _ _ n Y hY
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨-, -, hCB, -, -⟩ := _root_.GlobalTheory.JR.normalForm_invariants F n
  have hdet : (Cm Y).det * (Bm Y).det ≠ 0 := by
    rw [← Matrix.det_mul, hCB Y]
    exact hY
  have hB : IsUnit (Bm Y).det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  have hC : IsUnit (Cm Y).det := isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hdet)

  have hψ : Continuous (fun Z : Gl n F =>
      (Bm Z * (Bm Y)⁻¹, MulOpposite.op ((Cm Y)⁻¹ * Cm Z))) :=
    (GlobalTheory.JR.GLCompact.continuous_Bm.matrix_mul continuous_const).prodMk
      (MulOpposite.continuous_op.comp (continuous_const.matrix_mul GlobalTheory.JR.GLCompact.continuous_Cm))
  have hK := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_unit_box F n).image hψ)
  refine HasCompactSupport.intro hK ?_
  intro g hg
  have hgY : act g Y ∉ {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧
      (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1} := by
    intro hmem
    refine hg ⟨act g Y, hmem, Prod.ext ?_ ?_⟩
    · show Bm (act g Y) * (Bm Y)⁻¹ = (g : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.GLCompact.Bm_act, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
    · show MulOpposite.op ((Cm Y)⁻¹ * Cm (act g Y)) =
        MulOpposite.op ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.TransferFactor.Cm_act, Matrix.nonsing_inv_mul_cancel_left _ _ hC]
  have h0 : unitG n F (act g Y) = 0 := Set.indicator_of_notMem hgY _
  simp [h0]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTestUnitIndicatorHermitianBlockStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTest_unitIndicatorHermitianBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist F] [LocallyCompactSpace F] [IsUltrametricDist E] [LocallyCompactSpace E] (r : ℕ), (∀ y : E, ‖star y‖ = ‖y‖) → IsTest (unitU r F E) := by
  first | exact @GlobalTheory.JR.isTest_unitU | exact GlobalTheory.JR.isTest_unitU | (intros; apply GlobalTheory.JR.isTest_unitU <;> assumption)
end

