module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HarrisTaylorCardKilledByIdealEqAbsNormPow
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0038
public import GroundTheory.GlobalFields.LocalAtPlace
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCount
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummable

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.NonarchimedeanSelfdualMeasurePi
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiV

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

def ball (v : HeightOneSpectrum (𝓞 F)) (m : ℤ) : AddSubgroup (Fv F v) where
  carrier := {x | Valued.v x ≤ WithZero.exp m}
  add_mem' := by
    intro a b ha hb
    change Valued.v (a + b) ≤ _
    exact (Valuation.map_add _ a b).trans (max_le ha hb)
  zero_mem' := by
    change Valued.v (0 : Fv F v) ≤ _
    simp
  neg_mem' := by
    intro a ha
    change Valued.v (-a) ≤ _
    rw [Valuation.map_neg]
    exact ha

theorem mem_ball (m : ℤ) (x : Fv F v) : x ∈ ball v m ↔ Valued.v x ≤ WithZero.exp m := Iff.rfl

theorem ball_isCompact (m : ℤ) : IsCompact (ball v m : Set (Fv F v)) :=
  (GlobalTheory.LatticeDensity.ball_compact_open v m).1

theorem ball_isOpen (m : ℤ) : IsOpen (ball v m : Set (Fv F v)) :=
  (GlobalTheory.LatticeDensity.ball_compact_open v m).2

theorem ball_le {a b : ℤ} (hab : a ≤ b) : (ball v a : Set (Fv F v)) ⊆ ball v b :=
  fun _ hx => le_trans ((mem_ball _ _).1 hx) (WithZero.exp_le_exp.2 hab)

theorem exists_mem_ball (x : Fv F v) : ∃ m, x ∈ ball v m := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [mem_ball, hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), by rw [mem_ball, WithZero.exp_log hx]⟩

theorem exists_ball_of_isCompact (K : Set (Fv F v)) (hK : IsCompact K) :
    ∃ m, K ⊆ ball v m := by
  refine hK.elim_directed_cover (fun m : ℤ => (ball v m : Set (Fv F v))) ball_isOpen ?_
    (Monotone.directed_le fun a b hab => ball_le hab)
  intro x _
  obtain ⟨m, hm⟩ := exists_mem_ball x
  exact Set.mem_iUnion.2 ⟨m, hm⟩

theorem exists_ball_subset (U : Set (Fv F v)) (hU : U ∈ 𝓝 (0 : Fv F v)) :
    ∃ m, (ball v m : Set (Fv F v)) ⊆ U := by
  obtain ⟨W, hWU, hWo, h0⟩ := mem_nhds_iff.1 hU
  have hcl : ∀ m : ℤ, IsClosed (ball v m : Set (Fv F v)) := fun m => (ball_isCompact m).isClosed
  obtain ⟨n, hn⟩ := (ball_isCompact (v := v) 0).elim_directed_cover
    (fun n : ℕ => W ∪ (ball v (-(n : ℤ)) : Set (Fv F v))ᶜ)
    (fun n => hWo.union (hcl _).isOpen_compl)
    (by
      intro x _
      by_cases hx : x = 0
      · exact Set.mem_iUnion.2 ⟨0, Or.inl (hx ▸ h0)⟩
      · have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
        refine Set.mem_iUnion.2 ⟨(WithZero.log (Valued.v x)).natAbs + 1, Or.inr fun hm => ?_⟩
        have h1 := WithZero.exp_le_exp.1 ((WithZero.exp_log hv).le.trans ((mem_ball _ _).1 hm))
        omega)
    (Monotone.directed_le fun a b hab x hx => hx.imp id fun h hm =>
      h (ball_le (by omega) hm))
  refine ⟨min (-(n : ℤ)) 0, fun x hx => hWU ?_⟩
  rcases hn (ball_le (min_le_right _ _) hx) with h | h
  · exact h
  · exact absurd (ball_le (min_le_left _ _) hx) h

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y := by
  classical
  have h : pairA F 0 (singleV F v (x + y)) =
      pairA F 0 (singleV F v x) + pairA F 0 (singleV F v y) := by
    have : singleV F v (x + y) = singleV F v x + singleV F v y :=
      RestrictedProduct.single_add _ v x y
    rw [this]
    exact Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiV, h, AddChar.map_add_eq_mul]
  rfl

theorem ann_isCompact {χ : Fv F v → ℂ} (hc : Continuous χ) (h0 : χ 0 = 1) {y : Fv F v} (hy : χ y ≠ 1)
    (L : AddSubgroup (Fv F v)) (hLo : IsOpen (L : Set (Fv F v))) :
    IsCompact {t | ∀ s ∈ L, χ (s * t) = 1} := by
  obtain ⟨m, hm⟩ := exists_ball_subset (L : Set (Fv F v)) (hLo.mem_nhds L.zero_mem)
  have hy0 : y ≠ 0 := fun h => hy (h ▸ h0)
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  have hcl : IsClosed {t | ∀ s ∈ L, χ (s * t) = 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const
  refine (ball_isCompact (v := v) (WithZero.log (Valued.v y) - m)).of_isClosed_subset hcl ?_
  intro t ht
  by_contra hne
  have hlt : WithZero.exp (WithZero.log (Valued.v y) - m) < Valued.v t :=
    not_le.1 fun h => hne h
  have hvt : Valued.v t ≠ 0 := (lt_of_le_of_lt zero_le' hlt).ne'
  have ht0 : t ≠ 0 := (Valuation.ne_zero_iff _).1 hvt
  have hmem : y / t ∈ ball v m := by
    rw [mem_ball, map_div₀, div_le_iff₀ (zero_lt_iff.2 hvt)]
    calc Valued.v y = WithZero.exp m * WithZero.exp (WithZero.log (Valued.v y) - m) := by
          rw [← WithZero.exp_add, add_sub_cancel, WithZero.exp_log hv]
      _ ≤ WithZero.exp m * Valued.v t := mul_le_mul_right hlt.le _
  have := ht _ (hm hmem)
  rw [div_mul_cancel₀ _ ht0] at this
  exact hy this

theorem selfDual_pi_v : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiV F ψ v (x ⬝ᵥ y)) := by
  intro F _ _ ψ hψ v k hk ι _
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hc, y, hy⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have ha := psiV_add ψ v
  have hn : ∀ x, ‖psiV F ψ v x‖ = 1 := fun x => hψ.2.1 _
  refine GlobalTheory.CompanionTheory.SW.FourierPi.selfDual_pi (Fv F v) (psiV F ψ v) hc ha hn k hk
    ⟨ball v 0, ball_isCompact 0, ball_isOpen 0⟩
    (fun L _ hLo => ann_isCompact hc (GlobalTheory.CompanionTheory.SW.FourierPi.psi_zero ha hn) hy L hLo)
    (fun K hK => ?_) (fun U hU => ?_) ι
  · obtain ⟨m, hm⟩ := exists_ball_of_isCompact K hK
    exact ⟨ball v m, ball_isCompact m, ball_isOpen m, hm⟩
  · obtain ⟨m, hm⟩ := exists_ball_subset U hU
    exact ⟨ball v m, ball_isCompact m, ball_isOpen m, hm⟩

end GlobalTheory.CompanionTheory.SW.PiV
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurable
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PureMeas

theorem borelSpace_ainf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := by
  obtain ⟨⟨-, scA, -⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have scA' : SecondCountableTopology (Ainf F × Af F) := scA
  haveI : SecondCountableTopology (Ainf F) :=
    (isEmbedding_prodMkLeft (0 : Af F)).secondCountableTopology
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.AdeleTop.t2Space_infiniteAdeleRing_of_numberField_field F
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)).2.2.2.2.2.2.2.1 n M

theorem borelSpace_af (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.2.1 n M

theorem borelSpace_fv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M

theorem measurable_pureL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → Measurable (pureL b S φinf φ) := by
  intro F E _ _ _ _ _ σ hσ d b n M S φinf φ hφinf hφ
  obtain ⟨hpi, hpf, hpv, -, hint, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  haveI := borelSpace_af F E σ hσ n M
  haveI := borelSpace_ainf F E σ hσ n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => borelSpace_fv F E σ hσ n M v
  refine Measurable.indicator ?_ (hint S).measurableSet
  refine (hφinf.comp hpi.measurable).mul ?_
  refine Finset.measurable_prod _ fun v _ => ?_
  exact (hφ v).comp ((hpv v).comp hpf).measurable

end GlobalTheory.CompanionTheory.SW.PureMeas
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarProperties
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Vol

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_integers : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

theorem isOpen_integers : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

def mulAdd (c : Fv F v) (hc : c ≠ 0) : Fv F v ≃+ Fv F v where
  toFun t := c * t
  invFun t := c⁻¹ * t
  left_inv t := by simp [hc]
  right_inv t := by simp [hc]
  map_add' := mul_add c

theorem mulAdd_continuous (c : Fv F v) (hc : c ≠ 0) : Continuous (mulAdd v c hc) :=
  continuous_const.mul continuous_id

theorem mulAdd_symm_continuous (c : Fv F v) (hc : c ≠ 0) : Continuous (mulAdd v c hc).symm :=
  continuous_const.mul continuous_id

theorem vol_lt_one (lam : Measure (Fv F v)) (h : IsStdV v lam) :
    lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have key := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v (Fv F v) lam Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm {0}
  have e1 : {x : Fv F v | ∃ y : Unit → v.adicCompletionIntegers F,
      (∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm x i = (y i : Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈
        ({0} : Set (Unit → IsLocalRing.ResidueField (v.adicCompletionIntegers F)))} =
      {t | Valued.v t < 1} := by
    ext x
    simp only [Set.mem_setOf_eq, ← GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff v x]
    constructor
    · rintro ⟨y, h1, h2⟩
      exact ⟨y (), h1 (), congrFun h2 ()⟩
    · rintro ⟨y, h1, h2⟩
      exact ⟨fun _ => y, fun _ => h1, funext fun _ => h2⟩
  have e2 : {x : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm x i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext x
    simp
  rw [e1, e2, GroundTheory.Global.natCard_residueField_adicCompletionIntegers v] at key
  simp only [Fintype.card_unit, pow_one, Set.ncard_singleton, Nat.cast_one, one_mul] at key
  have hO : lam.real (v.adicCompletionIntegers F : Set (Fv F v)) = 1 := by
    simp [measureReal_def, h.2]
  rw [hO] at key
  have hfin : lam {t | Valued.v t < 1} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := lam (v.adicCompletionIntegers F : Set (Fv F v))) ?_ ?_
    · rw [h.2]; exact ENNReal.one_ne_top
    · exact measure_mono fun t (ht : Valued.v t < 1) => (le_of_lt ht : Valued.v t ≤ 1)
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  refine (ENNReal.toReal_eq_one_iff _).1 ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  exact key

theorem absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast this

theorem map_unit (lam : Measure (Fv F v)) (h : IsStdV v lam) (u : Fv F v) (hu : Valued.v u = 1) :
    lam.map (fun t => u * t) = lam := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨_, hl, hs, ht, _⟩ := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  refine (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open (Fv F v) (Fv F v) lam lam (mulAdd v u hu0) (mulAdd_continuous v u hu0)
    (mulAdd_symm_continuous v u hu0)).2 (v.adicCompletionIntegers F : Set (Fv F v))
    (v.adicCompletionIntegers F : Set (Fv F v)) (isCompact_integers v) (isOpen_integers v)
    ⟨0, zero_mem _⟩ (fun x => ?_) rfl
  change Valued.v (u * x) ≤ 1 ↔ Valued.v x ≤ 1
  rw [map_mul, hu, one_mul]

theorem exp_neg_one_mul_lt_one_iff (a : WithZero (Multiplicative ℤ)) :
    WithZero.exp (-1 : ℤ) * a < 1 ↔ a ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [← WithZero.exp_log ha, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp,
      WithZero.exp_le_exp]
    omega

theorem map_unif (lam : Measure (Fv F v)) (h : IsStdV v lam) (π : Fv F v)
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨_, hl, hs, ht, _⟩ := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have hq0 := absNorm_ne_zero v
  have hqt : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  haveI : ((Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul lam hq0 hqt
  refine (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open (Fv F v) (Fv F v) lam ((Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam)
    (mulAdd v π hπ0) (mulAdd_continuous v π hπ0) (mulAdd_symm_continuous v π hπ0)).2
    (v.adicCompletionIntegers F : Set (Fv F v)) {t | Valued.v t < 1} (isCompact_integers v)
    (isOpen_integers v) ⟨0, zero_mem _⟩ (fun x => ?_) ?_
  · change Valued.v (π * x) < 1 ↔ Valued.v x ≤ 1
    rw [map_mul, hπ]
    exact exp_neg_one_mul_lt_one_iff _
  · rw [h.2, Measure.smul_apply, vol_lt_one v lam h, smul_eq_mul, ENNReal.mul_inv_cancel hq0 hqt]

theorem volumes_in_completion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ∧ (∀ π : Fv F v, Valued.v π = WithZero.exp (-1 : ℤ) → lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam) ∧ (∀ u : Fv F v, Valued.v u = 1 → lam.map (fun t => u * t) = lam) ∧ Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal :=
  fun F _ _ v lam h => ⟨vol_lt_one v lam h, map_unif v lam h, map_unit v lam h,
    GroundTheory.Global.natCard_residueField_adicCompletionIntegers v⟩

end GlobalTheory.CompanionTheory.SW.Vol
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormula
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral

theorem thTerm_zero {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ)
    (τ : InfinitePlace F → ℂ) : thTerm B ρ P gf gi φ τ 0 = φ 0 := by
  have h1 : (fun j : ι => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
    funext j; simp
  have h2 : ∀ w, (fun j : ι => ρ w ((0 : ι → F) j)) = 0 := by
    intro w; funext j; simp
  simp only [thTerm, gauss, h1, h2, mulVec_zero]
  simp

theorem main : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → Integrable (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) Pr ∧ ENNReal.ofReal ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ ≤ ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr := by
  intro F _ _ _ _ lf _ _ ψ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC φ τ hφ hτ
  haveI : IsProbabilityMeasure Pr := hC.1
  have horth : ∀ ω, IsOrth B ρ (gf ω) (gi ω) := hC.2.2.2.1
  haveI : Countable F :=
    Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  obtain ⟨w0, -, h0⟩ := Finset.exists_min_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  obtain ⟨w1, -, h1⟩ := Finset.exists_max_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  have ht : 0 < (τ w0).im := hτ w0
  have hs : 0 < (τ w1).im := hτ w1
  obtain ⟨C, hCb⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound F ι M B ρ P hQ Ω Pr gf gi hC φ hφ
    ((τ w0).im / (τ w1).im) (τ w0).im (div_pos ht hs) ht
  obtain ⟨hmeas, hbd⟩ := hCb τ (fun w => h0 w (Finset.mem_univ w)) (by
    intro v w
    have hw : (τ w).im ≤ (τ w1).im := h1 w (Finset.mem_univ w)
    have hv : (τ w0).im ≤ (τ v).im := h0 v (Finset.mem_univ v)
    calc (τ w0).im / (τ w1).im * (τ w).im ≤ (τ w0).im / (τ w1).im * (τ w1).im :=
          mul_le_mul_of_nonneg_left hw (div_pos ht hs).le
      _ = (τ w0).im := div_mul_cancel₀ _ hs.ne'
      _ ≤ (τ v).im := hv)
  have hwt : 0 < wt M τ := Finset.prod_pos fun w _ => pow_pos (Real.sqrt_pos.2 (hτ w)) M
  have hfin : (∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr) ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top (by simpa using hwt)] at hbd
    simp at hbd
  have hsum : ∀ ω, Summable (thTerm B ρ P (gf ω) (gi ω) φ τ) := fun ω =>
    ((_root_.GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero F ι M B ρ P hQ (gf ω) (gi ω) (horth ω) τ hτ).1 φ hφ).of_norm
  have hsub : ∀ ω, Summable fun x : {x : ι → F // x ≠ 0} => thTerm B ρ P (gf ω) (gi ω) φ τ x.1 :=
    fun ω => (hsum ω).subtype _
  set g : Ω → ℂ := fun ω => ∑' x : {x : ι → F // x ≠ 0}, thTerm B ρ P (gf ω) (gi ω) φ τ x.1 with hg
  have hsplit : ∀ ω, theta B ρ P (gf ω) (gi ω) φ τ = φ 0 + g ω := by
    intro ω
    have h := (hsum ω).tsum_subtype_add_tsum_subtype_compl ({0} : Set (ι → F))
    rw [tsum_singleton, thTerm_zero] at h
    exact h.symm
  have hgm : Measurable g :=
    measurable_of_tendsto_metrizable' Filter.atTop
      (f := fun (s : Finset {x : ι → F // x ≠ 0}) ω => ∑ x ∈ s, thTerm B ρ P (gf ω) (gi ω) φ τ x.1)
      (fun s => Finset.measurable_sum _ fun x _ => hmeas x.1)
      (tendsto_pi_nhds.2 fun ω => (hsub ω).hasSum)
  have hgI : ∫⁻ ω, ‖g ω‖ₑ ∂Pr ≤
      ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr :=
    lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
  have hgint : Integrable g Pr := ⟨hgm.aestronglyMeasurable, lt_of_le_of_lt hgI hfin.lt_top⟩
  have hth : (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) = fun ω => φ 0 + g ω := funext hsplit
  refine ⟨by rw [hth]; exact (integrable_const _).add hgint, ?_⟩
  have hint : (∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0 = ∫ ω, g ω ∂Pr := by
    rw [hth, integral_add (integrable_const _) hgint]
    simp
  rw [hint, ofReal_norm_eq_enorm]
  exact (enorm_integral_le_lintegral_enorm g).trans hgI

end GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral
end

