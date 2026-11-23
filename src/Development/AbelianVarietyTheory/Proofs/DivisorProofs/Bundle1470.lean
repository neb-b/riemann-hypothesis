module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0015
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.Basics
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0615
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundPeriodicSchwartz
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem schA_line (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : ∀ g ∈ schA F κ, Continuous g ∧
    ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t :=
  _root_.GlobalTheory.ArchDecay.SchLine.schline F κ

theorem slice_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G) (π : G →+ (Fin N → ℝ))
    (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) (U : Set G)
    (hU : MeasurableSet {w | w - ι (π w) ∈ U})
    (hfin : ∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) (hper : ∀ w, ∀ u ∈ U, φ (w + u) = φ w) (y : G) :
    μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ :=
  GlobalTheory.T.lintegral_unitCube_translates_slabPeriodic_le μ ι π hι hπ hπι U hU hfin φ hφ hper y

theorem slab_top (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧
        ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ :=
  GlobalTheory.T.archimedeanSlab_open_unitCube_haar_pos_finite F κ

theorem slab_cover (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ c : ℕ, ∀ m : ℕ, 0 < m → slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧
      (∀ r ∈ R, arch F r = 0) ∧ ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m :=
  _root_.GlobalTheory.ArchDecay.slab_subset_and_cover F κ

end GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem wordD_cons (v : κ → mixedEmbedding.mixedSpace F) (w : List (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → AF F) → ℂ) : wordD F (v :: w) f = dD F v (wordD F w f) := rfl

theorem per_dD {m : ℕ} {f : (κ → AF F) → ℂ} (h : Per F m f) (v : κ → mixedEmbedding.mixedSpace F) :
    Per F m (dD F v f) := by
  intro x z hz
  unfold dD
  congr 1
  funext t
  rw [add_right_comm]
  exact h _ z hz

theorem per_wordD {m : ℕ} {f : (κ → AF F) → ℂ} (h : Per F m f) (w : List (κ → mixedEmbedding.mixedSpace F)) :
    Per F m (wordD F w f) := by
  induction w with
  | nil => exact h
  | cons v w ih => rw [wordD_cons]; exact per_dD ih v

theorem wordD_mem {f : (κ → AF F) → ℂ} (hf : f ∈ schA F κ) (w : List (κ → mixedEmbedding.mixedSpace F)) :
    wordD F w f ∈ schA F κ := by
  induction w with
  | nil => exact hf
  | cons v w ih => rw [wordD_cons]; exact _root_.GlobalTheory.ArchDecay.SchAStab.app_mem_schA F κ (Sum.inl v) _ ih

theorem archIn_single (j : Fin (dimA F κ)) (s : ℝ) :
    archIn F κ (Pi.single j s) = fun i => infAd F (s • ubasis F κ j i) := by
  funext i
  rw [archIn_apply]
  congr 1
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_eq_single j (fun c hc => by simp [Pi.single_apply, hc])]
  simp

theorem sobolev_schA {f : (κ → AF F) → ℂ} (hf : f ∈ schA F κ) (x : κ → AF F) (B : ℝ)
    (hB : ∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ dimA F κ → (∀ v ∈ w, ∃ j, v = ubasis F κ j) →
      ∫ t in cube (dimA F κ), ‖wordD F w f (x + archIn F κ t)‖ ^ 2 ≤ B) :
    ‖f x‖ ^ 2 ≤ 4 ^ dimA F κ * B := by
  let A : ℕ → Set ((κ → AF F) → ℂ) := fun p =>
    {u | ∃ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ p ∧ (∀ v ∈ w, ∃ j, v = ubasis F κ j) ∧
      u = wordD F w f}
  have hA : Monotone A := fun p q hpq u ⟨w, h1, h2, h3⟩ => ⟨w, h1.trans hpq, h2, h3⟩
  have key := GlobalTheory.ThetaGrowth.sobolev_iter (dimA F κ) 0 (fun j s => archIn F κ (Pi.single j s)) A B x
    (fun j => (continuous_archIn F κ).comp (continuous_single (A := fun _ : Fin (dimA F κ) => ℝ) j)) hA ?_ ?_ f ⟨[], by simp, by simp, rfl⟩
  · exact key
  · rintro p u ⟨w, h1, h2, rfl⟩
    have hmem := wordD_mem hf w
    refine ⟨(schA_line F κ _ hmem).1, fun j => ⟨wordD F (ubasis F κ j :: w) f,
      ⟨_, by simpa using h1, ?_, rfl⟩, fun y => ?_⟩⟩
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact ⟨j, rfl⟩
      · exact h2 v hv
    · have hd := (schA_line F κ _ hmem).2 (ubasis F κ j) y
      have hc : Continuous fun s : ℝ => y + fun i => infAd F (s • ubasis F κ j i) :=
        continuous_const.add (continuous_pi fun i => (continuous_infAd F).comp (continuous_id.smul continuous_const))
      have := GlobalTheory.sobolev_endpoint_one_variable ℂ (fun s => wordD F w f (y + fun i => infAd F (s • ubasis F κ j i)))
        (fun s => dD F (ubasis F κ j) (wordD F w f) (y + fun i => infAd F (s • ubasis F κ j i))) 1 one_pos
        (fun t _ => hd t)
        (((schA_line F κ _ (wordD_mem hf (ubasis F κ j :: w))).1.comp hc).continuousOn)
      simp only [archIn_single, wordD_cons]
      simpa [infAd_zero, ← Pi.zero_def] using this
  · rintro u ⟨w, h1, h2, rfl⟩
    have e : ∀ t : Fin (dimA F κ) → ℝ, ∑ j, archIn F κ (Pi.single j (t j)) = archIn F κ t := by
      intro t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.univ_sum_single]
    simp only [e]
    exact hB w (by simpa using h1) h2

end GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem cube_bound (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ φ : (κ → AF F) → ℂ, Continuous φ → Per F m φ → ∀ b : ℝ, 0 ≤ b →
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b → ∀ y,
        ∫ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨hopen, hμ1⟩ := slab_top F κ
  obtain ⟨h0, hfin1⟩ := hμ1 μ hμ
  obtain ⟨c, hc⟩ := slab_cover F κ
  have hQc : IsCompact (cube (dimA F κ)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hc₁ : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ≠ ⊤ := hfin1 _ hQc
  refine ⟨(μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal⁻¹, c, by positivity,
    fun m hm φ hφ hper b hb hL y => ?_⟩
  obtain ⟨hsub, R, hRc, hR0, hRcov⟩ := hc m hm
  have hcm : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ≤
      (m : ℝ≥0∞) ^ c * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by
    calc μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)
        ≤ ∑ r ∈ R, μ ((fun w => r + w) '' (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m)) := by
          refine (measure_mono ?_).trans (measure_biUnion_finset_le R _)
          rintro w ⟨hwQ, hw1⟩
          obtain ⟨r, hr, hwr⟩ := hRcov w hw1
          have hπr : archOut F κ r = 0 := by rw [archOut_apply, hR0 r hr, map_zero]
          refine Set.mem_biUnion hr ⟨w - r, ⟨?_, hwr⟩, by abel_nf⟩
          show archOut F κ (w - r) ∈ cube (dimA F κ)
          rw [map_sub, hπr, sub_zero]; exact hwQ
      _ = ∑ r ∈ R, μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Set.image_add_left, measure_preimage_add]
      _ = R.card * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr; exact_mod_cast hRc
  have hS := slice_le μ (archIn F κ) (archOut F κ) (continuous_archIn F κ) (continuous_archOut F κ)
    (archOut_archIn F κ) (perSet F κ m) (hopen m hm).measurableSet
    (fun A hA => ne_top_of_le_ne_top (hfin1 A hA) (measure_mono (Set.inter_subset_inter_right _ hsub)))
    (fun w => ‖φ w‖ₑ ^ 2) (hφ.measurable.enorm.pow_const 2)
    (fun w u hu => by simp only [hper w u hu]) y
  set X := ∫⁻ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ₑ ^ 2
  have h1 : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) * X ≤ (m : ℝ≥0∞) ^ c * ENNReal.ofReal b :=
    calc _ ≤ (m : ℝ≥0∞) ^ c * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) * X := by gcongr
      _ = (m : ℝ≥0∞) ^ c * (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) * X) := by ring
      _ ≤ _ := by gcongr; exact hS.trans hL
  have hI : ∫ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ ^ 2 = X.toReal := by
    have hcont : Continuous fun t => ‖φ (y + archIn F κ t)‖ ^ 2 :=
      (hφ.comp (continuous_const.add (continuous_archIn F κ))).norm.pow 2
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖φ (y + archIn F κ t)‖ ^ 2)
      (ae_of_all _ fun _ => by positivity) hcont.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h2 : (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal * X.toReal ≤ (m : ℝ) ^ c * b := by
    rw [← ENNReal.toReal_mul]
    refine (ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) h1).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hb]
  have hpos : 0 < (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal := ENNReal.toReal_pos h0.ne' hc₁
  rw [hI, mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hpos, mul_comm]
  exact h2

theorem sobolev_per : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ (P : ℕ) (C : ℝ) (c : ℕ), ∀ m : ℕ, 0 < m → ∀ f ∈ schA F κ,
      Per F m f → ∀ b : ℝ, 0 ≤ b → (∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ P → (∀ v ∈ w, ‖v‖ ≤ 1) →
        ∫⁻ x, ‖wordD F w f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b) → ∀ x, ‖f x‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  intro F _ _ κ _ μ hμ
  obtain ⟨C₀, c, -, hb⟩ := cube_bound μ hμ
  refine ⟨dimA F κ, 4 ^ dimA F κ * C₀, c, fun m hm f hf hper b hb0 hw x => ?_⟩
  have := sobolev_schA hf x (C₀ * m ^ c * b) fun w hl hv =>
    hb m hm _ (schA_line F κ _ (wordD_mem hf w)).1 (per_wordD hper w) b hb0
      (hw w hl fun v hv' => by obtain ⟨j, rfl⟩ := hv v hv'; rw [norm_ubasis]) x
  calc _ ≤ _ := this
    _ = _ := by ring

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeLabelIsCuspidalParabolicProductCharact
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.SqfreeCuspProd

theorem labO_irreducible {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
    (O : LabelMap K C) {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {σ : FDRep ℂ (GL κ K)} (hs : Simple σ) (hc : IsCuspidal K σ) : Irreducible (labO O σ) :=
  (O.lab_spec _ _ (Nat.succ_le_of_lt Fintype.card_pos) (Formalism.L2.PT.simple_transp _ hs)
    (Formalism.L2.PT.isCuspidal_transp _ hc)).2.1

theorem injective_of_squarefree {R : Type} [CommMonoid R] {s : ℕ} (F : Fin s → R)
    (hF : ∀ c, Irreducible (F c)) (hsq : Squarefree (∏ c, F c)) : Function.Injective F := by
  intro c c' h
  by_contra hne
  have hd : F c * F c' ∣ ∏ x, F x := by
    rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ c),
      ← Finset.mul_prod_erase (Finset.univ.erase c) F
        (Finset.mem_erase.2 ⟨fun h' => hne h'.symm, Finset.mem_univ c'⟩), ← mul_assoc]
    exact dvd_mul_right _ _
  rw [h] at hd
  exact (hF c').not_isUnit (hsq _ hd)

theorem character_eq_of_constituent {Γ : Type} [Group Γ] (τ : FDRep ℂ Γ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ Γ V) (hτ : Simple τ) (hρ : IsIrrRep ρ) (hc : IsConstituent τ ρ)
    (x : Γ) : τ.character x = LinearMap.trace ℂ V (ρ x) := by
  obtain ⟨φ, hφ, hne⟩ := hc
  have hirr := (PI.GreenHCLabel.simple_irreducible Γ τ).1 hτ
  have hker : LinearMap.ker φ = ⊥ := by
    rcases hirr.2 (LinearMap.ker φ) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have := congrArg (fun k => k v) (hφ g)
      simp only [LinearMap.comp_apply] at this
      rw [this, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hne
  have hran : LinearMap.range φ = ⊤ := by
    rcases hρ.2 (LinearMap.range φ) (fun g v hv => by
      obtain ⟨y, rfl⟩ := hv
      exact ⟨τ.ρ g y, by simpa using congrArg (fun k => k y) (hφ g)⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.1 h) hne
    · exact h
  let e : τ ≃ₗ[ℂ] V :=
    LinearEquiv.ofBijective φ ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩
  haveI : Module.Finite ℂ V := Module.Finite.equiv e
  have hconj : e.conj (τ.ρ x) = ρ x := by
    ext v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    show e (τ.ρ x (e.symm (e w))) = ρ x (e w)
    rw [e.symm_apply_apply]
    exact congrArg (fun k => k w) (hφ x)
  rw [FDRep.character, ← hconj, LinearMap.trace_conj']

theorem isCuspProdChar_of_squarefree : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K)
    (O : LabelMap K C) (r : ℕ) (τ : FDRep ℂ (GL (Fin r) K)) (f : K[X]), Simple τ → HasLabelO O τ f →
    Squarefree f → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => τ.character x) := by
  intro K _ _ _ C O r τ f hτ hL hsq
  obtain ⟨s, b, lam, hb, hl, hc, rfl⟩ := hL
  have hirrF : ∀ c, Irreducible (labO O (lam c)) := fun c => by
    obtain ⟨i, hi⟩ := hb c
    haveI : Nonempty {i // b i = c} := ⟨⟨i, hi⟩⟩
    exact labO_irreducible O (hl c).1 (hl c).2
  have hinj := injective_of_squarefree _ hirrF hsq
  have hirr := _root_.GlobalTheory.HcIrr.isIrrRep_hcRep K r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hl', hmono, htr⟩ := _root_.GlobalTheory.HCSort.exists_monotone_same_trace K r s b lam hb hl
  have hcp := _root_.GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep K r s b' lam' hb' hl' hmono
  have hfun : (fun x : GL (Fin r) K => τ.character x) =
      fun x => LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) := by
    funext x
    rw [htr x]
    exact character_eq_of_constituent τ _ hτ hirr hc x
  rw [hfun]
  exact hcp

end GlobalTheory.SqfreeCuspProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

def leftStab {G : Type} [Group G] (φ : G → ℂ) : Subgroup G where
  carrier := {γ | ∀ g, φ (γ * g) = φ g}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
  inv_mem' := fun {a} ha g => by rw [← ha (a⁻¹ * g), mul_inv_cancel_left]

theorem stdPar_eq_flag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S = GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ∧ GlobalTheory.StdPar.levi σ J X Y S = GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ∧ ∀ (K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ), GlobalTheory.StdPar.IsAutOn σ J X Y S K φ ↔ GlobalTheory.UAut.IsAutOn σ J (GlobalTheory.UAut.leftGrp σ J (X.submatrix id (Fin.castLE hs)) d) K φ := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  have hu := le_antisymm (_root_.GlobalTheory.TieStd.unip_le_unipFlag F E σ h n J hJ r X Y hW S s hs hS d hd) (_root_.GlobalTheory.TieStd.unipFlag_castLE_le_unip F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hl := le_antisymm (_root_.GlobalTheory.TieStd.levi_le_leviFlag F E σ h n J hJ r X Y hW S s hs hS d hd) (_root_.GlobalTheory.TieStd.leviFlag_le_levi F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hg := (_root_.GlobalTheory.LeviFlag.levi_decomposition F E σ h n J hJ s (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).2.2.1
  refine ⟨hu, hl, fun K φ => ⟨fun hφ => ⟨?_, hφ.level, hφ.cont, hφ.smooth, hφ.growth, GlobalTheory.UAut.kfin_iff.1 hφ.kfin, hφ.zfin⟩,
    fun hφ => ⟨fun u hu' g => hφ.left u ?_ g, fun γ hγ hγ' g => hφ.left γ ?_ g, hφ.level, hφ.cont, hφ.smooth, hφ.growth,
      GlobalTheory.UAut.kfin_iff.2 hφ.kfin, hφ.zfin⟩⟩⟩
  · rw [hg]
    have : GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ⊔ (ratPts σ J ⊓ GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d) ≤ leftStab φ :=
      sup_le (fun u hu' => hφ.leftN u (hu ▸ hu')) (fun γ hγ => hφ.leftM γ hγ.1 (hl ▸ hγ.2))
    exact fun γ hγ => this hγ
  · rw [hg]; exact Subgroup.mem_sup_left (hu ▸ hu')
  · rw [hg]; exact Subgroup.mem_sup_right ⟨hγ, hl ▸ hγ'⟩

end GlobalTheory.TieStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledTargetBoxProduct
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.DblThetaProd

theorem tsum_prod_mul {α β : Type} (f : α → ℂ) (g : β → ℂ) :
    ∑' p : α × β, f p.1 * g p.2 = (∑' a, f a) * (∑' b, g b) := by
  by_cases hf : Summable f
  · by_cases hg : Summable g
    · exact (tsum_mul_tsum_of_summable_norm ((summable_norm_iff (E := ℂ)).mpr hf)
        ((summable_norm_iff (E := ℂ)).mpr hg)).symm
    · rw [tsum_eq_zero_of_not_summable hg, mul_zero]
      by_cases h0 : ∀ a, f a = 0
      · simp [h0]
      · push_neg at h0
        obtain ⟨a, ha⟩ := h0
        refine tsum_eq_zero_of_not_summable fun hs => hg ?_
        have h1 : Summable fun b => f a * g b :=
          hs.comp_injective (i := fun b => (a, b)) (fun _ _ h => (Prod.ext_iff.mp h).2)
        simpa [ha] using h1.mul_left (f a)⁻¹
  · rw [tsum_eq_zero_of_not_summable hf, zero_mul]
    by_cases h0 : ∀ b, g b = 0
    · simp [h0]
    · push_neg at h0
      obtain ⟨b, hb⟩ := h0
      refine tsum_eq_zero_of_not_summable fun hs => hf ?_
      have h1 : Summable fun a => f a * g b :=
        hs.comp_injective (i := fun a => (a, b)) (fun _ _ h => (Prod.ext_iff.mp h).1)
      simpa [hb] using h1.mul_right (g b)⁻¹

theorem thetaTr_coDbl_boxFun : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro F E _ _ _ _ _ σ B hB hstd nS nT JT JA JB ξ hA κ _ co φ₁ _ φ₂ _
  have hψ : ∀ x, ‖B.ψ x‖ = 1 := hstd.1.2.1
  have hc : ∀ x, starRingEnd ℂ (B.ψ x) = B.ψ (-x) := fun x => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ x)]
  funext w
  rw [GlobalTheory.DblTargetDelta.deltaT_apply]
  have he : (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co).e w =
      (Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).1 (co.e (GlobalTheory.DblTargetDelta.botR w)).1,
        Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).2 (-(co.e (GlobalTheory.DblTargetDelta.botR w)).2)) := rfl
  have hn : co.e (-GlobalTheory.DblTargetDelta.botR w) = -(co.e (GlobalTheory.DblTargetDelta.botR w)) := map_neg _ _
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, he, hn]
  generalize co.e (GlobalTheory.DblTargetDelta.topR w) = p₁
  generalize co.e (GlobalTheory.DblTargetDelta.botR w) = p₂
  obtain ⟨x₁, y₁⟩ := p₁
  obtain ⟨x₂, y₂⟩ := p₂
  simp only

  set A : (κ → F) → (κ → AdeleRing (𝓞 F) F) := fun b i => algebraMap F (AdeleRing (𝓞 F) F) (b i) with hAdef
  have key : ∀ q : (κ → F) × (κ → F),
      schr B.ψ (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) (boxFun φ₁ φ₂)
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm q i)) =
        schr B.ψ (x₁, y₁) φ₁ (A q.1) *
          (B.ψ (-(A q.2 ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A q.2 + x₂)) := by
    rintro ⟨a, b⟩
    have h1 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inl = A a + x₁ := by
      funext i; simp [hAdef]
    have h2 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inr = A b + x₂ := by
      funext i; simp [hAdef]
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun]
    rw [h1, h2, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr, hAdef]
    ring
  rw [← (Equiv.sumArrowEquivProdArrow κ κ F).symm.tsum_eq]
  refine (tsum_congr key).trans ?_
  refine (tsum_prod_mul (fun a => schr B.ψ (x₁, y₁) φ₁ (A a))
    (fun b => B.ψ (-(A b ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A b + x₂))).trans ?_
  congr 1
  rw [Complex.conj_tsum]
  conv_rhs => rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun b => ?_
  have h3 : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.neg (κ → F)) b i)) = -A b := by
    funext i; simp [hAdef]
  simp only [GlobalTheory.WeilM.schr, h3, map_mul, Complex.conj_conj, hc,
    Prod.fst_neg, Prod.snd_neg]
  simp only [neg_dotProduct, dotProduct_neg, neg_neg, neg_add, sub_eq_add_neg, mul_neg]

end GlobalTheory.DblThetaProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulRelDimEqFinrankHarrisTaylorLattice
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem two_mul_relDim_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (K : Type) [Field K] (β : R →+* K) (o : Obj b N (spMap β)) (g : ℕ), SmoothOfRelativeDimension g o.A.hom → 2 * g = Module.finrank ℤ D.La := by
  intro p _ D R _ b N K _ β o g hg
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : ℓ.Coprime p := (Nat.coprime_primes hℓ (Fact.out)).2 (by omega)
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hℓK : (ℓ : K) ≠ 0 := by
    have h := (b.unit ℓ hcop).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hx : spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap β =
      spMap ((algebraMap K (AlgebraicClosure K)).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨I, -⟩ := o.geom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
    ((algebraMap K (AlgebraicClosure K)).comp β) hx
  have hc := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K (AlgebraicClosure K) o.A o.ab g hg ℓ hℓK
  let f : D.La →+ Additive (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ o.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev ℓ a)) fun a b => congrArg Additive.ofMul (I.add ℓ a b)
  have hk : f.ker = (nsmulAddMonoidHom ℓ : D.La →+ D.La).range := by
    ext a
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact (I.ker ℓ hℓ0 hcop a).trans ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩
  have h2 : Nat.card {x : ptOver K (AlgebraicClosure K) ⟶ o.A // x ^ ℓ = 1} = ℓ ^ Module.finrank ℤ D.La := by
    rw [← AddSubgroup.index_range_nsmul, ← hk, AddSubgroup.index_ker]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun u => I.onto ℓ hℓ0 hcop u)
  rw [hc] at h2
  exact Nat.pow_right_injective hℓ.two_le h2

end GlobalTheory.UPel.HT
end

