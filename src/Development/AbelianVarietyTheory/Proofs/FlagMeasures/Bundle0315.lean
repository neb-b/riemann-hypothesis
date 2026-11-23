module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SubsingletonIdxZero
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.IotaSigmaCompatibility

theorem iotaA_sigA : ∀ (D : D7) (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA →
    ∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a) := by
  intro D X ιA h a
  have he : ∀ x : X.B.I.E, X.ιE (X.B.I.cm.sig x) = Formalism.L2.Forms.sigD D (X.ιE x) := by
    intro x
    have h1 : X.B.I.cm.sig x = star x := rfl
    have h2 : Formalism.L2.Forms.sigD D (X.ιE x) = star (X.ιE x) := rfl
    rw [h1, h2, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]
  exact GlobalTheory.St.G.IotaConj.iota_sigR X.B.I.F X.B.I.E D.host.F D.host.E X.B.I.cm.sig
    (Formalism.L2.Forms.sigD D) X.ιE ιA he h.1 h.2 a

end GlobalTheory.St.G.IotaSigmaCompatibility
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundamentalDomainSmulIff
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

section General

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
  [BorelSpace K] (Γ : Subgroup K) (μ : Measure K)

theorem measure_eq [Countable Γ] [μ.IsMulLeftInvariant] {s t : Set K}
    (hs : IsFundamentalDomain Γ s μ) (ht : IsFundamentalDomain Γ t μ) : μ s = μ t := hs.measure_eq ht


theorem measure_ne_zero [Countable Γ] [μ.IsHaarMeasure] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) : μ s ≠ 0 :=
  hs.measure_ne_zero (NeZero.ne μ)

theorem measure_le_of_cover [Countable Γ] [μ.IsMulLeftInvariant] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) {C : Set K}
    (hcov : ∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) : μ s ≤ μ C := by
  open Pointwise in
  calc μ s ≤ μ (⋃ g : Γ, g • toMeasurable μ C ∩ s) := by
          refine measure_mono fun m hm => ?_
          obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov m
          refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_, hm⟩
          exact ⟨k, subset_toMeasurable μ C hk, rfl⟩
      _ ≤ ∑' g : Γ, μ (g • toMeasurable μ C ∩ s) := measure_iUnion_le _
      _ = μ (toMeasurable μ C) := (hs.measure_eq_tsum _).symm
      _ = μ C := measure_toMeasurable C


omit [TopologicalSpace K] [IsTopologicalGroup K] [BorelSpace K] in
theorem isFundamentalDomain_smul_iff {c : NNReal} (hc : c ≠ 0) (s : Set K) :
    IsFundamentalDomain Γ s (c • μ) ↔ IsFundamentalDomain Γ s μ := by
  have hc' : (c : ENNReal) ≠ 0 := by exact_mod_cast hc
  constructor
  · intro h
    refine h.mono fun t ht => ?_
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at ht
    exact ht.resolve_left hc'
  · intro h
    refine h.mono fun t ht => ?_
    rw [smul_apply, ht, smul_zero]

private theorem exists_measurableSet_unique_smul_mem_of_discrete {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (Γ : Subgroup G) {V : Set G} (hV : IsOpen V) (h1 : (1 : G) ∈ V)
    (hΓV : ∀ γ ∈ Γ, γ ∈ V → γ = 1) :
    ∃ s : Set G, MeasurableSet s ∧ ∀ x : G, ∃! g : Γ, g • x ∈ s := by
  classical

  obtain ⟨U, hUo, hU1, hUV⟩ := exists_open_nhds_one_split (hV.mem_nhds h1)
  let W : Set G := U ∩ (fun u => u⁻¹) ⁻¹' U
  have hWo : IsOpen W := hUo.inter (hUo.preimage continuous_inv)
  have hW1 : (1 : G) ∈ W := ⟨hU1, by simp only [Set.mem_preimage, inv_one]; exact hU1⟩
  have hWW : ∀ a ∈ W, ∀ b ∈ W, a * b⁻¹ ∈ V := fun a ha b hb => hUV a ha.1 b⁻¹ hb.2

  let A : G → Set G := fun g => (fun x => x * g⁻¹) ⁻¹' W
  have hAo : ∀ g, IsOpen (A g) := fun g => hWo.preimage (continuous_mul_const _)
  have hcov : ⋃ g, A g = Set.univ := Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.2 ⟨x, by simp only [A, Set.mem_preimage, mul_inv_cancel]; exact hW1⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable A hAo
  have hmemT : ∀ x, ∃ g ∈ T, x ∈ A g := fun x => by
    have hx : x ∈ ⋃ g ∈ T, A g := by rw [hTU, hcov]; exact Set.mem_univ x
    obtain ⟨g, hg, hx'⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨g, hg, hx'⟩
  have hTne : T.Nonempty := by
    obtain ⟨g, hg, -⟩ := hmemT 1
    exact ⟨g, hg⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let B : ℕ → Set G := fun i => A (f i)
  have hBo : ∀ i, IsOpen (B i) := fun i => hAo _
  have hBcov : ∀ x, ∃ i, x ∈ B i := by
    intro x
    obtain ⟨g, hgT, hx⟩ := hmemT x
    rw [hf] at hgT
    obtain ⟨i, rfl⟩ := hgT
    exact ⟨i, hx⟩

  have hinj : ∀ i y (δ : Γ), y ∈ B i → δ • y ∈ B i → δ = 1 := by
    intro i y δ hy hδy
    have hm := hWW (δ • y * (f i)⁻¹) hδy (y * (f i)⁻¹) hy
    have he : δ • y * (f i)⁻¹ * (y * (f i)⁻¹)⁻¹ = (δ : G) := by
      simp only [Subgroup.smul_def, smul_eq_mul]
      group
    rw [he] at hm
    exact Subtype.ext (hΓV _ δ.2 hm)

  let E : ℕ → Set G := fun j => ⋃ γ : Γ, (fun x => γ • x) ⁻¹' B j
  have hEo : ∀ j, IsOpen (E j) := fun j => isOpen_iUnion fun γ => (hBo j).preimage
    (by simpa only [Subgroup.smul_def, smul_eq_mul] using continuous_const_mul (γ : G))
  have hE : ∀ j y, y ∈ E j ↔ ∃ δ : Γ, δ • y ∈ B j := fun j y => by
    simp only [E, Set.mem_iUnion, Set.mem_preimage]

  let s : Set G := ⋃ i, (B i \ ⋃ (j : ℕ) (_ : j < i), E j)
  have hs : ∀ y, y ∈ s ↔ ∃ i, y ∈ B i ∧ ∀ j < i, ∀ δ : Γ, δ • y ∉ B j := by
    intro y
    simp only [s, Set.mem_iUnion, Set.mem_sdiff, not_exists]
    constructor
    · rintro ⟨i, hi, hn⟩
      exact ⟨i, hi, fun j hj δ hδ => hn j hj ((hE j y).2 ⟨δ, hδ⟩)⟩
    · rintro ⟨i, hi, hn⟩
      refine ⟨i, hi, fun j hj hy => ?_⟩
      obtain ⟨δ, hδ⟩ := (hE j y).1 hy
      exact hn j hj δ hδ
  refine ⟨s, MeasurableSet.iUnion fun i => (hBo i).measurableSet.diff
    (isOpen_iUnion fun j => isOpen_iUnion fun _ => hEo j).measurableSet, fun x => ?_⟩
  have hP : ∃ i, ∃ γ : Γ, γ • x ∈ B i := by
    obtain ⟨i, hi⟩ := hBcov x
    exact ⟨i, 1, by simpa only [one_smul] using hi⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec hP
  refine ⟨γ, (hs _).2 ⟨_, hγ, fun j hj δ hδ => Nat.find_min hP hj ⟨δ * γ, by rwa [mul_smul]⟩⟩,
    fun γ' hγ' => ?_⟩
  obtain ⟨i', hi', hmin'⟩ := (hs _).1 hγ'
  have hle : Nat.find hP ≤ i' := Nat.find_min' hP ⟨γ', hi'⟩
  have hge : i' ≤ Nat.find hP := by
    by_contra hlt
    exact hmin' _ (not_le.1 hlt) (γ * γ'⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hγ)
  rw [le_antisymm hge hle] at hi'
  have h1' := hinj _ (γ • x) (γ' * γ⁻¹) hγ (by rw [mul_smul, inv_smul_smul]; exact hi')
  exact mul_inv_eq_one.1 h1'

end General

theorem countable_and_exists_domain (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) :
    IsTopologicalGroup K ∧ BorelSpace K ∧
    Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) ∧
    ∀ μ : Measure K, ∃ 𝓕 : Set K,
      IsFundamentalDomain (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) 𝓕 μ := by
  obtain ⟨hc, hd, -⟩ := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ n J
  change Countable (HFinIn (AF F) σ J) at hc
  change DiscreteTopology (HFinIn (AF F) σ J) at hd

  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set (HFinIn (AF F) σ J)))
  have ht1 : (1 : HA (AF F) σ J) ∈ t := by
    have h : (1 : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := by rw [hteq]; exact Set.mem_singleton _
    exact h
  have htone : ∀ h ∈ HFinIn (AF F) σ J, h ∈ t → h = 1 := by
    intro h hh hht
    have h' : (⟨h, hh⟩ : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := hht
    rw [hteq] at h'
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 h')
  have hcnt : Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) := by
    refine Function.Injective.countable
      (f := fun x => (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_subgroupOf.1 x.2⟩ :
        HFinIn (AF F) σ J)) ?_
    intro x y hxy
    have h2 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h2)

  have : SecondCountableTopology (AF F) := AdelicUnitaryTop.secondCountable_adele F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' (AF F) (AF F ⊗[F] E)
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hφ
  have : SecondCountableTopology (AF F ⊗[F] E) :=
    Topology.IsOpenQuotientMap.secondCountableTopology hq
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) (AF F ⊗[F] E)) :=
    Units.isInducing_embedProduct.secondCountableTopology
  have : SecondCountableTopology (HA (AF F) σ J) :=
    (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : HR (AF F) σ J → GL (Fin n) (AF F ⊗[F] E))).secondCountableTopology
  have : IsTopologicalGroup (HA (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  refine ⟨inferInstance, inferInstance, hcnt, fun μ => ?_⟩
  have hK1 : IsTopologicalGroup K := inferInstance
  have hK2 : SecondCountableTopology K := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hK3 : OpensMeasurableSpace K := inferInstance
  obtain ⟨s, hs, hex⟩ := @exists_measurableSet_unique_smul_mem_of_discrete K _ _ hK1 hK2 _ hK3
    (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    ((Subtype.val : K → HA (AF F) σ J) ⁻¹' t) (ht.preimage continuous_subtype_val) ht1
    (fun γ hγ hγV => Subtype.ext (htone _ (Subgroup.mem_subgroupOf.1 hγ) hγV))
  exact ⟨s, IsFundamentalDomain.mk' hs.nullMeasurableSet hex⟩

theorem domains_and_covolume (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) (Γ : Subgroup K)
    (hΓ : Γ = Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    (cov : Measure K → ℝ)
    (hcov : ∀ ν : Measure K, (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν) →
      ∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν ∧ cov ν = (ν 𝓕).toReal)
    (μ : Measure K) (hμ : μ.IsHaarMeasure) :
    (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ) ∧
    (∀ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ → cov μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧
      ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧
    ∀ c : NNReal, c ≠ 0 → cov (c • μ) = (c : ℝ) * cov μ := by
  obtain ⟨hTG, hB, hcnt, hex⟩ := countable_and_exists_domain F E σ n J K
  rw [← hΓ] at hcnt hex
  have := hμ
  refine ⟨hex μ, fun 𝓕 h𝓕 => ?_, fun c hc => ?_⟩
  · obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    refine ⟨?_, @GlobalTheory.ClosedSubgroupCovol.measure_ne_zero _ _ _ hTG _ hB Γ μ hcnt _ _ h𝓕,
      fun C _ hC => @GlobalTheory.ClosedSubgroupCovol.measure_le_of_cover _ _ _ hTG _ hB Γ μ hcnt _ _ h𝓕 _ hC⟩
    rw [hcv, @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓕' h𝓕]
  · obtain ⟨𝓕, h𝓕⟩ := hex μ
    obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    obtain ⟨𝓖, h𝓖, hcv'⟩ := hcov (c • μ) ⟨𝓕, (isFundamentalDomain_smul_iff Γ μ hc 𝓕).2 h𝓕⟩
    have h𝓖μ := (isFundamentalDomain_smul_iff Γ μ hc 𝓖).1 h𝓖
    rw [hcv', hcv, smul_apply,
      @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓖μ h𝓕', ENNReal.smul_def,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

end GlobalTheory.ClosedSubgroupCovol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHCParamOfSetup
section
open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom.LowVec

variable {k r : ℕ}

abbrev flagSpan (k r : ℕ) (a : Fin (r + 1)) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} => bvec (eI k r b.1))

theorem mem_flagSpan {a : Fin (r + 1)} {y : Fin (2 * r + k + 1) → ℂ} :
    y ∈ flagSpan k r a ↔ ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0 := by
  constructor
  · intro hy i hi
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have := b.2
      exact Pi.single_eq_of_ne (fun e => by rw [e] at hi; simp only [eI] at hi; omega) _
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  · intro hy
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : a.val ≤ i.val
    · rw [hy i hi, Pi.single_zero]; exact Submodule.zero_mem _
    · have ha := a.isLt
      have : (Pi.single i (y i) : Fin (2 * r + k + 1) → ℂ) = y i • bvec (eI k r ⟨i.val, by omega⟩) := by
        rw [bvec, ← Pi.single_smul, smul_eq_mul, mul_one]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨i.val, by omega⟩, by simpa using hi⟩, rfl⟩)

theorem mulVec_sub {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z)
    (a : Fin (r + 1)) {y : Fin (2 * r + k + 1) → ℂ} (hy : y ∈ flagSpan k r a) :
    ∃ y' ∈ flagSpan k r a, s *ᵥ (fvec k r z a - y) = fvec k r z a - y' := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hc := ((WeylGroupFacts.nset_iff m).1 hm).2
  have ha := a.isLt
  have h1 : fvec k r z a - m *ᵥ (fvec k r z a - y) ∈ flagSpan k r a := by
    refine mem_flagSpan.2 fun i hi => ?_
    have : (m *ᵥ (fvec k r z a - y)) i = ((1 : Mat k r) *ᵥ (fvec k r z a - y)) i := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j.val ≤ r + k ∧ (j.val ≤ i.val ∨ r ≤ i.val)
      · rw [hc i j hj.1 hj.2, Matrix.one_apply]
      · have e1 : y j = 0 := mem_flagSpan.1 hy j (by omega)
        have e2 : fvec k r z a j = 0 := by
          unfold fvec
          split_ifs with h'
          · exact Pi.single_eq_of_ne (fun e => by rw [e] at hj; simp only [eI] at hj; omega) _
          · exact hz j (by omega)
        simp [e1, e2]
    rw [Pi.sub_apply, this, Matrix.one_mulVec, Pi.sub_apply, mem_flagSpan.1 hy i hi]; ring
  have h2 : ∀ x ∈ flagSpan k r a, h *ᵥ x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact (hh.2.1 b.1).1
    | zero => exact Matrix.mulVec_zero _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  have h3 : h *ᵥ fvec k r z a = fvec k r z a := by
    unfold fvec
    split_ifs with h'
    · exact (hh.2.1 _).1
    · exact hh.2.2
  refine ⟨_, h1, ?_⟩
  rw [← Matrix.mulVec_mulVec]
  have := h2 _ h1
  rw [Matrix.mulVec_sub, h3] at this
  rw [sub_sub_cancel]
  exact sub_right_injective this

theorem lA_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z) (g : Mat k r)
    (a : Fin (r + 1)) : lA k r z (s * g) a = lA k r z g a := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hu : IsUnit s.det := by
    obtain ⟨h, hh, m, hm, rfl⟩ := hs
    rw [Matrix.det_mul]
    exact ((uHGroup _ _ hH).2.2 h hh.1).1.mul ((uHGroup _ _ hH).2.2 m hm.1).1
  unfold lA
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz ((sGroup k r z hz).2.2 s hs) a hy
    exact ⟨y', hy', by rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, e]⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz hs a hy
    refine ⟨y', hy', ?_⟩
    rw [← e, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem eucl_unitary {N : ℕ} {t : Matrix (Fin N) (Fin N) ℂ} (ht : t ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (v : Fin N → ℂ) : eucl (t *ᵥ v) = eucl v := by
  have e : ∀ v : Fin N → ℂ, ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = star v ⬝ᵥ v := fun v => by
    simp [dotProduct, Complex.normSq_eq_conj_mul_self]
  have h1 : tᴴ * t = 1 := Matrix.mem_unitaryGroup_iff'.1 ht
  unfold eucl
  congr 1
  apply Complex.ofReal_injective
  rw [e, e, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]

theorem lA_right (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) {t : Mat k r}
    (ht : t ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) (a : Fin (r + 1)) :
    lA k r z (g * t) a = lA k r z g a := by
  have h1 : t⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 ht)]
    exact Unitary.star_mem ht
  unfold lA
  simp only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, eucl_unitary h1]

end GlobalTheory.Mom.LowVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaSlabSqueezedBetweenBalls
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_arith_lower {a s r t η u v : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s < t) (hrt : r < t)
    (ht : t ≤ 1 / 24) (hη : 0 < η) (htη : 3 * t * (1 + η) ≤ η) (h1 : a < 1 / 8 + s + a * s)
    (h2 : a ≤ u + a ^ 2) (h3 : u ≤ v + a * s) (h4 : v ≤ r) : a ≤ (1 + η) * r := by

  have hs24 : s < 1 / 24 := lt_of_lt_of_le hst ht
  have hA : a < 4 / 23 := by nlinarith [mul_nonneg ha (sub_nonneg.2 hs24.le)]
  have hkey : a * (1 - s - a) ≤ r := by nlinarith
  have hgap : 433 / 552 ≤ 1 - s - a := by linarith
  have hat : a * (433 / 552) < t := by nlinarith [mul_le_mul_of_nonneg_left hgap ha]
  have hsum : (1 + η) * (s + a) ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_left (show s + a ≤ 3 * t by linarith) (show (0 : ℝ) ≤ 1 + η by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 1 + η by linarith),
    mul_le_mul_of_nonneg_left hsum ha]

theorem slab_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η →
    ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 < r → r < t → ∀ k : Formalism.REAL.UJ ε, nrm (uMat k - 1) < t →
      crd E (uMat k - 1) = 0 → ∀ l ∈ S, (l ∈ hsBall ε (r / (1 + η)) → l * k ∈ slab ε E ρ r) ∧
        (l * k ∈ slab ε E ρ r → l ∈ hsBall ε ((1 + η) * r)) := by
  intro n ε S d E hS ρ η hρ hρ8 hη
  have hON := hS.isON
  obtain ⟨t, ht0, ht24, htη, htρ⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 24 ∧ 3 * t * (1 + η) ≤ η ∧ 3 * t ≤ ρ := by
    refine ⟨min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)),
      lt_min (by norm_num) (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_, ?_⟩
    · have h : min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)) * (3 * (1 + η)) ≤ η :=
        (le_div_iff₀ (by positivity)).1 (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have h := le_trans (min_le_right (1 / 24 : ℝ) _) (min_le_right (η / (3 * (1 + η))) (ρ / 3))
      linarith
  refine ⟨t, ht0, ?_⟩
  intro r hr hrt k hk hk0 l hl

  have hmul : uMat (l * k) - 1 = (uMat l - 1) + (uMat k - 1) + (uMat l - 1) * (uMat k - 1) := by
    have e : uMat (l * k) = uMat l * uMat k := rfl
    rw [e]; noncomm_ring
  have hXY : nrm ((uMat l - 1) * (uMat k - 1)) ≤ nrm (uMat l - 1) * nrm (uMat k - 1) := nrm_mul_le _ _
  have ha0 := nrm_nonneg (uMat l - 1)
  have hs0 := nrm_nonneg (uMat k - 1)
  have htle : t ≤ η := by nlinarith
  constructor
  · intro hlB
    have ha : nrm (uMat l - 1) ≤ r / (1 + η) := hlB
    have ha' : nrm (uMat l - 1) * (1 + η) ≤ r := (le_div_iff₀ (by positivity)).1 ha
    refine ⟨?_, ?_⟩
    ·
      have h1 : nrm (uMat (l * k) - 1) ≤ nrm (uMat l - 1) + nrm (uMat k - 1) + nrm ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul]
        exact le_trans (nrm_add_le _ _) (by linarith [nrm_add_le (uMat l - 1) (uMat k - 1)])
      have hat : nrm (uMat l - 1) < t := by nlinarith
      have hprod : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ t * t := by
        exact mul_le_mul hat.le hk.le hs0 ht0.le
      nlinarith
    ·
      have hc : crd E (uMat (l * k) - 1) = crd E (uMat l - 1) + crd E ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul, crd_add, crd_add, hk0, add_zero]
      have hlen : len (crd E (uMat (l * k) - 1)) ≤ nrm (uMat l - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
        rw [hc]
        exact le_trans (len_add_le _ _)
          (add_le_add (len_crd_le hON _) (le_trans (len_crd_le hON _) hXY))
      have hsη : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ nrm (uMat l - 1) * η :=
        mul_le_mul_of_nonneg_left (by linarith) ha0
      show len (crd E (uMat (l * k) - 1)) ≤ r
      nlinarith
  · intro hslab
    obtain ⟨hZ, hv⟩ := hslab
    show nrm (uMat l - 1) ≤ (1 + η) * r
    have hX : uMat l - 1 = (uMat (l * k) - 1) - (uMat k - 1) - (uMat l - 1) * (uMat k - 1) := by
      rw [hmul]; abel

    have h1 : nrm (uMat l - 1) < 1 / 8 + nrm (uMat k - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have e := nrm_sub_le ((uMat (l * k) - 1) - (uMat k - 1)) ((uMat l - 1) * (uMat k - 1))
      have e' := nrm_sub_le (uMat (l * k) - 1) (uMat k - 1)
      rw [← hX] at e
      linarith

    have h2 : nrm (uMat l - 1) ≤ len (crd E (uMat l - 1)) + nrm (uMat l - 1) ^ 2 := by
      have hp := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε S d E hS l hl
      have e := nrm_add_le (cmb E (crd E (uMat l - 1))) (uMat l - 1 - cmb E (crd E (uMat l - 1)))
      rw [add_sub_cancel, nrm_cmb hON] at e
      linarith

    have h3 : len (crd E (uMat l - 1)) ≤ len (crd E (uMat (l * k) - 1)) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have hc : crd E (uMat l - 1) = crd E (uMat (l * k) - 1) + -crd E ((uMat l - 1) * (uMat k - 1)) := by
        conv_lhs => rw [hX]
        rw [crd_sub, crd_sub, hk0, sub_zero, sub_eq_add_neg]
      rw [hc]
      refine le_trans (len_add_le _ _) (add_le_add le_rfl ?_)
      rw [len_neg]
      exact le_trans (len_crd_le hON _) hXY
    exact slab_arith_lower ha0 hs0 hk hrt ht24 hη htη (by linarith) h2 h3 hv

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTraceStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedFiniteCharacter_inverse_exp_trace : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.St.G.psiEf_transport_rat | exact GlobalTheory.St.G.psiEf_transport_rat | (intros; apply GlobalTheory.St.G.psiEf_transport_rat <;> assumption)
end

