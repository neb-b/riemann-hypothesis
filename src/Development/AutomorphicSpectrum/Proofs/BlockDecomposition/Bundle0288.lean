module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotient
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0283
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProductIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.NonPrime

variable {X : Scheme.{0}}

lemma secs_mk {E F : X.Modules} (f : F ⟶ E) [Mono f] (V : X.Opens) :
    secs (Subobject.mk f) V = Set.range (f.app V) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).hom.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).inv.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.underlyingIso_arrow]

lemma smul_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} (a : Γ(X, V)) {x : Γ(E, V)}
    (hx : x ∈ secs S V) : a • x ∈ secs S V := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨a • t, Scheme.Modules.Hom.app_smul S.arrow a t⟩

lemma add_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} {x y : Γ(E, V)}
    (hx : x ∈ secs S V) (hy : y ∈ secs S V) : x + y ∈ secs S V := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨s + t, map_add _ s t⟩

def idealSub (J : X.IdealSheafData) (E : X.Modules) : Subobject E :=
  Subobject.mk (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))

lemma secs_idealSub (J : X.IdealSheafData) (E : X.Modules) [E.IsQuasicoherent]
    (U : X.affineOpens) :
    secs (idealSub J E) U = ((J.ideal U • ⊤ : Submodule Γ(X, U) Γ(E, U)) : Set Γ(E, U)) := by
  rw [idealSub, secs_mk, ← (GlobalTheory.surjective_and_ker_unit_subschemeι J E U).2,
    ← GlobalTheory.QCoh.range_kernel_ι_app]
  rfl

lemma isQuasicoherent_idealSub (J : X.IdealSheafData) {E : X.Modules} (hE : IsCoherent E) :
    ((idealSub J E : Subobject E) : X.Modules).IsQuasicoherent := by
  have := hE.1
  have := (isCoherent_pullback J.subschemeι hE).1
  have h₀ : ((𝟭 X.Modules).obj E).IsQuasicoherent := hE.1
  have h₁ : ((Scheme.Modules.pullback J.subschemeι ⋙ Scheme.Modules.pushforward J.subschemeι).obj
      E).IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom J.subschemeι
    ((Scheme.Modules.pullback J.subschemeι).obj E)
  have hk : (kernel ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app
      E)).IsQuasicoherent := GlobalTheory.QCoh.isQuasicoherent_kernel _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι
      ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))).symm hk

lemma propSupp_mono {A : Type} [CommRing A] [X.Over (Spec (.of A))] {E : X.Modules}
    {S S' : Subobject E} (h : S ≤ S') (hS : PropSupp A S) : PropSupp A S' := by
  obtain ⟨T, hT, hsupp⟩ := hS
  refine ⟨T, hT, ?_⟩
  have w : S.arrow ≫ cokernel.π S'.arrow = 0 := by
    rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero]
  have : Epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) :=
    epi_of_epi_fac (cokernel.π_desc S.arrow (cokernel.π S'.arrow) w)
  exact Scheme.Modules.SupportedIn.of_epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) hsupp

theorem statement_of_mul_mem : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J J₁ J₂ : X.IdealSheafData),
    (∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U) →
    Statement I J₁ → Statement I J₂ → Statement I J := by
  intro A _ _ I X _ _ _ _ J J₁ J₂ hm h₁ h₂ E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hEq : E.IsQuasicoherent := hE.1
  set K : Subobject E := idealSub J₁ E with hKdef
  have hKq : (K : X.Modules).IsQuasicoherent := isQuasicoherent_idealSub J₁ hE
  have hS1 : ClosedSys I E (fun e => S e ⊔ K) :=
    { qcoh := fun e => (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh e) hKq).1
      pow_le := fun e => (hS.pow_le e).trans le_sup_left
      succ := fun e => by
        conv_lhs => rw [hS.succ e]
        exact sup_right_comm _ _ _ }
  have hK1 : ∀ e, Killed J₁ (S e ⊔ K) := by
    intro e U a ha x
    have hax : a • x ∈ secs K U := by
      rw [hKdef, secs_idealSub]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    exact (_root_.GlobalTheory.CompanionTheory.GE.le_iff_secs_subset K (S e ⊔ K)).1 le_sup_right U hax
  obtain ⟨B, hBq, hBP, hB⟩ := h₁ E hE _ hS1 hK1 (propSupp_mono le_sup_left hP)
  have hDq : ((B ⊔ K : Subobject E) : X.Modules).IsQuasicoherent :=
    (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ hBq hKq).1
  have hDP : PropSupp A (B ⊔ K) := propSupp_mono le_sup_left hBP
  have hc : ∀ e, S (e + 0) ≤ (B ⊔ K) ⊔ powSub I E (e + 1) := fun e =>
    (le_sup_left : S e ≤ S e ⊔ K).trans ((hB e).symm.le.trans (sup_le_sup_right le_sup_left _))
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP (B ⊔ K) hDq 0 hc
  have hkill : ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J₂.ideal U →
      ∀ x ∈ secs (B ⊔ K) U, a • x ∈ secs (S n) U := by
    intro n U a ha x hx
    have hle : B ⊔ K ≤ S n ⊔ K :=
      sup_le ((le_sup_left : B ≤ B ⊔ powSub I E (n + 1)).trans (hB n).le) le_sup_right
    have hx' := (_root_.GlobalTheory.CompanionTheory.GE.le_iff_secs_subset _ _).1 hle U hx
    rw [(GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh n) hKq).2 U U.2] at hx'
    obtain ⟨s, hs, k, hk, rfl⟩ := hx'
    rw [smul_add]
    refine add_mem_secs _ (smul_mem_secs _ a hs) ?_
    rw [hKdef, secs_idealSub] at hk
    refine Submodule.smul_induction_on (p := fun k => a • k ∈ secs (S n) U) hk
      (fun b hb y _ => ?_) (fun y z hy hz => ?_)
    · rw [smul_smul, mul_comm]
      exact hK n U _ (hm U b a hb ha) y
    · rw [smul_add]
      exact add_mem_secs _ hy hz
  exact halg (h₂ _ (GlobalTheory.T.coherent_subobject_coherent hE _ hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J₂ _ S c' hkill) hP') hDP

end GlobalTheory.CompanionTheory.GE.NonPrime
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarQK
section
open MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotVan

def HaarQK : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (Q K : Subgroup G) (_ : IsClosed (Q : Set G)) (_ : IsCompact (K : Set G))
  (_ : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
  (νQ : Measure Q) [νQ.IsHaarMeasure] (κ : Measure K) [κ.IsHaarMeasure],
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    μ = c • (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G))

private theorem cancel_lemma_0 {a b s : ℝ≥0∞} (h0 : s ≠ 0) (ht : s ≠ ⊤) (h : s * a = s * b) : a = b := by
  calc a = s⁻¹ * (s * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ = s⁻¹ * (s * b) := by rw [h]
    _ = b := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

private theorem mapMulRight_lemma {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H]
    (ν : Measure H) [ν.IsMulLeftInvariant] (a : H) : (ν.map (· * a)).IsMulLeftInvariant := by
  constructor
  intro b
  rw [Measure.map_map (measurable_const_mul b) (measurable_mul_const a)]
  rw [show ((b * ·) ∘ (· * a)) = ((· * a) ∘ (b * ·)) from funext fun x => (mul_assoc b x a).symm]
  rw [← Measure.map_map (measurable_mul_const a) (measurable_const_mul b), MeasureTheory.map_mul_left_eq_self]

private theorem cptRight_lemma_2 {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (κ : Measure H) [κ.IsHaarMeasure] : κ.IsMulRightInvariant := by
  constructor
  intro a
  haveI := mapMulRight_lemma κ a
  have h := Measure.isMulLeftInvariant_eq_smul (κ.map (· * a)) κ
  have hu := congrArg (fun ν : Measure H => ν Set.univ) h
  simp only [Measure.map_apply (measurable_mul_const a) MeasurableSet.univ, Set.preimage_univ,
    Measure.nnreal_smul_coe_apply] at hu
  have h0 : κ Set.univ ≠ 0 := (isOpen_univ.measure_pos κ Set.univ_nonempty).ne'
  have ht : κ Set.univ ≠ ⊤ := measure_ne_top κ _
  have hc : ((κ.map (· * a)).haarScalarFactor κ : ℝ≥0∞) = 1 :=
    cancel_lemma_0 h0 ht (by rw [mul_one, mul_comm]; exact hu.symm)
  rw [h, show (κ.map (· * a)).haarScalarFactor κ = 1 from ENNReal.coe_eq_one.1 hc, one_smul]

theorem haarQK : HaarQK := by
  unfold HaarQK
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hQK νQ _ κ _
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : κ.IsMulRightInvariant := cptRight_lemma_2 κ
  have hνR : ∀ q0 : Q, ∃ c : NNReal, νQ.map (· * q0) = c • νQ := by
    intro q0
    haveI := mapMulRight_lemma νQ q0
    haveI : IsFiniteMeasureOnCompacts (νQ.map (· * q0)) := ⟨fun C hC => by
      rw [Measure.map_apply (measurable_mul_const q0) hC.measurableSet]
      exact ((Homeomorph.mulRight q0).isCompact_preimage.2 hC).measure_lt_top⟩
    exact ⟨_, Measure.isMulLeftInvariant_eq_smul (νQ.map (· * q0)) νQ⟩
  have hT : ∀ g : G, ∃ c : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) =
        c * ∫⁻ h : Q × K, f ((h.1 : G) * (h.2 : G)) ∂(νQ.prod κ) := by
    intro g
    obtain ⟨q0, hq0, k0, hk0, rfl⟩ := hQK g
    obtain ⟨c, hc⟩ := hνR ⟨q0, hq0⟩
    refine ⟨(c : ℝ≥0∞), fun f hf => ?_⟩
    have hF : Measurable (fun p : Q × K => f ((p.1 : G) * (p.2 : G))) := by fun_prop
    rw [lintegral_prod _ (by fun_prop), lintegral_prod _ hF.aemeasurable]
    have h1 : ∀ q : Q, ∫⁻ k : K, f ((q : G) * (q0 * k0) * (k : G)) ∂κ =
        ∫⁻ k : K, f (((q * ⟨q0, hq0⟩ : Q) : G) * (k : G)) ∂κ := by
      intro q
      rw [← lintegral_mul_left_eq_self (fun k : K => f (((q * ⟨q0, hq0⟩ : Q) : G) * (k : G))) ⟨k0, hk0⟩]
      congr 1
      funext k
      simp [mul_assoc]
    calc ∫⁻ q : Q, ∫⁻ k : K, f ((q : G) * (q0 * k0) * (k : G)) ∂κ ∂νQ
        = ∫⁻ q : Q, (fun q' : Q => ∫⁻ k : K, f ((q' : G) * (k : G)) ∂κ) (q * ⟨q0, hq0⟩) ∂νQ :=
          lintegral_congr fun q => h1 q
      _ = ∫⁻ q : Q, (fun q' : Q => ∫⁻ k : K, f ((q' : G) * (k : G)) ∂κ) q ∂(νQ.map (· * ⟨q0, hq0⟩)) :=
          (lintegral_map hF.lintegral_prod_right' (measurable_mul_const _)).symm
      _ = (c : ℝ≥0∞) * ∫⁻ q : Q, ∫⁻ k : K, f ((q : G) * (k : G)) ∂κ ∂νQ := by
          rw [hc, lintegral_smul_measure]
          rfl

  have hswap : ∀ f φ : G → ℝ≥0∞, Measurable f → Measurable φ →
      ∫⁻ g, φ g * ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) ∂μ =
        ∫⁻ g, f g * ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) ∂μ := by
    intro f φ hf hφ
    have e1 : ∀ g, φ g * ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) =
        ∫⁻ h : Q × K, φ g * f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) := fun g =>
      (lintegral_const_mul _ (by fun_prop)).symm
    have e2 : ∀ g, f g * ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) =
        ∫⁻ h : Q × K, f g * φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) := fun g =>
      (lintegral_const_mul _ (by fun_prop)).symm
    rw [lintegral_congr e1, lintegral_congr e2]
    have m1 : Measurable (fun p : G × (Q × K) => φ p.1 * f ((p.2.1 : G) * p.1 * (p.2.2 : G))) := by fun_prop
    have m2 : Measurable (fun p : G × (Q × K) => f p.1 * φ ((p.2.1 : G)⁻¹ * p.1 * (p.2.2 : G)⁻¹)) := by fun_prop
    rw [lintegral_lintegral_swap m1.aemeasurable]
    conv_rhs => rw [lintegral_lintegral_swap m2.aemeasurable]
    refine lintegral_congr fun h => ?_
    have inv : ∀ F : G → ℝ≥0∞, ∫⁻ g, F ((h.1 : G) * g * (h.2 : G)) ∂μ = ∫⁻ g, F g ∂μ := by
      intro F
      rw [lintegral_mul_left_eq_self (fun x => F (x * (h.2 : G))) (h.1 : G),
        lintegral_mul_right_eq_self F (h.2 : G)]
    rw [← inv (fun g => f g * φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹))]
    refine lintegral_congr fun g => ?_
    rw [mul_comm]
    simp [mul_assoc]
  have hS : ∀ φ : G → ℝ≥0∞, Measurable φ → ∀ g : G,
      ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * g * (h.2 : G)⁻¹) ∂(νQ.prod κ) =
        ∫⁻ h : Q × K, φ ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) := by
    intro φ hφ g
    obtain ⟨q0, hq0, k0, hk0, rfl⟩ := hQK g
    rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
    have hin : ∀ x : G, ∫⁻ k : K, φ (x * k0 * (k : G)⁻¹) ∂κ = ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ := by
      intro x
      rw [← lintegral_mul_right_eq_self (fun k : K => φ (x * k0 * (k : G)⁻¹)) ⟨k0, hk0⟩]
      refine lintegral_congr fun k => ?_
      simp [mul_assoc]
    have hΨ : Measurable (fun p : G × K => φ (p.1 * (p.2 : G)⁻¹)) := by fun_prop
    calc ∫⁻ q : Q, ∫⁻ k : K, φ ((q : G)⁻¹ * (q0 * k0) * (k : G)⁻¹) ∂κ ∂νQ
        = ∫⁻ q : Q, (fun x : G => ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ) ((q : G)⁻¹ * q0) ∂νQ := by
          refine lintegral_congr fun q => ?_
          show _ = ∫⁻ k : K, φ ((q : G)⁻¹ * q0 * (k : G)⁻¹) ∂κ
          rw [← hin ((q : G)⁻¹ * q0)]
          simp only [mul_assoc]
      _ = ∫⁻ q : Q, (fun x : G => ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ)
            (((⟨q0, hq0⟩ * q : Q) : G)⁻¹ * q0) ∂νQ :=
          (lintegral_mul_left_eq_self
            (fun q : Q => (fun x : G => ∫⁻ k : K, φ (x * (k : G)⁻¹) ∂κ) ((q : G)⁻¹ * q0)) ⟨q0, hq0⟩).symm
      _ = ∫⁻ q : Q, ∫⁻ k : K, φ ((q : G)⁻¹ * (k : G)⁻¹) ∂κ ∂νQ := by
          refine lintegral_congr fun q => ?_
          simp [mul_assoc]

  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have h1C : (1 : G) ∈ interior C := mem_interior_iff_mem_nhds.2 hC1
  obtain ⟨f0, hf0⟩ : ∃ f0 : G → ℝ≥0∞, f0 = C.indicator 1 := ⟨_, rfl⟩
  have hf0m : Measurable f0 := hf0 ▸ measurable_one.indicator hCm
  have hΦm : Measurable (fun p : Q × K => (p.1 : G) * (p.2 : G)) := by fun_prop
  have hΦc : Continuous (fun p : Q × K => (p.1 : G) * (p.2 : G)) := by fun_prop
  have hΨm : Measurable (fun p : Q × K => (p.1 : G)⁻¹ * (p.2 : G)⁻¹) := by fun_prop
  have hΨc : Continuous (fun p : Q × K => (p.1 : G)⁻¹ * (p.2 : G)⁻¹) := by fun_prop
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Measure G, ρ = (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G)) := ⟨_, rfl⟩
  have hPρ : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ h : Q × K, f ((h.1 : G) * (h.2 : G)) ∂(νQ.prod κ) = ∫⁻ g, f g ∂ρ := fun f hf => by
    rw [hρ, lintegral_map hf hΦm]
  have hρC : ρ C = (νQ.prod κ) ((fun p : Q × K => (p.1 : G) * (p.2 : G)) ⁻¹' C) := by
    rw [hρ, Measure.map_apply hΦm hCm]
  have hρCt : ρ C ≠ ⊤ := by
    rw [hρC]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (t := (Subtype.val ⁻¹' ((fun x : G × G => x.1 * x.2) '' (C ×ˢ (K : Set G))) : Set Q) ×ˢ
      (Set.univ : Set K)) ?_) ((hQ.isClosedEmbedding_subtypeVal.isCompact_preimage ((hCc.prod hK).image continuous_mul)).prod
        isCompact_univ).measure_lt_top)
    intro p hp
    refine ⟨?_, Set.mem_univ _⟩
    exact ⟨((p.1 : G) * (p.2 : G), ((p.2 : K) : G)⁻¹), ⟨hp, K.inv_mem p.2.2⟩, by simp⟩
  have hρC0 : ρ C ≠ 0 := by
    rw [hρC]
    exact ((isOpen_interior.preimage hΦc).measure_pos _ ⟨(1, 1), by simpa using h1C⟩).trans_le
      (measure_mono (Set.preimage_mono interior_subset)) |>.ne'
  have hμCt : μ C ≠ ⊤ := hCc.measure_lt_top.ne
  have hμC0 : μ C ≠ 0 :=
    ((isOpen_interior.measure_pos μ ⟨1, h1C⟩).trans_le (measure_mono interior_subset)).ne'
  have hs : ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) =
      (νQ.prod κ) ((fun p : Q × K => (p.1 : G)⁻¹ * (p.2 : G)⁻¹) ⁻¹' C) := by
    rw [lintegral_map (f := f0) hf0m hΨm |>.symm, hf0, lintegral_indicator_one hCm, Measure.map_apply hΨm hCm]
  have hst : ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) ≠ ⊤ := by
    rw [hs]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (t := (Subtype.val ⁻¹' ((fun x : G × G => x.1 * x.2⁻¹) '' ((K : Set G) ×ˢ C)) : Set Q) ×ˢ
      (Set.univ : Set K)) ?_) ((hQ.isClosedEmbedding_subtypeVal.isCompact_preimage ((hK.prod hCc).image (by fun_prop))).prod
        isCompact_univ).measure_lt_top)
    intro p hp
    refine ⟨?_, Set.mem_univ _⟩
    exact ⟨(((p.2 : K) : G)⁻¹, (p.1 : G)⁻¹ * (p.2 : G)⁻¹), ⟨K.inv_mem p.2.2, hp⟩, by group⟩
  have hs0 : ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) ≠ 0 := by
    rw [hs]
    exact ((isOpen_interior.preimage hΨc).measure_pos _ ⟨(1, 1), by simpa using h1C⟩).trans_le
      (measure_mono (Set.preimage_mono interior_subset)) |>.ne'

  have hμf0 : ∫⁻ g, f0 g ∂μ = μ C := by rw [hf0, lintegral_indicator_one hCm]
  have hρf0 : ∫⁻ g, f0 g ∂ρ = ρ C := by rw [hf0, lintegral_indicator_one hCm]
  choose c hc using hT
  have hTm : Measurable (fun g : G => ∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) :=
    (by fun_prop : Measurable (fun p : G × (Q × K) => f0 ((p.2.1 : G) * p.1 * (p.2.2 : G)))).lintegral_prod_right'
  have key : ∀ f : G → ℝ≥0∞, Measurable f → (∫⁻ g, f g ∂μ) * ρ C = μ C * ∫⁻ g, f g ∂ρ := by
    intro f hf
    set s0 := ∫⁻ h : Q × K, f0 ((h.1 : G)⁻¹ * (h.2 : G)⁻¹) ∂(νQ.prod κ) with hs0def
    have A := hswap f f0 hf hf0m
    have B := hswap f0 f0 hf0m hf0m
    simp only [hS f0 hf0m] at A B
    rw [lintegral_mul_const _ hf] at A
    rw [lintegral_mul_const _ hf0m, hμf0] at B
    have e : ∀ g, f0 g * (∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) * ρ C =
        f0 g * (∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) * ∫⁻ x, f x ∂ρ := by
      intro g
      rw [hc g f hf, hc g f0 hf0m, hPρ f hf, hPρ f0 hf0m, hρf0]
      ring
    have hmain : s0 * ((∫⁻ g, f g ∂μ) * ρ C) = s0 * (μ C * ∫⁻ g, f g ∂ρ) := by
      calc s0 * ((∫⁻ g, f g ∂μ) * ρ C) = (∫⁻ g, f g ∂μ) * s0 * ρ C := by ring
        _ = (∫⁻ g, f0 g * ∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) ∂μ) * ρ C := by
            rw [A]
        _ = ∫⁻ g, f0 g * (∫⁻ h : Q × K, f ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) * ρ C ∂μ :=
            (lintegral_mul_const' _ _ hρCt).symm
        _ = ∫⁻ g, f0 g * (∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ)) *
              ∫⁻ x, f x ∂ρ ∂μ := lintegral_congr e
        _ = (∫⁻ g, f0 g * ∫⁻ h : Q × K, f0 ((h.1 : G) * g * (h.2 : G)) ∂(νQ.prod κ) ∂μ) *
              ∫⁻ x, f x ∂ρ := lintegral_mul_const _ (hf0m.mul hTm)
        _ = s0 * (μ C * ∫⁻ g, f g ∂ρ) := by rw [B]; ring
    exact cancel_lemma_0 hs0 hst hmain
  refine ⟨μ C * (ρ C)⁻¹, mul_ne_zero hμC0 (ENNReal.inv_ne_zero.2 hρCt),
    ENNReal.mul_ne_top hμCt (ENNReal.inv_ne_top.2 hρC0), ?_⟩
  rw [← hρ]
  ext B hB
  have hk := key (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, lintegral_indicator_one hB] at hk
  rw [Measure.smul_apply, smul_eq_mul]
  calc μ B = μ B * ρ C * (ρ C)⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel hρC0 hρCt, mul_one]
    _ = μ C * ρ B * (ρ C)⁻¹ := by rw [hk]
    _ = μ C * (ρ C)⁻¹ * ρ B := by ring

end GlobalTheory.CompanionTheory.QuotVan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompMulVec
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.LtrFourier

noncomputable section

theorem map_mulVec_fin {k : Type} [Field k] [NumberField k] {n : ℕ} (A : GL (Fin n) 𝔸[k]) :
    (adeleMeasurePi k).map (fun x : Fin n → 𝔸[k] => (A : Matrix (Fin n) (Fin n) 𝔸[k]) *ᵥ x) =
      ENNReal.ofReal ((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ •
        adeleMeasurePi k (ι := Fin n) := by
  have hmap := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi (tInv (A⁻¹))
  have hdet : Matrix.GeneralLinearGroup.det (tInv (A⁻¹)) = Matrix.GeneralLinearGroup.det A := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    change (((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ.det = _
    rw [Matrix.det_transpose, inv_inv]
  have hfun : (fun x : Fin n → 𝔸[k] =>
      x ᵥ* ((tInv (A⁻¹) : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])) =
      fun x => (A : Matrix (Fin n) (Fin n) 𝔸[k]) *ᵥ x := by
    funext x
    change x ᵥ* (((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ = _
    rw [inv_inv]
    exact Matrix.vecMul_transpose _ x
  rwa [hdet, hfun] at hmap

theorem map_mulVec {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : GL ι 𝔸[k]) :
    (adeleMeasurePi k).map (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) =
      ENNReal.ofReal ((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ •
        adeleMeasurePi k (ι := ι) := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let P : GL (Fin (Fintype.card ι)) 𝔸[k] :=
    ⟨(A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm,
      ((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm,
      by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩
  have hdet : Matrix.GeneralLinearGroup.det P = Matrix.GeneralLinearGroup.det A := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    exact Matrix.det_submatrix_equiv_self _ _
  have h1 : MeasurePreserving (fun x : ι → 𝔸[k] => x ∘ e.symm) (adeleMeasurePi k)
      (adeleMeasurePi k) := GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e.symm
  have h3 : MeasurePreserving (fun x : Fin (Fintype.card ι) → 𝔸[k] => x ∘ e) (adeleMeasurePi k)
      (adeleMeasurePi k) := GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e
  have hP : Measurable fun x : Fin (Fintype.card ι) → 𝔸[k] =>
      (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hfun : (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) =
      (fun x => x ∘ e) ∘
        (fun x => (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x) ∘
          (fun x => x ∘ e.symm) := by
    funext x
    simp only [Function.comp_apply]
    change _ = ((A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm *ᵥ (x ∘ e.symm)) ∘ e
    have hx : (x ∘ e.symm) ∘ e = x := by
      funext j
      simp
    rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hx]
    funext i
    simp
  rw [hfun, ← Measure.map_map h3.measurable (hP.comp h1.measurable),
    ← Measure.map_map hP h1.measurable, h1.map_eq, map_mulVec_fin P, hdet, Measure.map_smul,
    h3.map_eq]
  exact h3.measurable.aemeasurable

def mulVecHomeo {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : GL ι 𝔸[k]) : (ι → 𝔸[k]) ≃ₜ (ι → 𝔸[k]) where
  toFun x := (A : Matrix ι ι 𝔸[k]) *ᵥ x
  invFun x := ((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ x
  left_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem integral_comp_mulVec {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : GL ι 𝔸[k]) (f : (ι → 𝔸[k]) → ℂ) :
    ∫ x, f ((A : Matrix ι ι 𝔸[k]) *ᵥ x) ∂adeleMeasurePi k =
      (((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ : ℂ) *
        ∫ x, f x ∂adeleMeasurePi k := by
  have hemb : MeasurableEmbedding (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) :=
    (mulVecHomeo A).measurableEmbedding
  rw [← hemb.integral_map, map_mulVec, integral_smul_measure, ENNReal.toReal_ofReal
      (inv_nonneg.2 (ideleModule k (Matrix.GeneralLinearGroup.det A)).2.le),
    Complex.real_smul, Complex.ofReal_inv]

theorem adelicFourierPi_ltr : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ), adelicFourierPi k (ltr A F) =
      (((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ : ℂ) •
        ltr (tInv A) (adelicFourierPi k F) := by
  intro k _ _ ι _ _ A F
  funext y
  have h := integral_comp_mulVec A (fun z => F z *
    (adelicChar k (∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i) : ℂ))
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
  have hp : ∀ z : ι → 𝔸[k], ∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i =
      ∑ i, z i * (((tInv A : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ y) i := by
    intro z
    change (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) ⬝ᵥ y =
      z ⬝ᵥ ((((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]))ᵀ *ᵥ y)
    rw [Matrix.mulVec_transpose, dotProduct_comm _ y, Matrix.dotProduct_mulVec,
      dotProduct_comm]
  simp only [hp] at h
  simpa only [adelicFourierPi, ltr, Pi.smul_apply, smul_eq_mul] using h

end

end GlobalTheory.CompanionTheory.LtrFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneVanishAboveDimStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_level_one_vanish_above_dim : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (d : ℕ), (∀ α, U.d α ≤ d) →
    ∀ j, Subsingleton (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | exact GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | (intros; apply GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish <;> assumption)
end

