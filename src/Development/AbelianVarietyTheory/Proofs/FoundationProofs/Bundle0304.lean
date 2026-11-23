module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAndMass
section
noncomputable section

namespace GlobalTheory.DefiniteDecomp

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers GlobalTheory.Mass NumberField
open scoped TensorProduct Matrix

theorem exists_reps {G : Type} [Group G] {Γ K : Subgroup G} (h : FiniteClasses Γ K) :
    ∃ (n : ℕ) (g : Fin n → G), (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k) ∧
      (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) ∧
      (∀ i, (Unfold.stab Γ K (g i)).Finite) ∧
      ∑ i, ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = classMass Γ K := by
  haveI := h.1
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin (Formalism.UG.ClassSet Γ K)
  have e : ∀ g, Unfold.stab Γ K g = Formalism.UG.stabAt Γ K g := fun g => by
    ext γ; simp only [Unfold.stab, Formalism.UG.stabAt, mul_assoc]
  refine ⟨n, fun i => (φ.symm i).out, fun x => ?_, fun i j γ γ' k k' e => ?_, fun i => ?_, ?_⟩
  · obtain ⟨γ, hγ, k, hk, e⟩ := (@DoubleCoset.eq _ _ Γ K _ x).1 (DoubleCoset.out_eq' (DoubleCoset.mk Γ K x))
    refine ⟨φ (DoubleCoset.mk Γ K x), ⟨γ, hγ⟩, ⟨k, hk⟩, ?_⟩
    exact e.trans (congrArg (fun c : Formalism.UG.ClassSet Γ K => γ * c.out * k) (φ.symm_apply_apply _).symm)
  · apply φ.symm.injective
    rw [← DoubleCoset.out_eq' (φ.symm i), ← DoubleCoset.out_eq' (φ.symm j)]
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(γ'⁻¹ * γ : Γ), (γ'⁻¹ * γ).2, (k * k'⁻¹ : K), (k * k'⁻¹).2, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc, mul_assoc, ← mul_assoc (γ : G), ← mul_assoc, ← mul_assoc,
      mul_assoc _ _ (k : G), e]
    simp [mul_assoc]
  · rw [e]
    exact h.2 _
  · rw [classMass_eq_sum_of_bijective (fun i => (φ.symm i).out)]
    · simp only [e]
    · simp only [DoubleCoset.out_eq']
      exact φ.symm.bijective

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem levelK_eq {π : HA (AF F) σ J →* HA (Af F) σ J} (hπ : IsFinProj σ J π)
    (Λ : Submodule (𝓞 E) (Fin M → E)) :
    levelK σ J (Λ : Set (Fin M → E)) =
      ((((Formalism.UG.levelAfL σ J Λ).subgroupOf (Formalism.UG.UPts σ J (Af F))).comap
        (swapPts (Af F) σ J : HA (Af F) σ J →* Formalism.UG.UPts σ J (Af F))).comap π) := by
  ext g
  have h1 : g ∈ ((((Formalism.UG.levelAfL σ J Λ).subgroupOf (Formalism.UG.UPts σ J (Af F))).comap
        (swapPts (Af F) σ J : HA (Af F) σ J →* Formalism.UG.UPts σ J (Af F))).comap π) ↔
      (swapPts (Af F) σ J (π g) : GL (Fin M) (E ⊗[F] Af F)) ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ) :=
    ⟨fun h => h.2, fun h => ⟨(swapPts (Af F) σ J (π g)).2, h⟩⟩
  rw [h1, coe_swapPts, hπ g]
  have h2 : ∀ y : Fin M → Af F ⊗[F] E, (fun i => GlobalTheory.LevSplit.swp F E ((finMat σ J g *ᵥ y) i)) =
      (finMat σ J g).map (GlobalTheory.LevSplit.swp F E) *ᵥ fun i => GlobalTheory.LevSplit.swp F E (y i) :=
    fun y => funext fun i => RingHom.map_mulVec _ _ _ i
  change (∀ y, y ∈ latHat F E (Λ : Set (Fin M → E)) ↔ finMat σ J g *ᵥ y ∈ latHat F E (Λ : Set (Fin M → E))) ↔
    ∀ x, x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔
      (finMat σ J g).map (GlobalTheory.LevSplit.swp F E) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ
  simp only [GlobalTheory.LevSplit.latHat_iff, h2]
  refine ⟨fun h x => ?_, fun h y => h _⟩
  choose y hy using fun i => (GlobalTheory.LevSplit.swp_bij (F := F) (E := E)).2 (x i)
  have := h y
  simpa only [hy] using this

end Level

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [inst : StarRing E] [Algebra F E]

theorem standardLattice_span_eq_top (W : HSpace E) :
  Submodule.span E (W.L0 : Set W.V) = ⊤ := by
  let U := Submodule.span E (W.L0 : Set W.V)
  change U = ⊤
  by_contra h
  let e : W.V ≃ₗ⋆[E] W.V :=
    (W.frame.equivFun.trans (starLinearEquiv E)).trans W.frame.equivFun.symm
  let g : W.V →ₗ[E] Module.Dual E U :=
    (LinearMap.domRestrict' U).comp (W.hT.comp e.toLinearMap)
  have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E W.V := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt h
  obtain ⟨x, hx, hx₀⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
  have hsmul (a : E) : a • e x ∈ W.L0 := by
    rw [← W.baseLattice_isUnimodular, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hxy : W.hT (e x) y = 0 :=
      congrArg (fun f : Module.Dual E U => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
    have hyx : W.hT y (e x) = 0 := by
      rw [← W.herm.eq, hxy, map_zero]
    simp [hyx]
  let i : E →ₗ[𝓞 E] W.L0 :=
    ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict W.L0 hsmul
  let : Module.Finite (𝓞 E) W.L0 := Module.Finite.iff_fg.mpr W.standardTuple_isLattice.fg
  let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

theorem mass_coord (hc : CMData F E) (W : HSpace E) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (W.rank, 0))
    (hσ : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e) :
    (letI := Formalism.UG.CS.starOfInv (hc.sig : E →+* E) hσ
    Formalism.HermitianLatticesTheory.mass (Formalism.UG.CS.formJ (hc.sig : E →+* E) hσ W.gram 1) (tMap (Formalism.L2.Herm.crd W) W.L0)) =
      Formalism.HermitianLatticesTheory.mass W.hT W.L0 := by
  let h' : (Fin W.rank → E) →ₗ⋆[E] (Fin W.rank → E) →ₗ[E] E :=
    Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) ((1 : E) • W.gram)
  change Formalism.HermitianLatticesTheory.mass h' (tMap (Formalism.L2.Herm.crd W) W.L0) = _
  have he : ∀ x y, h' (Formalism.L2.Herm.crd W x) (Formalism.L2.Herm.crd W y) = W.hT x y := fun x y => by
    rw [Formalism.L2.Herm.hT_crd hc]
    simp only [h', one_smul, Matrix.toLinearMapₛₗ₂'_apply, Formalism.UG.hform, RingHom.id_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change star _ * _ = star _ * _ * _
    ring
  obtain ⟨h1, h2, -⟩ := Formalism.HermitianLatticesTheory.massBasic _ _ W.hT W.herm
    (GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.trace_pos hc.cmUnram.2.1 W hW hs) W.L0
    (by
      letI := W.standardTuple_isLattice
      exact { span_eq_top := standardLattice_span_eq_top W })
  have h3 := mass_transport (Formalism.L2.Herm.crd W).symm (isoSymm _ he) (tMap (Formalism.L2.Herm.crd W) W.L0)
    (by rwa [tMap_symm]) (by rwa [tMap_symm])
  rwa [tMap_symm] at h3

theorem coe_tMap (W : HSpace E) : (tMap (Formalism.L2.Herm.crd W) W.L0 : Set (Fin W.rank → E)) = latCoord W := by
  ext x
  rw [SetLike.mem_coe, mem_tMap]
  change W.frame.equivFun.symm x ∈ W.L0 ↔ _
  rw [Module.Basis.equivFun_symm_apply]
  rfl

theorem finite_and_mass (hc : CMData F E) (W : HSpace E) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (W.rank, 0))
    (hJ : IsHermND hc.sig W.gram) (hd : Formalism.UG.IsTotDef hc.sig W.gram) :
    FiniteClasses (ratIn (AF F) hc.sig W.gram) (levelW hc W) ∧
      classMass (ratIn (AF F) hc.sig W.gram) (levelW hc W) = Formalism.HermitianLatticesTheory.mass W.hT W.L0 := by
  have hσ : IsCMExt F E hc.sig := ⟨hc.totReal, hc.cmUnram.1, hc.deg2, hc.cmUnram.2.1⟩
  have hL := tMap_lattice (Formalism.L2.Herm.crd W) W.L0 W.standardTuple_isLattice
  have hf : Module.Finite (𝓞 E) (tMap (Formalism.L2.Herm.crd W) W.L0) := Module.Finite.iff_fg.2 hL.fg
  have hsp0 := standardLattice_span_eq_top W
  have hsp : Submodule.span E (tMap (Formalism.L2.Herm.crd W) W.L0 : Set (Fin W.rank → E)) = ⊤ := by
    have h := congrArg (Submodule.map (Formalism.L2.Herm.crd W : W.V →ₗ[E] (Fin W.rank → E))) hsp0
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    exact h
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj hc.sig W.gram
  rw [levelW, ← coe_tMap, levelK_eq hπ]
  constructor
  · rw [finiteClasses_comap π _ _ hπ.surjective hπ.injOn, hπ.map_ratIn]
    exact finiteClasses_lattice hσ hJ hd _ hf hsp
  · have hi : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
    rw [← hπ.unitaryMass_eq, unitaryMass_lattice_eq_genus_mass hσ hJ hd hi _ hf hsp]
    exact mass_coord hc W hW hs hi

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem defClassDecomp : ∀ D : D7, DefClassDecomp D := by
  intro D W hW hs θ hθ A hA
  rw [GlobalTheory.DecompCompare.KSub_eq D W hW hs θ hθ A hA]
  have hd : Formalism.UG.IsTotDef D.sp.cm.sig W.gram := GlobalTheory.DefiniteQuotient.isTotDef_of_posDef W fun τ => by
    have := hW (Formalism.BasicNotions.TH.tauE D τ)
    rw [hs] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨h1, h2⟩ := finite_and_mass D.sp.cm W hW hs (GlobalTheory.DefiniteQuotient.gram_hermND W) hd
  haveI := Unfold.borelHA D.sp.cm.sig W.gram
  refine ⟨(GlobalTheory.DecompCompare.isOpen_levelW D W).measurableSet, ?_⟩
  rw [← h2]
  exact exists_reps h1

end GlobalTheory.DefiniteDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
section
noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Topology
open scoped ENNReal

namespace GlobalTheory.RestrMeas

section Pi

theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

theorem lintegral_fintype_prod_eq_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod_eq_prod fun i => hf _

end Pi

variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v}
  {K : ∀ v, Set (Yf v)}

theorem finprod_eq_prod_of_mem {M : Type} [CommMonoid M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) {x : X} (hx : ∀ v ∉ S, pf v x ∈ K v) :
    ∏ᶠ v, ff v (pf v x) = ∏ v ∈ S, ff v (pf v x) :=
  finprod_eq_prod_of_mulSupport_subset _ fun v hv => by_contra fun h' => hv (h1 v h' _ (hx v h'))

theorem finprod_eq_zero_of_notMem {M : Type} [CommMonoidWithZero M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ff v = (K v).indicator 1) {x : X} (hx : ∀ᶠ v in cofinite, pf v x ∈ K v)
    (hx' : ¬ ∀ v ∉ S, pf v x ∈ K v) : ∏ᶠ v, ff v (pf v x) = 0 := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_of_eventually hx
  push Not at hx'
  obtain ⟨u, hu, hu'⟩ := hx'
  rw [finprod_eq_prod_of_mem (K := K) (S := S ∪ T)
    (fun v hv y hy => by rw [h1 v fun h' => hv (Finset.mem_union_left _ h'), indicator_of_mem hy, Pi.one_apply])
    fun v hv => hT v fun h' => hv (Finset.mem_union_right _ h')]
  exact Finset.prod_eq_zero (Finset.mem_union_right _ (by_contra fun h' => hu' (hT u h')))
    (by rw [h1 u hu, indicator_of_notMem hu'])

variable [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)] [Countable V]

theorem measurableSet_level (hf : ∀ v, Measurable (pf v)) (hK : ∀ v, MeasurableSet (K v)) (S : Finset V) :
    MeasurableSet {x | ∀ v ∉ S, pf v x ∈ K v} := by
  simp only [setOf_forall]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hf v (hK v)

variable [Fintype W] {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}
  [∀ w, SigmaFinite (μa w)] [∀ v, SigmaFinite (μf v)]


omit [Countable V] in
theorem IsCylProd.measurePreserving_level (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w))
    (hf : ∀ v, Measurable (pf v)) {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1) :
    MeasurePreserving (fun x => (fun w => pa w x, fun v : S => pf v x)) (μ.restrict {x | ∀ v ∉ S, pf v x ∈ K v})
      ((Measure.pi μa).prod (Measure.pi fun v : S => μf v)) := by
  classical
  have hπ : Measurable fun x => (fun w => pa w x, fun v : S => pf v x) :=
    (Measurable.of_eval ha).prodMk (Measurable.of_eval fun v => hf v)
  refine ⟨hπ, (prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    (FiniteSpanningSetsIn.pi fun w => (μa w).toFiniteSpanningSetsIn)
    (FiniteSpanningSetsIn.pi fun v : S => (μf v).toFiniteSpanningSetsIn) ?_).symm⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  have hm := (MeasurableSet.univ_pi fun w => hA w (mem_univ _)).prod (MeasurableSet.univ_pi fun v => hB v (mem_univ _))
  have e := h.2 S hS A (fun v => if hv : v ∈ S then B ⟨v, hv⟩ else univ) (fun w => hA w (mem_univ _))
    fun v hv => by simp only [dif_pos hv]; exact hB ⟨v, hv⟩ (mem_univ _)
  rw [Measure.map_apply hπ hm, Measure.restrict_apply (hπ hm), Measure.pi_pi, Measure.pi_pi]
  convert e using 2
  · ext x
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, mem_cyl, mem_setOf_eq, and_assoc, Subtype.forall]
    exact and_congr_right fun _ => and_congr_left fun _ => forall₂_congr fun v hv => by rw [dif_pos hv]
  · rw [← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => by rw [dif_pos v.2]

variable (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w)) (hf : ∀ v, Measurable (pf v))
  (hK : ∀ v, MeasurableSet (K v))

include h ha hf hK

section Nonneg

variable {fa : ∀ w, Ya w → ℝ≥0∞} {ff : ∀ v, Yf v → ℝ≥0∞}

end Nonneg

variable {𝕜 : Type} [RCLike 𝕜] {fa : ∀ w, Ya w → 𝕜} {ff : ∀ v, Yf v → 𝕜}

theorem IsCylProd.setIntegral_tensor {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1)
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) (hfa : ∀ w, Integrable (fa w) (μa w))
    (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    IntegrableOn (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} μ ∧
    ∫ x in {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  have hp := h.measurePreserving_level ha hf hS
  have hi := (Integrable.fintype_prod_dep hfa).mul_prod
    (Integrable.fintype_prod_dep (μ := fun v : S => μf v) fun v : S => hff v v.2)
  have e : EqOn (fun x => (∏ w, fa w (pa w x)) * ∏ v : S, ff v (pf v x))
      (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} := fun x hx => by
    simp only [finprod_eq_prod_of_mem h1 hx, ← Finset.prod_coe_sort S]
  refine ⟨IntegrableOn.congr_fun (hp.integrable_comp_of_integrable hi) e (measurableSet_level hf hK S), ?_⟩
  rw [← setIntegral_congr_fun (measurableSet_level hf hK S) e, ← Finset.prod_coe_sort S,
    ← integral_fintype_prod_eq_prod, ← integral_fintype_prod_eq_prod, ← integral_prod_mul, ← hp.map_eq,
    integral_map hp.aemeasurable (hp.map_eq ▸ hi.aestronglyMeasurable)]

theorem IsCylProd.integral_tensor_indicator (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S : Finset V}
    (hS : ∀ v ∉ S, μf v (K v) = 1) (h1 : ∀ v ∉ S, ff v = (K v).indicator 1)
    (hfa : ∀ w, Integrable (fa w) (μa w)) (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    Integrable (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) μ ∧
    ∫ x, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  obtain ⟨hi, e⟩ := h.setIntegral_tensor ha hf hK hS
    (fun v hv y hy => by rw [h1 v hv, indicator_of_mem hy, Pi.one_apply]) hfa hff
  have h0 : ∀ x ∉ {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) = 0 := fun x hx => by
    rw [finprod_eq_zero_of_notMem h1 (hX x) hx, mul_zero]
  exact ⟨hi.integrable_of_forall_notMem_eq_zero h0, by rw [← e, setIntegral_eq_integral_of_forall_compl_eq_zero h0]⟩


end GlobalTheory.RestrMeas

namespace GlobalTheory.AdelicU

open NumberField IsDedekindDomain GlobalTheory.RestrMeas

end GlobalTheory.AdelicU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLatHatIffOfSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField GlobalTheory.SplitHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicU.SplitFrame

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem map_map_sndA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (u : HeightOneSpectrum (𝓞 F))
    (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem vecLoc_finPart {n : ℕ} (u : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (y : Fin n → AE D) :
    vecLoc u (fun i => finPart D (e * y i)) =
      compFin D.host.F D.host.E u e • fun i => compFin D.host.F D.host.E u (y i) :=
  funext fun i => (map_map_sndA u (e * y i)).trans ((compFin D.host.F D.host.E u).map_mul e (y i))

theorem compFin_eq_zero (he : IsSplitIdem D e) (hπ : Chart e v π) {u : HeightOneSpectrum (𝓞 D.host.F)}
    (hu : u ≠ v) : compFin D.host.F D.host.E u e = 0 := by
  obtain ⟨h1, h2, v', ε, ⟨α, rfl, -, ha⟩, hε⟩ := he
  have p1 : π e = 1 := by
    have := (hπ.2.1 (1 - e)).2 (by rw [mul_sub, mul_one, h1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have p2 : π (cA D e) = 0 := (hπ.2.1 _).2 h2
  have p3 : evalV D.host.F v α = 1 := by
    have := hπ.2.2.1 (pairA D.host.F 0 α)
    rw [← hε, map_add (f := _), p1, p2, add_zero] at this
    exact this.symm
  have hv : v = v' := by
    by_contra hne
    rw [ha v hne] at p3
    exact zero_ne_one p3
  subst hv
  have p4 : compFin D.host.F D.host.E u (e + cA D e) = 0 := by
    rw [hε]
    change (evalV D.host.F u α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [ha u hu, TensorProduct.zero_tmul]
  have p5 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [p5, map_mul, p4, mul_zero]

theorem mem_latHat_iff_of_support {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) {y : Fin n → Af F ⊗[F] E} {z : Fin n → Fv F v}
    (hv : vecLoc v y = splitIncl h τ z) (hu : ∀ u, u ≠ v → vecLoc u y = 0) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ z ∈ splitLat τ L := by
  rw [mem_latHat_iff hL, ← splitIncl_mem_latLoc_iff h, ← hv]
  refine ⟨fun h => h v, fun h u => ?_⟩
  by_cases huv : u = v
  · subst huv; exact h
  · rw [hu u huv]; exact zero_mem _

theorem vecLoc_self (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D) :
    vecLoc v (fun i => finPart D (e * y i)) = splitIncl (isCMExt_host D) (chartEmb hπ) (fun k => π (y k)) := by
  have : (fun k => π (y k)) = splitVec (chartEmb hπ) (fun k => compFin D.host.F D.host.E v (y k)) :=
    funext fun k => chart_eq_splitProj hπ _
  rw [this, splitIncl_splitVec, vecLoc_finPart, compFin_eq_splitIdem he hπ]

theorem vecLoc_ne (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D)
    (u : HeightOneSpectrum (𝓞 D.host.F)) (hu : u ≠ v) : vecLoc u (fun i => finPart D (e * y i)) = 0 := by
  rw [vecLoc_finPart, compFin_eq_zero he hπ hu]
  exact funext fun i => zero_mul _

theorem lamHat_eq (V : HSp D) :
    LamHat V = Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) :=
  congrArg (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E) (hermitianSpaceBaseLattice_eq_frameLattice V)

theorem mem_lamHat_iff (he : IsSplitIdem D e) (hπ : Chart e v π) (V : HSp D) (y : Fin V.rank → AE D) :
    (fun i => finPart D (e * y i)) ∈ LamHat V ↔ (fun k => π (y k)) ∈ splitLat (chartEmb hπ) (frameLat V) := by
  rw [lamHat_eq]
  exact mem_latHat_iff_of_support (isCMExt_host D) _ (frameLat_fg V) (vecLoc_self he hπ y) (vecLoc_ne he hπ y)

theorem frame_iff_isSplitBasis : ∀ {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v}, IsSplitIdem D e → ∀ (hπ : Chart e v π) (V : HSp D)
    (β : GL (Fin V.rank) (Fv D.host.F v)),
    Frame V e π β ↔ GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.AdelicU.chartEmb hπ) (GlobalTheory.AdelicU.frameLat V) β := by
  intro D e v π he hπ V β
  refine ⟨fun h u => ?_, fun h y => ?_⟩
  · choose y hy using fun k => hπ.1 ((β.1 *ᵥ u) k)
    have h1 := h y
    rw [mem_lamHat_iff he hπ, show (fun k => π (y k)) = β.1 *ᵥ u from funext hy, Matrix.mulVec_mulVec,
      Units.inv_mul, Matrix.one_mulVec] at h1
    simpa only [isInt_Ov] using h1.symm
  · rw [mem_lamHat_iff he hπ, h.mem_iff]
    simp only [isInt_Ov]

end GlobalTheory.AdelicU.SplitFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterMul
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem theta_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, theta ψ (a * b) = theta ψ a * theta ψ b := by
  intro k _ _ _ _ n ψ hψ a ha b hb
  have P := _root_.GlobalTheory.PsType.triv_ev_props k
  obtain ⟨-, -, -, -, -, -, hevmul, hevcong, hevtriv⟩ := P
  unfold theta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  by_cases ht : Triv (ψ m / nxt ψ m) 1
  · rw [hevtriv _ _ ht, hevtriv _ _ ht, hevtriv _ _ ht, one_mul]
  · obtain ⟨hv, hc⟩ := _root_.GlobalTheory.PsType.minor_mul_mod k n ψ hψ m ht
    have hab := _root_.GlobalTheory.PsType.grp_mul_closed k n ψ hψ a ha b hb
    have va := hv a ha
    have vb := hv b hb
    have vab := hv (a * b) hab
    have vprod : valuation k (minor a m * minor b m) = 1 := by rw [map_mul, va, vb, one_mul]
    rw [hevcong _ _ _ vab vprod (hc a ha b hb), hevmul _ _ _ va vb]

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalVectorNotInBorelJacquetKernel
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType
open GlobalTheory.DepthZeroJac GlobalTheory.IwahoriInj GlobalTheory.StepData

theorem unipRad_points_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    unipRad k (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) = unipB k (Fin n) := by
  ext g
  rw [mem_unipB, mem_unipRad, mem_parab]
  simp only [blk, Equiv.sigmaUnique_symm_apply, Equiv.sigmaUnique_apply]
  refine and_congr Iff.rfl ⟨fun h i => (h i 0 0).trans (by simp), fun h a i j => ?_⟩
  rw [h a, Subsingleton.elim i j]
  simp

theorem eq_zero_of_fixed_KO_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v ∈ twKer π (unipB k (Fin n)) 1, (∀ g ∈ KO k (Fin n), π g v = v) → v = 0 := by
  intro k _ _ _ _ n V _ _ π hπ v h1 hfix
  rw [← unipRad_points_eq] at h1
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_deep (k := k) 1
  obtain ⟨M, hM⟩ := (eventually_mem_twKer (hc := hc0) hc1 hc2 h1).exists
  refine claim_of_antitone hc1 hc2 hπ _ _ rfl (antitone_expo M) v ?_ hM
  exact mem_fixed.2 fun g hg => hfix g ((sup_le KOne_le_KO inf_le_right) hg)

end GlobalTheory.PsType
end

