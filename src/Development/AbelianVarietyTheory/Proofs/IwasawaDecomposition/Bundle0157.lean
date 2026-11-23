module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAlgHomRayField
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

namespace GlobalTheory.UnramInRay

theorem isModulus_of_top {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {χ : (L ≃ₐ[K] L) →* ℂˣ} (h : IsModulus L χ ⊤) {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) : IsModulus L χ 𝔪 := by
  refine ⟨hm, fun 𝔭 _ => h.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd)), ?_⟩
  rintro α β ⟨ha, hb, -, -, -, hpos⟩
  have hc : ∀ I : Ideal (𝓞 K), IsCoprime I ⊤ := fun I => Ideal.isCoprime_iff_sup_eq.2 (sup_top_eq I)
  exact h.2.2 α β ⟨ha, hb, hc _, hc _, Submodule.mem_top, hpos⟩

theorem nonempty_algHom_rayField : GlobalArtinReciprocity → ∀ (K L R : Type) [Field K] [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field R] [NumberField R]
    [Algebra K R] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → IsRayField K R 𝔪 →
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) → Nonempty (L →ₐ[K] R) := by
  intro H K L R _ _ _ _ _ _ _ _ _ _ 𝔪 hm hR hL
  have := hR.1
  exact rayClassFieldMaximalSt_holds K R L 𝔪 hm hR.2 fun χ =>
    isModulus_of_top (GlobalTheory.UnramModulus.isModulus_top H K L hL χ) hm

end GlobalTheory.UnramInRay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt
section
open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

theorem GlobalTheory.Published.GlobalArtinReciprocity.principalIdealSt (H : GlobalArtinReciprocity) : PrincipalIdealSt := by
  intro K L _ _ _ _ _ _ h 𝔞
  have hKL := h.1
  have : IsTotallyComplex L := isTotallyComplex_of_algebra K L
  obtain ⟨N, _, _, _, hN⟩ := rayField_iff.1 H.rayClassFieldSt L ⊤ top_ne_bot
  let : Algebra K N := ((algebraMap L N).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := GlobalTheory.RayTopGalois.isGalois_of_isRayField_top K L N hN
  have := hN.1
  have h' := (GlobalTheory.HilbertClass.isRayField_top_iff L).1 h
  have hN' := (GlobalTheory.HilbertClass.isRayField_top_iff N).1 hN
  have hun := GlobalTheory.Mem.UnramTower.unramIn_trans K L N h'.2.1 hN'.2.1
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker = commutator (N ≃ₐ[K] N) := by
    refine le_antisymm ?_ ?_
    · let M := IntermediateField.fixedField (commutator (N ≃ₐ[K] N))
      have : IsAbelianGalois K M := by
        have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun a b => by
          obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) N a
          obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) N b
          rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, ← MonoidHom.mem_ker,
            IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩⟩
        exact {}
      obtain ⟨f⟩ := rayClassFieldMaximalSt_holds K L M ⊤ top_ne_bot h.2
        (GlobalTheory.UnramModulus.isModulus_top_of_isTotallyComplex H K M fun 𝔭 => GlobalTheory.RayMaximal.unramIn_of_tower (hun 𝔭))
      intro σ hσ
      rw [← IntermediateField.fixingSubgroup_fixedField (commutator (N ≃ₐ[K] N)), IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      let g : M →ₐ[K] N := (IsScalarTower.toAlgHom K L N).comp f
      have hr : g.fieldRange = M := by
        rw [AlgHom.fieldRange_of_normal]
      obtain ⟨y, rfl⟩ : x ∈ g.fieldRange := hr.symm ▸ hx
      have := σ.restrictNormal_commutes L (f y)
      rw [show σ.restrictNormal L = 1 from hσ] at this
      exact this.symm
    · rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm' _ _
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => rw [Ideal.zero_eq_bot, Ideal.map_bot]; infer_instance
  | h₂ I hI => rw [Ideal.isUnit_iff.1 hI, Ideal.map_top]; infer_instance
  | h₃ I p _ hp ih =>
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hP : (p.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
      refine (hN'.2.2.2 _ (Ideal.map_ne_bot_of_ne_bot hp.ne_zero)).1 fun χ => ?_
      obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob N 𝔭
      let r : (N ≃ₐ[L] N) →* (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker :=
        { toFun := fun τ => ⟨τ.restrictScalars K, AlgEquiv.ext fun x => (algebraMap L N).injective
            (((τ.restrictScalars K).restrictNormal_commutes L x).trans (τ.commutes x))⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hr : Function.Bijective r := ⟨fun a b e => AlgEquiv.ext fun x => congrArg (fun t => t.1 x) e, fun t =>
        ⟨AlgEquiv.ofRingEquiv (f := t.1.toRingEquiv) fun x => by
          have := t.1.restrictNormal_commutes L x
          rw [show t.1.restrictNormal L = 1 from t.2] at this
          exact this.symm, rfl⟩⟩
      let φ := χ.comp (MulEquiv.ofBijective r hr).symm.toMonoidHom
      have hv := GlobalTheory.FrobTransfer.heckeIdeal_map_eq_transfer K L N 𝔭 (hun 𝔭) σ hσ χ φ fun τ _ => congrArg χ ((MulEquiv.ofBijective r hr).symm_apply_apply τ)
      have key : ∀ (A : Subgroup (N ≃ₐ[K] N)) (_ : A = commutator _) (ψ : A →* ℂˣ), MonoidHom.transfer ψ = 1 := by
        rintro _ rfl ψ
        exact GlobalTheory.TransferCommutator.transfer_eq_one _ _ ψ
      rw [key _ hker φ] at hv
      exact hv
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := ih
    rw [Ideal.map_mul, ha, hb]
    exact ⟨a * b, Ideal.span_singleton_mul_span_singleton a b⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaChangeSetsOutsideFiniteSet
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeSetChange

theorem abstract_change {ι X Z : Type} [Countable ι] {Y : ι → Type} [MeasurableSpace X]
    [MeasurableSpace Z] [∀ v, MeasurableSpace (Y v)] (ν : Measure X) (mi : Measure Z)
    (mv : ∀ v, Measure (Y v)) (p : X → Z) (q : ∀ v, X → Y v) (hq : ∀ v, Measurable (q v))
    (S T S' : Finset ι) (A L : ∀ v, Set (Y v)) (c : ℝ≥0∞)
    (hS' : ∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) (hd : Disjoint S T) (hA : ∀ v, MeasurableSet (A v))
    (hL : ∀ v ∉ S', A v = L v)
    (H : ∀ (fi : Z → ℝ≥0∞) (fv : ∀ v, Y v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ x in {x | ∀ v ∉ S', q v x ∈ L v}, fi (p x) * ∏ v ∈ S', fv v (q v x) ∂ν =
        (∫⁻ y, fi y ∂mi) * (∏ v ∈ S', ∫⁻ y, fv v y ∂(mv v)) * c)
    (fi : Z → ℝ≥0∞) (fv : ∀ v, Y v → ℝ≥0∞) (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v)) :
    ∫⁻ x in {x | ∀ v ∉ S, q v x ∈ A v}, fi (p x) * ∏ v ∈ S, fv v (q v x) ∂ν =
      (∫⁻ y, fi y ∂mi) * (∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * c) := by
  classical
  have hSeq : S' = S ∪ T := by
    ext v; rw [hS', Finset.mem_union]
  subst hSeq
  have hmeas : ∀ U : Finset ι, MeasurableSet {x | ∀ v ∉ U, q v x ∈ A v} := by
    intro U
    have : {x | ∀ v ∉ U, q v x ∈ A v} = ⋂ v, ⋂ (_ : v ∉ U), q v ⁻¹' A v := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hq v (hA v)
  let gv : ∀ v, Y v → ℝ≥0∞ := fun v => if v ∈ S then fv v else (A v).indicator 1
  have hgS : ∀ v ∈ S, gv v = fv v := fun v hv => if_pos hv
  have hgT : ∀ v ∈ T, gv v = (A v).indicator 1 := fun v hv =>
    if_neg (fun h => Finset.disjoint_left.mp hd h hv)
  have hgm : ∀ v, Measurable (gv v) := by
    intro v
    by_cases hv : v ∈ S
    · rw [hgS v hv]; exact hfv v
    · have : gv v = (A v).indicator 1 := if_neg hv
      rw [this]; exact measurable_one.indicator (hA v)
  have h1 := H fi gv hfi hgm
  have hset : {x | ∀ v ∉ S ∪ T, q v x ∈ L v} = {x | ∀ v ∉ S ∪ T, q v x ∈ A v} := by
    ext x
    refine forall_congr' fun v => forall_congr' fun hv => ?_
    rw [hL v hv]
  rw [hset, Finset.prod_union hd, ← lintegral_indicator (hmeas _)] at h1
  have e1 : ∏ v ∈ S, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v) :=
    Finset.prod_congr rfl fun v hv => by rw [hgS v hv]
  have e2 : ∏ v ∈ T, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ T, mv v (A v) :=
    Finset.prod_congr rfl fun v hv => by rw [hgT v hv]; exact lintegral_indicator_one (hA v)
  rw [e1, e2] at h1
  rw [← lintegral_indicator (hmeas _), ← mul_assoc, mul_assoc (∫⁻ y, fi y ∂mi), ← h1]
  refine lintegral_congr fun x => ?_
  have e3 : ∏ v ∈ S, gv v (q v x) = ∏ v ∈ S, fv v (q v x) :=
    Finset.prod_congr rfl fun v hv => by rw [hgS v hv]
  by_cases hx : x ∈ {x | ∀ v ∉ S, q v x ∈ A v}
  · have hx' : x ∈ {x | ∀ v ∉ S ∪ T, q v x ∈ A v} := fun v hv =>
      hx v fun h => hv (Finset.mem_union_left _ h)
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Finset.prod_union hd, e3]
    have : ∏ v ∈ T, gv v (q v x) = 1 := Finset.prod_eq_one fun v hv => by
      rw [hgT v hv, Set.indicator_of_mem (hx v fun h => Finset.disjoint_left.mp hd h hv)]
      rfl
    rw [this, mul_one]
  · rw [Set.indicator_of_notMem hx]
    by_cases hx' : x ∈ {x | ∀ v ∉ S ∪ T, q v x ∈ A v}
    · rw [Set.indicator_of_mem hx', Finset.prod_union hd]
      simp only [Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hvS, hvA⟩ := hx
      have hvT : v ∈ T := by
        by_contra h
        exact hvA (hx' v (by simp [hvS, h]))
      have : ∏ v ∈ T, gv v (q v x) = 0 := Finset.prod_eq_zero hvT (by
        rw [hgT v hvT, Set.indicator_of_notMem hvA])
      rw [this, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem hx']

theorem product_formula_change_sets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → (∀ v, MeasurableSet (A v)) → (∀ v ∉ S', A v = latV b v) → (∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S', projV v (projFin X) ∈ latV b v}, fi (projInf X) * ∏ v ∈ S', fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S', ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S') → ∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ A v}, fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * tailProd b mv S') := by
  intro F E _ _ _ _ _ d b n M ν mi mv S T S' A hS' hd hA hL H fi fv hfi hfv
  haveI : Countable (HeightOneSpectrum (𝓞 F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hc := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.2.2
  exact abstract_change ν mi mv projInf (fun v X => projV v (projFin X))
    (fun v => (hc v).measurable) S T S' A (fun v => latV b v) _ hS' hd hA hL H fi fv hfi hfv

end GlobalTheory.GaugeSetChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaHaarModulusCmFieldElement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem algebraMap_eq_inclR_mul_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (u : E) (k : F) (hk : algebraMap F E k = u * σ u) :
    algebraMap R (R ⊗[F] E) (algebraMap F R k) = inclR R u * sigR R σ (inclR R u) := by
  have h1 : sigR R σ (inclR R u) = inclR R (σ u) := by
    simp [sigR, inclR]
  rw [h1, ← map_mul, ← hk, ← IsScalarTower.algebraMap_apply]
  exact ((Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes k).symm

theorem prod_modu_inclR : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ u : E, u ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)).Finite ∧ modu (Ainf F ⊗[F] E) (inclR (Ainf F) u) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) = 1 := by
  intro F E _ _ _ _ _ σ h u hu
  haveI := h.1
  obtain ⟨k, hk⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h (u * σ u) (by
    rw [map_mul, GlobalTheory.HermLineZeros.conj_invol h, mul_comm])
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact mul_ne_zero hu ((map_ne_zero σ).2 hu) hk.symm
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) =
      modu (Fv F v) (algebraMap F (Fv F v) k) := fun v =>
    (_root_.GlobalTheory.GaugeEx.modu_eq_modu_norm F E σ h (Fv F v) _ _ (hu.isUnit.map _)
      (algebraMap_eq_inclR_mul_sigR σ _ u k hk)).2
  have hi : modu (Ainf F ⊗[F] E) (inclR (Ainf F) u) = modu (Ainf F) (algebraMap F (Ainf F) k) :=
    (_root_.GlobalTheory.GaugeEx.modu_eq_modu_norm F E σ h (Ainf F) _ _ (hu.isUnit.map _)
      (algebraMap_eq_inclR_mul_sigR σ _ u k hk)).2
  simp only [hv, hi]
  exact _root_.GlobalTheory.GaugeProdFormula.prod_modu_eq_one F k hk0

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDual
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ProjSpace GlobalTheory.Cartier

namespace GlobalTheory.ProjBlowup

private theorem gm_id_val_eq_germ {X : Scheme.{0}} {V : X.Opens} (y : X) (hy : y ∈ V) (a : Γ(X, V)ˣ) :
    (gm (𝟙 X) y V a).val = X.presheaf.germ V y hy a.val := by
  simp only [gm, pullU, dif_pos (show (𝟙 X) y ∈ V from hy)]
  simp
  rfl

private theorem germ_res_val_eq_germ {X : Scheme.{0}} {V W : X.Opens} (h : W ≤ V) (y : X) (hy : y ∈ W)
    (a : Γ(X, V)ˣ) : X.presheaf.germ W y hy (res h a).val = X.presheaf.germ V y (h hy) a.val := by
  simp [res]

theorem isLB_of_chartPull_id {X : Scheme.{0}} {A B : LB X} (hB : B.IsLB) (a : ChartPull A B (𝟙 X))
    (hc : ⨆ i, A.U i = ⊤) : A.IsLB := {
  cover := hc
  g_self := by
    obtain ⟨idx, hle, hg⟩ := a
    intro i
    apply Units.ext
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ (fun y hy => ?_)
    have hy' : y ∈ B.U (idx i) := hle i hy
    change X.presheaf.germ (A.U i) y hy (res _ (A.g i i)).val = X.presheaf.germ (A.U i) y hy (1 : Γ(X, A.U i)ˣ).val
    rw [germ_res_val_eq_germ, ← gm_id_val_eq_germ, hg y i i hy hy,
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx i) from ⟨hy', hy'⟩),
      ← germ_res_val_eq_germ (le_inf le_rfl le_rfl : B.U (idx i) ≤ _) y hy', hB.g_self (idx i)]
    simp
  cocycle := by
    obtain ⟨idx, hle, hg⟩ := a
    intro i j k
    apply Units.ext
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ (fun y hy => ?_)
    have hi : y ∈ A.U i := hy.1.1
    have hj : y ∈ A.U j := hy.1.2
    have hk : y ∈ A.U k := hy.2
    have hi' : y ∈ B.U (idx i) := hle i hi
    have hj' : y ∈ B.U (idx j) := hle j hj
    have hk' : y ∈ B.U (idx k) := hle k hk
    change X.presheaf.germ _ y hy ((res _ (A.g i j)).val * (res _ (A.g j k)).val) =
      X.presheaf.germ _ y hy (res _ (A.g i k)).val
    rw [map_mul, germ_res_val_eq_germ, germ_res_val_eq_germ, germ_res_val_eq_germ, ← gm_id_val_eq_germ, ← gm_id_val_eq_germ,
      ← gm_id_val_eq_germ, hg y i j hi hj, hg y j k hj hk, hg y i k hi hk,
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx j) from ⟨hi', hj'⟩),
      gm_id_val_eq_germ y (show y ∈ B.U (idx j) ⊓ B.U (idx k) from ⟨hj', hk'⟩),
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx k) from ⟨hi', hk'⟩)]
    have hB3 := congrArg (fun u : Γ(X, B.U (idx i) ⊓ B.U (idx j) ⊓ B.U (idx k))ˣ =>
      X.presheaf.germ _ y (show y ∈ B.U (idx i) ⊓ B.U (idx j) ⊓ B.U (idx k) from ⟨⟨hi', hj'⟩, hk'⟩) u.val)
      (hB.cocycle (idx i) (idx j) (idx k))
    simp only [Units.val_mul, map_mul, germ_res_val_eq_germ] at hB3
    exact hB3 }

private theorem gm_id_res_eq {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (y : X) (hy : y ∈ V)
    (a : Γ(X, U)ˣ) : gm (𝟙 X) y V (res h a) = gm (𝟙 X) y U a := by
  apply Units.ext
  rw [gm_id_val_eq_germ y hy, gm_id_val_eq_germ y (h hy), germ_res_val_eq_germ]

private theorem gs_resG_eq {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V)
    (a : Γ(X, U)) : gs f y V (resG X h a) = gs f y U a :=
  gs_res f y h hy a

private theorem mul_eq_unit_mul_of_relations {S : Type _} [CommRing S] (G t t' : Sˣ) (ap aq fp fq sp sq : S)
    (h5 : (t' : S) * t = 1) (E1 : sp = ap * fp) (E2 : sq = aq * fq) (E3 : sp = G * sq) (E4 : fp = t * fq) :
    ap * fp = ((G * t' : Sˣ) : S) * aq * fp := by
  rw [Units.val_mul]
  linear_combination (-1 : S) * E1 + E3 + (G : S) * E2 - ((G : S) * aq * fq) * h5 - ((G : S) * t' * aq) * E4

theorem lbIso_pull_O1_of_proportional (R : Type) [CommRing R] (X W : Scheme.{0}) (J : X.IdealSheafData)
    (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (D : GlobalTheory.EffCartierData W)
    (hL : L₀.IsLB) (hJ : Generates J σ) (hP : Proportional σ g ψ) (hD : D.idealSheaf = J.comap g) :
    LBIso ((GlobalTheory.ProjSpace.O1 R m).pull ψ) (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := by
  classical
  have hT : (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL g) (GlobalTheory.CechPic.isLB_dual D.isLB_lb)
  have hGA := generatesAlong_comap_of_generates X W J L₀ m σ g hJ
  rw [← hD] at hGA
  have loc : ∀ (k : L₀.ι) (d : D.ι) (A : W.affineOpens) (hk : A.1 ≤ g ⁻¹ᵁ L₀.U k) (hd : A.1 ≤ D.U d),
      ∃ a c : Fin (m + 1) → Γ(W, A.1), (∀ j, (g.appLE (L₀.U k) A.1 hk).hom ((σ j).f k) =
        a j * resG W hd (D.f d)) ∧ ∑ j, c j * a j = 1 := by
    intro k d A hk hd
    refine exists_quot_of_span_eq (D.regular d A.1 hd) ?_
    rw [← D.ideal_idealSheaf A d hd, hGA.2 k A hk]
  let Idx := {p : L₀.ι × D.ι × W.affineOpens // p.2.2.1 ≤ g ⁻¹ᵁ L₀.U p.1 ∧ p.2.2.1 ≤ D.U p.2.1}
  let tI : Idx → (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).ι := fun p => (fun _ => p.1.1, p.1.2.1)
  have hle : ∀ p : Idx, p.1.2.2.1 ≤ (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).U (tI p) :=
    fun p y hy => ⟨mem_pull.2 (p.2.1 hy), p.2.2 hy⟩
  let N : LB W :=
    { ι := Idx
      U := fun p => p.1.2.2.1
      g := fun p q => res (inf_le_inf (hle p) (hle q))
        ((GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).g (tI p) (tI q)) }
  let cp : ChartPull N (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) (𝟙 W) :=
    ⟨tI, hle, fun y p q hp hq => gm_id_res_eq _ y (show y ∈ N.U p ⊓ N.U q from ⟨hp, hq⟩) _⟩
  have hcov : ⨆ p, N.U p = ⊤ := by
    refine eq_top_iff.2 (fun y _ => ?_)
    have hgy : g y ∈ ⨆ k, L₀.U k := by rw [hL.cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hgy
    obtain ⟨d, hd⟩ := D.exists_mem y
    obtain ⟨A, hyA, hA⟩ := GlobalTheory.EffCartierData.exists_affine_le (X := W)
      (show y ∈ g ⁻¹ᵁ L₀.U k ⊓ D.U d from ⟨hk, hd⟩)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(k, d, A), hA.trans inf_le_left, hA.trans inf_le_right⟩, hyA⟩
  have hN : N.IsLB := isLB_of_chartPull_id hT cp hcov
  have H2 : LBIso N (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := GlobalTheory.CechPic.iso_of_chart hT cp
  choose af cf haf hcf using fun p : Idx => loc p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2
  have hcomp : ∀ (j : Fin (m + 1)) (p q : Idx),
      resG W (inf_le_left : N.U p ⊓ N.U q ≤ N.U p) (af p j) =
        (N.g p q : Γ(W, N.U p ⊓ N.U q)) * resG W (inf_le_right : N.U p ⊓ N.U q ≤ N.U q) (af q j) := by
    intro j p q
    have hV : N.U p ⊓ N.U q ≤ D.U p.1.2.1 := inf_le_left.trans p.2.2
    refine (mul_cancel_right_mem_nonZeroDivisors (D.regular p.1.2.1 _ hV)).1 ?_
    refine fn_ext (fun y hy => ?_)
    have hyp : y ∈ p.1.2.2.1 := hy.1
    have hyq : y ∈ q.1.2.2.1 := hy.2
    rw [gs_mul (𝟙 W) y _ hy, gs_mul (𝟙 W) y _ hy, gs_mul (𝟙 W) y _ hy, gs_resG_eq _ y _ hy,
      gs_resG_eq _ y _ hy, gs_resG_eq _ y _ hy, gs_unit (𝟙 W) y _ hy]
    change _ = (gm (𝟙 W) y _ (res _ _)).val * _ * _
    rw [gm_id_res_eq _ y hy, GlobalTheory.CechPic.gm_tens _ _ _ y _ _ (hle p hyp) (hle q hyq),
      gm_pull_g L₀ g (𝟙 W) y _ _ (hle p hyp).1 (hle q hyq).1]
    have E1 := congrArg (gs (𝟙 W) y (N.U p)) (haf p j)
    rw [gs_appLE g _ _ _ (𝟙 W) y hyp, gs_mul _ _ _ hyp, gs_resG_eq _ _ _ hyp] at E1
    have E2 := congrArg (gs (𝟙 W) y (N.U q)) (haf q j)
    rw [gs_appLE g _ _ _ (𝟙 W) y hyq, gs_mul _ _ _ hyq, gs_resG_eq _ _ _ hyq] at E2
    have hk2 : (𝟙 W ≫ g) y ∈ L₀.U p.1.1 ⊓ L₀.U q.1.1 := ⟨p.2.1 hyp, q.2.1 hyq⟩
    have E3 := congrArg (gs (𝟙 W ≫ g) y (L₀.U p.1.1 ⊓ L₀.U q.1.1)) ((σ j).compat p.1.1 q.1.1)
    rw [gs_res _ _ _ hk2, gs_mul _ _ _ hk2, gs_unit _ _ _ hk2, gs_res _ _ _ hk2] at E3
    have hd2 : (𝟙 W) y ∈ D.U p.1.2.1 ⊓ D.U q.1.2.1 := ⟨p.2.2 hyp, q.2.2 hyq⟩
    have E4 := congrArg (gs (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1)) (D.trans_spec p.1.2.1 q.1.2.1)
    rw [gs_resG_eq _ _ _ hd2, gs_mul _ _ _ hd2, gs_unit _ _ _ hd2, gs_resG_eq _ _ _ hd2] at E4
    have E5 : ((gm (𝟙 W) y ((GlobalTheory.CechPic.dual D.lb).U (tI p).2 ⊓ (GlobalTheory.CechPic.dual D.lb).U (tI q).2))
        ((GlobalTheory.CechPic.dual D.lb).g (tI p).2 (tI q).2)).val *
        (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)).val = 1 := by
      change (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)⁻¹).val *
        (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)).val = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    exact mul_eq_unit_mul_of_relations _ _ _ _ _ _ _ _ _ E5 E1 E2 E3 E4
  let t : Fin (m + 1) → N.Sec := fun j => { f := fun p => af p j, compat := fun p q => hcomp j p q }
  have ht : ⨆ i, Out.nonzeroLocus (t i) = ⊤ := by
    refine eq_top_iff.2 (fun y _ => ?_)
    have hy : y ∈ ⨆ p, N.U p := by rw [hcov]; trivial
    obtain ⟨p, hyp⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_of_sum (hcf p) hyp
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, GlobalTheory.basicOpen_le_nonzeroLocus (t j) p hj⟩
  have hch : ∀ y : W, ∃ i, y ∈ ψ ⁻¹ᵁ chart R m i := by
    intro y
    have h := iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R m) ψ
    have hy : y ∈ ⨆ i, Out.nonzeroLocus (secPull (coord R m i) ψ) := by rw [h]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    have e := toProj_preimage_chart (ψ ≫ PSpace.str R m) (fun i => secPull (coord R m i) ψ)
      (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R m) ψ) i
    rw [toProj_secPull_coord] at e
    rw [e]
    exact hi
  have hψ : ψ = toProj (ψ ≫ PSpace.str R m) t ht := by
    refine eq_toProj_of_locally (s := t) ht rfl (fun y => ?_)
    have hy : y ∈ ⨆ p, N.U p := by rw [hcov]; trivial
    obtain ⟨p, hyp⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨i, hi⟩ := hch y
    refine ⟨N.U p ⊓ ψ ⁻¹ᵁ chart R m i, ⟨hyp, hi⟩, p, inf_le_left, i, inf_le_right,
      resG W inf_le_left (af p i), fun j => ?_⟩
    have hV : N.U p ⊓ ψ ⁻¹ᵁ chart R m i ≤ D.U p.1.2.1 := inf_le_left.trans p.2.2
    have hk' : N.U p ⊓ ψ ⁻¹ᵁ chart R m i ≤ g ⁻¹ᵁ L₀.U p.1.1 := inf_le_left.trans p.2.1
    refine (mul_cancel_right_mem_nonZeroDivisors (D.regular p.1.2.1 _ hV)).1 ?_
    refine fn_ext (fun z hz => ?_)
    have hzp : z ∈ N.U p := hz.1
    have Ej := congrArg (gs (𝟙 W) z (N.U p)) (haf p j)
    rw [gs_appLE g _ _ _ (𝟙 W) z hzp, gs_mul _ _ _ hzp, gs_resG_eq _ _ _ hzp] at Ej
    have Ei := congrArg (gs (𝟙 W) z (N.U p)) (haf p i)
    rw [gs_appLE g _ _ _ (𝟙 W) z hzp, gs_mul _ _ _ hzp, gs_resG_eq _ _ _ hzp] at Ei
    have Eh := congrArg (gs (𝟙 W) z _) (hP _ p.1.1 hk' i inf_le_right j)
    rw [gs_appLE g _ _ _ (𝟙 W) z hz, gs_mul _ _ _ hz, gs_appLE g _ _ _ (𝟙 W) z hz] at Eh
    rw [gs_mul _ _ _ hz, gs_mul _ _ _ hz, gs_mul _ _ _ hz, gs_resG_eq _ _ _ hz, gs_resG_eq _ _ _ hz,
      gs_resG_eq _ _ _ hz]
    linear_combination (-1 : W.presheaf.stalk z) * Ej + Eh + gs (𝟙 W) z _ (pullRatio ψ _ i inf_le_right j) * Ei
  have H1 : LBIso ((O1 R m).pull ψ) N := by
    have h := lbIso_pullback_O1_toProj (ψ ≫ PSpace.str R m) t ht
    rw [← hψ] at h
    exact h
  exact LBIso.trans (pull_isLB (O1_isLB R m) ψ) hN hT H1 H2

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwistedStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted : ∀ (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X), Generates J σ → GeneratesAlong (J.comap g) σ g := by
  first | exact @GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | exact GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | (intros; apply GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates <;> assumption)
end

