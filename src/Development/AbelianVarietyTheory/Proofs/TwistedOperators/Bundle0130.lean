module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrict
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.HaarOpenEmb

theorem nnreal_smul_cancel {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [LocallyCompactSpace Y]
    (ρ : Measure Y) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [Nonempty Y] {a b : ℝ≥0}
    (h : a • ρ = b • ρ) : a = b := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds y
  have h0 : ρ K ≠ 0 := (Measure.measure_pos_of_mem_nhds ρ hKn).ne'
  have hT : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have e := congrArg (fun μ : Measure Y => μ K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  exact_mod_cast (ENNReal.mul_left_inj h0 hT).1 e

theorem addEquivAddHaarChar_eq_of_isOpenEmbedding :
    ∀ (G G' : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [T2Space G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (j : G' →+ G), IsOpenEmbedding j → ∀ (e : G ≃ₜ+ G) (e' : G' ≃ₜ+ G'), (∀ x, e (j x) = j (e' x)) → addEquivAddHaarChar e = addEquivAddHaarChar e' := by
  intro G G' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj e e' hcomm
  by_cases hne : Nonempty G'
  swap
  · have : IsEmpty G' := not_nonempty_iff.1 hne
    exact absurd ⟨0⟩ hne
  let μ : Measure G := Measure.addHaar
  let ν : Measure G' := μ.comap j
  haveI : ν.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ hj
  haveI : ν.Regular := inferInstance
  have hjm : ∀ s, MeasurableSet s → MeasurableSet ((j : G' → G) '' s) :=
    fun s hs => hj.measurableEmbedding.measurableSet_image' hs
  have hem : ∀ s, MeasurableSet s → MeasurableSet ((e : G → G) '' s) :=
    fun s hs => e.toHomeomorph.measurableEmbedding.measurableSet_image' hs
  have he'm : ∀ s, MeasurableSet s → MeasurableSet ((e' : G' → G') '' s) :=
    fun s hs => e'.toHomeomorph.measurableEmbedding.measurableSet_image' hs
  have h1 := addEquivAddHaarChar_smul_eq_comap μ e
  have h2 := addEquivAddHaarChar_smul_eq_comap ν e'
  have hfun : (e : G → G) ∘ (j : G' → G) = (j : G' → G) ∘ (e' : G' → G') := funext hcomm
  have key : addEquivAddHaarChar e • ν = addEquivAddHaarChar e' • ν := by
    rw [h2]
    change addEquivAddHaarChar e • μ.comap j = (μ.comap j).comap e'
    rw [Measure.comap_comap he'm hj.injective hjm, ← hfun,
      ← Measure.comap_comap hjm e.injective hem, ← h1]
    have hs : ∀ (c : ℝ≥0) (m : Measure G), c • m = (c : ℝ≥0∞) • m := fun c m => by
      ext s hs; rw [Measure.smul_apply, Measure.smul_apply]; rfl
    have hs' : ∀ (c : ℝ≥0) (m : Measure G'), c • m = (c : ℝ≥0∞) • m := fun c m => by
      ext s hs; rw [Measure.smul_apply, Measure.smul_apply]; rfl
    rw [hs, hs', Measure.comap_smul]
  exact nnreal_smul_cancel ν key

end GlobalTheory.HaarOpenEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.ModuArtin

theorem addEquivAddHaarChar_mulVecCE (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] :
    IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)]
      [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det),
      addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  intro hA hR κ _ _ inst hB M hM
  have heq : inst = MeasurableSpace.pi := by
    exact hB.measurable_eq.trans (@BorelSpace.measurable_eq (κ → B) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst heq
  set ν : Measure B := Measure.addHaar
  set μ : Measure (κ → B) := Measure.pi fun _ : κ => ν
  have h1 := addEquivAddHaarChar_smul_map μ (mulVecCE M hM)
  have h2 : (modu B M.det : ℝ≥0∞) • Measure.map M.mulVec μ = μ :=
    GlobalTheory.GaugeEx.ModDet.smul_map_mulVec_pi ν M hM
  have hfun : ⇑(mulVecCE M hM) = M.mulVec := funext fun x => mulVecCE_apply M hM x
  rw [hfun] at h1
  obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (κ → B)))
  have hpos : μ K ≠ 0 := ((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le
    (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  set m := (Measure.map M.mulVec μ) (K : Set (κ → B))
  have e1 : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h1]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have e2 : (modu B M.det : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h2]
    rw [Measure.smul_apply, smul_eq_mul]
  have hm0 : m ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hpos e1.symm
  have hmt : m ≠ ⊤ := by
    intro h
    rw [h] at e1
    have hc : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (addEquivAddHaarChar_pos (mulVecCE M hM)).ne'
    rw [ENNReal.mul_top hc] at e1
    exact hfin e1.symm
  have := (ENNReal.mul_left_inj hm0 hmt).1 (e1.trans e2.symm)
  exact_mod_cast this

end GlobalTheory.ModuArtin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem addEquivAddHaarChar_prodCE (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁]
    [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]
    [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂]
    [MeasurableSpace G₂] [BorelSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) :
    addEquivAddHaarChar (prodCE e₁ e₂) = addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂ := by
  set μ₁ : Measure G₁ := Measure.addHaar
  set μ₂ : Measure G₂ := Measure.addHaar
  set μ : Measure (G₁ × G₂) := μ₁.prod μ₂
  have hμ : μ.IsAddHaarMeasure := by infer_instance
  have hreg : μ.Regular := by infer_instance
  set φ := prodCE e₁ e₂
  have h1 := addEquivAddHaarChar_smul_map μ₁ e₁
  have h2 := addEquivAddHaarChar_smul_map μ₂ e₂
  have h := addEquivAddHaarChar_smul_map μ φ
  have hm1 : (μ₁.map e₁).IsAddHaarMeasure := e₁.isAddHaarMeasure_map μ₁
  have hm2 : (μ₂.map e₂).IsAddHaarMeasure := e₂.isAddHaarMeasure_map μ₂
  have hmap : μ.map φ = (μ₁.map e₁).prod (μ₂.map e₂) := by
    have := Measure.map_prod_map μ₁ μ₂ e₁.continuous.measurable e₂.continuous.measurable
    exact this.symm
  have hc : (addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂) • μ.map φ = μ := by
    rw [hmap]
    conv_rhs => rw [show μ = μ₁.prod μ₂ from rfl, ← h1, ← h2]
    rw [mul_smul]
    rw [Measure.prod_smul_left, Measure.prod_smul_right]
  have hν : (μ.map φ).IsAddHaarMeasure := φ.isAddHaarMeasure_map μ
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G₁ × G₂)
  have hpos : (μ.map φ) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hfin : (μ.map φ) K ≠ ∞ := hK.measure_lt_top.ne
  have key := congrArg (fun m : Measure (G₁ × G₂) => m K) (h.trans hc.symm)
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at key
  have := (ENNReal.mul_left_inj hpos hfin).1 key
  exact_mod_cast this

end GlobalTheory.ModuLR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceGen

open GlobalTheory.AdelicU

theorem piCoprod_mem {ι G : Type} [Fintype ι] [Monoid G] {N : ι → Type} [∀ i, Monoid (N i)] (φ : ∀ i, N i →* G)
    (h : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y)) (M : Submonoid G) (hM : ∀ i x, φ i x ∈ M)
    (x : ∀ i, N i) : MonoidHom.noncommPiCoprod φ h x ∈ M := by
  rw [MonoidHom.noncommPiCoprod_apply]
  exact Submonoid.noncommProd_mem _ _ _ _ fun i _ => hM i (x i)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

omit [NumberField E] in
theorem levelOff_anti {S S' : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ S') :
    levelOff σ J L S' ≤ levelOff σ J L S := fun g hg => by
  rw [mem_levelOff] at hg ⊢
  refine ⟨hg.1, fun v hv => hg.2.1 v (h hv), fun v _ => ?_⟩
  by_cases hv : v ∈ S'
  · rw [hg.2.1 v hv]; exact one_mem _
  · exact hg.2.2 v hv

theorem exists_levelOff_le [Submodule.IsFullLattice E L] (U : Subgroup (GAd σ J)) (hU : IsOpen (U : Set (GAd σ J))) :
    ∃ S, levelOff σ J L S ≤ U := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (levelOff σ J L S : Set (GAd σ J)) \ (U : Set (GAd σ J)))
    (fun S S' => ⟨S ∪ S', Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_left),
      Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_right)⟩)
    (fun S => Set.diff_nonempty.2 (hcon S))
    (fun S => (isCompact_levelOff σ J L S).diff hU)
    (fun S => ((isCompact_levelOff σ J L S).diff hU).isClosed)
  rw [Set.mem_iInter] at hg
  have h1 : g = 1 := GAd_ext σ J
    (fun w => by rw [mem_finPts_iff_forall.1 (mem_levelOff.1 (hg ∅).1).1 w, map_one])
    fun v => by rw [(mem_levelOff.1 (hg {v}).1).2.1 v (Finset.mem_singleton_self v), map_one]
  exact (hg ∅).2 (h1 ▸ one_mem U)

omit [NumberField E] in
theorem emb_proj_mem_levelOff {S : Finset (HeightOneSpectrum (𝓞 F))} {k : GAd σ J} (hk : k ∈ levelOff σ J L S)
    (v : HeightOneSpectrum (𝓞 F)) : emb σ J v (proj σ J v k) ∈ levelOff σ J L S := by
  by_cases hv : v ∈ S
  · rw [(mem_levelOff.1 hk).2.1 v hv, map_one]; exact one_mem _
  · exact emb_mem_levelOff hv ((mem_levelOff.1 hk).2.2 v hv)

theorem eq_top_of_local [Submodule.IsFullLattice E L] (M : Submonoid (GAd σ J)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h1 : ∀ v x, emb σ J v x ∈ M) (h2 : ∀ w x, embArch σ J w x ∈ M) (h3 : ∀ k ∈ levelOff σ J L S, k ∈ M) :
    M = ⊤ := by
  classical
  refine top_unique fun g _ => ?_
  have hinf : ∀ y, ofInf σ J y ∈ M := fun y => by
    rw [← (infEquivPi σ J).symm_apply_apply y]
    generalize infEquivPi σ J y = x
    have : embArchPi σ J x ∈ M.comap (ofInf σ J) := by
      exact piCoprod_mem (fun w => embArchInf σ J w) _ _ (fun w y => h2 w y) x
    exact this
  have hat : ∀ S' x, embAt σ J S' x ∈ M := fun S' x => by
    exact piCoprod_mem (fun v : S' => emb σ J v) _ _ (fun v y => h1 v y) x
  have hf := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ J L g)
  set g' := ofFin σ J (projFin σ J g) with hg'
  set S' := S ∪ hf.toFinset with hS'
  have hfin : g' ∈ finPts σ J := mem_finPts.2 (by simp [hg'])
  have hx := mem_atPts.1 (embAt_mem σ J S' (projAt σ J S' g'))
  have hrest : (partAway σ J S' g' : GAd σ J) ∈ levelOff σ J L S' := by
    refine mem_levelOff.2 ⟨mul_mem (inv_mem hx.1) hfin, mem_awayPts.1 (partAway σ J S' g').2, fun v hv => ?_⟩
    change proj σ J v ((embAt σ J S' (projAt σ J S' g'))⁻¹ * g') ∈ _
    rw [map_mul, map_inv, hx.2 v hv, inv_one, one_mul, hg', proj_ofFin, projFinLoc_projFin]
    by_contra hc
    exact hv (Finset.mem_union_right _ (hf.mem_toFinset.2 hc))
  rw [← ofInf_projInf_mul_ofFin_projFin σ J g, ← hg', ← embAt_mul_partAway σ J S' g']
  exact mul_mem (hinf _) (mul_mem (hat _ _) (h3 _ (levelOff_anti σ J L Finset.subset_union_left hrest)))

end General

theorem gen_by_local : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → (∀ g : GA D V, {p : Place D | ¬ (gAt V p g ∈ U ∧ gAt V p g ∈ GfC V)}.Finite) ∧ Submonoid.closure ({g : GA D V | ∃ p, gAt V p g = g} ∪ {k : GA D V | k ∈ U ∧ k ∈ GfC V ∧ ∀ p, gAt V p k ∈ U ∧ gAt V p k ∈ GfC V}) = ⊤ := by
  intro D V U hU
  haveI hL : Submodule.IsFullLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  obtain ⟨S, hS⟩ := exists_levelOff_le D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) U hU
  have hG : ∀ k ∈ levelOff D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) S, k ∈ U ∧ k ∈ GfC V :=
    fun k hk => ⟨hS hk, (mem_levelOff.1 hk).1⟩
  refine ⟨fun g => ?_, eq_top_of_local D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) _ S
    (fun v x => Submonoid.subset_closure (Or.inl ⟨.inl v, by simp [gAt]⟩)) (fun w x => ?_) fun k hk => ?_⟩
  · have hf := Filter.eventually_cofinite.1
      (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) g)
    haveI : Finite D.what₂.Tau := Finite.of_injective _ (placeOf_bijective D).1
    refine (((hf.union S.finite_toSet).image Sum.inl).union (Set.finite_range Sum.inr)).subset ?_
    rintro (v | τ) hp
    · refine Or.inl ⟨v, ?_, rfl⟩
      by_contra hc
      rw [Set.mem_union, not_or] at hc
      exact hp (hG _ (emb_mem_levelOff hc.2 (not_not.1 hc.1)))
    · exact Or.inr ⟨τ, rfl⟩
  · obtain ⟨τ, rfl⟩ : ∃ τ, plTau D τ = w := (placeOf_bijective D).2 w
    refine Submonoid.subset_closure (Or.inl ⟨.inr τ, ?_⟩)
    simp only [gAt, projArch_embArch_self]
  · refine Submonoid.subset_closure (Or.inr ⟨(hG k hk).1, (hG k hk).2, ?_⟩)
    rintro (v | τ)
    · exact hG _ (emb_proj_mem_levelOff _ _ _ hk v)
    · have : gAt V (.inr τ) k = 1 := by
        simp only [gAt, mem_finPts_iff_forall.1 (mem_levelOff.1 hk).1 _, map_one]
      rw [this]
      exact ⟨one_mem _, one_mem _⟩

end GlobalTheory.PlaceGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceComponent

section General

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']

theorem tens_comp (φ : R'' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (k : R' →ₗ[F] R'')
    (hk : ∀ a b, k (a * b) = k a * k b) (h : ∀ a, k (j (φ a)) = k (j 1) * a) (z : R'' ⊗[F] E) :
    tensNU k hk (tensNU j hj (Algebra.TensorProduct.map φ (AlgHom.id F E) z)) = (k (j 1) ⊗ₜ[F] (1 : E)) * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]

theorem mat_ext_ext_map (φ : R'' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (k : R' →ₗ[F] R'')
    (hk : ∀ a b, k (a * b) = k a * k b) (h : ∀ a, k (j (φ a)) = k (j 1) * a) (g : HA R'' σ J) :
    (HA.mat R'' σ J (extH σ J k hk (extH σ J j hj (mapH σ J φ g)))).1 =
      (k (j 1) ⊗ₜ[F] (1 : E)) • (HA.mat R'' σ J g).1 +
        (1 - k (j 1) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin M) (Fin M) (R'' ⊗[F] E)) := by
  refine Matrix.ext fun r s => ?_
  have e1 : tensNU (E := E) k hk (tensNU (E := E) j hj 1) = k (j 1) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.one_def, tensNU_tmul, tensNU_tmul]
  rw [mat_extH, mat_extH, mat_mapH, map_add (f := _), tens_comp φ j hj k hk h, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases e : r = s
  · subst e
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, mul_one, mul_one, map_sub, e1]
    ring
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, mul_zero, mul_zero, mul_zero, map_zero, zero_add, zero_add,
      add_zero]

theorem mix_mul {A l m n : Type} [CommRing A] [Fintype m] {b : A} (hb : b * b = b) (X X' : Matrix l m A)
    (Y Y' : Matrix m n A) :
    (b • X + (1 - b) • X') * (b • Y + (1 - b) • Y') = b • (X * Y) + (1 - b) • (X' * Y') := by
  have h1 : b * (1 - b) = 0 := by linear_combination -hb
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, hb, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_act {A m n : Type} [CommRing A] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {b : A}
    (hb : b * b = b) (X : Matrix m m A) (w : Matrix m n A) (Y : Matrix n n A) :
    (b • X + (1 - b) • (1 : Matrix m m A)) * w * (b • Y + (1 - b) • (1 : Matrix n n A)) =
      b • (X * w * Y) + (1 - b) • w := by
  have e : w = b • w + (1 - b) • w := by rw [← add_smul, add_sub_cancel, one_smul]
  conv_lhs => rw [e]
  rw [mix_mul hb, mix_mul hb, Matrix.one_mul, Matrix.mul_one]

theorem mix_act_smul {A m n : Type} [CommRing A] [Fintype m] [Fintype n] {b : A}
    (hb : b * b = b) (X : Matrix m m A) (w : Matrix m n A) (Y : Matrix n n A) :
    b • (X * w * Y) = b • (X * (b • w) * Y) + (1 - b) • b • w := by
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul, hb, h2, zero_smul, add_zero]

end General

variable {D : D7}

theorem mt_gAt (V : HSp D) (p : Place D) (g : GA D V) :
    Formalism.L2.Theta.mt V (gAt V p g) =
      idem D p • Formalism.L2.Theta.mt V g + (1 - idem D p) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  classical
  cases p with
  | inl v =>
    refine mat_ext_ext_map (R'' := AF D.host.F) D.sp.cm.sig V.gram (GlobalTheory.AdelicU.evFin D.host.F v)
      (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v)
      (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl) (fun a => ?_) g
    refine Prod.ext (zero_mul _).symm (GlobalTheory.AdelicU.af_ext fun u => ?_)
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ u (GlobalTheory.AdelicU.singleFin v _) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ u (GlobalTheory.AdelicU.singleFin v 1 * a.2)
    rw [map_mul]
    by_cases e : u = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, GlobalTheory.AdelicU.evalV_singleFin_ne e, zero_mul]
  | inr τ =>
    refine mat_ext_ext_map (R'' := AF D.host.F) D.sp.cm.sig V.gram (GlobalTheory.AdelicU.evInf D.host.F (plTau D τ))
      (GlobalTheory.AutFunCompare.sgW (plTau D τ)) (GlobalTheory.AutFunCompare.sgW_mul _)
      (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm) (fun a => ?_) g
    refine Prod.ext (funext fun u => ?_) (zero_mul _).symm
    change (Pi.single (M := fun w : InfinitePlace D.host.F => w.Completion) (plTau D τ) (a.1 (plTau D τ))) u =
      (Pi.single (M := fun w : InfinitePlace D.host.F => w.Completion) (plTau D τ) 1) u * a.1 u
    by_cases e : u = plTau D τ
    · subst e
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne e, zero_mul]

theorem idem_mul_self (p : Place D) : idem D p * idem D p = idem D p := by
  cases p with
  | inl v =>
    change algebraMap (AF D.host.F) (AE D) _ * algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [← map_mul]
    refine congrArg _ (Prod.ext (mul_zero _) ?_)
    exact (GlobalTheory.AdelicU.singleFin_mul v 1 1).symm.trans (by rw [mul_one]; rfl)
  | inr τ =>
    change algebraMap (AF D.host.F) (AE D) _ * algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [← map_mul]
    refine congrArg _ (Prod.ext ?_ (mul_zero _))
    exact (GlobalTheory.AutFunCompare.sgW_mul (plTau D τ) 1 1).symm.trans (by rw [mul_one]; rfl)

theorem gAt_gAt_self (V : HSp D) (p : Place D) (g : GA D V) : gAt V p (gAt V p g) = gAt V p g := by
  cases p <;> simp [gAt]

theorem gAt_gAt_ne (V : HSp D) (p : Place D) (g : GA D V) (q : Place D) (h : q ≠ p) : gAt V q (gAt V p g) = 1 := by
  cases p with
  | inl v =>
    cases q with
    | inl u =>
      have e : u ≠ v := fun e => h (congrArg _ e)
      simp only [gAt]
      rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e, map_one]
    | inr ρ => simp [gAt]
  | inr τ =>
    cases q with
    | inl u => simp [gAt]
    | inr ρ =>
      have e : plTau D ρ ≠ plTau D τ := fun e => h (congrArg _ ((GlobalTheory.AdelicU.placeOf_bijective D).1 e))
      simp only [gAt]
      rw [GlobalTheory.AdelicU.projArch_embArch_ne _ _ e, map_one]

theorem actO_gAt (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T) :
    actO S T (gAt S p g) (gAt T p h) w = idem D p • actO S T g h w + (1 - idem D p) • w := by
  unfold actO
  rw [← gAt_inv, mt_gAt, mt_gAt]
  exact mix_act (idem_mul_self p) _ _ _

theorem wAt_actO (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T) :
    wAt p (actO S T g h w) = actO S T (gAt S p g) (gAt T p h) (wAt p w) := by
  rw [actO_gAt]
  exact mix_act_smul (idem_mul_self p) _ _ _

theorem gAt_laws : ∀ (D : D7), (∀ (V : HSp D) (p : Place D) (g : GA D V), Formalism.L2.Theta.mt V (gAt V p g) = idem D p • Formalism.L2.Theta.mt V g + (1 - idem D p) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ gAt V p (gAt V p g) = gAt V p g ∧ ∀ q, q ≠ p → gAt V q (gAt V p g) = 1) ∧ ∀ (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T), actO S T (gAt S p g) (gAt T p h) w = idem D p • actO S T g h w + (1 - idem D p) • w ∧ wAt p (actO S T g h w) = actO S T (gAt S p g) (gAt T p h) (wAt p w) :=
  fun _ => ⟨fun V p g => ⟨mt_gAt V p g, gAt_gAt_self V p g, gAt_gAt_ne V p g⟩,
    fun S T p g h w => ⟨actO_gAt S T p g h w, wAt_actO S T p g h w⟩⟩

end GlobalTheory.PlaceComponent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdicCompletionIntegersNormEqOneOfMulEqOne
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem adicCompletionIntegers_norm_eq_one_of_mul_eq_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletionIntegers F) (h : x * y = 1) : ‖(x : Fv F v)‖ = 1 := by
  have hx : ‖(x : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr x.2
  have hy : ‖(y : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr y.2
  have hxy : ‖(x : Fv F v)‖ * ‖(y : Fv F v)‖ = 1 := by
    rw [← norm_mul]
    have : ((x : Fv F v) * (y : Fv F v)) = 1 := by
      have := congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) h
      simpa using this
    rw [this, norm_one]
  have h0 := norm_nonneg (x : Fv F v)
  have h0' := norm_nonneg (y : Fv F v)
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData
section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.ChrTie

theorem unrAt_iff_and_val_eq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (UnrAt c w ↔ χ.UnrAt w) ∧ val c w = χ.val w :=
  fun _ _ _ h w => ⟨GlobalTheory.LFun.unrAt_iff_of_chrEq h w, GlobalTheory.LFun.val_eq_of_chrEq h w⟩

end GlobalTheory.ChrTie
end

