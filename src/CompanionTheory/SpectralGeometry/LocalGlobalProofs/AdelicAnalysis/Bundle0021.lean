module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0005
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import GroundTheory.GlobalFields.LocalAtPlace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxLatticeCountRatio
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Pack

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def intSub {d M : ℕ} (b : Module.Basis (Fin d) F E) {Λ : Type} [AddCommGroup Λ]
    (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) : AddSubgroup Λ where
  carrier := {l | ∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin (e l)) a i) ∈ latV b v}
  zero_mem' := by
    intro v a i k
    simp [projV, projFin]
  add_mem' := by
    intro x y hx hy v a i k
    have h := add_mem (hx v a i k) (hy v a i k)
    simpa [projV, projFin, mul_add, map_add (f := _)] using h
  neg_mem' := by
    intro x hx v a i k
    have h := neg_mem (hx v a i k)
    simpa [projV, projFin, mul_neg, map_neg] using h

def coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin 1 → Fin M → AF F ⊗[F] E) →+ PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ) :=
  AddMonoidHom.mk' (fun X => WithLp.toLp 1 fun p =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal p.2.2.2)
      ((Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X p.1 p.2.1) p.2.2.1 p.2.2.2)) (by
    intro X Y
    ext p
    simp only [projInf, map_add (f := _), Pi.add_apply, Finsupp.coe_add, PiLp.add_apply]
    exact map_add _ _ _)

theorem norm_coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ‖coord hF b X‖ = sizeTup b (projInf X) := by
  rw [PiLp.norm_eq_of_L1]
  simp only [sizeTup, sizeInf, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun v _ => ?_
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).norm_map_of_map_zero
    (map_zero _) _

theorem finrank_coord (hF : IsTotallyReal F) (d M : ℕ) :
    Module.finrank ℝ (PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ)) =
      d * Module.finrank ℚ F * M := by
  have h : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    simp only [IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
    omega
  rw [(WithLp.linearEquiv 1 ℝ _).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_prod, Fintype.card_fin, h]
  ring

theorem box_packing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) * ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l) := by
  intro F E _ _ _ _ _ σ hσ d b M Λ _ e N r R hr hrR
  obtain ⟨hF, -, h2, -⟩ := hσ
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have key := _root_.GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing (PiLp 1 (fun _ : Fin 1 × Fin M × Fin 2 × InfinitePlace F => ℝ)) (intSub b e N)
    ((coord hF b).comp (e.comp (intSub b e N).subtype)) r R hr hrR
  rw [finrank_coord hF 2 M] at key
  have conv : ∀ t : ℝ, ∑' l : Λ, (Set.indicator (box b N t) (fun _ => (1 : ℝ≥0∞))) (e l) =
      ∑' l : intSub b e N, Set.indicator {l : intSub b e N |
        ‖((coord hF b).comp (e.comp (intSub b e N).subtype)) l‖ ≤ t} (fun _ => (1 : ℝ≥0∞)) l := by
    intro t
    have h := tsum_subtype ((intSub b e N : AddSubgroup Λ) : Set Λ)
      (fun l => Set.indicator {l : Λ | sizeTup b (projInf (e l)) ≤ t} (fun _ => (1 : ℝ≥0∞)) l)
    refine Eq.trans ?_ (Eq.trans h.symm ?_)
    · refine tsum_congr fun l => ?_
      have hb : e l ∈ box b N t ↔ l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ) ∧
          l ∈ {l : Λ | sizeTup b (projInf (e l)) ≤ t} := Iff.rfl
      by_cases hm : e l ∈ box b N t
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hb.1 hm).1, Set.indicator_of_mem (hb.1 hm).2]
      · rw [Set.indicator_of_notMem hm]
        by_cases h1 : l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ)
        · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem fun h => hm (hb.2 ⟨h1, h⟩)]
        · rw [Set.indicator_of_notMem h1]
    · refine tsum_congr fun l => ?_
      simp [Set.indicator, norm_coord]
  rw [conv R, conv r]
  exact key

end GlobalTheory.CompanionTheory.SW.Pack
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MeasProj

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

theorem repr_map {d : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]

theorem continuous_mapTens {d : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map f (AlgHom.id F E) : R ⊗[F] E → S ⊗[F] E) := by
  rw [(TopK.isHomeomorph_coord S b).isInducing.continuous_iff]
  refine continuous_pi fun k => ?_
  simp only [Function.comp_def, repr_map]
  exact hf.comp ((continuous_apply k).comp (TopK.isHomeomorph_coord R b).continuous)

theorem continuous_mapTup {d n M : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (fun (X : Fin n → Fin M → R ⊗[F] E) (a : Fin n) (i : Fin M) =>
      Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_mapTens b f hf).comp ((continuous_apply i).comp (continuous_apply a))


omit [IsTopologicalRing S] [TopologicalSpace S] [CommRing S] [Algebra F S] in
def tupHomeo {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → R) :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => TopK.coordHomeo R b

end Gen

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

theorem continuous_sndA : Continuous (sndA F) := continuous_snd

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval v

theorem coord_projInf {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).1 :=
  repr_map b (fstA F) _ k

theorem coord_projFin {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Af F) b).repr (projFin X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 :=
  repr_map b (sndA F) _ k

theorem coord_projV {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Af F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v X a i) k =
      ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k) v :=
  repr_map b (evalV F v) _ k

theorem latV_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      tupHomeo b n M ⁻¹' (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
        (v.adicCompletionIntegers F : Set (Fv F v))) := by
  ext Y
  simp only [latV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  rfl

theorem isCompact_latV {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  rw [latV_eq, (tupHomeo b n M).isCompact_preimage]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc

theorem isOpen_latV {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  rw [latV_eq]
  refine IsOpen.preimage (tupHomeo b n M).continuous ?_
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => ho

theorem projV_mem_latV_iff {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ↔
      ∀ a i k, ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k) v ∈
        v.adicCompletionIntegers F := by
  simp only [latV, Set.mem_setOf_eq, coord_projV]

end Adelic

section Adelic2

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isOpen_intOff {d n M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := by
  have hA : IsOpen {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v => v ∉ S)
  have hE : (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k,
      (fun X : Fin n → Fin M → AF F ⊗[F] E =>
        sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k)) ⁻¹'
        {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
    ext X
    simp only [intOff, Set.mem_setOf_eq, projV_mem_latV_iff, coord_projFin, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h a i k v hv => h v hv a i k, fun h v hv a i k => h a i k v hv⟩
  rw [hE]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun k => hA.preimage (continuous_sndA.comp ?_)
  exact (continuous_apply k).comp ((TopK.isHomeomorph_coord (AF F) b).continuous.comp
    ((continuous_apply i).comp (continuous_apply a)))

theorem eventually_mem_latV {d n M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, projV v X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  simp only [projV_mem_latV_iff, Filter.eventually_all]
  intro a i k
  exact ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k).2

theorem ext_proj {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X Y : Fin n → Fin M → AF F ⊗[F] E)
    (h1 : projInf X = projInf Y) (h2 : ∀ v, projV v (projFin X) = projV v (projFin Y)) : X = Y := by
  funext a i
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext k
  refine Prod.ext (α := Ainf F) (β := Af F) ?_ ?_
  · rw [← coord_projInf, ← coord_projInf, h1]
  · refine Subtype.ext (funext fun v => ?_)
    have e : ∀ T : Fin n → Fin M → AF F ⊗[F] E, ((Algebra.TensorProduct.basis (AF F) b).repr (T a i) k).2 v =
        (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin T) a i) k := fun T => by
      rw [coord_projV, coord_projFin]
    have h3 : (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
        (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin Y) a i) k := by rw [h2 v]
    exact (e X).trans (h3.trans (e Y).symm)

def glueFin (z : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in Filter.cofinite, z v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨z, h⟩ : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)

theorem exists_glue {d n M : ℕ} (b : Module.Basis (Fin d) F E) (Y : Fin n → Fin M → Ainf F ⊗[F] E)
    (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E))
    (hZ : ∀ᶠ v in Filter.cofinite, Z v ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v := by
  have ev : ∀ a i k, ∀ᶠ v in Filter.cofinite,
      (Algebra.TensorProduct.basis (Fv F v) b).repr (Z v a i) k ∈ v.adicCompletionIntegers F :=
    fun a i k => hZ.mono fun v hv => hv a i k
  let x : Fin n → Fin M → Fin d → AF F := fun a i k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k)
      (glueFin (fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Z v a i) k) (ev a i k))
  let X : Fin n → Fin M → AF F ⊗[F] E := fun a i =>
    (Algebra.TensorProduct.basis (AF F) b).equivFun.symm (x a i)
  have hX : ∀ a i k, (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k = x a i k := fun a i k =>
    congrFun ((Algebra.TensorProduct.basis (AF F) b).equivFun.apply_symm_apply (x a i)) k
  refine ⟨X, ?_, fun v => ?_⟩
  · funext a i
    apply (Algebra.TensorProduct.basis (Ainf F) b).repr.injective
    ext k
    rw [coord_projInf, hX]
    rfl
  · funext a i
    apply (Algebra.TensorProduct.basis (Fv F v) b).repr.injective
    ext k
    rw [coord_projV, coord_projFin, hX]
    rfl

theorem continuous_sizeTup {d n M : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
  unfold sizeTup sizeInf
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => continuous_norm.comp ?_
  exact (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v).comp
    ((continuous_apply k).comp ((TopK.isHomeomorph_coord (Ainf F) b).continuous.comp
      ((continuous_apply i).comp (continuous_apply a))))

end Adelic2

theorem proj_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), Continuous (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ Continuous (projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ (∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _)) ∧ (∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) ∧ (∀ S, IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ X : (Fin n → Fin M → Af F ⊗[F] E), ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v) ∧ (∀ X Y : (Fin n → Fin M → AF F ⊗[F] E), projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ (Y : (Fin n → Fin M → Ainf F ⊗[F] E)) (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ᶠ v in Filter.cofinite, Z v ∈ latV b v) → ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v) ∧ Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
  intro F E _ _ _ _ _ σ _ d b n M
  exact ⟨continuous_mapTup b (fstA F) continuous_fstA, continuous_mapTup b (sndA F) continuous_sndA,
    fun v => continuous_mapTup b (evalV F v) (continuous_evalV v),
    fun v => ⟨isCompact_latV b v, isOpen_latV b v⟩, fun S => isOpen_intOff b S,
    fun X => eventually_mem_latV b X, fun X Y => ext_proj b X Y,
    fun Y Z h => exists_glue b Y Z h, continuous_sizeTup b⟩

end GlobalTheory.CompanionTheory.SW.MeasProj
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompact
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TopH

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hform_mulVec {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (J g : Matrix (Fin m) (Fin m) A)
    (hg : cT σ g * J * g = J) (x y : Fin m → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have key : ∀ x y : Fin m → A, hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [key, key, hs]
  conv_lhs => rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  congr 1
  change cT σ g *ᵥ (J *ᵥ (g *ᵥ y)) = J *ᵥ y
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

theorem isClosed_HR [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] (σ : E →ₐ[F] E) (hs : Continuous (sigR R σ)) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
  have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val
  have hc : Continuous fun g : GL (Fin M) (R ⊗[F] E) =>
      cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) _) := by
    refine ((Continuous.matrix_transpose (Continuous.matrix_map hv hs)).matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const

end

theorem topH_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalGroup (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) ∧ BorelSpace (HA R σ J) ∧ ∀ n : ℕ, (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, actW R σ J 1 X = X) ∧ (∀ (g h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), actW R σ J (g * h) X = actW R σ J g (actW R σ J h X)) ∧ ∀ (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ J (actW R σ J h X) = gramR R σ J X := by
  intro F E _ _ _ _ _ σ hCM M J _ R _ _ _ _ _ _ _
  obtain ⟨h1, h2, h3, h4, hs, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  haveI : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin M) (R ⊗[F] E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hcl := isClosed_HR R σ hs J
  haveI g1 : IsTopologicalGroup (HR R σ J) := inferInstance
  haveI g2 : LocallyCompactSpace (HR R σ J) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI g3 : SecondCountableTopology (HR R σ J) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI g4 : T2Space (HR R σ J) := inferInstance
  refine ⟨g1, g2, g3, g4, ⟨rfl⟩, fun n => ⟨?_, ?_, ?_, ?_⟩⟩
  · have hm : Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) =>
        ((HA.mat R σ J p.1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
    exact continuous_pi fun a => hm.matrix_mulVec ((continuous_apply a).comp continuous_snd)
  · intro X
    funext a
    exact Matrix.one_mulVec (X a)
  · intro g h X
    funext a
    change ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * (HA.mat R σ J h : Matrix (Fin M) (Fin M) _)) *ᵥ X a = _
    exact (Matrix.mulVec_mulVec _ _ _).symm
  · intro h X
    funext a b
    exact hform_mulVec (sigR R σ) (JR R J) _ h.2 (X a) (X b)

end GlobalTheory.CompanionTheory.SW.TopH
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerate
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem det_blockOne_eq_mul {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hsub : (Matrix.of (Fin.cons (Fin.cons t fun _ ↦ 0) fun i ↦ Fin.cons 0 (A i)) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) K).submatrix Fin.succ Fin.succ = A := by
    ext i j
    simp
  simp [blockOne, hsub]

theorem isHermND_blockOne_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  intro F E _ _ _ _ _ σ M J hJ t ht
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne]
    · simp [blockOne]
    · simp [blockOne]
    · simpa [blockOne] using hJ.1 i j
  · rw [det_blockOne_eq_mul]
    exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ClosedSubgroupQuotientMeasure
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

noncomputable def closedEmbeddingRangeEquiv {G G₁ : Type} [Group G] [TopologicalSpace G]
    [Group G₁] [TopologicalSpace G₁] (ι : G₁ →* G) (hι : IsClosedEmbedding ι) :
    G₁ ≃ₜ* ι.range :=
  have hemb : IsEmbedding ι.rangeRestrict :=
    IsEmbedding.of_comp (hι.continuous.subtype_mk _) continuous_subtype_val hι.isEmbedding
  { MulEquiv.ofBijective ι.rangeRestrict
      ⟨hemb.injective, ι.rangeRestrict_surjective⟩ with
    continuous_toFun := hemb.continuous
    continuous_invFun :=
      (hemb.toHomeomorphOfSurjective ι.rangeRestrict_surjective).symm.continuous }

theorem exists_weight_mass_one_right_coset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by
  intro G _ _ _ _ _ _ _ _ G₁ _ _ _ _ _ _ _ ι hι μ₁ _ _
  have hclosed : IsClosed ((ι.range : Subgroup G) : Set G) := by
    rw [MonoidHom.coe_range]; exact hι.isClosed_range
  let e : G₁ ≃ₜ* ι.range := closedEmbeddingRangeEquiv ι hι
  haveI : IsFiniteMeasureOnCompacts μ₁.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  haveI : μ₁.inv.IsOpenPosMeasure :=
    ⟨fun U hU hne => by
      rw [Measure.inv_apply]; exact hU.inv.measure_ne_zero μ₁ hne.inv⟩
  haveI hinv : μ₁.inv.IsHaarMeasure := {}
  have hν : (μ₁.inv.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ₁.inv e
  obtain ⟨β, hβ, hmass⟩ := PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat G ι.range hclosed _ hν
  refine ⟨fun g => β g⁻¹, hβ.comp measurable_inv, fun g => ?_⟩
  have hem : Measurable e := e.continuous.measurable
  have hf : Measurable fun h : ι.range => β (g⁻¹ * (h : G)) :=
    hβ.comp (measurable_const.mul measurable_subtype_coe)
  have h1 := hmass g⁻¹
  have hcomp : Measurable fun a : G₁ => β (g⁻¹ * (e a : G)) := hf.comp hem
  rw [lintegral_map hf hem, Measure.inv, lintegral_map hcomp measurable_inv] at h1
  refine Eq.trans (lintegral_congr fun u => ?_) h1
  have : ((e u⁻¹ : ι.range) : G) = (ι u)⁻¹ := by
    show ι u⁻¹ = _
    exact map_inv ι u
  show β (ι u * g)⁻¹ = β (g⁻¹ * ((e u⁻¹ : ι.range) : G))
  rw [this, mul_inv_rev]

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExistsStatement
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_family_eq_on_open_subset : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B B' : Set X), IsOpen B → IsOpen B' → B' ⊆ B → ∀ fib fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib' → ∀ b ∈ B', fib' b = fib b := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq | exact GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq | (intros; apply GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq <;> assumption)
end

