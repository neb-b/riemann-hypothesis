module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralSelfDualEqAdelicFourier
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0432
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicBoxCompact
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt

theorem properSpace_completion (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    ProperSpace w.Completion := by
  have hi := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have hce := hi.isClosedEmbedding
  refine ⟨fun x r => ?_⟩
  have e : Metric.closedBall x r = NumberField.InfinitePlace.Completion.extensionEmbedding w ⁻¹'
      Metric.closedBall (NumberField.InfinitePlace.Completion.extensionEmbedding w x) r := by
    ext y
    simp [Metric.mem_closedBall, hi.dist_eq]
  rw [e]
  exact hce.isCompact_preimage (isCompact_closedBall _ _)

theorem isCompact_boxF_one (F : Type) [Field F] [NumberField F] : IsCompact (boxF F 1) := by
  have h1 : IsCompact (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) := by
    haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion := fun w => properSpace_completion F w
    exact isCompact_univ_pi fun w => isCompact_closedBall 0 1
  have h2 := GroundTheory.Global.isCompact_integralFiniteAdeles F
  have e : boxF F 1 = (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := by
    ext a
    simp only [boxF, Set.mem_setOf_eq]
    change _ ↔ (a.1 ∈ (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ∧
      a.2 ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
    refine and_congr ⟨fun h => Set.mem_univ_pi.mpr fun w => ?_, fun h w => ?_⟩ Iff.rfl
    · simpa [Metric.mem_closedBall, dist_zero_right] using h w
    · simpa [Metric.mem_closedBall, dist_zero_right] using Set.mem_univ_pi.mp h w
  rw [e]
  exact h1.prod h2

theorem isCompact_boxE_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsCompact (boxE F E 1) := by
  set b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E) with hb
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := inferInstance
  have hK : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank F E) => boxF F 1) :=
    isCompact_univ_pi fun _ => isCompact_boxF_one F
  have hc : Continuous
      ((b.equivFun.symm : (Fin (Module.finrank F E) → AF F) →ₗ[AF F] AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have e : boxE F E 1 = b.equivFun.symm '' (Set.univ.pi fun _ => boxF F 1) := by
    ext x
    simp only [boxE, Set.mem_setOf_eq, Set.mem_image, Set.mem_univ_pi, ← hb]
    constructor
    · intro hx
      exact ⟨b.equivFun x, fun k => by rw [Module.Basis.equivFun_apply]; exact hx k,
        b.equivFun.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩ k
      have h : b.repr (b.equivFun.symm y) k = y k := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [h]
      exact hy k
  rw [e]
  exact hK.image hc

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsCompact (boxF F 1) ∧ IsCompact (boxE F E 1) := by
  intro F E _ _ _ _ _
  exact ⟨isCompact_boxF_one F, isCompact_boxE_one F E⟩

end GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicHaarSplitsAsArchTimesFinite
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord

section Coords

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def tupCrd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ (Fin n × Fin M × Fin d → R) where
  toFun X p := (Algebra.TensorProduct.basis R b).repr (X p.1 p.2.1) p.2.2
  invFun Y a i := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm fun k => Y (a, i, k)
  left_inv X := by
    funext a i
    exact (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm_apply_apply (X a i)
  right_inv Y := by
    funext p
    obtain ⟨a, i, k⟩ := p
    exact congrFun ((GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).apply_symm_apply fun k => Y (a, i, k)) k
  map_add' X Y := by
    funext p
    simp
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2.2).comp ((GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).continuous.comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1)))
  continuous_invFun := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    exact (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.continuous.comp
      (continuous_pi fun k => continuous_apply (a, i, k))

theorem tupCrd_apply (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) (X : Fin n → Fin M → R ⊗[F] E)
    (p : Fin n × Fin M × Fin d) :
    tupCrd R b n M X p = (Algebra.TensorProduct.basis R b).repr (X p.1 p.2.1) p.2.2 := rfl

end Coords

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem tupCrd_projInf {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    tupCrd (Ainf F) b n M (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projInf X) = fun p => (tupCrd (AF F) b n M X p).1 := by
  funext p
  rw [tupCrd_apply, tupCrd_apply]
  exact repr_map (fstA F) b (X p.1 p.2.1) p.2.2

theorem tupCrd_projFin {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    tupCrd (Af F) b n M (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projFin X) = fun p => (tupCrd (AF F) b n M X p).2 := by
  funext p
  rw [tupCrd_apply, tupCrd_apply]
  exact repr_map (sndA F) b (X p.1 p.2.1) p.2.2

def splitHomeo (F : Type) [Field F] [NumberField F] (ι : Type) :
    (ι → AF F) ≃ₜ (ι → Ainf F) × (ι → Af F) where
  toFun y := (fun i => (y i).1, fun i => (y i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv y := rfl
  right_inv p := rfl
  continuous_toFun :=
    (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
      (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun :=
    continuous_pi fun i => ((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)

end Split

theorem map_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure →
  ∃ (μ₁ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (μ₂ : Measure (Fin n → Fin M → Af F ⊗[F] E)) (c : ℝ≥0∞),
    μ₁.IsAddHaarMeasure ∧ μ₂.IsAddHaarMeasure ∧ SFinite μ₁ ∧ SFinite μ₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    dx.map (fun X => (projInf X, projFin X)) = c • μ₁.prod μ₂ := by
  intro F E _ _ _ _ _ σ hCM M n dx hdx
  have h2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasis F E
  obtain ⟨tA, -, sA, -, -, -, -, hBA, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  obtain ⟨tI, -, sI, -, -, -, -, hBI, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
  obtain ⟨tF, -, sF, -, -, -, -, hBF, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)
  haveI := hBA n M
  haveI := hBI n M
  haveI := hBF n M
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let ι := Fin n × Fin M × Fin (Module.finrank F E)
  let e := tupCrd (AF F) b n M
  let eI := tupCrd (Ainf F) b n M
  let eF := tupCrd (Af F) b n M
  let eA : (Fin n → Fin M → AF F ⊗[F] E) ≃+ (ι → AF F) := e
  have hm : (dx.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map dx eA e.continuous e.symm.continuous
  let m₁ : Measure (ι → Ainf F) := Measure.addHaar
  let m₂ : Measure (ι → Af F) := Measure.addHaar
  haveI : m₁.IsAddHaarMeasure := by dsimp only [m₁]; infer_instance
  haveI : m₂.IsAddHaarMeasure := by dsimp only [m₂]; infer_instance
  haveI : SFinite m₁ := by dsimp only [m₁]; infer_instance
  haveI : SFinite m₂ := by dsimp only [m₂]; infer_instance
  obtain ⟨c, -, hcT, hc⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod F ι (dx.map e) m₁ m₂ hm inferInstance inferInstance
  let S := splitHomeo F ι
  let H : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ
      (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) :=
    e.toHomeomorph.trans (S.trans (eI.symm.toHomeomorph.prodCongr eF.symm.toHomeomorph))
  have hH : (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) = H := by
    funext X
    refine Prod.ext ?_ ?_
    · show _ = eI.symm (fun i => (e X i).1)
      rw [show (fun i => (e X i).1) = eI (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projInf X) from (tupCrd_projInf b X).symm]
      exact (eI.symm_apply_apply _).symm
    · show _ = eF.symm (fun i => (e X i).2)
      rw [show (fun i => (e X i).2) = eF (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.projFin X) from (tupCrd_projFin b X).symm]
      exact (eF.symm_apply_apply _).symm
  have hc' : (dx.map e).map S = c • m₁.prod m₂ := hc
  have he : Measurable e := e.continuous.measurable
  have hPI : Measurable eI.symm := eI.symm.continuous.measurable
  have hPF : Measurable eF.symm := eF.symm.continuous.measurable
  refine ⟨m₁.map eI.symm, m₂.map eF.symm, c, ?_, ?_, inferInstance, inferInstance, hcT, ?_, ?_⟩
  · let eIA : (ι → Ainf F) ≃+ (Fin n → Fin M → Ainf F ⊗[F] E) := eI.symm
    exact AddEquiv.isAddHaarMeasure_map m₁ eIA eI.symm.continuous eI.continuous
  · let eFA : (ι → Af F) ≃+ (Fin n → Fin M → Af F ⊗[F] E) := eF.symm
    exact AddEquiv.isAddHaarMeasure_map m₂ eFA eF.symm.continuous eF.continuous
  · rw [hH]
    exact H.measurableEmbedding
  · rw [hH, Measure.map_prod_map m₁ m₂ hPI hPF, ← Measure.map_smul, ← hc',
      Measure.map_map (hPI.prodMap hPF) S.continuous.measurable,
      Measure.map_map ((hPI.prodMap hPF).comp S.continuous.measurable) he]
    rfl
    exact (hPI.prodMap hPF).aemeasurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicTensorRationalApproximation
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet

theorem exists_nsmul_sub_mem {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (S : AddSubgroup G) (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ S, x - γ ∈ K)
    (V : Set G) (hV : V ∈ nhds (0 : G)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ b : G, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧ ∃ γ ∈ S, q • b - γ ∈ V := by
  open scoped Pointwise in
  obtain ⟨W, hWo, hW0, hWV⟩ := exists_open_nhds_zero_half hV
  set U : Set G := W ∩ -W with hUdef
  have hUo : IsOpen U := hWo.inter hWo.neg
  have hU0 : (0 : G) ∈ U := ⟨hW0, by simpa using hW0⟩
  have hUV : ∀ v ∈ U, ∀ w ∈ U, v - w ∈ V := by
    intro v hv w hw
    rw [sub_eq_add_neg]
    exact hWV v hv.1 (-w) (by simpa using hw.2)
  obtain ⟨t, ht⟩ := compact_covered_by_add_left_translates (V := U) hK
    (by rw [hUo.interior_eq]; exact ⟨0, hU0⟩)
  refine ⟨t.card + 1, le_add_self, fun b => ?_⟩
  have hx : ∀ m : Fin (t.card + 2), ∃ γ ∈ S, ∃ g ∈ t, g + (((m : ℕ) + 1) • b - γ) ∈ U := by
    intro m
    obtain ⟨γ, hγ, hγK⟩ := hcov (((m : ℕ) + 1) • b)
    have := ht hγK
    simp only [Set.mem_iUnion, Set.mem_preimage] at this
    obtain ⟨g, hg, hgU⟩ := this
    exact ⟨γ, hγ, g, hg, hgU⟩
  choose γ hγ g hg hgU using hx
  obtain ⟨i, j, hij, hg_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (t.card + 2) => (⟨g m, hg m⟩ : t)) (by simp)
  simp only [Subtype.mk.injEq] at hg_eq
  have key : ∀ i j : Fin (t.card + 2), (i : ℕ) < j → g i = g j →
      ∃ q : ℕ, 1 ≤ q ∧ q ≤ t.card + 1 ∧ ∃ γ' ∈ S, q • b - γ' ∈ V := by
    intro i j hlt hgij
    refine ⟨(j : ℕ) - i, by omega, by omega, γ j - γ i, S.sub_mem (hγ j) (hγ i), ?_⟩
    have h := hUV _ (hgU j) _ (hgU i)
    have e : (j : ℕ) + 1 = ((j : ℕ) - i) + ((i : ℕ) + 1) := by omega
    rw [e, add_nsmul, hgij] at h
    convert h using 1
    abel
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i j h hg_eq
  · exact key j i h hg_eq.symm

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem boxF_mem_nhds {ε : ℝ} (hε : 0 < ε) : boxF F ε ∈ nhds (0 : AF F) := by
  have hopen : IsOpen ({a : AF F | (∀ w : InfinitePlace F, ‖a.1 w‖ < ε)} ∩
      {a : AF F | a.2 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}) := by
    refine IsOpen.inter ?_ ?_
    · simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun w =>
        isOpen_lt (continuous_norm.comp ((continuous_apply w).comp continuous_fst)) continuous_const
    · exact GroundTheory.Global.isOpen_integralFiniteAdeles.preimage continuous_snd
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨fun w => ?_, (zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F) : _)⟩) ?_
  · show ‖(0 : AF F).1 w‖ < ε
    rw [show (0 : AF F).1 w = 0 from rfl, norm_zero]; exact hε
  · rintro a ⟨h1, h2⟩
    exact ⟨fun w => (h1 w).le, h2⟩

theorem repr_inclR (c : E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr (inclR (F := F) (AF F) c) k =
      algebraMap F (AF F) ((Module.finBasis F E).repr c k) := by
  have : inclR (F := F) (AF F) c = (1 : AF F) ⊗ₜ[F] c := rfl
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem exists_compact_pi (d : ℕ) :
    ∃ K : Set (Fin d → AF F), IsCompact K ∧ ∀ x : Fin d → AF F, ∃ f : Fin d → F,
      (x - fun k => algebraMap F (AF F) (f k)) ∈ K := by
  obtain ⟨C, hC, hx⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
  refine ⟨Set.univ.pi fun _ => C ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _),
    isCompact_univ_pi fun _ => hC.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F), fun x => ?_⟩
  choose f hf using fun k => hx (x k)
  exact ⟨f, fun k _ => hf k⟩

theorem dirichlet (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, 1 ≤ N ∧ ∀ b : AF F ⊗[F] E, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧
    ∃ c : E, (q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c ∈ boxE F E ε := by
  set d := Module.finrank F E
  let S : AddSubgroup (Fin d → AF F) :=
    (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom (Fin d)).range
  obtain ⟨K, hK, hcov⟩ := exists_compact_pi F d
  have hV : (Set.univ.pi fun _ : Fin d => boxF F ε) ∈ nhds (0 : Fin d → AF F) :=
    set_pi_mem_nhds Set.finite_univ fun _ _ => boxF_mem_nhds F hε
  obtain ⟨N, hN, hb⟩ := exists_nsmul_sub_mem S K hK
    (fun x => by
      obtain ⟨f, hf⟩ := hcov x
      exact ⟨_, ⟨f, rfl⟩, hf⟩) _ hV
  refine ⟨N, hN, fun b => ?_⟩
  set B := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  obtain ⟨q, hq1, hqN, γ, ⟨f, rfl⟩, hmem⟩ := hb (fun k => B.repr b k)
  refine ⟨q, hq1, hqN, (Module.finBasis F E).equivFun.symm f, fun k => ?_⟩
  have hk := hmem k (Set.mem_univ _)
  rw [← nsmul_eq_mul, map_sub, map_nsmul, Finsupp.sub_apply, Finsupp.smul_apply, repr_inclR]
  have hc : (Module.finBasis F E).repr ((Module.finBasis F E).equivFun.symm f) k = f k := by
    have := congrFun ((Module.finBasis F E).equivFun.apply_symm_apply f) k
    rwa [Module.Basis.equivFun_apply] at this
  rw [hc]
  simpa using hk

end GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicVectorIntegralProduct
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff.Split

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def rowEquiv (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ) :
    (Fin k → InfiniteAdeleRing E) ≃ᵐ (Fin k → Cinf E) :=
  MeasurableEquiv.piCongrRight fun _ =>
    { toEquiv := (infEq E).symm.toEquiv
      measurable_toFun := (GlobalTheory.CuspRep.GASplit.continuous_infEq_symm E).measurable
      measurable_invFun := (continuous_infEq E).measurable }

theorem nuInf_eq (k : ℕ) :
    nuInf E k = (Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).map (rowEquiv E k) := rfl

theorem integral_split {k : ℕ} (A : (Fin k → Cinf E) → ℂ) (B : (Fin k → Af E) → ℂ) :
    ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) =
      (∫ x, A x ∂nuInf E k) * ∫ f, B f ∂nuFin E k := by
  have hmp := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)
    (fun _ => GroundTheory.Global.infiniteAdeleMeasure E) (fun _ => GroundTheory.Global.finiteAdeleMeasure E)
  haveI : SFinite (nuFin E k) := by unfold nuFin; infer_instance
  have e : (fun y : Fin k → Ad E => A (fun i => pInf E (y i)) * B (fun i => pFin E (y i))) =
      fun x => (A ∘ rowEquiv E k) ((MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)) x).1 *
        B ((MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)) x).2 := by
    funext y
    rfl
  have h1 : ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) =
      ∫ z, (A ∘ rowEquiv E k) z.1 * B z.2 ∂((Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).prod
        (nuFin E k)) := by
    rw [e]
    exact (hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun z => (A ∘ rowEquiv E k) z.1 * B z.2))
  rw [h1, integral_prod_mul, nuInf_eq, integral_map_equiv]
  rfl

end GlobalTheory.CompanionTheory.CutOff.Split
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterRealPairing
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.JSPair

def dotL (E : Type) [Field E] [NumberField E] (k : ℕ) :
    (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] Cinf E :=
  ∑ i : Fin k, (ContinuousLinearMap.mul ℝ (Cinf E)).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)

theorem dotL_apply {E : Type} [Field E] [NumberField E] {k : ℕ} (x z : Fin k → Cinf E) :
    dotL E k x z = ∑ i, x i * z i := by
  simp [dotL, ContinuousLinearMap.sum_apply]

theorem exists_pairing : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  intro E _ _ _ k ψ h8 hψ
  obtain ⟨l, hl⟩ := h8 (InfinitePlace E) (GlobalTheory.CompanionTheory.JSInfStep.chiInf ψ)
    (hψ.cont.comp GlobalTheory.CompanionTheory.JSInfStep.continuous_sInf) (fun z => hψ.norm _)
  let β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (Fin k → Cinf E) (Cinf E) ℝ (-l)) ∘L dotL E k
  have hβ : ∀ x z, β x z = -l (∑ i, x i * z i) := fun x z => by
    simp [β, dotL_apply]
  refine ⟨β, fun y hy => ?_, fun x z => ?_⟩
  · funext i
    refine GlobalTheory.CompanionTheory.JSInfStep.chiInf_nondeg hψ (y i) fun w => ?_
    have h0 := hy (Pi.single i w)
    rw [hβ] at h0
    have e : ∑ j, (Pi.single i w : Fin k → Cinf E) j * y j = y i * w := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_comm]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · simp
    rw [e] at h0
    have h1 : l (y i * w) = 0 := neg_eq_zero.1 h0
    rw [hl, h1]
    simp
  · have := hl (∑ i, x i * z i)
    rw [GlobalTheory.CompanionTheory.JSInfStep.chiInf_apply] at this
    rw [this, hβ]
    simp

end GlobalTheory.CompanionTheory.JSPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardComapMulCardKerMulCardEq
section
namespace GlobalTheory.CompanionTheory.Counting

theorem card_comap_mul_card_ker_mul_card_eq :
    ∀ (n : ℕ) [NeZero n] (H H' P P' : Type) [AddCommGroup H] [Module (ZMod n) H] [Finite H] [AddCommGroup H'] [Module (ZMod n) H'] [Finite H'] [AddCommGroup P] [Module (ZMod n) P] [Finite P] [AddCommGroup P'] [Module (ZMod n) P'] [Finite P'] (B : P' →ₗ[ZMod n] P →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ (loc : H →ₗ[ZMod n] P) (loc' : H' →ₗ[ZMod n] P'), LinearMap.range loc = (⨅ y ∈ LinearMap.range loc', LinearMap.ker (B y)) → ∀ L : Submodule (ZMod n) P, Nat.card ↥(L.comap loc) * Nat.card ↥(LinearMap.ker loc') * Nat.card P = Nat.card ↥((⨅ x ∈ L, LinearMap.ker (B.flip x)).comap loc') * Nat.card H * Nat.card ↥L := by
  intro n _ H H' P P' _ _ _ _ _ _ _ _ _ _ _ _ B hB hB' loc loc' hR L
  have e1 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H P loc L
  have e2 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H' P' loc'
    (⨅ x ∈ L, LinearMap.ker (B.flip x))
  have e3 := card_eq_card_ker_mul_card_range (ZMod n) H P loc
  have hflip : B.flip.flip = B := LinearMap.flip_flip B
  have hdd := GlobalTheory.T.double_annihilator_eq_self n P' P B.flip hB' (by rw [hflip]; exact hB) (LinearMap.range loc')
  rw [hflip, ← hR] at hdd
  have e4 := GlobalTheory.T.annihilator_intersection_card n P P' B hB hB' (LinearMap.range loc) L
  rw [hdd] at e4
  rw [e1, e2, e3]
  have key : Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card P * Nat.card ↥(LinearMap.range loc ⊓ L)) =
      Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card ↥(LinearMap.range loc' ⊓ ⨅ x ∈ L, LinearMap.ker (B.flip x)) *
        Nat.card ↥(LinearMap.range loc) * Nat.card ↥L) := by
    rw [e4]
  linarith [key]

end GlobalTheory.CompanionTheory.Counting
end

