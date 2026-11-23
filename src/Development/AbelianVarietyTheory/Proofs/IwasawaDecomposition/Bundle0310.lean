module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedDatumNeZeroIffDoubleCoset
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreCompatibleAdelicDataCharacters
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

theorem exists_tieIn_reCore : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → FrameKs T.Q.c.F R.MW → ∃ dict mu chiW x₀, TieIn (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) ∧ LawsCore (reCore T dict mu chiW x₀ T.cE).toCore := by
  intro D G _ _ Pl0 T0 A T _ R hvol hJ hC ha hlev hval hfr
  obtain ⟨chiW, hchi, hchi'⟩ := _root_.GlobalTheory.ConjRefChar.exists_chiAt D G Pl0 T0 A T R hJ.pins ha hlev hval
  obtain ⟨x₀, hx, hx'⟩ := _root_.GlobalTheory.RealGeo.BaseFrame.exists_baseFrame D G Pl0 T0 A T R hJ ha hfr
  obtain ⟨mu, hJ1, hC1⟩ := _root_.GlobalTheory.RealGeo.exists_mu_reCore D T chiW hJ hC hchi'
  obtain ⟨dict, hJ2, hC2⟩ := GlobalTheory.T.exists_dictionary_core_laws_baseFrame_change D (reCore T T.dict mu chiW T.x₀ T.cE) x₀ hvol hJ1 hC1 hx'
  exact ⟨dict, mu, chiW, x₀, tieIn_top (reCore T dict mu chiW x₀ T.cE) R hJ2 ha
    (_root_.GlobalTheory.LowSmooth.lowSm_MW D G Pl0 T0 A T.Q.c.F R) hchi hx, hC2⟩

end GlobalTheory.RealGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicUnramifiedCompletedIntegers
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CycClosure

variable {l : ℕ} [Fact l.Prime]

theorem mem_clC {F : IntermediateField ℚ_[l] (PadicAlgCl l)} {x : ℂ_[l]} :
    x ∈ clC l F ↔ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖x‖ ≤ 1 := by
  simp only [clC, Subring.mem_inf]
  apply and_congr Iff.rfl
  change x ∈ PadicComplexInt l ↔ _
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem coe_clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    (clC l F : Set ℂ_[l]) =
      closure ((fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1}) := by
  have hc : IsClopen (Metric.closedBall (0 : ℂ_[l]) 1) :=
    IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have e : (fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1} =
      (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∩ Metric.closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, h⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [mem_closedBall_zero_iff, PadicComplex.norm_extends]; exact h⟩
    · rintro ⟨⟨y, hy, rfl⟩, h⟩
      rw [mem_closedBall_zero_iff] at h
      exact ⟨y, ⟨hy, by rw [← PadicComplex.norm_extends]; exact h⟩, rfl⟩
  rw [e]
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, mem_clC] at hx
    exact hc.isOpen.closure_inter ⟨hx.1, by simpa using hx.2⟩
  · intro x hx
    have := closure_inter_subset_inter_closure _ _ hx
    rw [hc.isClosed.closure_eq] at this
    exact mem_clC.2 ⟨this.1, by simpa using this.2⟩

theorem clC_mono {F G : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : F ≤ G) {x : ℂ_[l]}
    (hx : x ∈ clC l F) : x ∈ clC l G :=
  mem_clC.2 ⟨closure_mono (Set.image_mono h) (mem_clC.1 hx).1, (mem_clC.1 hx).2⟩

theorem clC_props (LL : Loc.FinExt l) (F : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hF : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = F) :
    ∃ _ : IsDiscreteValuationRing ↥(clC l F),
      IsAlgClosed (IsLocalRing.ResidueField ↥(clC l F)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l F)) ↥(clC l F) ∧
      IsAdic (IsLocalRing.maximalIdeal ↥(clC l F)) ∧
      (∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) := by
  subst hF
  obtain ⟨O, hdvr, -, -, hdiv, hres, hcomp, hadic, hO⟩ := GlobalTheory.BigInt.exists_integers_completion l LL
  have e : O = clC l (LL.1 ⊔ Loc.MaximalUnramifiedExtension l) := SetLike.coe_injective (hO.trans (coe_clC _).symm)
  subst e
  exact ⟨hdvr, hres, hcomp, hadic, hdiv⟩

theorem muK_spec (k : ℕ) : FiniteDimensional ℚ_[l] ↥(muK l k) ∧
    ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ (l ^ k) ∧ muK l k = IntermediateField.adjoin ℚ_[l] {ζ} := by
  have hn : 0 < l ^ k := pow_pos (Fact.out : l.Prime).pos k
  haveI : NeZero (l ^ k) := ⟨hn.ne'⟩
  classical
  have hfin : ({x | x ^ (l ^ k) = 1} : Set (PadicAlgCl l)).Finite := by
    refine (Polynomial.nthRoots (l ^ k) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hx
  haveI := hfin.to_subtype
  refine ⟨IntermediateField.finiteDimensional_adjoin fun x hx =>
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [show x ^ (l ^ k) = 1 from hx]⟩, ?_⟩
  have hdeg : (cyclotomic (l ^ k) (PadicAlgCl l)).degree ≠ 0 := by
    rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have hp : IsPrimitiveRoot ζ (l ^ k) := (isRoot_cyclotomic_iff).1 hζ
  refine ⟨ζ, hp, le_antisymm ?_ ?_⟩
  · rw [muK, IntermediateField.adjoin_le_iff]
    intro x hx
    have hx' : x ^ (l ^ k) = 1 := hx
    obtain ⟨i, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx'
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ) _
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin _ _ hp.pow_eq_one

end GlobalTheory.CycClosure

namespace GlobalTheory.CycClosure

theorem exists_cyclotomic_integers : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ), ∃ _ : IsDiscreteValuationRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), IsAlgClosed (IsLocalRing.ResidueField ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ (∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∀ y ∈ clC l (Kt l K₀ L ⊔ muK l k), ‖x‖ ≤ ‖y‖ → x / y ∈ clC l (Kt l K₀ L ⊔ muK l k)) ∧ muK l 0 = ⊥ ∧ (∃ T : Finset ℂ_[l], ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ Submodule.span ↥(clC l (Kt l K₀ L)) (T : Set ℂ_[l])) ∧ ∃ ζ ∈ clC l (Kt l K₀ L ⊔ muK l k), IsPrimitiveRoot ζ (l ^ k) ∧ ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ (p : Polynomial ↥(clC l (Kt l K₀ L))) (d : ↥(clC l (Kt l K₀ L))), d ≠ 0 ∧ x * (d : ℂ_[l]) = Polynomial.aeval ζ p := by
  intro l _ K₀ L k
  have hp : l.Prime := Fact.out
  obtain ⟨hfd, ζ, hζ, hmu⟩ := muK_spec (l := l) k
  let LL : Loc.FinExt l := ⟨K₀.1 ⊔ L.1 ⊔ muK l k, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  have hM : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = Kt l K₀ L ⊔ muK l k := by
    simp only [LL, Kt]; exact sup_right_comm _ _ _
  let L0 : Loc.FinExt l := ⟨K₀.1 ⊔ L.1, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  obtain ⟨hdvr, hres, hcomp, hadic, hdiv⟩ := clC_props LL _ hM
  obtain ⟨hdvr0, -, -, -, -⟩ := clC_props L0 (Kt l K₀ L) rfl
  have mu0 : muK l 0 = ⊥ := by
    rw [muK, eq_bot_iff, IntermediateField.adjoin_le_iff]
    intro x hx
    have : x = 1 := by simpa using hx
    rw [this]; exact one_mem _
  have hn : 0 < l ^ k := pow_pos hp.pos k
  have hint : IsIntegral ℚ_[l] ζ :=
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [hζ.pow_eq_one]⟩
  obtain ⟨n, Cb, hC⟩ := _root_.GlobalTheory.closure_adjoin_unitBall_coeff_bound l (Kt l K₀ L) ζ hint
  have hB : ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ clC l (Kt l K₀ L ⊔ IntermediateField.adjoin ℚ_[l] {ζ}) := by
    intro x; rw [hmu]
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [← map_natCast (algebraMap (PadicAlgCl l) ℂ_[l])]
    refine lt_of_eq_of_lt (PadicComplex.norm_extends l (l : PadicAlgCl l)) ?_
    rw [GlobalTheory.UnramValue.norm_l]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (max Cb 1) by positivity) hl
  have cmem : ∀ c ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((Kt l K₀ L : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))),
      ‖c‖ ≤ Cb → (l : ℂ_[l]) ^ N * c ∈ clC l (Kt l K₀ L) := by
    intro c hc hcb
    refine mem_clC.2 ⟨map_mem_closure (continuous_const.mul continuous_id) hc ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨(l : PadicAlgCl l) ^ N * z, mul_mem (pow_mem (natCast_mem _ _) _) hz, ?_⟩
      simp
    · rw [norm_mul, norm_pow]
      have h1 : ‖c‖ ≤ max Cb 1 := hcb.trans (le_max_left _ _)
      have h2 : (0 : ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      calc ‖(l : ℂ_[l])‖ ^ N * ‖c‖ ≤ ‖(l : ℂ_[l])‖ ^ N * max Cb 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 / max Cb 1 * max Cb 1 := mul_le_mul_of_nonneg_right hN.le h2.le
        _ = 1 := by field_simp
  set ζ' : ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] ζ with hζ'
  have hζn : ‖ζ‖ = 1 := by
    have := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hζB : ζ' ∈ clC l (Kt l K₀ L ⊔ muK l k) := by
    rw [hB]
    refine mem_clC.2 ⟨subset_closure ⟨ζ, (le_sup_right : IntermediateField.adjoin ℚ_[l] {ζ} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ), rfl⟩, ?_⟩
    exact ((PadicComplex.norm_extends l ζ).trans hζn).le
  have hAB : ∀ x ∈ clC l (Kt l K₀ L), x ∈ clC l (Kt l K₀ L ⊔ muK l k) := fun x hx => clC_mono le_sup_left hx
  have hlN : (l : ℂ_[l]) ^ N ∈ clC l (Kt l K₀ L) := pow_mem (natCast_mem _ _) _
  have rep : ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ c : Fin n → ℂ_[l],
      (∀ i, (l : ℂ_[l]) ^ N * c i ∈ clC l (Kt l K₀ L)) ∧ x = ∑ i, c i * ζ' ^ (i : ℕ) := by
    intro x hx
    rw [hB] at hx
    obtain ⟨c, hc, e⟩ := hC x (mem_clC.1 hx).1 (mem_clC.1 hx).2
    exact ⟨c, fun i => cmem _ (hc i).1 (hc i).2, e⟩
  refine ⟨hdvr, hres, hcomp, hadic, hdiv, mu0, ?_, ζ', hζB, hζ.map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, ?_⟩
  · classical
    let g : Fin n → ℂ_[l] := fun i => ((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ)
    let P : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] := Submodule.span ↥(clC l (Kt l K₀ L)) (Set.range g)
    let B' : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] :=
      { carrier := (clC l (Kt l K₀ L ⊔ muK l k) : Set ℂ_[l])
        add_mem' := fun ha hb => add_mem ha hb
        zero_mem' := zero_mem _
        smul_mem' := fun a x hx => by
          rw [Subring.smul_def, smul_eq_mul]
          exact mul_mem (hAB _ a.2) hx }
    have hBP : B' ≤ P := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := rep x hx
      refine Submodule.sum_mem _ fun i _ => ?_
      have := Submodule.smul_mem P (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L)))
        (Submodule.subset_span ⟨i, rfl⟩ : g i ∈ P)
      convert this using 1
      rw [Subring.smul_def, smul_eq_mul]
      change c i * ζ' ^ (i : ℕ) = ((l : ℂ_[l]) ^ N * c i) * (((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ))
      field_simp
    haveI : IsNoetherian ↥(clC l (Kt l K₀ L)) ↥P :=
      isNoetherian_of_fg_of_noetherian P (Submodule.fg_span (Set.finite_range g))
    have hfg : B'.FG := by
      have h1 : (B'.comap P.subtype).FG := IsNoetherian.noetherian _
      have h2 := h1.map P.subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.2 hBP] at h2
    obtain ⟨T, hT⟩ := hfg
    exact ⟨T, fun x => by rw [hT]; rfl⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := rep x hx
    refine ⟨∑ i : Fin n, monomial (i : ℕ) (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L))),
      ⟨(l : ℂ_[l]) ^ N, hlN⟩, fun h => pow_ne_zero N hl0 (congrArg Subtype.val h), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, aeval_monomial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change c i * ζ' ^ (i : ℕ) * (l : ℂ_[l]) ^ N = ((l : ℂ_[l]) ^ N * c i) * ζ' ^ (i : ℕ)
    ring

end GlobalTheory.CycClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFamilyLabelContainingFiniteTypeParts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LabProof


set_option maxHeartbeats 2000000 in
theorem hasLab_exists : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ p, HasLab Y σ p := by
  intro hW hDS hHC hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hPins hHolds hHost σ
  obtain ⟨c, hE, hWp⟩ := GlobalTheory.T.exists_sphericalEigensystem_of_finiteType_with_parts hW hDS hHC hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost σ
  have hcar := GlobalTheory.T.eigensystem_carried_by_finiteType_of_meets_level_rows hW hDS hHC hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  obtain ⟨U, hU, hU0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨x, hx, hxU⟩ := hE b U hU
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hxU
    exact hU0 hxU.symm
  obtain ⟨p, hp⟩ := hcar c b x hx0 hx (by rw [hxU]; exact hU.1)
  have hinjW : ∀ i, Function.Injective (R.HW i (sg0 D A3.A)).e := fun i => (hPins.char.base.models.HW i _).1
  refine ⟨p, fun i => ?_, fun k hk => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := (Y.tied.lift.isot i σ y).1 hy
    rw [Y.prtWE] at h1
    obtain ⟨U', hU', hU'e⟩ := h1
    obtain ⟨w, hw, hwU⟩ := hWp i U' hU'
    rw [Y.mjRead] at hU'e
    have h2 : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) = (R.HW i (sg0 D A3.A)).e w := by
      rw [hwU]
      exact (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective hU'e.symm
    have h3 : Y.mj.eW i y ∈ R.Wc' i c := (hinjW i h2) ▸ hw
    exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.Wc' i c) c hp le_rfl h3
  · have h1 := Y.tied.base.ft k
    rw [hk, Y.prtE0] at h1
    obtain ⟨U', hU', hU'e⟩ := h1
    obtain ⟨w, hw, hwU⟩ := hE false U' hU'
    refine ⟨w, le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl hw, ?_⟩
    rw [← hU'e, hwU]
    rfl

end GlobalTheory.Mem.R3.LabProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersToCompletedUnramifiedCompositum
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.HeightCounting.ToClC

theorem norm_le_one_of_mem_OL (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (x : ↥(Loc.OL K)) :
    ‖((x : ↥K.1) : PadicAlgCl l)‖ ≤ 1 := by
  have h : IsIntegral ℤ_[l] ((x : ↥K.1) : PadicAlgCl l) :=
    (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).2 x.2
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral _))]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact ((minpoly ℤ_[l] _).coeff n).2

theorem mem_clC_of_OL (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (y : ↥(Loc.OL K₀)) :
    algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) ∈ clC l (Kt l K₀ L) := by
  refine ⟨Subring.le_topologicalClosure _ ⟨((y : ↥K₀.1) : PadicAlgCl l), ?_, rfl⟩, ?_⟩
  · show ((y : ↥K₀.1) : PadicAlgCl l) ∈ Kt l K₀ L
    exact (le_sup_left.trans (le_sup_left : K₀.1 ⊔ L.1 ≤ _)) (y : ↥K₀.1).2
  · change algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) ∈ PadicComplexInt l
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, ← PadicComplex.coe_eq, PadicComplex.valuation_extends, ← NNReal.coe_le_one, PadicAlgCl.valuation_coe]
    exact norm_le_one_of_mem_OL l K₀ y

def toClC (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)) :=
  ((algebraMap (PadicAlgCl l) ℂ_[l]).comp (K₀.1.val.toRingHom.comp (Loc.OL K₀).val.toRingHom)).codRestrict _
    fun y => mem_clC_of_OL l K₀ L y

theorem exists_toClC : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l), ∃ f : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)),
    ∀ y, (f y : ℂ_[l]) = algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) :=
  fun l _ K₀ L => ⟨toClC l K₀ L, fun _ => rfl⟩

end GlobalTheory.HeightCounting.ToClC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepCombinationPurePowerTraceStatement
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polyRep_combination_pure_power_trace : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι) (i : ℕ), 1 ≤ i → ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ), ∀ (A : Mat m S) (b : ℕ), b ≤ n → ∑ j, c j • (ρ j).ptr b A = if b = i then ((A τ) ^ i).trace else 0 := by
  first | exact @GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace | exact GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace | (intros; apply GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAlgClosedOverNumberFieldCompEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

set_option autoImplicit false

namespace GlobalTheory.AlgClosedIsoOverNumberField

open Cardinal

theorem exists_ringEquiv_commutes (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  classical

  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hL : ℵ₀ < #L := hKL ▸ hK
  have hs' : #K = #s :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have ht' : #L = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hL
  obtain ⟨f⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (hs'.symm.trans (hKL.trans ht'))

  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht

  let e₀ : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R f).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e₀.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem exists_ringEquiv_comp_eq :
    ∀ (K Ω₁ Ω₂ : Type) [Field K] [NumberField K] [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁]
      [IsAlgClosed Ω₂] [CharZero Ω₁] [CharZero Ω₂] (a : K →+* Ω₁) (b : K →+* Ω₂),
      Cardinal.mk Ω₁ = Cardinal.mk Ω₂ → Cardinal.aleph0 < Cardinal.mk Ω₁ →
        ∃ ι : Ω₁ ≃+* Ω₂, ∀ x, ι (a x) = b x := by
  intro K Ω₁ Ω₂ _ _ _ _ _ _ _ _ a b hcard hbig
  let : Algebra K Ω₁ := a.toAlgebra
  let : Algebra K Ω₂ := b.toAlgebra

  have hK : #K ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
    rwa [Cardinal.mkRat, max_self] at this
  obtain ⟨e, he⟩ := exists_ringEquiv_commutes K Ω₁ Ω₂ hK hbig hcard
  exact ⟨e, he⟩

end GlobalTheory.AlgClosedIsoOverNumberField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityLiftFromResidueField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameLift

theorem valuation_sub_lt_of_redThrough_eq {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) {x y : Ω} (hx : x ∈ A) (hy : y ∈ A)
    (h : redThrough A κ x = redThrough A κ y) : A.valuation (x - y) < 1 := by
  unfold redThrough at h
  rw [dite_eq_left hx, dite_eq_left hy] at h
  have h1 := κ.injective h
  have h2 : (⟨x, hx⟩ : A) - ⟨y, hy⟩ ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h1, sub_self]
  have := (A.valuation_lt_one_iff _).1 h2
  simpa using this

theorem exists_lift : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime],
    ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m →
    ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c := by
  intro E Ω _ _ _ _ _ A v hA g hg hgv κ m hm hgm c hc
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩

  have hvg : A.valuation (g : Ω) < 1 := by
    have := (hA (g : 𝓞 E)).2 hgv
    simpa using this

  have hvm : ¬ A.valuation (m : Ω) < 1 := by
    intro hlt
    have hcop : Nat.Coprime m g :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hg.out).mpr hgm)
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have e : ((u : Ω) * (m : Ω)) + (w : Ω) * (g : Ω) = 1 := by
      have := congrArg (fun z : ℤ => (z : Ω)) huw
      push_cast at this
      exact this
    have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A u)
    have hw : A.valuation (w : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A w)
    have h1 : A.valuation ((u : Ω) * (m : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hu) hlt
    have h2 : A.valuation ((w : Ω) * (g : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hw) hvg
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hζA : ζ ∈ A := mem_of_pow_eq_one A hm hζ.pow_eq_one
  have hr : IsPrimitiveRoot (redThrough A κ ζ) m := by
    refine IsPrimitiveRoot.mk_of_lt _ hm ?_ ?_
    · rw [← redThrough_pow A κ hζA, hζ.pow_eq_one, redThrough_one]
    · intro l hl hlm hrl
      rw [← redThrough_pow A κ hζA, ← redThrough_one A κ] at hrl
      have hv := valuation_sub_lt_of_redThrough_eq A κ (pow_mem hζA l) (one_mem A) hrl
      have heq : ζ ^ l = 1 := eq_of_pow_eq_one A hvm
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow _) hv
      exact hζ.pow_ne_one_of_pos_of_lt hl.ne' hlm heq
  obtain ⟨i, -, hi⟩ := hr.eq_pow_of_pow_eq_one hc
  refine ⟨ζ ^ i, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [redThrough_pow A κ hζA, hi]

end GlobalTheory.TameLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedDatumNeZeroIffDoubleCosetStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → cst.sharp = true → L.Ok Ch sel mu cst G m2 → ∀ i, i < m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) → SameDC (Pr := Pr) cst.sharp i P.1 1 hal → (FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h ↔ FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h) := by
  first | exact @GlobalTheory.SrcDoubleCoset.unfoldedDatum_ne_zero_iff_doubleCoset' | exact GlobalTheory.SrcDoubleCoset.unfoldedDatum_ne_zero_iff_doubleCoset' | (intros; apply GlobalTheory.SrcDoubleCoset.unfoldedDatum_ne_zero_iff_doubleCoset' <;> assumption)
end

