module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsSpanLevel
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

namespace GlobalTheory.HCFGLct

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_haar_fd_one (r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] :
    ∃ (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratN E a r) 𝓕 μ ∧ μ 𝓕 = 1 := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  obtain ⟨𝓕, h𝓕, h0, hT⟩ := GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN E a r
    (Measure.addHaar : Measure (BlockIx a r → Ad E))
  refine ⟨((Measure.addHaar : Measure (BlockIx a r → Ad E)) 𝓕)⁻¹ • Measure.addHaar, 𝓕, ?_,
    h𝓕.mono Measure.smul_absolutelyContinuous, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT.ne) (ENNReal.inv_ne_top.2 h0)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hT.ne]

theorem setIntegral_eq_zero_all {r : ℕ} [m : MeasurableSpace (BlockIx a r → Ad E)] [hm : BorelSpace (BlockIx a r → Ad E)]
    (μ₀ : Measure (BlockIx a r → Ad E)) (𝓕₀ : Set (BlockIx a r → Ad E)) (hμ₀ : μ₀.IsAddHaarMeasure)
    (h𝓕₀ : IsAddFundamentalDomain (ratN E a r) 𝓕₀ μ₀) (φ : GA E a → ℂ) (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (hz : ∀ g, ∫ x in 𝓕₀, φ (unip x * g) ∂μ₀ = 0) :
    ∀ [m' : MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
      (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
      ∀ g, ∫ x in 𝓕, φ (unip x * g) ∂μ = 0 := by
  intro m' hm' μ 𝓕 hμ h𝓕 g
  obtain rfl : m' = m := hm'.measurable_eq.trans hm.measurable_eq.symm
  haveI := hμ
  haveI := hμ₀
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), φ (unip (γ +ᵥ x) * g) = φ (unip x * g) := by
    rintro ⟨_, e, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = φ (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  have h𝓕' : IsAddFundamentalDomain (ratN E a r) 𝓕 μ₀ :=
    h𝓕.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  rw [Measure.isAddLeftInvariant_eq_smul μ μ₀, Measure.restrict_smul, integral_smul_nnreal_measure,
    h𝓕'.setIntegral_eq h𝓕₀ (f := fun x => φ (unip x * g)) hinv, hz, smul_zero]

theorem cont_left_of_mem_span {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ} {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    Continuous φ.1 ∧ ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left⟩
  | zero => exact ⟨continuous_const, fun _ _ => rfl⟩
  | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2 γ h) (hy.2 γ h)⟩
  | smul c x _ hx => exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2 γ h)⟩

theorem exists_ct_map : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, ∀ L : Subgroup (GL (Fin b) (Af E)), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (formsGL E b L W X N))) → ∀ L : Subgroup (GL (Fin a) (Af E)), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ), ∃ (n : ℕ) (T : Sm E a →ₗ[ℂ] (Fin n → ℂ)), ∀ φ ∈ formsGL E a L W {χ} N, T φ = 0 → IsCuspidal φ.1 := by
  intro E _ _ _ a ih L hL W hW χ N
  classical
  set V := Submodule.span ℂ (formsGL E a L W {χ} N) with hVdef
  let ι := {r : Fin a // 0 < (r : ℕ)}
  have key : ∀ i : ι, ∃ c : Sm E a → GA E a → ℂ,
      (∀ φ ∈ V, ∀ ψ ∈ V, c (φ + ψ) = c φ + c ψ) ∧ (∀ (t : ℂ) (φ : Sm E a), c (t • φ) = t • c φ) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : V => c φ.1)) ∧
      ∀ φ ∈ V, c φ = 0 → ∀ [MeasurableSpace (BlockIx a (i.1 : ℕ) → Ad E)] [BorelSpace (BlockIx a (i.1 : ℕ) → Ad E)]
        (μ : Measure (BlockIx a (i.1 : ℕ) → Ad E)) (𝓕 : Set (BlockIx a (i.1 : ℕ) → Ad E)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratN E a i.1) 𝓕 μ → ∀ g, ∫ x in 𝓕, φ.1 (unip x * g) ∂μ = 0 := by
    intro i
    letI mB : MeasurableSpace (BlockIx a (i.1 : ℕ) → Ad E) := borel _
    haveI hB : BorelSpace (BlockIx a (i.1 : ℕ) → Ad E) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := exists_haar_fd_one (E := E) (a := a) (i.1 : ℕ)
    haveI := hμ
    refine ⟨fun φ g => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ, fun φ hφ ψ hψ => ?_, fun t φ => ?_, ?_, fun φ hφ h0 => ?_⟩
    · funext g
      obtain ⟨hc, hl⟩ := cont_left_of_mem_span hφ
      obtain ⟨hc', hl'⟩ := cont_left_of_mem_span hψ
      exact integral_add (CuspidalL2GL.integrableOn_unip hc hl μ h𝓕 g) (CuspidalL2GL.integrableOn_unip hc' hl' μ h𝓕 g)
    · funext g
      exact integral_const_mul t _
    · exact GlobalTheory.HCFct.finiteDimensional_constTerm E a ih L hL W hW {χ} (Set.finite_singleton χ) N i.1 i.2 i.1.isLt
        μ 𝓕 hμ h𝓕 h1
    · exact setIntegral_eq_zero_all (m := mB) (hm := hB) μ 𝓕 hμ h𝓕 φ.1 (cont_left_of_mem_span hφ).2 (fun g => congrFun h0 g)
  choose c hadd hsmul hfin hzero using key
  let Λ : V →ₗ[ℂ] (ι × GA E a → ℂ) :=
    { toFun := fun φ p => c p.1 φ.1 p.2
      map_add' := fun φ ψ => funext fun p => congrFun (hadd p.1 φ.1 φ.2 ψ.1 ψ.2) p.2
      map_smul' := fun t φ => funext fun p => congrFun (hsmul p.1 t φ.1) p.2 }
  let S : ι → Submodule ℂ (GA E a → ℂ) := fun i => Submodule.span ℂ (Set.range fun φ : V => c i φ.1)
  haveI : ∀ i, FiniteDimensional ℂ (S i) := hfin
  let U : ((i : ι) → S i) →ₗ[ℂ] (ι × GA E a → ℂ) :=
    { toFun := fun f p => (f p.1).1 p.2
      map_add' := fun f f' => rfl
      map_smul' := fun t f => rfl }
  have hmem : ∀ φ : V, Λ φ ∈ LinearMap.range U := fun φ =>
    ⟨fun i => ⟨c i φ.1, Submodule.subset_span ⟨φ, rfl⟩⟩, rfl⟩
  obtain ⟨s, hs⟩ := GlobalTheory.finiteDim_functions_detected_by_finset (ι × GA E a) (LinearMap.range U) inferInstance
  let e := s.equivFin
  let T₀ : V →ₗ[ℂ] (Fin s.card → ℂ) := LinearMap.pi fun j => (LinearMap.proj (e.symm j).1).comp Λ
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  refine ⟨s.card, T, fun φ hφ h0 => ?_⟩
  have hV : φ ∈ V := Submodule.subset_span hφ
  have hT0 : T₀ ⟨φ, hV⟩ = 0 := by
    rw [← hT]; exact h0
  have hΛ : Λ ⟨φ, hV⟩ = 0 := hs _ (hmem _) fun p hp => by
    have := congrFun hT0 (e ⟨p, hp⟩)
    simpa [T₀] using this
  intro r h0' h1'
  exact hzero ⟨⟨r, h1'⟩, h0'⟩ φ hV (funext fun g => congrFun hΛ (⟨⟨r, h1'⟩, h0'⟩, g))

end GlobalTheory.HCFGLct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorMinorProductOriginEqPeriodsJet
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

def scaleCLM {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) : VC D N N' →L[ℂ] VC D N N' :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z τ i j => c τ * Z τ i j
      map_add' := fun Z Z' => by funext τ i j; simp [mul_add]
      map_smul' := fun s Z => by funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem scaleCLM_apply {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (Z : VC D N N') :
    scaleCLM c Z = fun τ i j => c τ * Z τ i j := rfl

theorem scaleCLM_coordV {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (k : D.what₂.Tau × Fin N' × Fin N) :
    scaleCLM c (Formalism.MainNotions.TaylorLogMetric.coordV D k) = c k.1 • Formalism.MainNotions.TaylorLogMetric.coordV D k := by
  funext τ i j
  simp only [scaleCLM_apply, Formalism.MainNotions.TaylorLogMetric.coordV, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [h.1]
  · simp

theorem prod_toList_get {ι : Type} (m : ι →₀ ℕ) (g : ι → ℂ)
    (h : ∀ i : Fin (Finsupp.toMultiset m).card, (i : ℕ) < (Finsupp.toMultiset m).toList.length) :
    (∏ i : Fin (Finsupp.toMultiset m).card, g ((Finsupp.toMultiset m).toList.get ⟨i, h i⟩)) =
      m.prod fun k e => g k ^ e := by
  have hl : (Finsupp.toMultiset m).card = (Finsupp.toMultiset m).toList.length := (Multiset.length_toList _).symm
  calc (∏ i : Fin (Finsupp.toMultiset m).card, g ((Finsupp.toMultiset m).toList.get ⟨i, h i⟩))
      = ∏ i : Fin (Finsupp.toMultiset m).toList.length, g ((Finsupp.toMultiset m).toList.get i) :=
        Fin.prod_congr' (fun i => g ((Finsupp.toMultiset m).toList.get i)) hl
    _ = ((Finsupp.toMultiset m).toList.map g).prod := Fin.prod_univ_fun_getElem _ g
    _ = (Multiset.map g (Finsupp.toMultiset m)).prod := by
        conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
        rw [Multiset.map_coe, Multiset.prod_coe]
    _ = m.prod fun k e => g k ^ e := by
        rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
          Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

theorem taylor_scale {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (G : VC D N N' → ℂ) (hG : Differentiable ℂ G)
    (α : Formalism.MainNotions.TaylorLogMetric.Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun Z : VC D N N' => G fun τ i j => c τ * Z τ i j) α =
      (α.prod fun k e => c k.1 ^ e) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  have hfun : (fun Z : VC D N N' => G fun τ i j => c τ * Z τ i j) = G ∘ scaleCLM c := rfl
  have hGc : ContDiff ℂ ⊤ G := (GlobalTheory.SCV.analyticOnNhd_of_differentiable hG Set.univ).contDiff
  rw [Formalism.MainNotions.TaylorLogMetric.taylor, Formalism.MainNotions.TaylorLogMetric.taylor, hfun,
    (scaleCLM c).iteratedFDeriv_comp_right hGc 0 le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  simp only [scaleCLM_coordV]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_div_assoc]
  congr 1
  exact prod_toList_get α (fun k => c k.1) _

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

def placeWt (D : D7) (a d : ℕ) : Formalism.MainNotions.GL3Theta.Idx D a d → D.what₂.Tau → ℕ := fun k => Pi.single k.1 1

theorem prod_eq_prod_weight {D : D7} {a d : ℕ} (f : D.what₂.Tau → ℂ) (v : Formalism.MainNotions.GL3Theta.Idx D a d →₀ ℕ) :
    (v.prod fun k e => f k.1 ^ e) = ∏ τ, f τ ^ Finsupp.weight (placeWt D a d) v τ := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single k.1]
  · simp [placeWt]
  · intro τ _ hτ
    simp [placeWt, hτ]
  · simp

theorem minorPol_isWeightedHomogeneous {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (t : Tup D a d n) :
    (minorPol D t).IsWeightedHomogeneous (placeWt D a d) (fun τ => a * n τ) := by
  have hdet : ∀ τ j, (Matrix.of fun i i' => (MvPolynomial.X (τ, (t τ j).1 i, i') :
      MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det.IsWeightedHomogeneous (placeWt D a d) (a • Pi.single τ 1) := by
    intro τ j
    rw [← MvPolynomial.mem_weightedHomogeneousSubmodule, Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem ?_ _
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
      (fun i => (MvPolynomial.X (τ, (t τ j).1 (σ i), i) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ))
      (fun _ => (Pi.single τ 1 : D.what₂.Tau → ℕ))
      (fun i _ => MvPolynomial.isWeightedHomogeneous_X ℂ (placeWt D a d) (τ, (t τ j).1 (σ i), i))
    simpa using this
  have h := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun τ _ =>
    MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun j _ => hdet τ j
  have hdeg : (fun τ => a * n τ) = ∑ τ, ∑ _j : Fin (n τ), a • (Pi.single τ 1 : D.what₂.Tau → ℕ) := by
    funext τ'
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hdeg]
  exact h

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

theorem fock_minorPol_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ (n : D.what₂.Tau → ℕ) (t : Tup D a d n),
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f
        (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hT.symm k.2.1, Fin.cast hS.symm k.2.2) : FVar D T.rank S.rank))
          (minorPol D t)) 0 =
      (∏ τ, period D δ r τ ^ (a * n τ)) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D t) G := by
  intro D ψ θ S T a d hS hT cc δ r hs G f hG hR n t
  subst hS hT
  have hren : MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D S.rank T.rank =>
      ((k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2) : FVar D T.rank S.rank)) (minorPol D t) = minorPol D t :=
    MvPolynomial.rename_id_apply _
  rw [hren]
  obtain ⟨hstd, hinf, hgS, hgT, hcrv, hsc⟩ := hs
  have hrd := (reads_iff hcrv hsc G f).1 hR
  have hΦ : Differentiable ℂ (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) :=
    hG.comp (scaleCLM (fun τ => δ * embT D τ r)).differentiable
  have hfr : ∀ m, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin m) D.host.E) = fun _ => 1 := fun m =>
    funext fun _ => Matrix.map_one _ (map_zero _) (map_one _)
  have hon : ∀ V : HSp D, V.gram = 1 →
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 * V.gram *
        (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    simp [Formalism.UG.cT, hV]
  have hmono := GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ S T 1 1 hstd hinf (hon S hgS) (hon T hgT) f _ hΦ hrd.2
  rw [hfr, hfr] at hmono
  set P := minorPol D t with hPdef
  have hP : P = ∑ v ∈ P.support, AddMonoidAlgebra.coeff P v • MvPolynomial.monomial v (1 : ℂ) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    exact Finset.sum_congr rfl fun v _ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [hP, map_sum, Finset.sum_apply]
  rw [Formalism.MainNotions.GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hmono v]
  have happ : Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial v 1)
      (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) =
      (v.prod fun _ e => (e.factorial : ℂ)) *
        Formalism.MainNotions.TaylorLogMetric.taylor D (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) v := by
    rw [Formalism.MainNotions.GL3Theta.applyAt0, Finset.sum_subset MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
    intro x _ hx
    rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul, zero_mul]
  rw [happ, taylor_scale (fun τ => δ * embT D τ r) G hG v]
  have hw : Finsupp.weight (placeWt D S.rank T.rank) v = fun τ => S.rank * n τ :=
    minorPol_isWeightedHomogeneous t (MvPolynomial.mem_support_iff.1 hv)
  have hper : (∏ τ, period D δ r τ ^ (S.rank * n τ)) =
      (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (v.sum fun _ e => e) *
        v.prod fun k e => (δ * embT D k.1 r) ^ e := by
    rw [← Finset.prod_congr rfl fun τ _ => congrArg (period D δ r τ ^ ·) (congrFun hw τ),
      ← prod_eq_prod_weight]
    simp only [period, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← mul_pow,
      div_eq_mul_inv]
    exact Finset.prod_congr rfl fun k _ => by ring
  rw [hper]
  ring

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfinityExponentOfFinitePartPower
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormExact.InfExp

open IsDedekindDomain

theorem finAdEquiv_one_tmul (D : D7) (k : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) =
      GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D k) := by
  apply FiniteAdeleRing.ext
  intro w
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp only [GlobalTheory.BotFormula.toFinE, Formalism.MainNotions.StandardLatticesGL3.inc, Formalism.UG.inclE, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.comm_tmul]
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp

theorem eq_inf {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ)
    (hf : HasFinPart χ c e) (k : D.host.Eˣ) (x y : (AE D)ˣ) (hxy : Units.map (incA D).toMonoidHom k = x * y)
    (hy : infPart D (y : AE D) = 1) (hy' : finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) :
    ((χ x : Circle) : ℂ) =
      ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
  have hfin : ((χ y : Circle) : ℂ) = ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) ^ e : ℂˣ) : ℂ) :=
    hf y _ ⟨hy, by rw [hy']; exact finAdEquiv_one_tmul D k⟩
  have h5 : ((χ x : Circle) : ℂ) * ((χ y : Circle) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← map_mul, ← hxy, hχ.2 k, Circle.coe_one]
  have haut := c.aut k
  set F : ℂ := ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) : ℂˣ) : ℂ) with hF
  have hF0 : F ≠ 0 := (c.f _).ne_zero
  have hP : ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (c.n τ) = F⁻¹ :=
    eq_inv_of_mul_eq_one_right haut
  rw [Units.val_zpow_eq_zpow_val, ← hF] at hfin
  rw [hfin] at h5
  have hx : ((χ x : Circle) : ℂ) = (F ^ e)⁻¹ := eq_inv_of_mul_eq_one_left h5
  rw [hx, ← inv_zpow, ← hP, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm]


set_option maxHeartbeats 1000000 in
open Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in
theorem hasInfExp_of_hasFinPart : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    HasFinPart χ c e → ∀ τ, HasInfExp D χ τ ((e : ℚ) * (c.n τ : ℚ) / 2) := by
  intro D N c e χ hχ hf τ₀
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  refine ⟨e * c.n τ₀, by push_cast; ring, ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩, fun θ hθ => ?_⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau := ⟨τ₀⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((χ (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
    intro z
    refine (denseRange_units (tauE D) hd).induction_on z (isClosed_eq
      (continuous_subtype_val.comp (hχ.1.comp Tc)) (continuous_finsetProd _ fun τ _ => ?_)) fun k => ?_
    · have h1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have h2 : ∀ z : D.what₂.Tau → ℂˣ, ((‖(z τ : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z =>
        Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (z τ).ne_zero)
      exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h2).zpow₀ _ fun z =>
        Or.inl (div_ne_zero (z τ).ne_zero (h2 z))
    · refine Eq.trans ?_ (GlobalTheory.NormExact.InfExp.eq_inf c e χ hχ hf k _ _ (hab _) (hb _).1 (hb _).2)
      rw [hT _ (ha (Units.map (incA D).toMonoidHom k)).2]
      congr 3
      funext τ
      exact Units.ext ((congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)).symm
  intro x hx hx'
  refine (congrArg (fun u => ((χ u : Circle) : ℂ)) (hT x hx)).trans ((key _).trans ?_)
  refine Finset.prod_eq_single τ₀ (fun τ _ hτ => ?_) (fun h => absurd (Finset.mem_univ _) h)
  have : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom x : ℂˣ) : ℂ) = 1 := hx' τ hτ
  rw [this, norm_one, Complex.ofReal_one, div_one, one_zpow]

end GlobalTheory.NormExact.InfExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.NormExact

theorem heisO_finPt_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Reads ψ θ hS hT cc δ r G f → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
    Reads ψ θ hS hT cc δ r (U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) (heisO ψ S T (finPt hS hT r z) f) := by
  intro D ψ θ S T a d hS hT cc δ r hs G f hf z
  subst hS hT
  have hc := hs.crv
  have hr := hs.scale
  have hr0 : r ≠ 0 := IsScale.ne_zero hc.1.1 hr
  rw [reads_iff hc hr] at hf ⊢
  refine ⟨GlobalTheory.TwistFactorCompare.isTheta_heisO hs.std hf.1 _, fun w hw => ?_⟩
  set X : VC D S.rank T.rank := fun τ i j => embT D τ (r⁻¹ * z i j) with hXdef
  have hX : (fun τ a b => -(((GlobalTheory.FockPos.frAt (1 : GL (Fin T.rank) D.host.E) τ)⁻¹ *
      Matrix.of (GlobalTheory.VacUnique.infRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) τ) *
      GlobalTheory.FockPos.frAt (1 : GL (Fin S.rank) D.host.E) τ) a b)) = X := by
    funext τ a b
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [e, inv_one, Matrix.one_mul, Matrix.mul_one]
    show -(embT D τ (-(r⁻¹ * z a b))) = embT D τ (r⁻¹ * z a b)
    rw [map_neg, neg_neg]
  have h := GlobalTheory.MovedTrans.heisO_finRat_real ψ θ S T 1 1 (by simp [Formalism.UG.cT_one, hs.gS])
    (by simp [Formalism.UG.cT_one, hs.gT]) hs.std hs.inf f hf.1 (fun Z => G fun τ i j => δ * embT D τ r * Z τ i j) hf.2
    (Matrix.of fun i j => -(r⁻¹ * z i j)) _ hX.symm w hw
  have e1 : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) r z =
      GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) := rfl
  have hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * X τ i j := by
    funext τ i j
    show δ * embT D τ (z i j) = δ * embT D τ r * embT D τ (r⁻¹ * z i j)
    rw [mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  rw [e1, h, hpt]
  simp only [U]
  rw [Hf_scale hc hr, Hf_scale hc hr]
  have hY : ((fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j) + fun τ i j => δ * embT D τ r * X τ i j) =
      fun τ i j => δ * embT D τ r * (GlobalTheory.FockPos.zCo θ 1 1 w + X) τ i j := by
    funext τ i j
    simp only [Pi.add_apply]
    ring
  rw [hY]

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminormsStatement
section
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_schwartz_of_summable_seminorms : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ → SchwartzMap E ℂ),
    (∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) → Summable t := by
  first | exact @GlobalTheory.ConvSeries.summable_of_summable_seminorm | exact GlobalTheory.ConvSeries.summable_of_summable_seminorm | (intros; apply GlobalTheory.ConvSeries.summable_of_summable_seminorm <;> assumption)
end

