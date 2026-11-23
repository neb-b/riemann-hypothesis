module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0421
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdeal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMemUnipSymOfFlagCongruences

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LCIntegralField

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

def stab (f : X → ℂ) : AddSubgroup X where
  carrier := {v | ∀ y, f (y + v) = f y}
  zero_mem' := fun y => by simp
  add_mem' := by
    intro a b (ha : ∀ y, f (y + a) = f y) (hb : ∀ y, f (y + b) = f y) y
    show f (y + (a + b)) = f y
    rw [← add_assoc, hb, ha]
  neg_mem' := by
    intro a (ha : ∀ y, f (y + a) = f y) y
    show f (y + -a) = f y
    have := ha (y + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_stab {f : X → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsOpen (stab f : Set X) := by
  classical
  have hT : IsCompact (tsupport f) := hc
  haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hT
  have hfin : (f '' tsupport f).Finite := by
    have := (hf.comp_continuous (continuous_subtype_val : Continuous (Subtype.val : tsupport f → X))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at this
  have key : ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ᶠ v in nhds (0 : X), ∀ y, f y = c → f (y + v) = c := by
    intro c _ hc0
    have hLT : f ⁻¹' {c} ⊆ tsupport f := fun y hy =>
      subset_tsupport f (by rw [Function.mem_support, show f y = c from hy]; exact hc0)
    have hLc : IsCompact (f ⁻¹' {c}) :=
      hT.of_isClosed_subset (isClosed_singleton.preimage hf.continuous) hLT
    obtain ⟨V, hV, hKV⟩ := compact_open_separated_add_right hLc (hf.isOpen_fiber c) subset_rfl
    filter_upwards [hV] with v hv y hy
    exact hKV (Set.add_mem_add hy hv)
  have h1 : ∀ᶠ v in nhds (0 : X), ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ y, f y = c → f (y + v) = c :=
    (Filter.eventually_all_finite hfin).2 fun c hc => by
      by_cases h0 : c = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd h0 h
      · exact (key c hc h0).mono fun v hv _ => hv
  have h2 := (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually h1
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  filter_upwards [h1, h2] with v hv hv'
  show ∀ y, f (y + v) = f y
  intro y
  by_cases hy : f y = 0
  · by_contra hne
    have hne' : f (y + v) ≠ 0 := by rw [hy] at hne; exact hne
    have hmem : f (y + v) ∈ f '' tsupport f := ⟨y + v, subset_tsupport f hne', rfl⟩
    have := hv' _ hmem hne' (y + v) rfl
    rw [add_neg_cancel_right] at this
    exact hne this.symm
  · exact hv (f y) ⟨y, subset_tsupport f hy, rfl⟩ hy y rfl

theorem discrete_quot (U : AddSubgroup X) (hU : IsOpen (U : Set X)) : DiscreteTopology (X ⧸ U) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H g =>
    have hpre : (QuotientAddGroup.mk : X → X ⧸ U) ⁻¹' {(g : X ⧸ U)} = (fun x => -g + x) ⁻¹' (U : Set X) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [eq_comm, QuotientAddGroup.eq]
    rw [← (QuotientAddGroup.isQuotientMap_mk (N := U)).isOpen_preimage, hpre]
    exact hU.preimage (continuous_const.add continuous_id)

theorem integral_eq_sum [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant]
    (U : AddSubgroup X) (hU : IsOpen (U : Set X)) (hUfin : μ U ≠ ⊤) (g : X → ℂ)
    (hg : ∀ u ∈ U, ∀ y, g (y + u) = g y) (hc : HasCompactSupport g) :
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  classical
  haveI := discrete_quot U hU
  have hfin : ((QuotientAddGroup.mk : X → X ⧸ U) '' tsupport g).Finite :=
    (hc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T := hfin.toFinset with hT
  have hind : ∀ (c : X ⧸ U) y, (Quotient.out c : X) = (Quotient.out c : X) →
      (-(Quotient.out c) + y ∈ U ↔ c = (y : X ⧸ U)) := by
    intro c y _
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  have hdec : g = fun y => ∑ c ∈ T,
      ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator (fun _ => g (Quotient.out c)) y := by
    funext y
    have key : ∀ c : X ⧸ U, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator
        (fun _ => g (Quotient.out c)) y = if c = (y : X ⧸ U) then g y else 0 := by
      intro c
      by_cases h : c = (y : X ⧸ U)
      · rw [if_pos h, Set.indicator_of_mem (show y ∈ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from (hind c y rfl).2 h)]
        have hm : -(Quotient.out c) + y ∈ U := (hind c y rfl).2 h
        have := hg _ hm (Quotient.out c)
        rw [add_neg_cancel_left] at this
        exact this.symm
      · rw [if_neg h, Set.indicator_of_notMem (show y ∉ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from fun hm => h ((hind c y rfl).1 hm))]
    simp only [key]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [hT, Set.Finite.mem_toFinset] at hmem
      exact image_eq_zero_of_notMem_tsupport (fun hs => hmem ⟨y, hs, rfl⟩)
  have hmeas : ∀ c : X ⧸ U, MeasurableSet ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) := fun c =>
    (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hvol : ∀ c : X ⧸ U, μ ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) = μ U := fun c =>
    measure_preimage_add μ _ _
  refine ⟨T.image Quotient.out, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]
  conv_lhs => rw [hdec]
  rw [integral_finsetSum]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_indicator_const _ (hmeas c)]
    simp only [Measure.real, hvol, Complex.real_smul]
    ring
  · intro c _
    refine (integrable_indicator_iff (hmeas c)).2 (integrableOn_const ?_)
    rw [hvol]; exact hUfin

theorem integral_mem_range [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] [T2Space X]
    (μ : Measure X) [μ.IsAddLeftInvariant] (H : Set X) (hHo : IsOpen H) (hHc : IsCompact H) (hH0 : (0 : X) ∈ H)
    (hμH : μ H = 1) {K : Type} [Field K] (σ : K →+* ℂ) (f : X → ℂ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (hv : ∀ e, f e ∈ Set.range σ) : ∫ e, f e ∂μ ∈ Set.range σ := by
  classical
  set h : X → ℂ := H.indicator (fun _ => 1) with hh
  have hloc : IsLocallyConstant h := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ H
    · exact ⟨H, hHo, hx, fun y hy => by rw [hh, Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨Hᶜ, hHc.isClosed.isOpen_compl, hx, fun y hy => by
        rw [hh, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  have hch : HasCompactSupport h := HasCompactSupport.intro hHc fun x hx => Set.indicator_of_notMem hx _
  set U := stab f ⊓ stab h with hU
  have hUo : IsOpen (U : Set X) := by
    rw [hU, AddSubgroup.coe_inf]; exact (isOpen_stab hf hc).inter (isOpen_stab hloc hch)
  have hUH : (U : Set X) ⊆ H := by
    intro u hu
    have h1 := (AddSubgroup.mem_inf.1 hu).2 0
    rw [zero_add] at h1
    by_contra hn
    rw [hh, Set.indicator_of_notMem hn, Set.indicator_of_mem hH0] at h1
    exact zero_ne_one h1
  have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top (by rw [hμH]; exact ENNReal.one_ne_top) (measure_mono hUH)
  obtain ⟨s, hs⟩ := integral_eq_sum μ U hUo hUfin f (fun u hu => (AddSubgroup.mem_inf.1 hu).1) hc
  obtain ⟨s', hs'⟩ := integral_eq_sum μ U hUo hUfin h (fun u hu => (AddSubgroup.mem_inf.1 hu).2) hch
  have hint : ∫ y, h y ∂μ = 1 := by
    rw [hh, integral_indicator_const _ hHo.measurableSet]
    simp [Measure.real, hμH]
  rw [hint] at hs'
  have hr := eq_inv_of_mul_eq_one_right hs'.symm
  rw [hs, hr, ← RingHom.coe_fieldRange]
  have hv' : ∀ e, f e ∈ σ.fieldRange := fun e => by rw [← SetLike.mem_coe, RingHom.coe_fieldRange]; exact hv e
  have hh' : ∀ e, h e ∈ σ.fieldRange := fun e => by
    rw [hh, Set.indicator_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  exact mul_mem (sum_mem fun γ _ => hv' γ) (inv_mem (sum_mem fun γ _ => hh' γ))

end GlobalTheory.LCIntegralField

namespace GlobalTheory.LCIntegralField
open GlobalTheory.FunObj ValuativeRel

theorem integral_vars_mem_range : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (ν : MeasureTheory.Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ {K : Type} [Field K] (σ : K →+* ℂ) (f : Vars G → ℂ), IsLocallyConstant f → HasCompactSupport f → (∀ e, f e ∈ Set.range σ) → ∫ e, f e ∂(varsVol G ν) ∈ Set.range σ := by
  intro k _ _ _ _ _ _ G ν hν K _ σ f hf hc hv
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI := hν.1
  haveI : (varsVol G ν).IsAddLeftInvariant := by unfold varsVol; infer_instance
  refine integral_mem_range (varsVol G ν) (Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)) ?_ ?_ ?_ ?_
    σ f hf hc hv
  · exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => Model.isOpen_int
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  · exact fun _ _ _ _ => zero_mem _
  · simp [varsVol, Measure.pi_pi, hν.2]

end GlobalTheory.LCIntegralField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionThird
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ClassSumLift

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem theta_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL μ j) :
    D.what₂.thetaP ν j (D.what₂.jMt ν j (h ▸ x)) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) := by
  subst h; rfl

theorem exists_heq_fin {K : Type} {a b : ℕ} (h : a = b) (z : Fin a → K) : ∃ y : Fin b → K, HEq z y := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem exists_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL ν j) :
    ∃ x' : D.what₂.MtL μ j, x = h ▸ x' := by
  subst h; exact ⟨x, rfl⟩


end GlobalTheory.ClassSumLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterOnStabilizerEqProdResidueCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

theorem levelCharacter_on_stabilizer_eq_prod_residue_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ R.Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → X.chi2 ((iotaX X h).toMulEquiv κ).2 = ∏ PP ∈ R.Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG
  obtain ⟨hg, hcov⟩ := _root_.GlobalTheory.SeeConjRead.places_over_g R hL
  obtain ⟨ψ, hψ, hprod⟩ := GlobalTheory.T.conjInstanceCharacter_eq_prod_residueField_addChars X h R.Pg hg hcov (GlobalTheory.T.levelPlaces_not_isConjPlace_realDat R F hL hG)
  refine ⟨ψ, hψ, fun κ hκ => ?_⟩
  obtain ⟨hi, he⟩ := _root_.GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset X h κ hκ
  rw [he, hprod _ hi]

end GlobalTheory.SeeConjChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftUpMultiplicitySpacesSpanKFiniteVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.EvenOnto.LiftUp

theorem liftUp_stage_span : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) ω f, c.Is → k < c.m → s.Is c k → s'.Is c (k + 1) → PreStep c k s s' ω f → ∃ T : PolF D s'.V.rank s.V.rank → SmT s.M → SmT s'.M, (∀ P v, T P v ∈ s'.KF) ∧ s'.KF ≤ Submodule.span ℂ {w | ∃ P v, w = T P v} ∧ GlobalTheory.PairLift.LiftsM c.θ s.M s'.M s.ν s.fd (fun P h g => conj (thetaKO ω g h (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M f P))) T := by
  intro hDS hHC hCD hCW D c k s s' ω f hc hk hs _hs' hp
  obtain ⟨X, hX, _h1, _h2, h3, h4, h5⟩ := _root_.GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
  have hIn : Inputs D X := _root_.GlobalTheory.PairLift.inputs_of_chosenSeries hDS hHC hCD hCW D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X hIn (_root_.GlobalTheory.PairLift.cuspAll_of_lowAll D X hIn (_root_.GlobalTheory.PairLift.lowAll_of_lowFock D X hIn (_root_.GlobalTheory.LowerMembersRule.lowFock D X hIn)))
  have hW := hp.weil
  have hstd : IsStdChar D c.ψ (-1) := hW.std
  have hadj : AdjLaw c.ψ s.V s'.V := _root_.GlobalTheory.AdjLawPf.adjLaw D c.ψ hstd s.V s'.V
  have h0 : adjO s.V s'.V 0 = 0 := by
    have := hadj.add 0 0
    simpa using this
  obtain ⟨ω', hW', hω'⟩ := _root_.GlobalTheory.WeilConj.exists_conj_weilDatum D c.ψ s.V s'.V (c.χ k) (c.χ k) ω hW
  obtain ⟨j, -, hj⟩ := _root_.GlobalTheory.FockAdjoint.fock_dag D c.ψ c.θ hstd hc.inf s.V s'.V (Fr.ofModel s.M) (Fr.ofModel s'.M)
  obtain ⟨hvac', hpt⟩ := hj f (isVacF_of_isVacVec hp.vac)
  have hω'e : IsWeilExp c.ψ s'.V s.V (c.a k) (c.a k) ω' :=
    ⟨c.χ k, c.χ k, hW', fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  have hne : dag s.V s'.V f ≠ 0 := by
    intro hz
    apply hp.vac.ne
    funext x
    have hx := congrFun hz (adjO s'.V s.V x)
    simp only [dag, hadj.invol, Pi.zero_apply] at hx
    simpa using hx
  have hf' : IsVacVec c.ψ c.θ s'.M s.M (dag s.V s'.V f) := ⟨hvac'.1, hne, hvac'.2⟩
  obtain ⟨It, hIt⟩ := (_root_.GlobalTheory.EvenOnto.upPair_itW hDS hHC D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf hp.par).2
  have hItW := hIt ω' (dag s.V s'.V f) hω'e hf'
  have hrule : ∀ τ, RulePar X (s'.par τ) (s.par τ) (c.a k τ) (c.a k τ) :=
    fun τ => ((_root_.GlobalTheory.EvenOnto.upPair_arch hDS hHC D c.t _ _ _ _ (hp.par τ)).2 X h3 h4 h5).2
  have hL := hPL _ _ _ _ hrule s'.V s.V s'.M s.M c.θ c.ψ hc.inf ω' hω'e (dag s.V s'.V f) It hf' hItW s.ν s.fd hs.haar hs.fund
    (dag s.V s'.V f) (isVacF_of_isVacVec hf')
  refine ⟨fun P v => It (j P) v, fun P v =>
    _root_.GlobalTheory.ItKFin.itKFin D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf' hItW (j P) v, ?_, ?_⟩
  · refine (GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf'
      hItW).trans (Submodule.span_mono ?_)
    rintro w ⟨P, v, -, rfl⟩
    exact ⟨j.symm P, v, by simp⟩
  · intro F hF
    obtain ⟨F', hF', hF'e⟩ := hL F hF
    refine ⟨F', hF', fun P v h => ?_⟩
    have key : ∀ g, conj (thetaKO ω g h (ptOf c.ψ c.θ s.M s'.M f P)) =
        thetaKO ω' h g (ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P)) := by
      intro g
      have e1 : ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P) = dag s.V s'.V (ptOf c.ψ c.θ s.M s'.M f P) := hpt P
      simp only [thetaKO]
      rw [e1, hω']
      simp [dag, h0]
    simp only [key]
    exact hF'e (j P) v h

end GlobalTheory.EvenOnto.LiftUp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_frame_hermitian_ideal : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (Pg : Finset (Pl D.host.E)), IsFrame β (II D).L → (∀ PP ∈ Pg, ∃ w : Bool, LocAt g e0 f0 z0 bw bwd ew β PP w) → (∀ (c : EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc' : sigA (II D) c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Pg, resS D.host.F PP ⟨c, hc⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) c, hc'⟩ = 0) → ZMod' (II D) g c) → ∀ (x : (II D).Gf) (M : GL (Fin (Yc D 0).rank) (EAf D)), x ∈ (II D).Kset → (II D).fmat x = M.val → M ∈ St β → (∀ PP ∈ Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) → K2cong (II D) g e0 z0 bw x := by
  first | exact @GlobalTheory.SeeConjGroup.Bwd.k2cong_of_unipSym | exact GlobalTheory.SeeConjGroup.Bwd.k2cong_of_unipSym | (intros; apply GlobalTheory.SeeConjGroup.Bwd.k2cong_of_unipSym <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchOfPolMatch
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.PolMatchConst

def finProd {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)

theorem match_of_polMatch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' → Φ' ∈ G.M'.So B.ψ B.τ₁ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hT Φ Φ' hP hSo
  have hP0 := hP
  obtain ⟨T, hXT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', _⟩ := hP
  have hstd : ∀ (κ : Type) (ψ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
      (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      (∀ v ∉ T, ψ v = vac v) →
      ∀ᶠ v in Filter.cofinite, ψ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    intro κ ψ vac hvac hψ
    filter_upwards [hvac, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    rw [hψ v hvT, hv]
  have hg : ∀ i, finProd (φ i) ∈ GlobalTheory.WeilM.SB _ := fun i =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2)⟩
  have hg' : ∀ j, finProd (φ' j) ∈ GlobalTheory.WeilM.SB _ := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2)⟩
  have e : Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (finProd (φ i)) := hΦ
  have e' : Φ' = ∑ j, GlobalTheory.WeilM.pureA F (f' j) (finProd (φ' j)) := hΦ'
  refine ⟨hSo, m, m', fun i => finProd (φ i), f, fun _ => f, fun j => finProd (φ' j), f', fun _ => f',
    fun i => ⟨hg i, tendsto_const_nhds⟩, fun j => ⟨hg' j, tendsto_const_nhds⟩, e, e', fun _ => ?_⟩
  rw [← e, ← e']
  exact ⟨hSo, hP0⟩

end GlobalTheory.SquareAgree.PolMatchConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMemUnipSymOfFlagCongruencesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_mem_unipSym_of_flag_congruences : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bb cc : Fin D.R.k → VA (II D)) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E), IsFrame β (II D).L → ((g : 𝓞 D.host.E) ∈ PP.asIdeal) → RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bb z0) → (∀ i, cc i ∈ (II D).Lf ∧ redV β PP (cc i) = 0) → ∀ M : GL (Fin (Yc D 0).rank) (EAf D), M ∈ St β → (∀ a, (M.val - 1) *ᵥ e0 a ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (e0 '' {b | b.1 < a.1})) → ((M.val - 1) *ᵥ z0 ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (Set.range e0)) → (∀ i, (M.val - 1) *ᵥ bb i ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (Set.range e0 ∪ Set.range cc ∪ bb '' {j | j.1 < i.1})) → (∀ b, (M.val - 1) *ᵥ f0 b ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (Set.range e0 ∪ {z0} ∪ Set.range bb ∪ Set.range cc ∪ f0 '' {c | b < c})) → upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k := by
  first | exact @GlobalTheory.SeeConjGroup.redFn_mem_unipSym_of_cong | exact GlobalTheory.SeeConjGroup.redFn_mem_unipSym_of_cong | (intros; apply GlobalTheory.SeeConjGroup.redFn_mem_unipSym_of_cong <;> assumption)
end

