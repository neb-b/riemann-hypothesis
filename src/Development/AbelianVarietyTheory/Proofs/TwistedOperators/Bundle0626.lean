module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0783
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRepresentativesHalfQuotientPairingTrivialD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CoreOnto.Reps

private theorem selfDual_core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) ∧ IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := by
  have hV : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.core k)) (G.Λ (.core k)) := fun k hk =>
    (G.isV (X := .core k) hk (fun j h => Node.noConfusion h)).sd
  exact ⟨isSelfDualC_neg (hV (i + 1) hi), hV i hi.le⟩

private theorem nsmul_inj {D : D7} {m n : ℕ} {K : ℕ} (hK : 0 < K) {x y : Mx D m n} (h : K • x = K • y) : x = y := by
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have h' := congrArg (fun z : Mx D m n => incA D (K : D.host.E)⁻¹ • z) h
  rwa [← Nat.cast_smul_eq_nsmul (AE D), ← Nat.cast_smul_eq_nsmul (AE D), smul_smul, smul_smul, mul_comm, inv,
    one_smul, one_smul] at h'

private theorem isHalf_add {D : D7} {m n : ℕ} {c : AE D} {x y : Mx D m n} (hx : IsHalf c x) (hy : IsHalf c y) :
    IsHalf c (x + y) := fun a b => by simp only [Matrix.add_apply, mul_add, hx a b, hy a b]

private theorem isHalf_neg {D : D7} {m n : ℕ} {c : AE D} {x : Mx D m n} (hx : IsHalf c x) : IsHalf c (-x) := fun a b => by
  simp only [Matrix.neg_apply, mul_neg, hx a b]

private theorem isHalf_zero {D : D7} {m n : ℕ} (c : AE D) : IsHalf c (0 : Mx D m n) := fun a b => by simp

private theorem symplO_zero_right {D : D7} (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  have := GlobalTheory.ConjHalfDual.symplO_add_right' S T x 0 0
  simp only [add_zero] at this
  exact (add_eq_left.1 this.symm)

private theorem symplO_neg_right {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have := GlobalTheory.ConjHalfDual.symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

private theorem psi_ne_zero {F : Type*} [AddGroup F] (ψ : AddChar F ℂ) (a : F) : ψ a ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

private theorem finLat_of_nsmul {D : D7} {m n : ℕ} {Λ A : AddSubgroup (Mx D m n)} (h : GlobalTheory.AscFin.FinLat Λ)
    (hle : A ≤ Λ) {K : ℕ} (hK : 0 < K) (hA : ∀ u ∈ Λ, K • u ∈ A) : GlobalTheory.AscFin.FinLat A := by
  obtain ⟨U, h1, h2, h3⟩ := h.opn
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have hc : Continuous fun a : Mx D m n => incA D (K : D.host.E)⁻¹ • a :=
    continuous_id.const_smul (incA D (K : D.host.E)⁻¹)
  refine GlobalTheory.AscFinWit.finLat_of (fun a ha => h.fin a (hle ha))
    ⟨_, h1.preimage hc, by rwa [Set.mem_preimage, smul_zero], fun a ha hb => ?_⟩ h.cpt fun a ha => hle ha
  have := hA _ (h3 _ ha fun i j => Ideal.mul_mem_left _ _ (hb i j))
  rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, inv, one_smul] at this

end GlobalTheory.CoreOnto.Reps

open GlobalTheory.CoreOnto.Reps in
theorem _root_.GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∃ R : Finset (WO (G.pS (.core i)) (G.pT (.core i))), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) ∧ (∀ y, IsHalf (cA D e) y → (∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) ∧ (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True) → y = y') ∧ (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf e u ∧ W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) ≠ W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y')) := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he
  classical
  obtain ⟨hS, hT⟩ := selfDual_core G i hi
  set Λ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) := latO (G.pS (.core i)) (G.pT (.core i))
    (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True) with hΛ
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hinf : infPart D e = 0 := Formalism.IndefR.Fin.infPart_idemSum he
  have hfin : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hdual : ∀ u, IsHalf (cA D e) u → (u ∈ Λ ↔ ∀ l ∈ Λ, IsHalf e l →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l u) = 1) :=
    GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf D W.ψ _ _ _ _ W.ψ_std hS hT e hee hec hinf hfin
  obtain ⟨K, hK, hKΛ⟩ : ∃ K : ℕ, 0 < K ∧ ∀ u ∈ Λ, K • u ∈ depLat G (.core i) := by
    obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := G.pT (.core i)) (ΛT := G.latT (.core i)) hS
      (G.pl.modul_ne_bot sc)
    refine ⟨K, hK, fun u hu => ⟨nsmul_mem hu K, fun e' he' => ?_⟩⟩
    rw [smul_comm]
    exact h _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e'
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he'])) _ hu)

  have hKy : ∀ y, IsHalf (cA D e) y → (∀ u ∈ depLat G (.core i),
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) → K • y ∈ Λ := by
    intro y hy hyt
    refine (hdual _ (GlobalTheory.StdHalfLat.half_nsmul hy K)).2 fun l hl _ => ?_
    rw [← GlobalTheory.DownLift.SplitSep.symplO_nsmul_swap]
    exact hyt _ (hKΛ l hl)
  let A : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) :=
    { carrier := {y | IsHalf (cA D e) y ∧ ∀ u ∈ depLat G (.core i),
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1}
      add_mem' := fun {a b} ha hb => ⟨isHalf_add ha.1 hb.1, fun u hu => by
        rw [GlobalTheory.ConjHalfDual.symplO_add_right', AddChar.map_add_eq_mul, ha.2 u hu, hb.2 u hu, one_mul]⟩
      zero_mem' := ⟨isHalf_zero _, fun u _ => by rw [symplO_zero_right, AddChar.map_zero_eq_one]⟩
      neg_mem' := fun {a} ha => ⟨isHalf_neg ha.1, fun u hu => by
        rw [symplO_neg_right, AddChar.map_neg_eq_inv, ha.2 u hu, inv_one]⟩ }
  let KΛ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) := Λ.map (nsmulAddMonoidHom K)
  have hKΛle : KΛ ≤ Λ := by
    rintro _ ⟨w, hw, rfl⟩
    exact nsmul_mem hw K
  have finΛ : GlobalTheory.AscFin.FinLat Λ := GlobalTheory.AscFinWit.finLat_latO (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hT)
  have finKΛ : GlobalTheory.AscFin.FinLat KΛ :=
    finLat_of_nsmul finΛ hKΛle hK (fun u hu => ⟨u, hu, rfl⟩)
  let N : AddSubgroup ↥Λ := KΛ.addSubgroupOf Λ
  haveI : CompactSpace ↥Λ := isCompact_iff_compactSpace.mp finΛ.cpt
  have hNopen : IsOpen (N : Set ↥Λ) := by
    obtain ⟨U, hU, h0, hUK⟩ := finKΛ.opn
    refine AddSubgroup.isOpen_of_mem_nhds N (g := 0) ?_
    refine Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds (by simpa using h0)) ?_
    intro a ha
    exact AddSubgroup.mem_addSubgroupOf.2 (hUK _ ha (finΛ.fin _ a.2))
  haveI : Finite (↥Λ ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N hNopen
  let f : ↥A →+ ↥Λ :=
    { toFun := fun y => ⟨K • (y : WO (G.pS (.core i)) (G.pT (.core i))), hKy _ y.2.1 y.2.2⟩
      map_zero' := by ext1; simp
      map_add' := fun a b => by ext1; simp [nsmul_add] }
  let g : ↥A →+ ↥Λ ⧸ N := (QuotientAddGroup.mk' N).comp f
  have hker : ∀ y : ↥A, y ∈ g.ker ↔ (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ Λ := by
    intro y
    rw [AddMonoidHom.mem_ker]
    change (QuotientAddGroup.mk (f y) : ↥Λ ⧸ N) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    change K • (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ KΛ ↔ _
    constructor
    · rintro ⟨w, hw, hwe⟩
      have : w = (y : WO (G.pS (.core i)) (G.pT (.core i))) := nsmul_inj hK (by simpa using hwe)
      exact this ▸ hw
    · intro hy
      exact ⟨_, hy, by simp⟩
  haveI : Finite (↥A ⧸ g.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective g)
  haveI : Fintype (↥A ⧸ g.ker) := Fintype.ofFinite _
  let sec : ↥A ⧸ g.ker → ↥A := Function.surjInv QuotientAddGroup.mk_surjective
  have hsec : ∀ q, (QuotientAddGroup.mk (sec q) : ↥A ⧸ g.ker) = q := Function.surjInv_eq _
  have hsame : ∀ a b : ↥A, ((a : WO (G.pS (.core i)) (G.pT (.core i))) - b ∈ Λ) ↔
      (QuotientAddGroup.mk a : ↥A ⧸ g.ker) = QuotientAddGroup.mk b := by
    intro a b
    rw [QuotientAddGroup.eq, hker]
    push_cast
    rw [show -(a : WO (G.pS (.core i)) (G.pT (.core i))) + (b : WO (G.pS (.core i)) (G.pT (.core i))) =
      -((a : WO (G.pS (.core i)) (G.pT (.core i))) - (b : WO (G.pS (.core i)) (G.pT (.core i)))) by abel, neg_mem_iff]
  let R : Finset (WO (G.pS (.core i)) (G.pT (.core i))) :=
    Finset.univ.image (fun q => (sec q : WO (G.pS (.core i)) (G.pT (.core i))))
  have hR : ∀ y ∈ R, y ∈ A := by
    intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (sec q).2
  have hsep : ∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ Λ → y = y' := by
    intro y hy y' hy' hyy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy'
    have := (hsame _ _).1 hyy
    rw [hsec, hsec] at this
    rw [this]
  refine ⟨R, fun y hy => hR y hy, ?_, hsep, ?_⟩
  · intro y hy hyt
    let a : ↥A := ⟨y, hy, hyt⟩
    refine ⟨sec (QuotientAddGroup.mk a), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (hsame a _).2 (hsec _).symm
  · intro y hy y' hy' hne
    have hnot : y - y' ∉ Λ := fun h => hne (hsep y hy y' hy' h)
    have hhalf : IsHalf (cA D e) (y - y') := by
      rw [sub_eq_add_neg]
      exact isHalf_add (hR y hy).1 (isHalf_neg (hR y' hy').1)
    obtain ⟨l, hl, hle, hne1⟩ : ∃ l ∈ Λ, IsHalf e l ∧
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y')) ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hnot ((hdual _ hhalf).2 hc)
    refine ⟨l, hl, hle, fun h => hne1 ?_⟩
    have hsplit : symplO (G.pS (.core i)) (G.pT (.core i)) l y =
        symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y') + symplO (G.pS (.core i)) (G.pT (.core i)) l y' := by
      rw [← GlobalTheory.ConjHalfDual.symplO_add_right', sub_add_cancel]
    rw [hsplit, AddChar.map_add_eq_mul] at h
    exact (mul_eq_right₀ (psi_ne_zero _ _)).1 h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusProdLocalUnitIdeles
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

noncomputable section

namespace GlobalTheory.ProductIdeleModulus

theorem exists_under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact bot_le
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQc, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, ?_⟩
  ext1
  exact hQc

theorem valuation_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x = 1 ↔ Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem norm_comp_le_one {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : GlobalTheory.IdemSupport.Comp D Φ)
    {z : AE D} (hz : finPart D z ∈ intAE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
      ((Algebra.norm (AF D.host.F) z).2 (Q.under (𝓞 D.host.F)))) ≤ 1 := by
  have hm : finPart D (z * cA D z) ∈ intAE D := by
    rw [map_mul]
    exact GlobalTheory.SplitLatBasis.mul_mem_intAE D hz (GlobalTheory.IdemSupport.finPart_cA_mem hz)
  have h := (hΦ.int _).1 hm Q
  rw [← GlobalTheory.SplitDetCharacter.algebraMap_norm, hΦ.base] at h
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h

theorem absFin_eq_one_of_int {D : D7} (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D)
    (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin
  refine (finprod_congr fun v => ?_).trans finprod_one
  obtain ⟨Q, rfl⟩ := exists_under_eq (E := D.host.E) v
  have a1 := norm_comp_le_one hΦ h1 Q
  have a2 := norm_comp_le_one hΦ h2 Q
  have hn : Algebra.norm (AF D.host.F) (x : AE D) * Algebra.norm (AF D.host.F) ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hprod : Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
        ((Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)))) *
      Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
        ((Algebra.norm (AF D.host.F) ((x⁻¹ : (AE D)ˣ) : AE D)).2 (Q.under (𝓞 D.host.F)))) = 1 := by
    rw [← map_mul, ← map_mul]
    have : (Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)) *
        (Algebra.norm (AF D.host.F) ((x⁻¹ : (AE D)ˣ) : AE D)).2 (Q.under (𝓞 D.host.F)) = 1 := by
      have := congrArg (fun a : AF D.host.F => a.2 (Q.under (𝓞 D.host.F))) hn
      exact this
    rw [this, map_one, map_one]
  have hv1 : Valued.v (GlobalTheory.AdeleBaseChange.locMap D.host.F Q
      ((Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)))) = 1 :=
    le_antisymm a1 (hprod.symm.le.trans (mul_le_of_le_one_right' a2))
  have hv := (GlobalTheory.TwU.IntegralHilbert90Unramified.locMap_val_eq_one_iff Q _).1 hv1
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D (Q.under (𝓞 D.host.F)) x : (Fv D.host.F (Q.under (𝓞 D.host.F)))ˣ) :
      Fv D.host.F (Q.under (𝓞 D.host.F))) = (Algebra.norm (AF D.host.F) (x : AE D)).2 (Q.under (𝓞 D.host.F)) := rfl
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, e, hv]

end GlobalTheory.ProductIdeleModulus

namespace GlobalTheory.TopLevelInv

theorem absFin_prod_locIdele_unit : ∀ {D : D7} (P : Finset (Pl D.host.E)) (y : ∀ w : P, (Kw w.1)ˣ),
    (∀ w, valuation (Kw w.1) (y w : Kw w.1) = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (∏ w : P, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) = 1 := by
  intro D P y hy
  have hone : ∀ w : P, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) = 1 := by
    intro w
    have hv : Valued.v ((y w : Kw w.1)) = 1 := (GlobalTheory.ProductIdeleModulus.valuation_eq_one_iff w.1 _).1 (hy w)
    refine GlobalTheory.ProductIdeleModulus.absFin_eq_one_of_int _ ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w.1 (y w)).2 hv.le) ?_
    rw [← map_inv]
    refine (GlobalTheory.LFun.EulerTie.locIdele_int_iff w.1 (y w)⁻¹).2 ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  refine Finset.prod_induction _ (fun z => GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = 1)
    (fun a b ha hb => by rw [GlobalTheory.SplitLinear.absFin_mul, ha, hb, one_mul]) ?_ (fun w _ => hone w)
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]

end GlobalTheory.TopLevelInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlOrbitIntegralDepthDatumMemSubfield
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.SmallFInF

section Helpers
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_valLe (c : kˣ) : IsOpen {t : k | valuation k t ≤ valuation k (c : k)} := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  have e : {t : k | valuation k t ≤ valuation k (c : k)} = (fun t => t / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_div₀,
      div_le_one₀ h0]
  rw [e]
  exact IsOpen.preimage (continuous_id.div_const _) Valuation.isOpen_integer

theorem isOpen_cosetM {n m : Type} [Fintype n] [Fintype m] (c : kˣ) (x : Matrix n m k) :
    IsOpen {y : Matrix n m k | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_valLe c).preimage (f := fun y : Matrix n m k => y i j - x i j) (by fun_prop)

theorem isCompact_ballM {n : Type} [Fintype n] (R : kˣ) :
    IsCompact {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} := by
  have h0 : 0 < valuation k (R : k) := zero_lt_iff.2 (by simp)
  have e : {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} =
      (fun z : Matrix n n k => (R : k) • z) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨(R : k)⁻¹ • y, fun i j => ?_, ?_⟩
      · rw [Valuation.mem_integer_iff]
        simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        rw [inv_mul_le_iff₀ h0, mul_one]; exact hy i j
      · simp [smul_smul]
    · rintro ⟨z, hz, rfl⟩ i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hz i j))
  rw [e]
  exact isCompact_intMatrix.image (continuous_const_smul _)

end Helpers

theorem smallF_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → 1 ≤ e → CondLE ϖ e ν → ¬ IsUnram ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u (1 / 2) ∈ F) → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → (∀ X, Ψ X ∈ F) → ∀ h : GL D k, smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F := by
  intro k _ _ _ _ _ _ A A' D _ _ _ _ _ _ F J hJo hJK σ ν ϖ e hϖ he hcond hram hνF hapF c Ψ hΨ hΨF h
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨R, N, hbd, hper⟩ := _root_.GlobalTheory.DepthBound.latticeDepth_comp_frameBlock_bounded_periodic σ hϖ c hΨ h
  set Y := Y0 k σ * h.val with hY
  set cN : kˣ := ϖ ^ N with hcN
  set z : ℂ := (Fintype.card D : ℂ) / 2 with hz
  have hzF : ∀ u : kˣ, apow u z ∈ F := fun u => by
    have : apow u z = (apow u (1 / 2)) ^ (Fintype.card D) := by
      simp only [apow, hz]
      rw [← Complex.cpow_nat_mul]; congr 1; ring
    rw [this]; exact pow_mem (hapF u) _
  let Cs : Matrix A' A' k → Set (GL A' k) :=
    fun x => {g | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (cN : k)}
  have hCs_meas : ∀ x, MeasurableSet (Cs x) := fun x =>
    ((isOpen_cosetM cN x).preimage Units.continuous_val).measurableSet
  have hCs_eq : ∀ x y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) →
      Cs x = Cs y := by
    intro x y hxy
    ext g
    simp only [Cs, Set.mem_setOf_eq]
    constructor
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) ((Valuation.map_sub_swap _ _ _).le.trans (hxy i j))
      simpa using this
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) (hxy i j)
      simpa using this
  have hcoset : ∀ x, ∫ g in Cs x, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
    intro x
    by_cases hs : ∃ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) ∧ y.det = 0
    · obtain ⟨y, hy, hy0⟩ := hs
      rw [hCs_eq x y hy]
      rw [_root_.GlobalTheory.CosetVanish.integral_coset_singular_eq_zero (haarVol J) ν z hram cN y hy0]
      exact F.zero_mem
    · push_neg at hs
      exact _root_.GlobalTheory.GLBallInt.integral_glBall_mem F hJo hJK ν z hϖ hcond hνF hzF cN x hs

  let L : AddSubgroup (Matrix A' A' k) :=
    { carrier := {Z | ∀ i j, valuation k (Z i j) ≤ valuation k (cN : k)}
      add_mem' := fun ha hb i j => Valuation.map_add_le _ (ha i j) (hb i j)
      zero_mem' := fun i j => by simp
      neg_mem' := fun ha i j => by simpa using ha i j }
  let q : Matrix A' A' k → Matrix A' A' k ⧸ L := QuotientAddGroup.mk
  have hq : ∀ x y : Matrix A' A' k, q x = q y ↔ ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k) := by
    intro x y
    rw [QuotientAddGroup.eq]
    refine forall₂_congr fun i j => ?_
    show valuation k ((-x + y) i j) ≤ _ ↔ _
    rw [show (-x + y) i j = -(x i j - y i j) by simp; ring, Valuation.map_neg]

  obtain ⟨T0, hT0⟩ := (isCompact_ballM (n := A') R).elim_finite_subcover
    (fun y : Matrix A' A' k => {x : Matrix A' A' k | ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k)})
    (fun y => isOpen_cosetM cN y)
    (fun x _ => Set.mem_iUnion.2 ⟨x, fun i j => by simp⟩)
  classical
  let T : Finset (Matrix A' A' k ⧸ L) := T0.image q
  set f : GL A' k → ℂ := fun g => Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) z with hf
  have hdec : f = fun g => ∑ t ∈ T, ({g : GL A' k | q g.val = t}).indicator f g := by
    funext g
    by_cases h0 : f g = 0
    · rw [h0]; symm
      refine Finset.sum_eq_zero fun t _ => ?_
      simp [Set.indicator_apply, h0]
    · have hΨ0 : Ψ (g.val * Y) ≠ 0 := fun h1 => h0 (by simp [hf, h1])
      have hB := hbd g.val hΨ0
      obtain ⟨y, hyT, hy⟩ := Set.mem_iUnion₂.1 (hT0 hB)
      have hqt : q g.val ∈ T := Finset.mem_image.2 ⟨y, hyT, ((hq _ _).2 hy).symm⟩
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [Finset.sum_ite_eq]
      simp [hqt]
  show ∫ g, Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D : ℂ) / 2) ∂(haarVol J) ∈ F
  change ∫ g, f g ∂(haarVol J) ∈ F
  by_cases hint : Integrable f (haarVol J)
  · have hmeas : ∀ t, MeasurableSet {g : GL A' k | q g.val = t} := by
      intro t
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
      have : {g : GL A' k | q g.val = q y} = Cs y := by
        ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
      rw [this]; exact hCs_meas y
    rw [hdec, integral_finsetSum _ (fun t _ => hint.indicator (hmeas t))]
    refine sum_mem fun t _ => ?_
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
    have hset : {g : GL A' k | q g.val = q y} = Cs y := by
      ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
    rw [integral_indicator (hmeas _), hset]
    have hc : ∫ g in Cs y, f g ∂(haarVol J) =
        ∫ g in Cs y, Ψ (y * Y) * ((ν (gdet g) : ℂ) * apow (gdet g) z) ∂(haarVol J) := by
      refine setIntegral_congr_fun (hCs_meas y) fun g hg => ?_
      have h1 : g.val = y + (g.val - y) := by abel
      have h2 : Ψ (g.val * Y) = Ψ (y * Y) := by
        rw [h1, hper y (g.val - y) (fun i j => hg i j)]
      simp only [hf, h2, mul_assoc]
    rw [hc, integral_const_mul]
    exact F.mul_mem (hΨF _) (hcoset y)
  · rw [integral_undef hint]; exact F.zero_mem

end GlobalTheory.SmallFInF
end

