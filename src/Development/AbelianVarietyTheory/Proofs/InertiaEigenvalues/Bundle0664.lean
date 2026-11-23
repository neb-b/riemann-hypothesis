module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationIndepAinfModel
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0655
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BcSpehProof

theorem hasInfCharGL_unique {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ} (h : HasInfCharGL V τ m)
    (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  unfold GlobalTheory.SphGal.spehInf GlobalTheory.DefiniteBC.spehInf
  rw [← List.sum_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem isUnitarisable_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem isUnitarisable_of_isLocComp (H : GlobalTheory.Published.DiscreteSpectrumGL) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a : ℕ} (ha : 1 ≤ a) (P : CuspSub E a) (hP : GlobalTheory.DiscSpec.IsNormalised P)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : LocIrr w a) (hρ : P.IsLocComp w ρ) : IsUnitarisable ρ.ρ := by
  obtain ⟨V, ⟨hV, hS⟩, -⟩ := (H E a ha).2.1 a 1 P (one_mul a) hP
  have hc := (H E a ha).2.2.2.2 V hV a 1 P hP hS
  obtain ⟨-, σ', -, hσ'⟩ := hc.exLoc w
  obtain ⟨hd, h1⟩ := hc.loc w ρ σ' hρ hσ'
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred)
  obtain ⟨e⟩ := h1.unique h2
  have hu := _root_.GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E a V hV w σ' hσ'
  exact isUnitarisable_of_equiv' ((GlobalTheory.LocGL.IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e).symm hu

theorem hasInfChar_eq_of_sigma {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b : ℕ} {P : CuspSub E a}
    {Q : CuspSub E b} (h : (⟨a, CG.mk P⟩ : Σ c, CG E c) = ⟨b, CG.mk Q⟩) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (hm : P.HasInfChar τ m) (hm' : Q.HasInfChar τ m') : m = m' := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
  exact (CuspSub.Iso.hasInfChar (Quotient.exact (eq_of_heq h2)) hm).unique hm'

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem baseChange_speh_of_discreteSeries (H : GlobalTheory.Published.DiscreteSpectrumGL)
    (hW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
      ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {c : ℕ} {N : Fin c → ℕ} {h : ∑ i, N i = n}
    {V : ∀ i, Submodule ℂ (Sm E (N i))} {σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))}
    {m : Fin c → (E →+* ℂ) → Multiset ℂ} (bc : IsBaseChange π h V σ m) (a d : Fin c → ℕ) (P : ∀ i, CuspSub E (a i))
    (hPn : ∀ i, GlobalTheory.DiscSpec.IsNormalised (P i)) (hPs : ∀ i, GlobalTheory.DiscSpec.IsSpehOf (V i) (P i) (d i))
    (hNad : ∀ i, N i = d i * a i) :
    ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ) (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
        (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
        ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w)) := by
  have hN : ∀ i, 1 ≤ N i := bc.pos
  have hc : ∀ i, GlobalTheory.DiscSpec.HasSpehComp (V i) (P i) (d i) := fun i =>
    (H E (N i) (hN i)).2.2.2.2 (V i) (bc.discrete i) (a i) (d i) (P i) (hPn i) (hPs i)
  choose ρ σ' hρ hσ' using fun i w => (hc i).exLoc w
  choose m' hm1 hm2 using fun i τ => (hc i).inf τ
  have hmm : ∀ i τ, m i τ = GlobalTheory.DefiniteBC.spehInf (d i) (m' i τ) := fun i τ =>
    (hasInfCharGL_unique (bc.discrete i).ne_bot (bc.inf i τ) (hm2 i τ)).trans (spehInf_eq _ _)
  have hpos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i := fun i => by
    have := hN i
    rw [hNad i] at this
    exact ⟨Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this, Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this⟩
  have hcsd : ∀ i, (P i).IsCsd := fun i =>
    GlobalTheory.DiscSpec.isCsd_of_isSpehOf H (hN i) (bc.discrete i) (bc.csd i) (hPn i) (hPs i)
  have hsp : ∀ i w, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ :=
    fun i w => (hc i).loc w (ρ i w) (σ i w) (hρ i w) (bc.loc i w)
  have hun : ∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ := fun i w =>
    ⟨isUnitarisable_of_isLocComp H (hpos i).1 (P i) (hPn i) w (ρ i w) (hρ i w),
      _root_.GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E (N i) (V i) (bc.discrete i) w (σ i w) (bc.loc i w)⟩
  have hm0 : ∀ i τ, m i τ ≠ 0 := fun i τ h0 => by
    have h1 := (bc.inf i τ).1
    rw [h0, Multiset.card_zero] at h1
    have := hN i
    omega
  obtain rfl : N = fun i => d i * a i := funext hNad
  refine ⟨c, a, d, h, P, ρ, m', σ, ⟨hpos, hcsd, hρ, hm1, fun τ lam hl => ?_, fun i j hd hs => ?_, ?_⟩,
    fun i w => ⟨(hun i w).1, (hun i w).2, hsp i w⟩, bc.split⟩
  · rw [← bc.weight τ lam hl]
    exact Finset.sum_congr rfl fun i _ => (hmm i τ).symm
  · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨lam, hl⟩ := hW E n hn π hπ τ
    refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (hm0 i τ) ?_
    rw [hmm i τ, hmm j τ, hd, hasInfChar_eq_of_sigma hs (hm1 i τ) (hm1 j τ)]
  · intro w s ϖ q hs hU α hα
    exact _root_.GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hpos i).2) (fun i => hsp i w) _
      (bc.inert w s ϖ q hs hU α hα)

end GlobalTheory.BcSpehProof

theorem GlobalTheory.BcSpeh.bcSpeh_of_baseChange : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.DiscreteSpectrumGL → BcSpeh := by
  intro H1 H2 E _ _ _ hE n hn π hπ
  obtain ⟨c, N, h, V, σ, m, bc⟩ := H1 E hE n hn π hπ
  choose a d P _ hPn hPs using fun i => (H2 E (N i) (bc.pos i)).1 (V i) (bc.discrete i)
  exact GlobalTheory.BcSpehProof.baseChange_speh_of_discreteSeries H2 _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU hn hπ bc a d P hPn hPs fun i => (hPs i).mul_eq.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bhattScholzeIntegral : GlobalTheory.Published.BhattScholzeIntegral := by
  intro l _ K P₀ e H
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.Prism.realisation_indep_model l K P₀ e H
  refine ⟨?_, ?_⟩
  · intro P AI hstd V _ _ _ _ _ _ _ ρ L hc hcr
    obtain ⟨M, j₀, hj₀⟩ := GlobalTheory.T.crystallineLattice_prismaticFCrystal_perfectPrism l K P AI hstd V ρ L hc hcr
    obtain ⟨j, hj⟩ := ((ha M).2 ↥L.T (fun g => actT L g)).1 j₀ hj₀
    exact ⟨M, j, hj⟩
  · intro T T' _ _ _ _ ρ ρ' E E' j j' hj hj' f hf
    obtain ⟨j₀, hj₀, e₀⟩ := ((ha E).2 T ρ).2 j hj
    obtain ⟨j₀', hj₀', e₀'⟩ := ((ha E').2 T' ρ').2 j' hj'
    obtain ⟨u, hu⟩ := _root_.GlobalTheory.BSP.exists_fHom_of_equivariant l K T ρ T' ρ' E E' j₀ j₀' hj₀ hj₀' f hf
    refine ⟨u, fun x => ?_, fun u' hu' => ?_⟩
    · exact (e₀' _).symm.trans ((congrArg j₀' (u.u_tr a x).symm).trans
        ((hu _).trans (congrArg (f.lTensor (WCb l)) (e₀ x))))
    · refine _root_.GlobalTheory.BSP.fHom_eq_of_realises l K T' ρ' E E' j₀' hj₀' u' u fun y => ?_
      obtain ⟨x, rfl⟩ := (ha E).1.2 y
      exact (congrArg j₀' (u'.u_tr a x)).trans ((e₀' _).trans ((hu' x).trans
        ((congrArg (f.lTensor (WCb l)) (e₀ x).symm).trans (hu _).symm)))

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCycOInvPow
section
noncomputable section

namespace GlobalTheory.AdmLoc.CycWitness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct

section Line

variable {G Qp LL R : Type} [Group G] [Field Qp] [Field LL] [Algebra Qp LL] [CommRing R] [Algebra Qp R]

end Line

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

variable (hK : Function.Surjective (algebraMap Qp K)) (a : ℕ) (θ : G →* LLˣ)
  (hθ : ∀ g, (θ g : LL) = algebraMap Qp LL (((PD.χ g)⁻¹ ^ a : Qpˣ) : Qp))


include hK hθ

end Per

variable {l : ℕ} [Fact l.Prime]

def cycO (P : LocPrime l) (K LL : FinExt l) : ↥(GK K) →* (↥(OL LL))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem P K LL g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }

theorem cycO_val (P : LocPrime l) (K LL : FinExt l) (g : ↥(GK K)) :
    algebraMap ↥(OL LL) ↥LL.1 (cycO P K LL g) = algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g) := rfl

end GlobalTheory.AdmLoc.CycWitness
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentEqImpliesBaseComponentEq
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverRead.CompIndep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mul_mem_map_of_prod {R : Type} [CommRing R] [IsDedekindDomain R] (f : R →+* R) (A I : Ideal R) (m p : R) (hm : m ≠ 0)
    (h : A * A.map f = Ideal.span {m}) (h1 : A * I * (A * I).map f = Ideal.span {m * p}) :
    ∀ b ∈ A.map f, p * b ∈ (A * I).map f := by
  intro b hb
  have h0 : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm
  rw [Ideal.map_mul, ← Ideal.span_singleton_mul_span_singleton, mul_mul_mul_comm, h] at h1
  have h2 := mul_left_cancel₀ h0 h1
  have h3 : p ∈ I.map f := by
    have h4 := Ideal.mem_span_singleton_self p
    rw [← h2] at h4
    exact (Ideal.mul_le_inf h4).2
  rw [Ideal.map_mul, mul_comm p]
  exact Ideal.mul_mem_mul hb h3

theorem smul_pull {R : Type} [CommRing R] {n : ℕ} (κ : Matrix (Fin n) (Fin n) R) (M p : ℕ) (v y : Fin n → R)
    (e : κ *ᵥ (p • v) - p • v = (M * p) • y) : p • (κ *ᵥ v - v) = p • M • y := by
  rw [smul_sub, ← Matrix.mulVec_smul, e, mul_comm M p, mul_smul]

theorem ratio_mul_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (p : ℕ) (I : Ideal (𝓞 E)) (hM : l₂.M = l.M * p) (hI : l₂.Mb = l.Mb * I) :
    ∀ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), (p : 𝓞 E) * b ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have h1 := l₂.prod
  rw [hI, hM, Nat.cast_mul] at h1
  rw [hI]
  refine mul_mem_map_of_prod _ _ _ _ _ (Nat.cast_ne_zero.2 ?_) l.prod h1
  have := l.three_le
  omega

theorem congr_of_marked {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) (M p : ℕ) (hp : p ≠ 0)
    (J J₂ : Ideal (𝓞 D.host.E)) (hJ : ∀ b ∈ J, (p : 𝓞 D.host.E) * b ∈ J₂) (g g' k : GA D V)
    (hk : finHom V k = finHom V (g⁻¹ * g')) (hL : latG V g = latG V g')
    (x : La → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hm : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g,
      x a - (finHom V g).1.mulVec (finVec V (ι a)) = (M * p) • w)
    (hm' : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g',
      x a - (finHom V g').1.mulVec (finVec V (ι a)) = (M * p) • w) :
    ∀ b ∈ J, ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y := by
  refine ((GlobalTheory.Member.AALev.congruences_agree D V k).2 M J).2 fun v hv => ?_
  have hH : latGHat V g' = latGHat V g := by
    rw [GlobalTheory.RecDict.coset_latGHat, GlobalTheory.RecDict.coset_latGHat, hL]
  have hv' : v ∈ (J • (⊤ : Submodule (𝓞 D.host.E) La)).map ι := by
    rw [Submodule.map_smul'', Submodule.map_top, hι.2]
    exact hv
  obtain ⟨a, ha, rfl⟩ := hv'
  have hpa : p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La) := by
    refine Submodule.smul_induction_on (p := fun a => p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La)) ha
      (fun b hb c _ => ?_) (fun s t hs ht => ?_)
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul]
      exact Submodule.smul_mem_smul (hJ b hb) Submodule.mem_top
    · rw [smul_add]
      exact add_mem hs ht
  obtain ⟨w, hw, e⟩ := hm _ hpa
  obtain ⟨w', hw', e'⟩ := hm' _ hpa
  rw [hH] at hw'
  obtain ⟨y, hy, ey⟩ := GlobalTheory.RecDict.coset_fin (latGHat V 1) (latGHat V g) (finHom V g) (finHom V g') 1 (M * p)
    (fun u hu => ((GlobalTheory.MarkCoset.latG_spec D V g).2 u).1 hu) (fun u hu => by simpa using hu)
    (fun u hu => by simpa using hu) _ _ w w' 0 hw hw' (zero_mem _) e e' (by simp)
  refine ⟨y, hy, ?_⟩
  have hf : finVec V (ι (p • a)) = p • finVec V (ι a) := by
    rw [map_nsmul]
    exact AdLat.cap_fv_nsmul D.host.F p _
  rw [hf, one_mul, ← map_inv, ← map_mul, ← hk] at ey
  funext i
  exact GlobalTheory.MarkCoset.nsmul_cancel D.host.F p (Nat.cast_ne_zero.2 hp) (congrFun (smul_pull _ M p _ y ey) i)

theorem comp_eq_of_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h h' : GA D (T.V j σ), (C.dict₂ h).1 = (C.dict₂ h').1 → (T.dict j σ h).1 = (T.dict j σ h').1 := by
  intro D T hT j hj σ hσ C hC h h' hh
  obtain ⟨⟨-, hM, -, hI, -⟩, -, -, -, -, hr, g, e, F, ik, φ, th, -, -, -, hd⟩ := hC
  obtain ⟨hr', -, -, -, -, -, -, hι, -⟩ := hT.adPin j hj σ hσ
  obtain ⟨th', hr'', -, hQ, hK, ⟨x0, -, hR⟩, -⟩ := hT.dictU j hj σ hσ
  obtain ⟨γ, hγ, hΛ, hm, -⟩ := hd h
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hd h'
  rw [← hh] at hΛ' hm'
  have hinj : Function.Injective (fun v : Fin (T.V j σ).rank → D.host.E => v ∘ Fin.cast hr.symm) := fun u v huv =>
    funext fun i => congrFun huv (Fin.cast hr i)
  have hL : latG (T.V j σ) (γ * h) = latG (T.V j σ) (γ' * h') :=
    SetLike.coe_injective (hinj.image_injective (hΛ.symm.trans hΛ'))
  obtain ⟨a, ha, k, hk, eak⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ * h)⁻¹ * (γ' * h'))
  have hp : C.d.pd ≠ 0 := fun h0 => by
    have := C.d.l₂.three_le
    rw [hM, h0] at this
    omega
  have hk' : k ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k).2 ⟨hk, ?_⟩
    have hm₁ := hm
    have hm₂ := hm'
    rw [hM] at hm₁ hm₂
    exact congr_of_marked (T.V j σ) _ hι _ _ hp _ _ (ratio_mul_mem T.Q.l C.d.l₂ _ _ hM hI) (γ * h) (γ' * h') k
      (by rw [eak, map_mul, show finHom (T.V j σ) a = 1 from ha, one_mul]) hL _ hm₁ hm₂
  have q : ∀ δ ∈ GQ (T.V j σ), ∀ u, (T.dict j σ (δ * u)).1 = (T.dict j σ u).1 := fun δ hδ u => by
    obtain ⟨_, -, e⟩ := hQ δ hδ u
    rw [e]
  have q₁ : (T.dict j σ (γ * h * a * k)).1 = (T.dict j σ (γ * h * a)).1 := by
    obtain ⟨_, -, e⟩ := hK k hk' (γ * h * a)
    rw [e]
  have q₂ : (T.dict j σ (γ * h * a)).1 = (T.dict j σ (γ * h)).1 := by
    obtain ⟨_, -, e⟩ := hR (γ * h) a ha
    rw [e]
  rw [← q γ hγ h, ← q γ' hγ' h', ← q₂, ← q₁, mul_assoc (γ * h), ← eak, mul_inv_cancel_left]

end GlobalTheory.CoverRead.CompIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductiveStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_unique_of_inductive : BrauerDegreeZero → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ε ε' : WD h → ℂˣ), (∀ x y, ε (x.lpSum y) = ε x * ε y) → (∀ x y, ε' (x.lpSum y) = ε' x * ε' y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → ε x = ε y ∧ ε' x = ε' y) → (∀ ξ hξ, ε (WD.lpOfChar h ξ hξ) = ε' (WD.lpOfChar h ξ hξ)) → (∀ (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∀ (χ₁ χ₂ : H →* ℂˣ) (n : ℕ) (b₁ b₂ : WDRep h (Fin n → ℂ)) (v₁ v₂ : Fin n → ℂ), n = H.index → (∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) → (∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂) → Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤ → Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤ → ε (WD.mk b₁) * ε' (WD.mk b₂) = ε (WD.mk b₂) * ε' (WD.mk b₁)) → ∀ x, ε x = ε' x := by
  first | exact @GlobalTheory.WeilBrauer.eq_of_induced | exact GlobalTheory.WeilBrauer.eq_of_induced | (intros; apply GlobalTheory.WeilBrauer.eq_of_induced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def Maps (V : Submodule ℂ (Sm E a)) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

theorem iSup_range_eq (V : Submodule ℂ (Sm E a)) (hs : _root_.GlobalTheory.CuspRep.IsStable V) (hi : ∀ W ≤ V, _root_.GlobalTheory.CuspRep.IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) : ⨆ f : Maps V w σ, LinearMap.range f.1 = V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps V w σ) v, act o (f.1 v) ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => hs o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps V w σ) ⟨v, rfl⟩
  refine (hi _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (⨆ f : Maps V w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w
            (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, h1, hf⟩ := h
    refine h0 (LinearMap.ext fun v => ?_)
    have : f v ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨f, h1, hf⟩ : Maps V w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

theorem exists_comp_ne_zero (V : Submodule ℂ (Sm E a)) (hs : _root_.GlobalTheory.CuspRep.IsStable V) (hi : ∀ W ≤ V, _root_.GlobalTheory.CuspRep.IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) {X : Type} [AddCommGroup X] [Module ℂ X] (β : V →ₗ[ℂ] X) (hβ : β ≠ 0) :
    ∃ f : Maps V w σ, β ∘ₗ f.1.codRestrict V f.2.1 ≠ 0 := by
  by_contra hc
  push Not at hc
  refine hβ (LinearMap.ext fun φ => ?_)
  have hle : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (LinearMap.ker β).map V.subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨f.1 v, f.2.1 v⟩, LinearMap.congr_fun (hc f) v, rfl⟩
  rw [iSup_range_eq V hs hi w σ h] at hle
  obtain ⟨ψ, h1, h2⟩ := hle φ.2
  obtain rfl : ψ = φ := Subtype.ext h2
  exact h1

end GlobalTheory.LocDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistablePeriods
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem semistablePeriodFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Frame bk N d ρ), F.IsDR ∧ ((∀ g, s.κ g = 1) → F.IsCr) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨N, F, Y, Z, hY, hZ, hW⟩ := GlobalTheory.T.exists_breuilKisinBasis_of_semistablePeriods l K bk τ hτ d ρ hρ s
  obtain ⟨F₀, rfl, hε⟩ := GlobalTheory.T.semistablePeriods_breuilKisin_galoisStable l K bk τ hτ d ρ hρ s N F Y Z hY hZ hW
  refine ⟨N, F₀, ?_, ?_⟩
  · exact GlobalTheory.T.semistablePeriodFrame_isDeRham l K bk τ hτ d ρ hρ s N F₀ Y Z hY hZ hW hε
  · intro hκ
    exact GlobalTheory.T.isCr_of_wSeed_alt l K bk τ hτ d ρ hρ s N F₀ Y Z hY hZ hW hε hκ

end GlobalTheory
end

