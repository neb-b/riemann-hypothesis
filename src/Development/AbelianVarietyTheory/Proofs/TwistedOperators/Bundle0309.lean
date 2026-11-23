module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorTraceEqConstMulLocalTrace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.PureTensorTrace

theorem isIntegralOp_smoothOp {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
    [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ}
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ ρ f (smoothOp ρ μ f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf hc v
  refine ⟨?_, ?_⟩
  · have := integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
    simpa only [map_smul, smul_eq_mul] using this
  · rw [hρ.map_smoothOp (μ := μ) hf hc l v]
    simp only [smul_eq_mul]

theorem hasTrace_update_eq_const_mul : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ c : ℂ, ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, (∃ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b) ∧ ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V (Function.update ff u f)) (c * b) := by
  intro D V u μf hμ hK1 ν hν W _ _ σ hσ N _ _ π hπi hπa hloc ff hff
  haveI : (μf u).IsHaarMeasure := hμ u
  obtain ⟨H, K, hKo, hHc, hHf, hHop⟩ := _root_.GlobalTheory.OffOp.exists_offOp D V u μf hμ hK1 ν hν W σ hσ.1 ff hff
  have hcont : Continuous (locFin V u) := (continuous_emb _ _ u).subtype_mk _
  have hρ : GlobalTheory.PRep.IsSmooth (σ.comp (locFin V u)) := fun x => (hσ.1 x).preimage hcont
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.FinMultAway.exists_finset_fixed_away D V u W σ hσ N π hπi hπa hloc K hKo
  have hrange : ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))),
      LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
    refine ⟨s, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hs _ fun k hk hk1 => hHf x k hk hk1
  have hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id := fun φ =>
    _root_.GlobalTheory.SchurAdm.schur_admissible (Gv V u) (Kv V u) (isOpen_stabLoc _ _ _ u) (isCompact_stabLoc _ _ _ u) N π hπi hπa
      φ.toLinearMap fun g x => Representation.IntertwiningMap.isIntertwining _ _ φ g x
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.IsoTrace.trace_mul_isotypic (Gv V u) N W π (σ.comp (locFin V u)) hπi hschur hloc H
    (fun g x => hHc g x) hrange
  refine ⟨c, fun f hf => ⟨?_, ?_⟩⟩
  · have hfd := hπa.finiteDimensional_range_smoothOp (μ := μf u) hf.1 hf.2 (isOpen_stabLoc _ _ _ u)
      (isCompact_stabLoc _ _ _ u) (K := Kv V u)
    exact ⟨_, _, isIntegralOp_smoothOp hπa.1 hf.1 hf.2, hfd, rfl⟩
  · rintro b ⟨A, hA, hAb⟩
    obtain rfl := hA.unique (isIntegralOp_smoothOp hπa.1 hf.1 hf.2)
    have hB := isIntegralOp_smoothOp (μ := μf u) hρ hf.1 hf.2
    refine ⟨_, hHop f hf _ hB, hc _ _ (fun φ => ?_) b hAb⟩
    ext x
    exact (hπa.1.map_smoothOp_of_intertwining hρ hf.1 hf.2 φ.toLinearMap
      (fun g v => Representation.IntertwiningMap.isIntertwining _ _ φ g v) x).symm

end GlobalTheory.PureTensorTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientCharPartialLEntireNonvanishingIntegers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.QuotL

variable {D : D7}

theorem trivialOnF {c : Com D} (hc : c.Is) {k : ℕ} (hk : k < c.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.TrivialOnF (c.χ k) := fun a => by
  obtain ⟨⟨η, hη⟩, h⟩ := (hc.hecke k hk).2
  exact (h η hη a).trans (pow_zero _)

theorem quotL_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, i < j → j < c.m →
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
  intro D c hc i j hij hj
  have hi : i < c.m := hij.trans hj
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.χ i) τ (-e) ∧
      HasInfExp D (c.χ j) τ (-e') ∧ e ≠ e' :=
    ⟨τ, -(c.a i τ), -(c.a j τ), by rw [neg_neg]; exact hc.exp i hi τ, by rw [neg_neg]; exact hc.exp j hj τ,
      fun h => hc.ne i j hij hj τ (neg_injective h)⟩
  have R := GlobalTheory.HeckeRatio.heckeRatioPos D (c.χ i) (c.χ j) (hc.hecke i hi).1 (hc.hecke j hj).1
    (trivialOnF hc hi) (trivialOnF hc hj) hexp
  obtain ⟨Λ, hL, -⟩ := (R 0).2 c.S
  obtain ⟨hd, hp⟩ := hL
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h0 => ?_⟩
  · have hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
        GlobalTheory.LFun.UnrAt (c.χ i * (c.χ j)⁻¹) w := fun w hw =>
      (hc.unr i hi w hw).mul (hc.unr j hj w hw).inv
    have hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · obtain ⟨Λn, hLn, hpos⟩ := (R n).2 c.S
    have hEq : Λ = Λn := GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.IsPartialL.unique ⟨hd, hp⟩ hLn
    have := (hpos n h1 le_rfl).2
    rw [← hEq, h0, Complex.zero_re] at this
    exact lt_irrefl _ this

end GlobalTheory.EvenOnto.QuotL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.AlgCountDim

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

theorem eventually_evFin_integral (x : AF F) :
    ∀ᶠ v in Filter.cofinite, GlobalTheory.AdelicU.evFin F v x ∈ v.adicCompletionIntegers F := x.2.2

theorem eventually_vac_eq_one (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    (x : Fin n × Fin d → AF F) :
    ∀ᶠ v in Filter.cofinite, M.vac v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) = 1 := by
  have hint : ∀ᶠ v in Filter.cofinite, ∀ i, GlobalTheory.AdelicU.evFin F v (x i) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => eventually_evFin_integral (x i)
  filter_upwards [hM.std, hint] with v hv hi
  rw [hv]
  simp [Set.indicator, hi]


open Classical in
theorem pure_update_eq (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ) (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (x : Fin n × Fin d → AF F)
    (hx : {v | v ≠ a ∧ φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 1}.Finite) :
    ∃ c : ℂ, ∀ ζ : (Fin n × Fin d → Fv F a) → ℂ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ a ζ) x =
        f (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) * (ζ (fun i => GlobalTheory.AdelicU.evFin F a (x i)) * c) := by
  classical
  set s := hx.toFinset with hs
  have ha : a ∉ s := by simp [hs]
  refine ⟨∏ v ∈ s, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)), fun ζ => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset (s := insert a s)]
  · rw [Finset.prod_insert ha, Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    have : v ≠ a := fun h => ha (h ▸ hv)
    rw [Function.update_of_ne this]
  · intro v hv
    simp only [Function.mem_mulSupport] at hv
    by_cases h : v = a
    · simp [h]
    · rw [Function.update_of_ne h] at hv
      simp [hs, h, hv]

section Main

variable (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)


open Classical in
def gens : Set ((Fin n × Fin d → AF F) → ℂ) :=
  Set.range fun p : Σ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), Module.Basis.ofVectorSpaceIndex ℂ (M.Pol ψ emb) ×
      (∀ v : S, Module.Basis.ofVectorSpaceIndex ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v.1))) =>
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) p.2.1 : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (fun v => if h : v ∈ p.1 then
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (p.2.2 ⟨v, h⟩) :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v)


open Classical in
theorem pure_mem_span_gens (hM : M.IsGood ψ) (i : Module.Basis.ofVectorSpaceIndex ℂ (M.Pol ψ emb)) :
    ∀ (S T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ v, v ∉ S → v ∉ T → φ v = M.vac v) →
      (∀ v ∈ T, ∃ j, φ v = ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) j :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ)) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) i : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ ∈
        Submodule.span ℂ (gens M ψ emb) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro T φ _ hoff hT
    choose j hj using hT
    have hfun : (fun v => if h : v ∈ T then
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (j v h) :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v) = φ := by
      funext v
      by_cases h : v ∈ T
      · rw [dite_eq_left h]
        exact (hj v h).symm
      · rw [dite_eq_right h]
        exact (hoff v (Finset.notMem_empty v) h).symm
    exact Submodule.subset_span ⟨⟨T, i, fun v => j v.1 v.2⟩, congrArg (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
      ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) i : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) hfun⟩
  | insert a S ha ih =>
    intro T φ hSB hoff hT
    set g := ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) i : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    have hfin : ∀ x : Fin n × Fin d → AF F,
        {v | v ≠ a ∧ φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 1}.Finite := by
      intro x
      have h2 := Filter.eventually_cofinite.1 (eventually_vac_eq_one M ψ hM x)
      refine ((insert a S ∪ T : Finset _).finite_toSet.union h2).subset ?_
      rintro v ⟨_, hv⟩
      by_cases h : v ∈ insert a S ∪ T
      · exact Or.inl h
      · right
        simp only [Finset.mem_union, not_or] at h
        rw [hoff v h.1 h.2] at hv
        exact hv
    have key : ∀ ζ ∈ Submodule.span ℂ (Set.range fun j =>
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) j :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) : (Fin n × Fin d → Fv F a) → ℂ)),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ) ∈ Submodule.span ℂ (gens M ψ emb) := by
      intro ζ hζ
      induction hζ using Submodule.span_induction with
      | mem ζ hζ =>
        obtain ⟨j, rfl⟩ := hζ
        apply ih (insert a T)
        · intro v
          by_cases h : v = a
          · subst h
            rw [Function.update_self]
            exact (Module.Basis.ofVectorSpace ℂ _ j).2
          · rw [Function.update_of_ne h]
            exact hSB v
        · intro v hvS hvT
          have hva : v ≠ a := fun h => hvT (h ▸ Finset.mem_insert_self _ _)
          rw [Function.update_of_ne hva]
          exact hoff v (by simp [hva, hvS]) (fun h => hvT (Finset.mem_insert_of_mem h))
        · intro v hv
          by_cases h : v = a
          · subst h
            exact ⟨j, by rw [Function.update_self]⟩
          · rw [Function.update_of_ne h]
            exact hT v ((Finset.mem_insert.1 hv).resolve_left h)
      | zero =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a 0) = 0 := funext fun x => by
          obtain ⟨c, hc⟩ := pure_update_eq g φ a x (hfin x)
          rw [hc]
          simp
        rw [this]
        exact zero_mem _
      | add ζ₁ ζ₂ _ _ h₁ h₂ =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a (ζ₁ + ζ₂)) =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ₁) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ₂) :=
          funext fun x => by
            obtain ⟨c, hc⟩ := pure_update_eq g φ a x (hfin x)
            simp only [Pi.add_apply, hc]
            ring
        rw [this]
        exact add_mem h₁ h₂
      | smul r ζ _ h =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a (r • ζ)) = r • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ) :=
          funext fun x => by
            obtain ⟨c, hc⟩ := pure_update_eq g φ a x (hfin x)
            simp only [Pi.smul_apply, smul_eq_mul, hc]
            ring
        rw [this]
        exact Submodule.smul_mem _ r h
    have hmem : φ a ∈ Submodule.span ℂ (Set.range fun j =>
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) j :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) : (Fin n × Fin d → Fv F a) → ℂ)) := by
      have h1 : (⟨φ a, hSB a⟩ : GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) ∈
          Submodule.span ℂ (Set.range (Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)))) := by
        rw [Module.Basis.span_eq]
        trivial
      have := Submodule.apply_mem_span_image_of_mem_span (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)).subtype h1
      rw [← Set.range_comp] at this
      exact this
    simpa using key _ hmem

end Main

theorem rank_algD_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    Module.rank ℂ (M.Pol ψ emb) ≤ Cardinal.aleph0 →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), Module.rank ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ≤ Cardinal.aleph0) →
    Module.rank ℂ (GlobalTheory.SquareAgree.algD M ψ emb) ≤ Cardinal.aleph0 := by
  intro F E _ _ _ _ _ σ n d X W M ψ emb hM hPol hSB
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : Countable (Module.Basis.ofVectorSpaceIndex ℂ (M.Pol ψ emb)) := by
    rw [← Cardinal.mk_le_aleph0_iff, (Module.Basis.ofVectorSpace ℂ _).mk_eq_rank'']
    exact hPol
  haveI : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
      Countable (Module.Basis.ofVectorSpaceIndex ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v))) := fun v => by
    rw [← Cardinal.mk_le_aleph0_iff, (Module.Basis.ofVectorSpace ℂ _).mk_eq_rank'']
    exact hSB v
  have hle : GlobalTheory.SquareAgree.algD M ψ emb ≤ Submodule.span ℂ (gens M ψ emb) := by
    rw [GlobalTheory.SquareAgree.algD, Submodule.span_le]
    rintro _ ⟨f, φ, hf, hφ, hcof, rfl⟩
    have hfin := Filter.eventually_cofinite.1 hcof
    have key : ∀ g ∈ Submodule.span ℂ (Set.range (Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb))),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ ∈ Submodule.span ℂ (gens M ψ emb) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨i, rfl⟩ := hg
        exact pure_mem_span_gens M ψ emb hM i hfin.toFinset ∅ φ hφ (fun v hv _ => by simpa using hv) (by simp)
      | zero =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (((0 : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) φ = 0 :=
          funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
        rw [this]
        exact zero_mem _
      | add g₁ g₂ _ _ h₁ h₂ =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (((g₁ + g₂ : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) φ =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g₁ : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ +
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g₂ : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ :=
          funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
        rw [this]
        exact add_mem h₁ h₂
      | smul r g _ h =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (((r • g : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) φ =
            r • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ :=
          funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
        rw [this]
        exact Submodule.smul_mem _ r h
    exact key ⟨f, hf⟩ (by rw [Module.Basis.span_eq]; trivial)
  calc Module.rank ℂ (GlobalTheory.SquareAgree.algD M ψ emb) ≤ Module.rank ℂ (Submodule.span ℂ (gens M ψ emb)) :=
        Submodule.rank_mono hle
    _ ≤ Cardinal.mk (gens M ψ emb) := rank_span_le _
    _ ≤ Cardinal.aleph0 := by
        rw [Cardinal.mk_le_aleph0_iff]
        exact (Set.countable_range _).to_subtype

end GlobalTheory.AlgCountDim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemOfMkEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

section Quot

variable {V : Type} [AddCommGroup V]

abbrev mLat (m : ℕ) (Λ : AddSubgroup V) : AddSubgroup V := Λ.map (nsmulAddMonoidHom m)

abbrev Qm (m : ℕ) (Λ : AddSubgroup V) : Type := Λ ⧸ (mLat m Λ).addSubgroupOf Λ

def repm {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) : V := ((Quotient.out q : Λ) : V)

theorem mem_mLat {m : ℕ} {Λ : AddSubgroup V} {x : V} : x ∈ mLat m Λ ↔ ∃ l ∈ Λ, m • l = x := by
  simp [mLat]

theorem repm_mem {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) : repm q ∈ Λ := (Quotient.out q : Λ).2

theorem mk_repm {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) :
    (QuotientAddGroup.mk (⟨repm q, repm_mem q⟩ : Λ) : Qm m Λ) = q := by
  have : (⟨repm q, repm_mem q⟩ : Λ) = Quotient.out q := rfl
  rw [this]
  exact QuotientAddGroup.out_eq' q

theorem sub_mem_of_mk_eq {m : ℕ} {Λ : AddSubgroup V} {a b : V} (ha : a ∈ Λ) (hb : b ∈ Λ)
    (h : (QuotientAddGroup.mk (⟨a, ha⟩ : Λ) : Qm m Λ) = QuotientAddGroup.mk (⟨b, hb⟩ : Λ)) : b - a ∈ mLat m Λ := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
  simpa [sub_eq_neg_add] using h

theorem repm_mk_sub {m : ℕ} {Λ : AddSubgroup V} {a : V} (ha : a ∈ Λ) :
    repm (QuotientAddGroup.mk (⟨a, ha⟩ : Λ) : Qm m Λ) - a ∈ mLat m Λ :=
  sub_mem_of_mk_eq (m := m) ha (repm_mem _) (mk_repm _).symm

theorem repm_add_sub {m : ℕ} {Λ : AddSubgroup V} (q q' : Qm m Λ) :
    repm (q + q') - (repm q + repm q') ∈ mLat m Λ := by
  refine sub_mem_of_mk_eq (m := m) (Λ.add_mem (repm_mem q) (repm_mem q')) (repm_mem (q + q')) ?_
  rw [mk_repm]
  conv_rhs => rw [← mk_repm q, ← mk_repm q']
  rfl

theorem repm_zero_mem {m : ℕ} {Λ : AddSubgroup V} : repm (0 : Qm m Λ) ∈ mLat m Λ := by
  have h := repm_mk_sub (m := m) (Λ := Λ) Λ.zero_mem
  have h0 : (QuotientAddGroup.mk (⟨0, Λ.zero_mem⟩ : Λ) : Qm m Λ) = 0 := rfl
  rw [h0, sub_zero] at h
  exact h

end Quot

variable {D : D7}

def lamE (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (x : WO S T) : ℂ :=
  ψ (symplOH S T (e • x) (cA D e • x))

end GlobalTheory.FinDecomp

end
end

