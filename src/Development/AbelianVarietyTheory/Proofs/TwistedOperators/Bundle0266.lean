module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivativeIsotropicDirection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem isoPart_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    isoPart V W C (lineAt θ τ z t) = lineAt θ τ (dirAt V W C τ z) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO V W :=
    { toFun := fun t => isoPart V W C (lineAt θ τ z t)
      map_zero' := by unfold isoPart; rw [AddMonoidHom.map_zero, Matrix.zero_mul]
      map_add' := fun s t => by unfold isoPart; rw [AddMonoidHom.map_add (f := _), Matrix.add_mul] }
  have hL' : IsLineAt θ τ (dirAt V W C τ z) L := by
    refine ⟨(continuous_isoPart V W C).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (isoPart V W C (lineAt θ τ z t)).map (finPart D) = 0
      unfold isoPart
      rw [Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' (isoPart V W C (lineAt θ τ z t)) = _
      unfold isoPart
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      have e : compAt θ τ' ((adj D C * V.gram).map (incA D)) = (adj D C * V.gram).map (tauE D τ') := by
        unfold compAt
        rw [Matrix.map_map]
        congr 1
        funext e
        exact GlobalTheory.FockCompare.comp_incA hθ τ' e
      rw [e]
      split_ifs with h
      · subst h
        unfold dirAt
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem phase_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hCC : adj D C * V.gram * C' = 1) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    phase ψ V W C C' y (lineAt θ τ z t) = Complex.exp (2 * Real.pi * Complex.I *
      ((t * (2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re) : ℝ) : ℂ)) := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  rw [_root_.GlobalTheory.PhaseReal.phase_eq D V W r C C' hCC ψ hψ θ hθ y _ (hL.2.1 t)]
  congr 4
  simp only [hL.2.2 t]
  rw [Finset.sum_eq_single τ (fun b _ hb => by rw [if_neg hb, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re,
    mul_zero]) (by simp), if_pos rfl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

theorem term_dRho_dirAt : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y = (2 * Real.pi * Complex.I * ((2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hs hCC ψ hψ θ hθ μ 𝓨 h G hG τ z y
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re := ⟨_, rfl⟩
  rw [← hc]
  have hL'r := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := V) (T := W) hθ τ (dirAt V W C τ z)

  have hg : ∀ t : ℝ, term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y =
      Complex.exp (2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := fun t => by
    rw [← isoPart_lineAt hθ V W C τ z t, _root_.GlobalTheory.MixedTermTranslate.term_heisO_isoPart D V V' W r C C' B hs ψ hψ μ 𝓨 h G hG y _,
      phase_lineAt hθ V W C C' hCC hψ y τ z t, hc]
  have hd1 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (2 * Real.pi * Complex.I * (c : ℂ) * term ψ V V' W C C' B μ 𝓨 G y) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) (2 * Real.pi * Complex.I * (c : ℂ)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp).const_mul (2 * Real.pi * Complex.I)
      simpa using this
    have h2 := (h1.cexp).mul_const (term ψ V V' W C C' B μ 𝓨 G y)
    rw [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
    exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hg t)

  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : heisO ψ V W (lineAt θ τ (dirAt V W C τ z) 0) (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G) =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G := by
    rw [AddMonoidHom.map_zero, GlobalTheory.OrientedHeis.heisO_zero]
    rfl
  have hd2 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y) 0 := by
    rw [← e0]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓨) (x₀ := (0 : ℝ))
      (F' := fun t x => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D)))
        (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t)
          (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G)) (isoPart V W C x + midPart V V' W B 0))
      (bound := fun _ => K) (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const K) ?_).2
    · exact Filter.Eventually.of_forall fun t =>
        (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 t) hG) _ _).aestronglyMeasurable
    · exact integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0) hG) _ _
    · exact (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0)
        (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)) _ _).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1, GlobalTheory.HeisOrtho.norm_heisO hψ.1]
      exact hK _
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      exact (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL'r hG _ t).const_mul _
  rw [hd2.unique hd1]

end GlobalTheory.MixedTerm.IsoDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TranslatedEvalInj

section Count

open Formalism.MainNotions.S

theorem gfset_countable (I : AutInst) : I.GFset.Countable := by
  classical
  haveI : Countable I.E := (Module.finBasis ℚ I.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin I.n) (Fin I.n) I.E) :=
    inferInstanceAs (Countable (Fin I.n → Fin I.n → I.E))
  haveI : Countable (GL (Fin I.n) I.E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin I.n) I.E → Matrix (Fin I.n) (Fin I.n) I.E)) fun _ _ h => Units.ext h

  let W : GL (Fin I.n) I.E → Set I.GA := fun γ =>
    {x | (∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat x.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))}
  have hsub : I.GFset ⊆ ⋃ γ, W γ := by
    rintro x ⟨γ, -, h1, h2⟩
    exact Set.mem_iUnion.2 ⟨γ, h1, h2⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun γ => Set.Subsingleton.countable ?_)
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((hx1 v).trans (hy1 v).symm))
  · exact Subtype.ext (Units.ext (hx2.trans hy2.symm))

theorem eq_zero_of_ae_fund (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] {fund : Set I.GA}
    (hfund : I.IsFundDom (I.muA μf) fund) {φ : I.GA → ℂ} (hc : Continuous φ)
    (hinv : ∀ γ ∈ I.GFset, ∀ y, φ (γ * y) = φ y) (h0 : φ =ᵐ[(I.muA μf).restrict fund] 0) (y : I.GA) : φ y = 0 := by
  by_contra hy
  obtain ⟨hl, -, -, -, hpos⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf

  have hpre : ∀ γ : I.GA, ∀ A : Set I.GA, I.muA μf A = 0 → I.muA μf ((fun z => γ * z) ⁻¹' A) = 0 := by
    intro γ A hA
    obtain ⟨t, hAt, ht, ht0⟩ := exists_measurable_superset_of_null hA
    refine measure_mono_null (Set.preimage_mono hAt) ?_
    have hf : AEMeasurable (fun z => γ * z) (I.muA μf) :=
      (continuous_const_mul γ).measurable.aemeasurable
    rw [← Measure.map_apply_of_aemeasurable hf ht, hl γ]
    exact ht0
  have hopen : IsOpen {z | φ z ≠ 0} := isOpen_ne_fun hc continuous_const

  have hnull : I.muA μf ({z | φ z ≠ 0} ∩ fund) = 0 := by
    have h1 : ∀ᵐ z ∂(I.muA μf), z ∈ fund → φ z = 0 := (ae_restrict_iff' hfund.1).1 h0
    rw [ae_iff] at h1
    refine measure_mono_null ?_ h1
    intro z hz
    exact fun h => hz.1 (h hz.2)

  have hcov : {z | φ z ≠ 0} ⊆ ⋃ γ ∈ I.GFset, (fun z => γ * z) ⁻¹' ({z | φ z ≠ 0} ∩ fund) := by
    intro z hz
    obtain ⟨γ, hγ, hγz⟩ := hfund.2.1 z
    refine Set.mem_biUnion hγ ⟨?_, hγz⟩
    show φ (γ * z) ≠ 0
    rw [hinv γ hγ z]
    exact hz
  have hall : I.muA μf {z | φ z ≠ 0} = 0 := by
    refine measure_mono_null hcov ((measure_biUnion_null_iff (gfset_countable I)).2 fun γ _ => ?_)
    exact hpre γ _ hnull
  exact (hpos _ hopen ⟨y, hy⟩).ne' hall

theorem castGA_symm_mem {I I' : AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

end Count

section Cyclic

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : Formalism.IndefR.Datum.InfFam D} {M : DSModel V S} {J : Set (GA D V)}
  {χ : GA D V → ℂ}

theorem eq_zero_of_value {T : MMap M} (hT : IsMultMap θ M J χ T) (v₀ : M.Vec) (hv₀ : ∀ τ, (v₀ τ : M.H τ) ≠ 0)
    (h0 : T v₀ = 0) : T = 0 := by
  classical

  have step : ∀ (u : M.Vec) (τ : D.what₂.Tau), T u = 0 → (u τ : M.H τ) ≠ 0 →
      ∀ w : M.sm τ, T (Function.update u τ w) = 0 := by
    intro u τ hu hne w
    funext x
    obtain ⟨ℓ, hℓ, hval⟩ := hT.cont τ u x
    have horb : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ℓ (M.rep τ g (u τ)) = 0 := by
      intro g hg
      have hmem : M.rep τ g (u τ) ∈ M.sm τ := GlobalTheory.ConjMult.rep_mem_sm M τ hg (u τ).2
      have h1 := hval ⟨_, hmem⟩
      rw [hT.equiv τ g hg u ⟨_, hmem⟩ rfl, hu] at h1
      simpa [rTr] using h1
    have h2 := GlobalTheory.SmoothCyclic.eq_zero_of_orbit D V S M τ ℓ hℓ (u τ) (u τ).2 hne horb w w.2
    rw [hval w] at h2
    exact h2

  have key : ∀ s : Finset D.what₂.Tau, ∀ w : M.Vec, T (fun τ => if τ ∈ s then w τ else v₀ τ) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro w
      simpa using h0
    · intro a s ha ih w
      have hne : ((if a ∈ s then w a else v₀ a : M.sm a) : M.H a) ≠ 0 := by
        simp only [ha, if_false]
        exact hv₀ a
      have h3 := step _ a (ih w) hne (w a)
      convert h3 using 2
      funext τ
      rcases eq_or_ne τ a with rfl | hτ
      · simp
      · simp [hτ]
  apply MultilinearMap.ext
  intro w
  simpa using key Finset.univ w

end Cyclic

end GlobalTheory.TranslatedEvalInj

theorem GlobalTheory.TranslatedEvalInj.eq_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), (∀ τ, (v₀ τ : (MP R).H τ) ≠ 0) → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ S' : MMap (R.MY 0), S' = postOn (R.MY 0) R.e0 S - S → ((fun x => ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) =ᵐ[muX X] 0) → S' = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hmod t v₀ hv₀ S hS S' hS' hae

  have hsub : ∀ k ∈ (levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) : Set (GA D (Yc D 0))),
      k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) ∧
        levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k =
          levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) k := by
    intro k hk
    have h1 : Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k) = 1 := Subgroup.mem_bot.1 hk.2.2
    refine ⟨⟨hk.1, hk.2.1, ?_⟩, ?_⟩
    · change Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k) ∈ (R.levR F true).H
      rw [h1]
      exact Subgroup.one_mem _
    · rw [GlobalTheory.FlagAction.levChi_flag1]
      have e1 := Formalism.IndefR.Lev.levFn_withP (V := Yc D 0) (β := R.βY 0) (L := R.dat0 R.triv) (R.levR F true)
        (finE (Yc D 0) k)
      have e2 : Formalism.L2.DIV.ext1 (R.levR F true).H (R.levR F true).chi
          (Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k)) = 1 := by
        rw [h1]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      calc levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k
          = ((Formalism.L2.DIV.ext1 (R.levR F true).H (R.levR F true).chi
              (Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k)) *
              Formalism.L2.DIV.levFn (R.βY 0) (flagL (R.dat0 R.triv)) (finE (Yc D 0) k) : ℂˣ) : ℂ) :=
            congrArg Units.val e1
        _ = ((Formalism.L2.DIV.levFn (R.βY 0) (flagL (R.dat0 R.triv)) (finE (Yc D 0) k) : ℂˣ) : ℂ) := by
            rw [e2, one_mul]
  have hSp : S ∈ Mult R.θ (R.MY 0) (levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) : Set (GA D (Yc D 0)))
      (levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) :=
    GlobalTheory.ProjectedLift.mult_mono hsub hS
  have hS'm : S' ∈ Mult R.θ (R.MY 0) (levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) : Set (GA D (Yc D 0)))
      (levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) := by
    rw [hS']
    exact Submodule.sub_mem _
      (GlobalTheory.ProjectedLift.postOn_gaL_mem (β := R.βY 0) (L := R.dat0 R.triv) hmod.inf R.eG
        (RealDat.eC (A := A) D.what₂.embLL) hSp) hSp
  have hT := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hS'm

  have hQ : ∀ γ ∈ X.B.I.GFset, (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    have h1 := GlobalTheory.TranslatedEvalInj.castGA_symm_mem h.symm γ hγ
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    change Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact h1

  have hfun : ∀ y : X.B.I.GA, S' v₀ ((iotaX X h).symm (y * iotaX X h t)) =
      ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm y) t) := by
    intro y
    rw [map_mul]
    exact congrArg (fun z : GA D (D.sp.Y 0) => S' v₀ ((iotaX X h).symm y * z)) ((iotaX X h).symm_apply_apply t)
  have hv : ∀ y : X.B.I.GA, S' v₀ ((iotaX X h).symm (y * iotaX X h t)) = 0 := by
    have hc : Continuous fun y : X.B.I.GA => S' v₀ ((iotaX X h).symm (y * iotaX X h t)) :=
      (hT.aut v₀).cont.comp ((iotaX X h).symm.continuous.comp (continuous_mul_const _))
    have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y,
        S' v₀ ((iotaX X h).symm (γ * y * iotaX X h t)) = S' v₀ ((iotaX X h).symm (y * iotaX X h t)) := by
      intro γ hγ y
      rw [mul_assoc, map_mul]
      exact (hT.aut v₀).left _ (hQ γ hγ) _
    have hae' : (fun y : X.B.I.GA => S' v₀ ((iotaX X h).symm (y * iotaX X h t))) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
      have e : (fun y : X.B.I.GA => S' v₀ ((iotaX X h).symm (y * iotaX X h t))) =
          fun x => ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) :=
        funext hfun
      rw [e]
      exact hae
    exact GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hc hinv hae'
  have h0 : S' v₀ = 0 := by
    funext g
    have h2 := hv (iotaX X h (g * t⁻¹))
    have e : (iotaX X h).symm (iotaX X h (g * t⁻¹) * iotaX X h t) = g := by
      refine ((congrArg (iotaX X h).symm (map_mul (iotaX X h) (g * t⁻¹) t).symm).trans
        ((iotaX X h).symm_apply_apply _)).trans ?_
      first
        | exact inv_mul_cancel_right g t
        | simp
    rw [e] at h2
    exact h2
  exact GlobalTheory.TranslatedEvalInj.eq_zero_of_value hT v₀ hv₀ h0

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormRightConvolutionLeAdelicHeightPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ENNReal

namespace GlobalTheory.ConvGrowth

open GlobalTheory.AutomorphicL2Unitary

theorem lintegral_sq_le {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) (N : ℝ≥0∞) (hN : ∀ x : G, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (F : L2 Γ μ) :
    ∫⁻ z in S, ‖lift Γ F z‖ₑ ^ (2 : ℝ) ∂μ ≤ N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ := by
  have hm : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  rw [← lintegral_indicator hS,
    lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hS),
    ← lintegral_const_mul'' _ ((Lp.aestronglyMeasurable F).enorm.pow_const _)]
  refine lintegral_mono fun q => ?_
  have e : ∀ γ : Γ, S.indicator (fun z => ‖lift Γ F z‖ₑ ^ (2 : ℝ)) ((γ : G) * q.out) =
      {γ : Γ | (γ : G) * q.out ∈ S}.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) γ := by
    intro γ
    by_cases hγ : (γ : G) * q.out ∈ S
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]
      simp only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]
    · rw [Set.indicator_of_notMem hγ,
        Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]
  rw [tsum_congr e, ← tsum_subtype, ENNReal.tsum_set_const]
  gcongr
  exact hN _

theorem norm_convR_le_height : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Ω : Set (GA D V)}, IsCompact Ω → (∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A)) → ∃ (A : ℕ) (C : ℝ), ∀ f' : GA D V → ℂ, Continuous f' → tsupport f' ⊆ Ω → ∀ M : ℝ, (∀ y, ‖f' y‖ ≤ M) → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (g : GA D V), ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g‖ ≤ C * M * ‖F‖ * GlobalTheory.Grow.height V g ^ A := by
  intro D V μ _ _ Ω hΩ ⟨A, C, hC⟩
  refine ⟨A, (μ Ω ^ (1 / 2 : ℝ)).toReal * Real.sqrt (max C 0), ?_⟩
  intro f' hf' hsupp M hM F g
  set b : ℝ := Real.sqrt (max C 0) * GlobalTheory.Grow.height V g ^ A with hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hh : 0 ≤ GlobalTheory.Grow.height V g := zero_le_one.trans (GlobalTheory.Grow.one_le_height V g)
  have hb0 : 0 ≤ b := by positivity
  set S : Set (GA D V) := (g * ·) '' Ω with hSdef
  have hSc : IsCompact S := hΩ.image (continuous_const_mul g)
  have hS : MeasurableSet S := hSc.isClosed.measurableSet
  have hcount : ∀ x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ S}.encard ≤ ENNReal.ofReal b ^ 2 := by
    intro x
    obtain ⟨hfin, hle⟩ := hC g x
    rw [← hfin.cast_ncard_eq, ← ENNReal.ofReal_pow hb0]
    have e : b ^ 2 = max C 0 * GlobalTheory.Grow.height V g ^ (2 * A) := by
      rw [hb, mul_pow, Real.sq_sqrt (le_max_right _ _), ← pow_mul, mul_comm A 2]
    rw [e]
    calc (((({γ : GQ V | (γ : GA D V) * x ∈ S}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞)
        = ENNReal.ofReal ({γ : GQ V | (γ : GA D V) * x ∈ S}.ncard : ℝ) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  set φ : GA D V → ℂ := GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F with hφ
  have hm : AEStronglyMeasurable φ μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have hmp : MeasurePreserving (g * ·) (μ.restrict Ω) (μ.restrict S) := by
    have := (measurePreserving_mul_left μ g).restrict_preimage_emb (measurableEmbedding_mulLeft g) S
    rwa [hSdef, preimage_image_eq _ (mul_right_injective g)] at this
  have hm' : AEStronglyMeasurable (φ ∘ (g * ·)) (μ.restrict Ω) :=
    hm.restrict.comp_measurePreserving hmp

  have h1 : ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' φ g‖ₑ ≤ ENNReal.ofReal M * eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator hΩ.measurableSet]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy, enorm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (zero_le)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hM y)
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport fun h => hy (hsupp h)]
      simp
    exact hm'

  have h2 : eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω) ≤ eLpNorm φ 2 (μ.restrict S) * μ Ω ^ (1 / 2 : ℝ) := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm').trans (le_of_eq ?_)
    rw [eLpNorm_comp_measurePreserving hm.restrict hmp, Measure.restrict_apply_univ]
    norm_num

  have h3 : eLpNorm φ 2 (μ.restrict S) ≤ ENNReal.ofReal b * eLpNorm F 2 (quotMeasure (GQ V) μ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    calc (∫⁻ z in S, ‖φ z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal b ^ 2 * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure (GQ V) μ) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (lintegral_sq_le (GQ V) μ hS _ hcount F) (by norm_num)
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast two_ne_zero]
    exact Lp.aestronglyMeasurable F
    exact hm.restrict
  have hE := h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right h3 zero_le))
    zero_le)
  have hμ : μ Ω ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΩ.measure_lt_top.ne
  have hfin : ENNReal.ofReal M * (ENNReal.ofReal b * eLpNorm F 2 (quotMeasure (GQ V) μ) * μ Ω ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)) hμ)
  have := ENNReal.toReal_mono hfin hE
  rw [toReal_enorm] at this
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0,
    ENNReal.toReal_ofReal hb0, ← Lp.norm_def, hb]
  ring

end GlobalTheory.ConvGrowth
end

