module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0182
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwart
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactAvgSchwartz

variable {D : D7}

theorem mt_mul_inv_self (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_inv]
  exact Units.mul_inv _

theorem map_cancel {R : Type} [CommRing R] (φ : AE D →+* R) (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).map φ * (Formalism.L2.Theta.mt V g⁻¹).map φ = 1 := by
  rw [← Matrix.map_mul, mt_mul_inv_self, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem map_mul_entry {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin m) (Fin n) R) : (fun i j => φ ((M * x) i j)) = fun i j => ∑ c, φ (M i c) * φ (x c j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul]

theorem integrable_and_projS_mem {θ : InfFam D} (hθ : IsInfFam θ) {T : HSp D} {n : ℕ} {K : Subgroup (GA D T)}
    (hK : IsCompact (K : Set (GA D T))) (ν : Measure K) [IsFiniteMeasure ν] {Φ : Mx D T.rank n → ℂ}
    (hΦ : Φ ∈ schwartzA θ T.rank n) :
    (∀ x : Mx D T.rank n, Integrable (fun k : K => Φ (Formalism.L2.Theta.mt T (k : GA D T)⁻¹ ⬝ x)) ν) ∧
      projS ν Φ ∈ schwartzA θ T.rank n := by
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨fun x => integrable_zero _ _ _, ?_⟩
    have e : projS ν (0 : Mx D T.rank n → ℂ) = 0 := funext fun x => integral_zero _ _
    rw [e]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun x => (h1.1 x).add (h2.1 x), ?_⟩
    have e : projS ν (Φ + Ψ) = projS ν Φ + projS ν Ψ := funext fun x => integral_add (h1.1 x) (h2.1 x)
    rw [e]
    exact Submodule.add_mem _ h1.2 h2.2
  | smul c Φ _ h1 =>
    refine ⟨fun x => (h1.1 x).smul c, ?_⟩
    have e : projS ν (c • Φ) = c • projS ν Φ := funext fun x => integral_smul c _
    rw [e]
    exact Submodule.smul_mem _ c h1.2
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    haveI : OpensMeasurableSpace K := inferInstance
    have c1 : Continuous fun k : K => Formalism.L2.Theta.mt T (k : GA D T) :=
      (GlobalTheory.RealWeil.continuous_mt T).1.comp continuous_subtype_val
    have c2 : Continuous fun k : K => Formalism.L2.Theta.mt T (k : GA D T)⁻¹ :=
      (GlobalTheory.RealWeil.continuous_mt T).2.comp continuous_subtype_val
    obtain ⟨hint, t, F, ht, hF⟩ := integral_tensor_matrix (n := n) ν
      (fun (k : K) τ => compAt θ τ (Formalism.L2.Theta.mt T (k : GA D T)⁻¹))
      (fun (k : K) τ => compAt θ τ (Formalism.L2.Theta.mt T (k : GA D T)))
      (fun τ => (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp c2)
      (fun τ => (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp c1)
      (fun k τ => map_cancel ((θ τ).comp (infPart D)) T k)
      (fun k : K => (Formalism.L2.Theta.mt T (k : GA D T)⁻¹).map (finPart D))
      (fun k : K => (Formalism.L2.Theta.mt T (k : GA D T)).map (finPart D))
      (c2.matrix_map (GlobalTheory.Member.continuous_finPart D)) (c1.matrix_map (GlobalTheory.Member.continuous_finPart D))
      (fun k => map_cancel (finPart D) T k) f hg
    have e : ∀ (M : Mx D T.rank T.rank) (x : Mx D T.rank n),
        f (fun τ i j => compAt θ τ (M ⬝ x) i j) * g (fun i j => finPart D ((M ⬝ x) i j)) =
        f (fun τ i j => ∑ c, compAt θ τ M i c * compAt θ τ x c j) *
          g (fun i j => ∑ c, M.map (finPart D) i c * finPart D (x c j)) := fun M x => by
      have e1 := fun τ => map_mul_entry ((θ τ).comp (infPart D)) M x
      have e2 := map_mul_entry (finPart D) M x
      exact congrArg₂ (· * ·) (congrArg f (funext e1)) (congrArg g e2)
    refine ⟨fun x => ?_, ?_⟩
    · simp only [e]
      exact hint (fun τ i j => compAt θ τ x i j) (fun i j => finPart D (x i j))
    · have e2 : projS ν (fun x : Mx D T.rank n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) =
          ∑ g' ∈ t, fun x : Mx D T.rank n => F g' (fun τ i j => compAt θ τ x i j) * g' (fun i j => finPart D (x i j)) := by
        funext x
        rw [Finset.sum_apply]
        simp only [projS, e]
        exact hF (fun τ i j => compAt θ τ x i j) (fun i j => finPart D (x i j))
      rw [e2]
      exact Submodule.sum_mem _ fun g' hg' => Submodule.subset_span ⟨F g', g', ht g' hg', rfl⟩

theorem projS_mem : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T : HSp D) (n : ℕ) (K : Subgroup (GA D T)),
    IsCompact (K : Set (GA D T)) → ∀ ν : Measure K, IsProbabilityMeasure ν → ∀ Φ ∈ schwartzA θ T.rank n,
      projS ν Φ ∈ schwartzA θ T.rank n :=
  fun _ _ hθ _ _ _ hK ν _ _ hΦ => (integrable_and_projS_mem hθ hK ν hΦ).2

end GlobalTheory.CompactAvgSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageThetaFamilySmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaAvgSmooth

open GlobalTheory.WeilVacMove

theorem key {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {n : ℕ} (L : (Fin n → ℝ) →+ WO S T)
    (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) (w : WO S T) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (t : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun t => f (w + L t)) t (Pi.single i 1) =
      dLine ψ S T (L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i)) f (w + L t) +
        -phase lam S T (L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i) 1) (w + L t) * f (w + L t) := by
  set M := L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i) with hMdef
  have hs : Continuous (AddMonoidHom.single (fun _ : Fin n => ℝ) i) := by
    refine continuous_pi fun j => ?_
    by_cases h : j = i
    · subst h; simp; exact continuous_id'
    · simpa [h] using continuous_const
  have hM : Continuous M := hL.comp hs
  have hM0 : ∀ s, (M s).map (finPart D) = 0 := fun s => hL0 _
  set x := w + L t with hx
  set c := phase lam S T (M 1) x with hc
  obtain ⟨hd, -⟩ := hasDerivAt_zero_and_isTheta hψ hM hM0 hf
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * c))) (-c) 0 := by
    have := ((HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const c).neg.cexp
    simpa using this
  have h1 := hexp.mul (hd x)
  have hsm : ∀ s : ℝ, s • (Pi.single i (1 : ℝ) : Fin n → ℝ) = Pi.single i s := by
    intro s
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have e1 : ∀ s : ℝ, Complex.exp (-((s : ℂ) * c)) * heisO ψ S T (M s) f x =
      f (w + L (t + s • Pi.single i 1)) := by
    intro s
    rw [heisO, psi_sympl_line hl hlam hM hM0, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
      one_mul, hsm, map_add, hx, add_assoc]
    rfl
  have hg : DifferentiableAt ℝ (fun t => f (w + L t)) (t + (0 : ℝ) • Pi.single i 1) :=
    ((hf.smooth n L hL hL0 w).differentiable (by simp)).differentiableAt
  have hl' : HasDerivAt (fun s : ℝ => t + s • (Pi.single i (1 : ℝ) : Fin n → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin n → ℝ)).const_add t
  have h2 := hg.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl'
  rw [zero_smul, add_zero] at h2
  have h3 : HasDerivAt (fun s : ℝ => f (w + L (t + s • Pi.single i 1)))
      (-c * heisO ψ S T (M 0) f x + Complex.exp (-(((0 : ℝ) : ℂ) * c)) * dLine ψ S T M f x) 0 := by
    have e : (fun s : ℝ => f (w + L (t + s • Pi.single i 1))) =
        fun s : ℝ => Complex.exp (-((s : ℂ) * c)) * heisO ψ S T (M s) f x := funext fun s => (e1 s).symm
    rw [e]
    exact h1
  have := h2.unique h3
  rw [this, map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
  ring

theorem avg_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Set (K → WO S T → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × WO S T => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, IsThetaFunO ψ S T (F k)) → (∀ F ∈ 𝒢, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => ∫ k, F k (w + L t) ∂μ := by
  intro D ψ hψ S T K _ _ _ _ μ _ 𝒢 hc hth hcl F hF n L hL hL0 w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hs : ∀ i, Continuous (AddMonoidHom.single (fun _ : Fin n => ℝ) i) := by
    intro i
    refine continuous_pi fun j => ?_
    by_cases h : j = i
    · subst h; simp; exact continuous_id'
    · simpa [h] using continuous_const
  let M : Fin n → ℝ →+ WO S T := fun i => L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i)
  have hM : ∀ i, Continuous (M i) := fun i => hL.comp (hs i)
  have hM0 : ∀ i s, (M i s).map (finPart D) = 0 := fun i s => hL0 _
  let φ : Fin n → (Fin n → ℝ) → ℂ := fun i t => -phase lam S T (M i 1) (w + L t)
  let 𝒢' : Set (K → (Fin n → ℝ) → ℂ) := {G | ∃ F ∈ 𝒢, G = fun k t => F k (w + L t)}
  have hφ : ∀ i, ContDiff ℝ ∞ (φ i) := by
    intro i
    have hc' : Continuous ((phase lam S T (M i 1)).comp L) :=
      hl.comp (continuous_symplOH S T hL continuous_const)
    have e : φ i = fun t => -(phase lam S T (M i 1) w + ((phase lam S T (M i 1)).comp L) t) := by
      funext t
      simp only [φ, map_add (f := _), AddMonoidHom.comp_apply]
    rw [e]
    exact (contDiff_const.add (contDiff_additive _ hc')).neg
  have hmem : (fun k t => F k (w + L t)) ∈ 𝒢' := ⟨F, hF, rfl⟩
  refine _root_.GlobalTheory.AvgSmooth.main K μ n φ hφ 𝒢' ?_ ?_ ?_ _ hmem
  · rintro G ⟨F, hF, rfl⟩
    exact (hc F hF).comp (continuous_fst.prodMk (continuous_const.add (hL.comp continuous_snd)))
  · rintro G ⟨F, hF, rfl⟩ k
    exact ((hth F hF k).smooth n L hL hL0 w).differentiable (by simp)
  · rintro G ⟨F, hF, rfl⟩ i
    refine ⟨fun k t => GlobalTheory.WeilVacMove.dLine ψ S T (M i) (F k) (w + L t), ⟨_, hcl F hF (M i) (hM i) (hM0 i), rfl⟩,
      fun k t => ?_⟩
    exact GlobalTheory.ThetaAvgSmooth.key hψ hl hlam L hL hL0 w (F k) (hth F hF k) t i

end GlobalTheory.ThetaAvgSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjRowEqTranslatedEvaluationCuspFormMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SeeOnto

theorem see_onto : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ φ : L2X X, star φ ∈ HHX X → ∃ T ∈ MultT θ M J χ, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
  intro hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hM hCV φ hφ
  obtain ⟨c, hc, hv₀⟩ := hCV
  have hL := (GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps D X hGap).2.2.2.2.2
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X hL (star φ) hφ
  have hrep := _root_.GlobalTheory.ConjRowRep.exists_contRep hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ
  have hmult : GlobalTheory.ConjRowMult.conjMap X M c Φ h t ∈ Mult θ M J χ :=
    Submodule.subset_span
      ⟨_root_.GlobalTheory.ConjRowAut.conjMap_isAutFunSm hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       _root_.GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       _root_.GlobalTheory.ConjRowMult.conjMap_lev hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       fun τ g hg v w hw => _root_.GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep τ g hg v w hw,
       fun τ v x => _root_.GlobalTheory.ConjRowCont.conjMap_cont hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep τ v x⟩
  refine ⟨PiTensorProduct.lift (GlobalTheory.ConjRowMult.conjMap X M c Φ h t), (mem_multT θ M J χ _).2 (by simpa using hmult), ?_⟩
  have hw : GlobalTheory.ConjRowMult.vecC X M c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X M c v₀ X.B.w hv₀
  obtain ⟨ψ, hψ⟩ := hrep v₀
  rw [hw, hΦw] at hψ
  have key : ∀ x, evS X h t (PiTensorProduct.lift (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) (PiTensorProduct.tprod ℂ v₀)) x = star (ψ x) := by
    intro x
    rw [evS, PiTensorProduct.lift.tprod]
    refine (GlobalTheory.ConjRowMult.conjMap_apply X M c Φ h t v₀ _).trans ?_
    rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    have e : ∀ a b : GA D (D.sp.Y 0), a * b * b⁻¹ = a := fun a b => mul_inv_cancel_right a b
    erw [e, ContinuousMulEquiv.apply_symm_apply]
  filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
  rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.Core.SeeOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfPointNegMultipliesByCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct.ConjModul

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_sec (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem pr_trace (p : SplitPt D k) {m : ℕ} (M : Mx D m m) : p.pr M.trace = (M.map p.pr).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

theorem map_rat (p : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat M).map p.pr = M.map (iota p) := by
  ext i j; rfl


open GlobalTheory.FinPl.LineAct in
set_option maxHeartbeats 1600000 in
theorem conj_half_modul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf (cA D p.e) ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t)) ∧ ∀ x : WO W₀ S₀, IsHalf p.e x → ψ (symplO W₀ S₀ x ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t))) = (χ (-((fun j => rd β γ₀ x (Sum.inr 0) j) ⬝ᵥ t)) : ℂ) := by
  intro D k _ _ _ _ p ψ χ hχ n n'' _ _ _ _ S₀ A L W₀ o ζ hζ β γ γ₀ hγ t
  refine ⟨fun i j => ?_, fun x _ => ?_⟩
  · rw [OrthDec.resT_symm_apply]
    simp only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.neg_apply, mul_neg, Matrix.mul_apply, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [wCol, Matrix.of_apply]
    rw [mul_left_comm, ← map_mul, e_mul_sec]
  · have hy : (o.resT W₀) ((o.resT W₀).symm (0, -wCol p ζ β t)) = (0, -wCol p ζ β t) := AddEquiv.apply_symm_apply _ _
    rw [OrthDec.symplO_resT, hy]
    have h0 : symplO W₀ A ((o.resT W₀) x).1 0 = 0 := by
      rw [symplO_eq, hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]
    rw [h0, zero_add, symplO_eq, OrthDec.resT_apply, hO_eq_trace]
    set T := (giA W₀ ⬝ (adj (-wCol p ζ β t) ⬝ (gA L ⬝ (o.pB ⬝ x)))).trace with hT
    set u' : Fin L.rank → k := dualPick ((L.gram.map (iota p)) *ᵥ fun i => iota p (ζ i)) with hu'
    set v : Fin W₀.rank → k := fun j => (iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) j with hv
    have hadj : adj (-wCol p ζ β t) = Matrix.of fun i j => -p.sec (u' j * v i) := by
      ext i j
      simp only [adj, wCol, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.of_apply, map_neg,
        Formalism.L2.Theta.cA_cA, hu', hv]
    have hZ : p.e • adj (-wCol p ζ β t) = adj (-wCol p ζ β t) := by
      rw [hadj]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_neg, e_mul_sec]
    have heT : p.e * T = T := by
      conv_rhs => rw [hT, ← hZ]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hc : p.e * (incA D D.host.xi0 * T) = incA D D.host.xi0 * T := by rw [mul_left_comm, heT]
    have key : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * T)) =
        (χ (p.pr (incA D D.host.xi0 * T)) : ℂ) := by
      rw [hχ, p.sec_pr, hc]; rfl
    rw [key]
    have hxi : iota p D.host.xi0 ≠ 0 := (map_ne_zero (iota p)).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    set ζb : Fin L.rank → k := fun i => iota p (ζ i) with hζb
    set R := rd β γ₀ x with hR
    set η : n → k := fun j => R (Sum.inr 0) j with hη
    have hx : x.map p.pr = γ₀.b * R * β.b' := by
      rw [hR, rd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, γ₀.bb', Matrix.one_mul, Matrix.mul_assoc, β.bb',
        Matrix.mul_one]
    have hvec : (fun m => p.pr (ratV (vecB o ζ) m)) = (o.iB.map (iota p)) *ᵥ ζb := by
      funext m
      exact RingHom.map_mulVec (iota p) o.iB ζ m
    have hQ : o.qB.map (iota p) * γ₀.b = fromCols 0 (replicateCol (Fin 1) ζb) := by
      rw [hγ, Matrix.mul_fromCols, OrthDec.jA, map_rat, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qB_iA,
        Matrix.map_zero _ (map_zero _), Matrix.zero_mul]
      congr 1
      ext i j
      simp only [Matrix.mul_apply, Matrix.replicateCol_apply]
      change (o.qB.map (iota p) *ᵥ fun m => p.pr (ratV (vecB o ζ) m)) i = ζb i
      rw [hvec, Matrix.mulVec_mulVec, ← Matrix.map_mul, o.qB_iB, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    have hQR : fromCols (0 : Matrix (Fin L.rank) n'' k) (replicateCol (Fin 1) ζb) * R = vecMulVec ζb η := by
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_sum_type, vecMulVec_apply, hη]
    have hqx : o.qB.map (iota p) * x.map p.pr = vecMulVec ζb (η ᵥ* β.b') := by
      rw [hx, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, hQR, vecMulVec_mul]
    have hg : L.gram.map (iota p) *ᵥ ζb ≠ 0 := by
      intro h0
      apply hζ.2
      have h1 : L.gram *ᵥ ζ = 0 := by
        funext i
        apply (iota p).injective
        rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
        exact congrFun h0 i
      rw [h1, dotProduct_zero]
    have hu1 : u' ⬝ᵥ (L.gram.map (iota p) *ᵥ ζb) = 1 := dualPick_dot _ hg
    have hZb : (Matrix.of fun i j => -p.sec (u' j * v i)).map p.pr = -vecMulVec v u' := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_neg, p.pr_sec, Matrix.neg_apply, vecMulVec_apply, mul_comm]
    have hv' : v = (iota p D.host.xi0)⁻¹ • ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) := rfl
    have hGi : (W₀.gram⁻¹).map (iota p) * W₀.gram.map (iota p) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (gram_isUnit_det W₀), Matrix.map_one _ (map_zero _) (map_one _)]
    have hval : p.pr (incA D D.host.xi0 * T) = -(η ⬝ᵥ t) := by
      rw [map_mul, hT, pr_trace, hadj]
      simp only [Matrix.map_mul, giA, gA, OrthDec.pB, map_rat, hZb]
      rw [hqx, Matrix.mul_vecMulVec, Matrix.neg_mul, Matrix.vecMulVec_mul_vecMulVec, hu1, one_smul, Matrix.mul_neg,
        Matrix.mul_vecMulVec, Matrix.trace_neg, Matrix.trace_vecMulVec, hv', Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        hGi, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul, dotProduct_comm, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul, β.b'b, Matrix.vecMul_one]
      change iota p D.host.xi0 * -((iota p D.host.xi0)⁻¹ * (η ⬝ᵥ t)) = -(η ⬝ᵥ t)
      field_simp
    rw [hval]

end GlobalTheory.FinPl.LineAct.ConjModul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
section
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem continuous_mat_pt (D : D7) (n : ℕ) : Continuous (mat : G D n → _) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_of_mat_pt {D : D7} {n : ℕ} {X : Type} [TopologicalSpace X] {φ : X → G D n}
    (h : Continuous fun x => mat (φ x)) (h' : Continuous fun x => mat (φ x)⁻¹) : Continuous φ :=
  Continuous.subtype_mk (f := fun x => AdelicU.matHom _ D.sp.cm.sig (Jst D n) (φ x))
    (Units.continuous_iff.2 ⟨h, h'⟩) _

theorem chart_continuous : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → Continuous κ ∧ Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hT := (Tm_gram_inv D A μ hμ).2.1
  have h₁ : (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hT, rat_one]
  have h₂ : (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hT, rat_one]
  have e₁ : ∀ g, mat (κ g) = (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) *
      (Formalism.L2.Theta.mt (dblSp A) g * rat (Tm A μ)) := fun g => by
    rw [← hκ g, ← Matrix.mul_assoc, h₁, Matrix.one_mul]
  have e₂ : ∀ x, Formalism.L2.Theta.mt (dblSp A) (κ.symm x) =
      (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * mat x * rat (Tm A μ)⁻¹ := fun x => by
    have := hκ (κ.symm x)
    rw [κ.apply_symm_apply] at this
    rw [this]
    exact ((Matrix.mul_assoc _ _ _).trans ((congrArg _ h₂).trans (Matrix.mul_one _))).symm
  have c₁ : Continuous fun g => mat (κ g) := by
    simp only [e₁]
    exact continuous_const.matrix_mul ((continuous_mt (dblSp A)).matrix_mul continuous_const)
  refine ⟨continuous_of_mat_pt c₁ ?_, continuous_of_mt (dblSp A) ?_⟩
  · simp only [← map_inv]
    exact c₁.comp continuous_inv
  · simp only [e₂]
    exact (continuous_const.matrix_mul (continuous_mat_pt D A.rank)).matrix_mul continuous_const

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLeviPreimageOfFixIsotropicFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levi_preimage_of_fix_isotropic_frames : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S), mt S g ⬝ d.jX = d.jX → mt S g ⬝ d.jY = d.jY → ∃ b : GA D S₀, d.emb0 b = g := by
  first | exact @GlobalTheory.MixModel.HypDec.exists_emb0_eq_of_fix_jX_jY | exact GlobalTheory.MixModel.HypDec.exists_emb0_eq_of_fix_jX_jY | (intros; apply GlobalTheory.MixModel.HypDec.exists_emb0_eq_of_fix_jX_jY <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthRealHeisenbergTranslatesVacuumOfOrthFockStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orth_realHeisenbergTranslates_vacuum_of_orth_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → ∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  first | exact @GlobalTheory.FockRealOrth.orth_real_translate | exact GlobalTheory.FockRealOrth.orth_real_translate | (intros; apply GlobalTheory.FockRealOrth.orth_real_translate <;> assumption)
end

