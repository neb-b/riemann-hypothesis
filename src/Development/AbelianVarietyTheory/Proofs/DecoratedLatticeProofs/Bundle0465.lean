module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FlatVacuum

variable {D : D7}

theorem mulVec_mem_ideal {m n : ℕ} (I : Ideal (AE D)) (M : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (i : Fin m) : (M *ᵥ y) i ∈ I := by
  show ∑ j, M i j * y j ∈ I
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

theorem mulVec_latV_of_local {S S' : HSp D} {L : Lat S} {L' : Lat S'} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {P : Pl D → Prop} (M : Matrix (Fin S'.rank) (Fin S.rank) (AE D))
    (h : ∀ v, P v → ∀ y ∈ latV S L (· = v), M *ᵥ y ∈ latV S' L' (· = v)) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : M *ᵥ y ∈ latV S' L' P := by
  obtain ⟨h1, h2⟩ := (((_root_.GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 L y hL).1 hy
  refine (((_root_.GlobalTheory.FinPl.localComponents D P).2 S').2.2.2 L' _ hL').2 ⟨mulVec_mem_ideal _ M h1, fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact h v hv _ (h2 v hv e he)

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mulVec_latA {S S' : HSp D} {L : Lat S} {L' : Lat S'} {P : Pl D → Prop}
    (M : Matrix (Fin S'.rank) (Fin S.rank) (AE D)) (h : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV S' L' P)
    {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : M *ᵥ y ∈ latA S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    have e : (fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) : AE D)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • fun i => (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) : AE D) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e, Matrix.mulVec_smul]
    exact smul_mem_latA ha (h _ (AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

section Mono

variable {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L : Lat S} {L₀ : Lat S₀}

theorem p0_mem {v : Pl D} (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    d.p0 *ᵥ y ∈ latV S₀ L₀ (· = v) := ((h y).1 hy).2.2

theorem wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace {v : Pl D} (h : MonoAt d L L₀ v) {y : Fin S₀.rank → AE D} (hy : y ∈ latV S₀ L₀ (· = v)) :
    d.j0 *ᵥ y ∈ latV S L (· = v) := by
  have hX : d.pX *ᵥ (d.j0 *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.pX_j0).trans (Matrix.zero_mulVec _)
  have hY : d.pY *ᵥ (d.j0 *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.pY_j0).trans (Matrix.zero_mulVec _)
  have h0 : d.p0 *ᵥ (d.j0 *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec]; exact (congrArg (· *ᵥ y) d.p0_j0).trans (Matrix.one_mulVec _)
  have hc : ∀ (x : Mx D S.rank ρ) i, colMul x i 0 = 0 := fun x i => funext fun k => zero_mul _
  refine (h _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [hX, Pi.zero_apply, hc]; exact zero_mem _
  · rw [hY, Pi.zero_apply, hc]; exact zero_mem _
  · rw [h0]; exact hy

theorem wittExtendByZero_mem_completedHomLattice {T : HSp D} {LT : Lat T} {P : Pl D → Prop} (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hT : IsSelfDualC T LT) (h : ∀ v, P v → MonoAt d L L₀ v) {w : WO S₀ T}
    (hw : w ∈ latO S₀ T (L₀ : Set _) (LT : Set _) P) : d.ext0 T w ∈ latO S T (L : Set _) (LT : Set _) P := by
  obtain ⟨h1, h2⟩ := (LatMem.mem_latO_iff D S₀ T L₀ LT hL₀ hT P w).1 hw
  refine (LatMem.mem_latO_iff D S T L LT hL hT P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · show ∑ k, w i k * d.p0 k j ∈ idAt D P
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h1 i k)
  · have := h2 _ (mulVec_latV_of_local hL.1 hL₀.1 d.p0 (fun v hv z hz => p0_mem (h v hv) hz) hy)
    rw [Matrix.mulVec_mulVec] at this
    exact this

theorem wittCoreInclusion_mem_completedHomLattice {T : HSp D} {LT : Lat T} {P : Pl D → Prop} (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hT : IsSelfDualC T LT) (h : ∀ v, P v → MonoAt d L L₀ v) {w : WO T S₀}
    (hw : w ∈ latO T S₀ (LT : Set _) (L₀ : Set _) P) : d.inc0 T w ∈ latO T S (LT : Set _) (L : Set _) P := by
  obtain ⟨h1, h2⟩ := (LatMem.mem_latO_iff D T S₀ LT L₀ hT hL₀ P w).1 hw
  refine (LatMem.mem_latO_iff D T S LT L hT hL P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · show ∑ k, d.j0 i k * w k j ∈ idAt D P
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h1 k j)
  · have := mulVec_latA d.j0
      (fun z hz => mulVec_latV_of_local hL₀.1 hL.1 d.j0 (fun v hv z hz => wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace (h v hv) hz) hz) (h2 y hy)
    rw [Matrix.mulVec_mulVec] at this
    exact this

theorem isHalf_wittExtendByZero {T : HSp D} {e : AE D} {w : WO S₀ T} (hw : IsHalf e w) : IsHalf e (d.ext0 T w) :=
  fun i j => GlobalTheory.WeilSrc.entries_fix_right e hw d.p0 i j

theorem isHalf_wittCoreInclusion {T : HSp D} {e : AE D} {w : WO T S₀} (hw : IsHalf e w) : IsHalf e (d.inc0 T w) := by
  intro i j
  show e * (∑ k, d.j0 i k * w k j) = ∑ k, d.j0 i k * w k j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hw k j]

end Mono

theorem isLatVac_of_intertwine {m n m' n' : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)}
    {hs' : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)} {Λ : AddSubgroup (Mx D m n)} {Λ' : AddSubgroup (Mx D m' n')}
    (ι : Mx D m' n' →+ Mx D m n) (hΛ : ∀ u ∈ Λ', ι u ∈ Λ) (hh : ∀ e u, IsHalf e u → IsHalf e (ι u))
    (𝔉 : (Mx D m n → ℂ) → (Mx D m' n' → ℂ)) {f : Mx D m n → ℂ} (hF : ∀ u ∈ Λ', 𝔉 (hs (ι u) f) = hs' u (𝔉 f))
    (hf : IsLatVac hs Λ f) : IsLatVac hs' Λ' (𝔉 f) := by
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · rw [← hF _ (Λ'.nsmul_mem hu 2), map_nsmul, hf.1 _ (hΛ u hu)]
  · rw [← hF _ hu, hf.2 e he _ (hΛ u hu) (hh e u hue)]

theorem latO_empty {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {u : WO S T} (hu : u ∈ latO S T LS LT P) : u = 0 := by
  ext i j
  have h1 := LatMem.mul_indP (LatMem.latO_mxAt hu i j)
  have h2 : LatMem.indP D.host.F P = 0 := by
    classical
    refine Subtype.ext (funext fun v => ?_)
    exact if_neg (hP v)
  have h3 : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
  rw [h2, h3, TensorProduct.zero_tmul, mul_zero] at h1
  exact h1.symm

theorem vac_of_heisLaws {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ}
    {dW : HypDec W W₀ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ} {P : Pl D → Prop}
    {𝔉 : (WO V W → ℂ) → (WO V₀ W₀ → ℂ)} (H : HeisLaws ψ dV dW x y P 𝔉) {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W}
    {LW₀ : Lat W₀}
    (h : ∀ v, P v → IsSelfDualC V LV ∧ IsSelfDualC V₀ LV₀ ∧ IsSelfDualC W LW ∧ IsSelfDualC W₀ LW₀ ∧
      MonoAt dV LV LV₀ v ∧ MonoAt dW LW LW₀ v) {Φ : WO V W → ℂ} (hΦ : Vac ψ V W LV LW P Φ) :
    Vac ψ V₀ W₀ LV₀ LW₀ P (𝔉 Φ) := by
  refine ⟨H.theta Φ hΦ.1, isLatVac_of_intertwine ((dV.ext0 W).comp (dW.inc0 V₀)) (fun u hu => ?_)
    (fun e u hu => isHalf_wittExtendByZero (isHalf_wittCoreInclusion hu)) 𝔉 (fun u hu => H.core Φ hΦ.1 u (LatMem.latO_mxAt hu)) hΦ.2⟩
  by_cases hP : ∃ v, P v
  · obtain ⟨v, hv⟩ := hP
    obtain ⟨a, b, c, e, -⟩ := h v hv
    exact wittExtendByZero_mem_completedHomLattice a b c (fun v hv => (h v hv).2.2.2.2.1) (wittCoreInclusion_mem_completedHomLattice c e b (fun v hv => (h v hv).2.2.2.2.2) hu)
  · rw [latO_empty (not_exists.1 hP) hu, map_zero]
    exact zero_mem _

theorem flatVac : ∀ D : D7, GlobalTheory.FinPl.FlatVac D := by
  intro D ψ P
  refine ⟨fun ρ B J s LV LV₀ LW LW₀ h Φ hΦ => ?_, fun σ J B s LV LV₀ LW LW₀ h Φ hΦ => ?_,
    fun V V₀ T d L L₀ LT hL hL₀ hT h Φ hΦ => ?_⟩
  · exact vac_of_heisLaws ((_root_.GlobalTheory.FinPl.flatLaws_all D ψ P).1 ρ B J s).Heisenberg₂
      (fun v hv => ⟨(h v hv).sdV, (h v hv).sdV₀, (h v hv).sdW, (h v hv).sdW₀, (h v hv).monoV, (h v hv).monoW⟩) hΦ
  · exact vac_of_heisLaws ((_root_.GlobalTheory.FinPl.flatLaws_all D ψ P).2 σ J B s).Heisenberg₂
      (fun v hv => ⟨(h v hv).sdV, (h v hv).sdV₀, (h v hv).sdW, (h v hv).sdW₀, (h v hv).monoV, (h v hv).monoW⟩) hΦ
  · exact ⟨(GlobalTheory.WeilSrc.Zero.theta_iff d Φ).2 hΦ.1, isLatVac_of_intertwine (d.ext0 T)
      (fun u hu => wittExtendByZero_mem_completedHomLattice hL hL₀ hT h hu) (fun e u hu => isHalf_wittExtendByZero hu) (fun f w => f (d.ext0 T w))
      (fun u _ => GlobalTheory.WeilSrc.Zero.heisO_eqv d u Φ) hΦ.2⟩

end GlobalTheory.FinPl.FlatVacuum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodLiftEqIntegralUnfolded
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem per_lift_eq_integral_unfF : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → IntegrableOn (unfF s vL Y G Φ) 𝓑 s.vW.μ ∧ J.per ψ B.ζ Y (s.lift G Φ) = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have := s.vW.haar
  have := J.v0.haar
  have hI := _root_.GlobalTheory.Unf.FB.unfolded_integrable D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have hin := _root_.GlobalTheory.Unf.FB.fjN_unfold D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have hc := (_root_.GlobalTheory.Unf.FB.TFlatFam.main D hD ψ σ J B s vL Y Φ hY hΦ).2.2
  have hU : ∀ h, unfF s vL Y G Φ h = ∫ h₀ in J.v0.𝓕, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
    intro h
    rw [unfF, hc h, integral_const_mul]
  constructor
  · have := hI.integral_prod_right
    refine this.congr ?_
    exact Filter.Eventually.of_forall fun h => (hU h).symm
  · calc J.per ψ B.ζ Y (s.lift G Φ)
        = ∫ h₀ in J.v0.𝓕, ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ ∂J.v0.μ := by
          unfold JacLev.per fjSrcKer
          congr 1
          funext h₀
          exact hin h₀
      _ = ∫ h in 𝓑, ∫ h₀ in J.v0.𝓕, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ ∂s.vW.μ :=
          integral_integral_swap hI
      _ = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
          congr 1
          funext h
          exact (hU h).symm

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameColumnsUnitScaling
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimSplitLine

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cA_sec_mul' (p : SplitPt D k) (a : AE D) (t : k) :
    cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, cA_cA]

theorem colMul_split (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) {a : AE D}
    (ha : a ∈ idAt D (· = q.v)) :
    colMul d.jX i a = (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * q.pr (cA D (incA D (d.e r i)))))) := by
  funext r
  change a * incA D (d.e r i) = _
  conv_lhs => rw [GlobalTheory.SplitIntComp.eq_sec_add_csec q ha]
  rw [add_mul, sec_mul_right, cA_sec_mul' q, Pi.add_apply]

theorem mul_unit_mem_iff {b u : k} (hu : valuation k u = 1) : b * u ∈ 𝒪[k] ↔ b ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_mul, hu, mul_one]

theorem colMul_mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (i : Fin ρ) (y₁ y₂ : Y) (u₁ u₂ : k), IsSelfDualC S L → IntIn q S F L → valuation k u₁ = 1 → valuation k u₂ = 1 → (∀ r, F.β r y₁ = u₁ * q.pr (incA D (d.e r i))) → (∀ l, ∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (d.e t i))) = if l = y₂ then u₂ else 0) → ∀ a : AE D, (GlobalTheory.FinPl.colMul d.jX i a ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v)) := by
  intro D k _ _ _ _ q S S₀ ρ d L Y _ _ F i y₁ y₂ u₁ u₂ hL hF hu₁ hu₂ hcol₁ hcol₂ a
  have hu₁0 : u₁ ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at hu₁
    exact zero_ne_one hu₁
  have hu₂i : u₂ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hu₂.le
  have key : ∀ a ∈ idAt D (· = q.v), (colMul d.jX i a ∈ latV S L (· = q.v) ↔
      q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
    intro a ha
    rw [colMul_split q d i ha, decomp hL]
    refine and_congr ?_ ?_
    · have h1 : (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) =
          fun r => q.sec ((F.β *ᵥ Pi.single y₁ (q.pr a * u₁⁻¹)) r) := by
        funext r
        congr 1
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcol₁]
        field_simp
      rw [h1, ← hF]
      constructor
      · intro h
        have := h y₁
        rw [Pi.single_eq_same] at this
        rwa [mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])] at this
      · intro h j
        by_cases hj : j = y₁
        · subst hj
          rw [Pi.single_eq_same, mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])]
          exact h
        · rw [Pi.single_eq_of_ne hj]
          exact zero_mem _
    · rw [csec_mem_iff hL]
      set b := q.pr (cA D a) with hb
      have hsum : ∀ y : Y → k, ∑ r, ∑ t, (F.β *ᵥ y) r * q.pr (cA D (incA D (HSpace.gram S r t))) *
          (b * q.pr (cA D (incA D (d.e t i)))) = b * u₂ * y y₂ := by
        intro y
        have hr : b * u₂ * y y₂ = ∑ l, y l * b * (∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) *
            q.pr (cA D (incA D (d.e t i)))) := by
          simp only [hcol₂, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        rw [hr]
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
        symm
        refine Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm.trans
          (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun l _ => ?_))
        ring
      constructor
      · intro h
        have h2 := h (F.β *ᵥ Pi.single y₂ 1) ((hF _).1 fun j => by
          by_cases hj : j = y₂
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _)
        rw [hsum, Pi.single_eq_same, mul_one, mul_unit_mem_iff hu₂] at h2
        exact h2
      · intro hb' x hx
        have hx' : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
        rw [hx'] at hx ⊢
        rw [hsum]
        exact mul_mem (mul_mem hb' hu₂i) ((hF _).2 hx y₂)
  constructor
  · intro h
    have ha := GlobalTheory.FinPl.SuppShift.idAt_of_colMul d h
    exact (GlobalTheory.SplitIntComp.mem_intAt_iff q ha).2 ((key a ha).1 h)
  · intro h
    exact (key a h.1).2 ((GlobalTheory.SplitIntComp.mem_intAt_iff q h.1).1 h)

end GlobalTheory.PrimSplitLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomotheticOfMonomialPrimitiveSelfDualCores
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem homothetic_of_monomial_primitive_selfDual_cores : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S L → IsSelfDualC S L' → IsSelfDualC S₀ M → z ≠ 0 → MonoAt d L M v → MonoAt d L' M' v → PrimAt ψ d L v → PrimAt ψ d L' v → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → SMoves S c (d.emb0 γ) L L' v := by
  intro D ψ S S₀ ρ d z L L' M M' v c γ hL hL' hM hz hmL hmL' hpL hpL' hlL hlL' hc hγ hmv
  have hX : ∀ i : Fin ρ, ∀ a ∈ idAt D (· = v),
      (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
    suffices h : ∀ k : ℕ, ∀ i : Fin ρ, i.1 + k + 1 = ρ → ∀ a ∈ idAt D (· = v),
        (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) by
      intro i
      exact h (ρ - 1 - i.1) i (by omega)
    intro k
    induction k with
    | zero =>
      intro i hi
      exact _root_.GlobalTheory.Core.Mi.LastLine.lastLine_match D ψ S S₀ ρ d z L L' M M' v c γ hM hz hlL hlL' hc hγ hmv i (by omega)
    | succ k ih =>
      intro i hi
      exact _root_.GlobalTheory.Core.Mi.LatMatch.match_down_flag D ψ S S₀ ρ d L L' v c hL hpL hpL' hc i ⟨i.1 + 1, by omega⟩ rfl
        (ih ⟨i.1 + 1, by omega⟩ (by simp only; omega))
  have hY := _root_.GlobalTheory.Core.Mi.LatMatch.dualLine_match D S S₀ ρ d L L' M M' v c hL hL' hmL hmL' hc hX
  intro y hy
  have hpX : d.pX *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) = c • (d.pX *ᵥ y) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
  have hpY : d.pY *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) = c • (d.pY *ᵥ y) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
  have hp0 : d.p0 *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) =
      c • (Formalism.L2.Theta.mt S₀ γ *ᵥ (d.p0 *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding, ← Matrix.mulVec_mulVec]
  rw [hmL y, hmL' _, hpX, hpY, hp0]
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) ?_)
  · rw [Pi.smul_apply, smul_eq_mul]
    exact hX i _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  · rw [Pi.smul_apply, smul_eq_mul]
    exact hY i _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  · exact hmv _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy)

end GlobalTheory.Core.Mi.LatMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.AdaptFBIdeals

variable {D : D7}

theorem supp_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (v : Pl D) (i : Fin ρ) (a : AE D)
    (h : colMul d.jX i a ∈ latV S L (· = v)) : a ∈ idAt D (· = v) := by
  have hp : d.pX * d.jX = 1 := by
    have h := congrArg rat d.e'e
    rw [rat_one] at h
    simpa only [HypDec.pX, HypDec.qX, HypDec.jX, rat, Matrix.map_mul] using h
  have h1 : (d.pX * d.jX) i i = 1 := by rw [hp]; exact Matrix.one_apply_eq i
  rw [Matrix.mul_apply] at h1
  have h2 : a = ∑ k, d.pX i k * colMul d.jX i a k := by
    calc a = a * ∑ k, d.pX i k * d.jX k i := by rw [h1, mul_one]
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; simp only [colMul]; ring
  rw [h2]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.latV_supp h k)

theorem idV_supp (𝔞 : FI D) (v : Pl D) {a : AE D} (h : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, x, -, rfl⟩ := hy
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

end GlobalTheory.SeeSaw.AdaptFBIdeals

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorBesselExistenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_vector_bessel_existence : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ a : XGeo D, IsLineVec a.Lz a.ζ₀ → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → ∃ (y : YRat a) (B : GlobalTheory.Core.Mi.SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) ∧ B.lev = (y.bes 0 D.R.rS h0).lev (a.x 0).vol ∧ B.Adapted (W.S.tr u).wt ∧ GlobalTheory.MiTop.Framed B ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(((D.mem u).A.T : ℕ) : D.host.E) ∧ ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) k)) := by
  first | exact @GlobalTheory.Fam.RatDec.exists_yRat | exact GlobalTheory.Fam.RatDec.exists_yRat | (intros; apply GlobalTheory.Fam.RatDec.exists_yRat <;> assumption)
end

