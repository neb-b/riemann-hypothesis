module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.FinPl.Rebase

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nsmul_half (p : SplitPt D k) {S T : HSp D} {LS MS : Lat S} {LT MT : Lat T} (hLS : IsSelfDualC S LS)
    (hLT : IsSelfDualC T LT) (hMS : IsSelfDualC S MS) (hMT : IsSelfDualC T MT) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v),
      IsHalf p.e u → N • u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) := by
  obtain ⟨ε, hε, heq⟩ := p.above
  have he := p.split.1
  have hec := p.split.2.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hLS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hLT
  obtain ⟨M, hM, hMm⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (ΛS' := LS) (ΛT' := LT)
    hMS.1.fg hMT.1.fg inferInstance inferInstance
  refine ⟨M, hM, fun u hu hh => ?_⟩
  have h1 := (GlobalTheory.PlaceModel.idem_smul_mem hε he heε (hMm u (GlobalTheory.PlaceModel.latO_le_top _ hu))).1
  have h2 : p.e • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh)
  rwa [smul_comm, h2] at h1

theorem isHalf_nsmul {S T : HSp D} {e : AE D} {u : WO S T} (hu : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem sbHalf_mono : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → ∀ Φ : WO S T → ℂ, IsSBHalf p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) Φ := by
  intro D k _ _ _ _ p S T LS MS LT MT hLS hLT hMS hMT Φ hΦ
  obtain ⟨N, hN, hNm⟩ := exists_nsmul_half p hMS hMT hLS hLT
  obtain ⟨M, hM, hMm⟩ := exists_nsmul_half p hLS hLT hMS hMT
  obtain ⟨h1, k', hk', h2, h3⟩ := hΦ
  refine ⟨h1, k' * N * M, Nat.mul_pos (Nat.mul_pos hk' hN) hM, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have hu' : M • u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) :=
      nsmul_mem hu M
    have e : (k' * N * M) • u = k' • (N • (M • u)) := by rw [smul_smul, smul_smul, mul_assoc]
    rw [e]
    exact h2 _ (hNm _ hu' (isHalf_nsmul hh M)) (isHalf_nsmul (isHalf_nsmul hh M) N) t
  · have ht' := h1 t ht
    have e : (k' * N * M) • t = M • (N • (k' • t)) := by
      rw [smul_smul, smul_smul, mul_comm M N, mul_comm (N * M) k', mul_assoc]
    rw [e]
    exact hMm _ (nsmul_mem (h3 t ht) N) (isHalf_nsmul (isHalf_nsmul ht' k') N)

theorem placeIdem_mul {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    algebraMap (AF D.host.F) (AE D) ε * a = a := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  obtain ⟨hi, hw⟩ := GlobalTheory.FinPl.LatMem.mem_idAt_iff.1 ha
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun w => ?_
  · rw [map_mul, GlobalTheory.FinPl.LatMem.compInf_eq_zero hi, mul_zero]
  · rw [map_mul]
    have he : GlobalTheory.AdelicU.compFin D.host.F D.host.E w (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) =
        evalV D.host.F w β ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    by_cases hv : w = v
    · subst hv
      rw [he, h1]
      exact one_mul _
    · rw [GlobalTheory.FinPl.LatMem.compFin_eq_compAt a w, hw w hv, mul_zero]

theorem eq_add_halves (p : SplitPt D k) {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {u : WO S T} (hu : u ∈ latO S T LS LT (· = p.v)) : p.e • u + cA D p.e • u = u := by
  obtain ⟨ε, hε, heq⟩ := p.above
  rw [← add_smul, heq]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact placeIdem_mul hε (GlobalTheory.FinPl.LatMem.latO_mxAt hu i j)

theorem smul_conj_zero (e e' : AE D) (h : e' * cA D e' = 0) {S T : HSp D} (u : WO S T) (hu : e' • u = u) :
    cA D e' • (e • u) = 0 := by
  rw [← hu, smul_smul, smul_smul]
  rw [mul_comm (cA D e') e]
  rw [mul_assoc]
  rw [mul_comm (cA D e') e']
  rw [h, mul_zero, zero_smul]

theorem isHalf_add {S T : HSp D} {e : AE D} {a b : WO S T} (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e (a + b) :=
  fun i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]

theorem latVac_image : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 f₀ Tm → IsLatVac (heisO ψ S T) (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) (Tm (halfInd p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)))) := by
  intro D k _ _ _ _ p ψ hψ S T LS MS LT MT hLS hLT hMS hMT f₀ Tm hTm
  obtain ⟨ε, hε, heq⟩ := p.above
  have he := p.split.1
  have hec := p.split.2.1
  have hce : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
    rw [← heq]; linear_combination hce + hec
  set Λ' := latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v) with hΛ'
  have hΦ₀ : IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
      (halfInd p.e Λ') :=
    sbHalf_mono D k p S T LS MS LT MT hLS hLT hMS hMT _ (GlobalTheory.isSBHalf_halfInd p.e Λ')
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T MS MT hψ hMS hMT).1
  have hLL' : ∀ x ∈ Λ', IsHalf p.e x → ∀ y ∈ Λ', ψ (symplO S T x y) = 1 := fun x hx hh y hy =>
    (hdual x (GlobalTheory.PlaceModel.infPart_half hε heε ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh))).1
      (GlobalTheory.PlaceModel.latO_le_top _ hx) y (GlobalTheory.PlaceModel.latO_le_top _ hy)
  have hX : ∀ x ∈ Λ', IsHalf p.e x → heisO ψ S T x (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro x hx hh
    rw [← hTm.trans _ hΦ₀ x hh]
    congr 1
    funext t
    have hc : (t + x ∈ Λ' ∧ IsHalf p.e (t + x)) ↔ (t ∈ Λ' ∧ IsHalf p.e t) := by
      rw [Λ'.add_mem_cancel_right hx]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
    show halfInd p.e Λ' (t + x) = halfInd p.e Λ' t
    unfold halfInd
    by_cases h : t ∈ Λ' ∧ IsHalf p.e t
    · rw [if_pos (hc.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]
  have hY : ∀ y ∈ Λ', IsHalf (cA D p.e) y → heisO ψ S T y (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro y hy hh
    rw [← hTm.modul _ hΦ₀ y hh]
    congr 1
    funext t
    by_cases h : t ∈ Λ' ∧ IsHalf p.e t
    · rw [hLL' t h.1 h.2 y hy, one_mul]
    · simp [halfInd, h]
  have key : ∀ x y : WO S T, x ∈ Λ' → IsHalf p.e x → y ∈ Λ' → IsHalf (cA D p.e) y →
      ψ (symplOH S T y x) = 1 → heisO ψ S T (x + y) (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro x y hx hxh hy hyh h1
    have h := GlobalTheory.PlaceModel.heisL_heisL S T ψ y x (Tm (halfInd p.e Λ'))
    change heisO ψ S T y (heisO ψ S T x (Tm (halfInd p.e Λ'))) =
      ψ (symplOH S T y x) • heisO ψ S T (y + x) (Tm (halfInd p.e Λ')) at h
    rw [hX x hx hxh, hY y hy hyh, h1, one_smul, add_comm] at h
    exact h.symm
  have hpart : ∀ u ∈ Λ', (p.e • u ∈ Λ' ∧ IsHalf p.e (p.e • u)) ∧
      (cA D p.e • u ∈ Λ' ∧ IsHalf (cA D p.e) (cA D p.e • u)) := by
    intro u hu
    have a1 := GlobalTheory.PlaceModel.idem_smul_mem hε he heε (GlobalTheory.PlaceModel.latO_le_top _ hu)
    have a2 := GlobalTheory.PlaceModel.idem_smul_mem hε hce heε' (GlobalTheory.PlaceModel.latO_le_top _ hu)
    exact ⟨⟨a1.1, (GlobalTheory.PlaceModel.isHalf_iff S T).2 a1.2⟩, ⟨a2.1, (GlobalTheory.PlaceModel.isHalf_iff S T).2 a2.2⟩⟩
  refine ⟨fun w hw => ?_, fun e' hse' u hu hh => ?_⟩
  · obtain ⟨⟨hx, hxh⟩, ⟨hy, hyh⟩⟩ := hpart w hw
    have e2 : 2 • w = (p.e • w + p.e • w) + (cA D p.e • w + cA D p.e • w) := by
      conv_lhs => rw [← eq_add_halves p hw]
      abel
    rw [e2]
    refine key _ _ (add_mem hx hx) (isHalf_add hxh hxh) (add_mem hy hy) (isHalf_add hyh hyh) ?_
    have hb : ψ (symplO S T (cA D p.e • w) (p.e • w)) = 1 := by
      rw [GlobalTheory.PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, hLL' _ hx hxh _ hy, inv_one]
    have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
      norm_num
    have h3 : symplOH S T (cA D p.e • w + cA D p.e • w) (p.e • w + p.e • w) =
        symplO S T (cA D p.e • w) (p.e • w) + symplO S T (cA D p.e • w) (p.e • w) := by
      unfold symplOH
      simp only [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right]
      linear_combination (2 * symplO S T (cA D p.e • w) (p.e • w)) * h2
    rw [h3, AddChar.map_add_eq_mul, hb, one_mul]
  · obtain ⟨⟨hx, hxh⟩, ⟨hy, hyh⟩⟩ := hpart u hu
    rw [← eq_add_halves p hu]
    refine key _ _ hx hxh hy hyh ?_
    obtain ⟨-, hse2, -⟩ := hse'
    have hu' : e' • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh)
    have h0 : symplO S T (cA D p.e • u) (p.e • u) = 0 := by
      have e1 : cA D p.e • u = e' • (cA D p.e • u) := by rw [smul_comm, hu']
      have e2 : cA D e' • (p.e • u) = 0 := smul_conj_zero p.e e' hse2 u hu'
      rw [e1, GlobalTheory.PlaceModel.symplO_smul, e2, GlobalTheory.PlaceModel.symplO_zero_right]
    unfold symplOH
    rw [h0, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.FinPl.Rebase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmoothKFiniteUnitHighestWeightVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealZetaSmoothHi

theorem exists_smooth_highestUnit : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ w : M.H τ, w ∈ M.sm τ ∧ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ ∧ IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) w := by
  intro h D V S M τ
  obtain ⟨hC, hN, hU, hI, -, ⟨K, hK⟩, -⟩ := M.ds τ
  haveI := hC
  obtain ⟨v, hv, hv0, hw⟩ := hK.2.2.2.1
  have hwS : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ K := K.smul_mem _ hv
  have hKf : IsKFin (M.ε τ) (M.σ τ) (((‖v‖⁻¹ : ℝ) : ℂ) • v) := ⟨K, hK.1, hwS, hK.2.1⟩
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.subset_span ?_
    exact h.smoothVec hU hI hKf (M.fr_unit τ) (M.fr_gram τ)
  · exact Submodule.subset_span hKf
  · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
  · exact (le_sSup hK : K ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) hwS
  · intro θ hθ
    rw [map_smul, hw θ hθ, smul_comm]

end GlobalTheory.RealZetaSmoothHi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinPartIdemSumMulInvMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemSumInt

theorem finPart_idemSum_mul_inv_mem : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ t : 𝓞 D.host.E, (∀ Q ∈ SS, t ∉ Q.asIdeal) → finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D := by
  intro D e SS hS t ht
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hS
  by_cases h0 : t = 0
  · subst h0
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_mul, map_sum]
      refine AddSubgroup.sum_mem _ fun PP hPP => ?_
      by_contra hn
      exact ht PP hPP (((hes PP hPP).2 t h0).2 hn)

end GlobalTheory.IdemSumInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinRatMemLatOOfPerO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RatLatPer

open GlobalTheory.LatVac

theorem finRat_mem_latO_of_perO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (x)).reindex (finCongr hT.symm) (finCongr hS.symm)) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D ψ θ S T a b hS hT δ sc hP N N' ΛS ΛT hΛS hΛT h1 h2 x hx
  subst hS hT
  have e1 : N = ΛS := (SetLike.coe_injective h1).symm
  have e2 : N' = ΛT := (SetLike.coe_injective h2).symm
  subst e1 e2
  have hr : (LinearMap.toMatrix' x).reindex (finCongr (rfl : T.rank = T.rank)) (finCongr (rfl : S.rank = S.rank)) =
      LinearMap.toMatrix' x := by
    ext i j; rfl
  rw [hr, GlobalTheory.LatVacSign.finRat_eq]
  refine GlobalTheory.LatVac.finTens_mem_latO (one_mem_intAf _) ?_
  rw [GlobalTheory.AdForm.RatLat.mem_latRat_iff_perO N' hΛS, Matrix.toLin'_toMatrix', GlobalTheory.AdForm.RatLat.AA_eq hP.cc]
  exact hx

end GlobalTheory.AdForm.RatLatPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfCocycleIsotropicIdempotentHalvesTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfCocycle

theorem half_eq (D : D7) :
    incA D ((2 : D.host.E)⁻¹) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2)) := by
  have h2 : ((2 : D.host.E))⁻¹ = algebraMap D.host.F D.host.E (1 / 2) := by
    rw [map_div₀, map_one, map_ofNat, one_div]
  rw [h2, ← IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]
  show (inclR (AF D.host.F)) (algebraMap D.host.F D.host.E (1/2)) = _
  simp [inclR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]

theorem half_mul_symplO {D : D7} (S T : HSp D) (x y : WO S T) :
    algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x y = symplO S T (incA D ((2 : D.host.E)⁻¹) • x) y := by
  unfold symplO
  rw [GlobalTheory.SplitScalar.hO_smul_left, half_eq, mul_left_comm (incA D D.host.xi0),
    ← Algebra.smul_def (algebraMap D.host.F (AF D.host.F) (1 / 2)) (incA D D.host.xi0 * hO S T x y),
    LinearMap.map_smul, smul_eq_mul]

theorem half_idem_int {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hI : IsIdemSum e SS)
    (h2 : ∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) :
    finPart D (incA D ((2 : D.host.E)⁻¹) * e) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, _⟩ := hI
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun PP hPP => ?_
  have hn : (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro hm
    apply h2 PP hPP
    have h2Q : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
    obtain ⟨k, hk⟩ := h2Q
    rw [hk]
    push_cast
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hm))
  have hiff := (hes PP hPP).2 (2 : 𝓞 D.host.E) two_ne_zero
  have hc : ((2 : 𝓞 D.host.E) : D.host.E) = 2 := by first | rfl | simp | exact map_ofNat _ 2 | norm_cast
  rw [hc] at hiff
  rw [mul_comm]
  by_contra hc'
  exact hn (hiff.mpr hc')

end GlobalTheory.HalfCocycle


open GlobalTheory.HalfCocycle in
theorem GlobalTheory.HalfCocycle.char_symplOH_idem_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ u ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ v ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplOH S T (e • u) (cA D e • v)) = 1 := by
  intro D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' u hu v hv
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self hI
  have key : symplO S T (e • u) (cA D e • v) = symplO S T (e • u) v := by
    rw [← GlobalTheory.SplitScalar.symplO_smul, smul_smul, hee]
  rw [symplOH, key, half_mul_symplO, smul_smul]
  exact GlobalTheory.LatVac.char_sympl_eq_one hP.std hN hN'
    (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (half_idem_int hI h2) u hu) hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomAtIffLocPPerO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HomAtPer

theorem exists_den_away (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ z : 𝓞 D.host.E, z ∉ P.asIdeal ∧ ∀ t ∈ D.host.AA0, ∃ w : 𝓞 D.host.E, (w : D.host.E) = t * z := by
  haveI := P.isPrime
  have : Finite (𝓞 D.host.E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hl : (ringChar (𝓞 D.host.E ⧸ P.asIdeal)).Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ P.asIdeal) _
  have hlP : ((ringChar (𝓞 D.host.E ⧸ P.asIdeal) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _
  have h2 : ((D.host.QS : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_right _ h))
  have hq : ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ h))
  exact GlobalTheory.AAUnitAway.exists_den D P.asIdeal hl (UpperTheory.Ram.notMem_small_of_QS_notMem D.host hlP h2)
    (fun e => hq (e ▸ hlP)) hlP

theorem homAt_iff_locP_perO : ∀ (D : D7) (S T : HSp D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, x ∈ Formalism.L2.Col.homAt SS N N' ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D S T SS hSS N N' hN _hN' x
  constructor
  · intro hx P hP
    haveI := P.isPrime
    obtain ⟨gens, hgens⟩ := hN.1.fg
    have hden : ∀ g ∈ gens, ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x g ∈ N' := by
      intro g hg
      have hg' : g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N :=
        ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul, ← hgens]; exact Submodule.subset_span hg⟩
      obtain ⟨s, hs, hsx⟩ := hx P hP g hg'
      exact ⟨s, hs, hsx⟩
    choose! sg hsg using hden
    set s : 𝓞 D.host.E := ∏ g ∈ gens, sg g with hs
    have hsP : s ∉ P.asIdeal := by
      rw [hs]
      intro hm
      obtain ⟨g, hg, hgP⟩ := Ideal.IsPrime.prod_mem_iff.1 hm
      exact (hsg g hg).1 hgP
    have hsx : s • x ∈ homO N N' := by
      intro y hy
      rw [← hgens] at hy
      induction hy using Submodule.span_induction with
      | mem g hg =>
        have e : (s • x) g = (∏ g' ∈ gens.erase g, sg g') • (sg g • x g) := by
          rw [LinearMap.smul_apply, smul_smul, hs, ← Finset.mul_prod_erase gens sg hg, mul_comm]
        rw [e]; exact N'.smul_mem _ (hsg g hg).2
      | zero => rw [map_zero]; exact N'.zero_mem
      | add y z _ _ h1 h2 => rw [map_add (f := _)]; exact N'.add_mem h1 h2
      | smul o y _ h => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem _ h
    exact ⟨s, hsP, Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, s • x, hsx, (one_smul _ _).symm⟩⟩
  · intro hx P hP y hy
    haveI := P.isPrime
    obtain ⟨z, hz, hden⟩ := exists_den_away D P (hSS P hP)
    obtain ⟨s, hs, hsx⟩ := hx P hP
    obtain ⟨t, ht, hty⟩ := hy
    have hper : ∀ w ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∀ v ∈ N, (z • w) v ∈ N' := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w h =>
        obtain ⟨r, hr, h0, hh0, rfl⟩ := h
        intro v hv
        obtain ⟨ρ, hρ⟩ := hden r hr
        have e : (z • r • h0) v = ρ • h0 v := by
          rw [LinearMap.smul_apply, LinearMap.smul_apply, ← algebraMap_smul D.host.E z, ← algebraMap_smul D.host.E ρ, smul_smul]
          congr 1
          change (z : D.host.E) * r = (ρ : D.host.E)
          rw [hρ, mul_comm]
        rw [e]; exact N'.smul_mem ρ (hh0 v hv)
      | zero => intro v _; rw [smul_zero, LinearMap.zero_apply]; exact N'.zero_mem
      | add w₁ w₂ _ _ h1 h2 => intro v hv; rw [smul_add, LinearMap.add_apply]; exact N'.add_mem (h1 v hv) (h2 v hv)
      | smul r w₁ _ h1 => intro v hv; rw [smul_comm, LinearMap.smul_apply]; exact N'.smul_mem r (h1 v hv)
    refine ⟨z * s * t, P.asIdeal.primeCompl.mul_mem (P.asIdeal.primeCompl.mul_mem hz hs) ht, ?_⟩
    have e : (z * s * t) • x y = (z • s • x) (t • y) := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply, smul_smul, smul_smul]
      congr 1; ring
    rw [e]
    exact hper _ hsx _ hty

end GlobalTheory.HomAtPer
end
end

