module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0726
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0713
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0727
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import GroundTheory.LocalFields.CompleteTrivialLocal

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitian
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.SplitPair

section gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evInf_trace [FiniteDimensional F E] (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    evInf F w (Algebra.trace (AF F) (AF F ⊗[F] E) z) =
      Algebra.trace w.Completion (w.Completion ⊗[F] E) (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    have e : compInf F E w (a ⊗ₜ[F] x) = evInf F w a ⊗ₜ[F] x := rfl
    rw [e, GlobalTheory.OppLinChar.trace_tmul', GlobalTheory.OppLinChar.trace_tmul', map_mul, AlgHom.commutes]

theorem eq_single (v : HeightOneSpectrum (𝓞 F)) (y : AF F)
    (hi : ∀ w, evInf F w y = 0) (hf : ∀ v' ≠ v, evFin F v' y = 0) :
    y = pairA F 0 (singleV F v (evFin F v y)) := by
  classical
  refine Prod.ext (funext fun w => hi w) (GlobalTheory.AdelicU.af_ext fun u => ?_)
  by_cases h : u = v
  · subst h
    change _ = singleV F u _ u
    exact (RestrictedProduct.single_eq_same _ u _).symm
  · change _ = singleV F v _ u
    exact (hf u h).trans (RestrictedProduct.single_eq_of_ne _ _ h).symm

theorem cA_eq_sigR (σ : E →ₐ[F] E) (y : AF F ⊗[F] E) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ y = sigR (AF F) σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem psi_half_trace {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F))
    (τ : E →ₐ[F] Fv F v) (ψ : AddChar (AF F) ℂ) {n : ℕ}
    (x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) E)
    (hx : ∀ i j, sigR (AF F) σ (x j i) = x i j) (hb : ∀ i j, σ (b j i) = b i j)
    (hinf : ∀ w i j, compInf F E w (x i j) = 0) (hfin : ∀ v' ≠ v, ∀ i j, compFin F E v' (x i j) = 0) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ i, ∑ j, x i j * inclR (AF F) (b j i))) =
      psiV F ψ v (∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i)) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hcm.2.2.1
  set z : AF F ⊗[F] E := ∑ i, ∑ j, x i j * inclR (AF F) (b j i) with hz
  set a : Fv F v := ∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i) with ha
  have hzi : ∀ w, compInf F E w z = 0 := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, map_sum, map_mul, hinf, zero_mul, Finset.sum_const_zero]
  have hzf : ∀ v' ≠ v, compFin F E v' z = 0 := fun v' h => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, map_sum, map_mul, hfin v' h, zero_mul, Finset.sum_const_zero]
  have hpi : ∀ t : E →ₐ[F] Fv F v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z =
      ∑ i, ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (x i j) * t (b j i) := fun t => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, map_sum, map_mul, GlobalTheory.OppLinChar.piW_inclR]
  have h1 : splitProj τ (compFin F E v z) = a := hpi τ
  have h2 : splitProj (τ.comp σ) (compFin F E v z) = a := by
    refine (hpi (τ.comp σ)).trans ?_
    rw [ha, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (x i j) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (x j i) := by
      rw [← hx i j, ← cA_eq_sigR]
      exact GlobalTheory.OppLinChar.piW_cA hcm τ (x j i)
    rw [e, AlgHom.comp_apply, hb i j]
    rfl
  set y : AF F := algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E) z with hy
  have hv : evFin F v y = a := by
    rw [hy, map_mul, AlgHom.commutes, GlobalTheory.OppLinChar.evFin_trace, GlobalTheory.OppLinChar.trace_split hcm τ, h1, h2,
      ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]
    norm_num
  have hs := eq_single v y
    (fun w => by rw [hy, map_mul, evInf_trace, hzi, map_zero, mul_zero])
    (fun v' h => by rw [hy, map_mul, GlobalTheory.OppLinChar.evFin_trace, hzf v' h, map_zero, mul_zero])
  rw [hv] at hs
  rw [hs]
  rfl

end gen

theorem pch_rat_split : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (ψ : AddChar (AF D.host.F) ℂ) (x : hermA D n),
    (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) → (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) →
    ∀ β : HermE D n, pch ψ x.1 (rat β.1) =
      psiV D.host.F ψ v (Matrix.trace (tauC τ x.1 * β.1.map τ)) := by
  intro D n v τ ψ x hinf hfin β
  have hx : ∀ i j, sigR (AF D.host.F) D.sp.cm.sig (x.1 j i) = x.1 i j := fun i j =>
    congrFun (congrFun x.2 i) j
  have hb : ∀ i j, D.sp.cm.sig (β.1 j i) = β.1 i j := fun i j => congrFun (congrFun β.2 i) j
  exact psi_half_trace (isCMExt_host D) v τ ψ x.1 β.1 hx hb hinf hfin

end GlobalTheory.CompanionTheory.Jp.SplitPair
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTermsUniformlySummable
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf

theorem law_facts : ∀ {D : D7} {n : ℕ} {χ : (AE D)ˣ →* Circle} {s : ℂ} {f : G D n → ℂ}, IsHeckeChar D χ → Continuous f → IsLaw χ s f → (n : ℝ) / 2 < s.re →
    LeftInv (P D n ⊓ GF D n) f ∧
    (∀ q ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat q) = a.1 → Matrix.GeneralLinearGroup.det a = 1 → ∀ g, f (q * g) = f g) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ u : Cosets (P D n) (GF D n) → ℝ, Summable u ∧ ∀ q, ∀ g ∈ C, ‖term (P D n) (GF D n) f g q‖ ≤ u q := by
  intro D n χ s f hχ hc hl hs
  haveI := t2Space_adeleRing' (F := D.host.F)
  refine ⟨fun γ hγ g => ?_, fun q hq a ha h1 g => ?_, fun C hC => ?_⟩
  · obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨a, ha⟩ := exists_blkA hp
    obtain ⟨u, hu⟩ := det_rat hr a ha
    have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hu]; exact absE_inclR u
    have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hu]; exact hχ.2 u
    rw [hl γ hp a ha g, h1, h2]
    simp [npow]
  · rw [hl q hq a ha g, h1]
    simp [npow]
  · have hlaw : IndLaw (GlobalTheory.StdUnn.PolesModel.modP (D := D) (n := n))
        (χ.comp GlobalTheory.StdUnn.PolesModel.detP) (s + (n : ℂ) / 2) f := fun p g =>
      hl p p.2 (GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n) p) rfl g
    have h1 : Continuous (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n)) :=
      PolesModel.isIwasawa.continuous_iwAbs GlobalTheory.StdUnn.Model.isClosed_P PolesModel.continuous_modP GlobalTheory.StdUnn.Model.isCompact_K
    have h2 : Continuous fun g => Real.log (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n) g) :=
      (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (iwAbs_pos _ _ g)).ne'
    have hcf : Continuous fun x : ℂ × G D n => flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s x.1 x.2 := by
      simp only [flatSec, npow_eq_exp (iwAbs_pos _ _ _)]
      exact (hc.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
        (continuous_fst.sub continuous_const)).cexp)
    obtain ⟨u, hu, hb⟩ := exists_majorant (Φ := fun z => flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s z)
      (χ := χ.comp PolesModel.detP) (ρ := (n : ℝ) / 2) (σ := (n : ℝ) / 2) PolesModel.isIwasawa GlobalTheory.StdUnn.Model.isCompact_K
      hcf.continuousOn
      (fun z _ => by
        have := (PolesModel.isIwasawa (D := D) (n := n)).indLaw_flatSec hlaw z
        push_cast
        exact this) PolesModel.summable_spherical (S := {s}) isCompact_singleton (Set.singleton_subset_iff.2 hs) hC
    have e : flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s s = f := funext fun x => by
      simp [flatSec, npow_eq_exp (iwAbs_pos _ _ _)]
    refine ⟨u, hu, fun q g hg => ?_⟩
    have := hb q s rfl g hg
    rwa [e] at this

end GlobalTheory.CompanionTheory.ZUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlobalHermitianLocalApproximation
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp

open GlobalTheory.EmbChart (tensAt compFin_tensAt)

theorem compFin_tensAt_ne_place {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (y : Fv F v ⊗[F] E) :
    compFin F E u (tensAt E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    change (evalV F u (singleFin v a)) ⊗ₜ[F] x = 0
    rw [evalV_singleFin_ne h, TensorProduct.zero_tmul]

theorem compInf_tensAt_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    compInf F E w (tensAt E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    change (evInf F w (GlobalTheory.EmbChart.atPlace v a)) ⊗ₜ[F] x = 0
    rw [show evInf F w (GlobalTheory.EmbChart.atPlace v a) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), TensorProduct.zero_tmul]

theorem cA_tensAt (D : D7) (v : Pl D) (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    cA D (tensAt D.host.E v y) = tensAt D.host.E v (sigR (Fv D.host.F v) D.sp.cm.sig y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem splitProj_sigR (D : D7) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    splitProj τ (sigR (Fv D.host.F v) D.sp.cm.sig y) = splitProj (τ.comp D.sp.cm.sig) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem exists_herm_at (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (X : Matrix (Fin n) (Fin n) (Fv D.host.F v)) :
    ∃ x : hermA D n, (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) ∧
      (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) ∧ tauC τ x.1 = X ∧
      ((∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) →
        ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) := by
  have h := isCMExt_host D
  set M := splitPairMat h τ X Xᵀ with hM
  have p1 : ∀ i j, splitProj τ (M i j) = X i j := fun i j => by
    have := congrArg Prod.fst ((splitAlgEquiv h τ).apply_symm_apply (X i j, Xᵀ i j))
    rwa [splitAlgEquiv_apply] at this
  have p2 : ∀ i j, splitProj (τ.comp D.sp.cm.sig) (M i j) = X j i := fun i j => by
    have := congrArg Prod.snd ((splitAlgEquiv h τ).apply_symm_apply (X i j, Xᵀ i j))
    rwa [splitAlgEquiv_apply] at this
  have hs : ∀ i j, sigR (Fv D.host.F v) D.sp.cm.sig (M j i) = M i j := fun i j => by
    apply (splitAlgEquiv h τ).injective
    rw [splitAlgEquiv_apply, splitAlgEquiv_apply, splitProj_sigR, splitProj_comp_sigR h, p1, p2, p1, p2]
  have hc : ∀ i j, cv D v (tensAt D.host.E v (M i j)) = M i j := fun i j => compFin_tensAt v _
  refine ⟨⟨Matrix.of fun i j => tensAt D.host.E v (M i j), ?_⟩, ?_, ?_, ?_, ?_⟩
  · change adj _ = _
    ext i j
    change cA D (tensAt D.host.E v (M j i)) = tensAt D.host.E v (M i j)
    rw [cA_tensAt, hs]
  · intro w i j
    exact compInf_tensAt_eq_zero w v _
  · intro v' hv i j
    exact compFin_tensAt_ne_place hv _
  · refine Matrix.ext fun i j => ?_
    change splitProj τ (cv D v (tensAt D.host.E v (M i j))) = X i j
    rw [hc, p1]
  · intro hX i j
    change cv D v (tensAt D.host.E v (M i j)) ∈ _
    rw [hc, mem_intLoc_iff_split h τ, p1, p2]
    exact ⟨hX i j, hX j i⟩

end GlobalTheory.CompanionTheory.Jp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiTermsSummableStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_terms_summable : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ g : G D n, (∀ C : Set (G D n), IsCompact C → ∃ c : GlobalTheory.Eis.Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → ℝ, Summable c ∧ ∀ g ∈ C, ∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ c u) → ∃ t : GlobalTheory.Eis.Cosets (P D p) (GF D p) → ℝ, Summable t ∧ ∀ (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (y : Mx D ρ p), Summable (fun η : Matrix (Fin ρ) (Fin p) D.host.E => ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖) ∧ ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖ ≤ t q := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Domination.domination | exact GlobalTheory.CompanionTheory.FJE.Domination.domination | (intros; apply GlobalTheory.CompanionTheory.FJE.Domination.domination <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainUnfoldingTwoSums
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.UnfoldFam

open GlobalTheory.CompanionTheory.UnfoldAbs

theorem unfold_fam : ∀ {A X Y U : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] [Countable U] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : U → A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1)
    (Um : X → ℝ) (_ : Summable Um) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (_ : ∀ b, ∃ l : Λ, ∀ q, ‖F q b‖ ≤ Um (τ l q))
    (e : Λ × U → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l l' : Λ) u, τ l' (e (l, u)) = e (l' + l, u))
    (_ : ∀ (l : Λ) u b, F (e (l, u)) b = F0 u ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    (∀ u, Integrable (F0 u) lam ∧ ∫ b, ‖F0 u b‖ ∂lam ≤ ∑' l : Λ, Um (e (l, u))) ∧
    HasSum (fun u => ∫ b, F0 u b * ch b ∂lam) (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) := by
  intro A X Y U _ _ _ lam _ Λ _ 𝓖 h𝓖 h1 _ _ c y0 F F0 ch hF hch hnorm hmul hΛ Um hUm τ hτ hcτ hbd
    e he hfib hτe hF0 hν
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by simp [h1]⟩

  have hUm0 : ∀ q, 0 ≤ Um q := by
    intro q
    obtain ⟨l, hl⟩ := hbd 0
    have := hl ((τ l).symm q)
    rw [Equiv.apply_symm_apply] at this
    exact (norm_nonneg _).trans this

  have hb : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ ∑' q, Um q := by
    intro b
    obtain ⟨l, hl⟩ := hbd b
    have hs : Summable (fun q => Um (τ l q)) := (τ l).summable_iff.mpr hUm
    have hs1 : Summable (fun q => ‖F q b‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hl hs
    refine ⟨hs1, ?_⟩
    calc ∑' q, ‖F q b‖ ≤ ∑' q, Um (τ l q) := hs1.tsum_le_tsum hl hs
      _ = ∑' q, Um q := (τ l).tsum_eq Um
  have hsub : ∀ {Z : Type} (j : Z → X), Function.Injective j → ∀ b,
      Summable (fun z => ‖F (j z) b‖) ∧ ∑' z, ‖F (j z) b‖ ≤ ∑' q, Um q := by
    intro Z j hj b
    refine ⟨(hb b).1.comp_injective hj, ?_⟩
    exact (tsum_comp_le_tsum_of_inj (hb b).1 (fun _ => norm_nonneg _) hj).trans (hb b).2
  have key : ∀ {Z : Type} [Countable Z] (j : Z → X), Function.Injective j →
      HasSum (fun z => ∫ b in 𝓖, F (j z) b * ch b ∂lam)
        (∫ b in 𝓖, (∑' z, F (j z) b) * ch b ∂lam) := by
    intro Z _ j hj
    have := hasSum_integral_of_norm_bound (lam.restrict 𝓖) (fun z b => F (j z) b * ch b)
      (fun z => ((hF (j z)).mul hch).restrict) (∑' q, Um q) (fun b => by
        simpa [hnorm] using hsub j hj b)
    simpa only [tsum_mul_right] using this

  have heu : ∀ u, Function.Injective (fun l : Λ => e (l, u)) := fun u a b h =>
    (Prod.mk.inj (he h)).1
  have hF0e : ∀ u, F0 u = F (e (0, u)) := by
    intro u
    funext b
    have := hF0 0 u b
    simpa using this.symm
  have hm0 : ∀ u, AEStronglyMeasurable (F0 u) lam := fun u => hF0e u ▸ hF (e (0, u))
  have hSs : ∀ u, Summable (fun l : Λ => Um (e (l, u))) := fun u => hUm.comp_injective (heu u)
  have hS0 : ∀ u, 0 ≤ ∑' l : Λ, Um (e (l, u)) := fun u => tsum_nonneg fun _ => hUm0 _
  have horb : ∀ u b, Summable (fun l : Λ => ‖F0 u ((l : A) + b)‖) ∧
      ∑' l : Λ, ‖F0 u ((l : A) + b)‖ ≤ ∑' l : Λ, Um (e (l, u)) := by
    intro u b
    obtain ⟨l0, hl0⟩ := hbd b
    have hle : ∀ l : Λ, ‖F0 u ((l : A) + b)‖ ≤ Um (e (l0 + l, u)) := by
      intro l
      rw [← hF0 l u b, ← hτe l l0 u]
      exact hl0 _
    have hs : Summable (fun l : Λ => Um (e (l0 + l, u))) :=
      (Equiv.addLeft l0).summable_iff.mpr (hSs u)
    have hs1 : Summable (fun l : Λ => ‖F0 u ((l : A) + b)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
    refine ⟨hs1, ?_⟩
    calc ∑' l : Λ, ‖F0 u ((l : A) + b)‖ ≤ ∑' l : Λ, Um (e (l0 + l, u)) :=
          hs1.tsum_le_tsum hle hs
      _ = ∑' l : Λ, Um (e (l, u)) :=
          (Equiv.addLeft l0).tsum_eq (fun l : Λ => Um (e (l, u)))
  have hint0 : ∀ u, Integrable (F0 u) lam := fun u =>
    integrable_of_lattice_bound lam Λ 𝓖 h𝓖 h1 (F0 u) (hm0 u) _ (horb u)
  have hnb : ∀ u, ∫ b, ‖F0 u b‖ ∂lam ≤ ∑' l : Λ, Um (e (l, u)) := by
    intro u
    rw [integral_norm_eq_lintegral_enorm (hm0 u)]
    refine ENNReal.toReal_le_of_le_ofReal (hS0 u) ?_
    have ee : ∫⁻ b, ‖F0 u b‖ₑ ∂lam = ∑' l : Λ, ∫⁻ b in 𝓖, ‖F0 u ((l : A) + b)‖ₑ ∂lam :=
      h𝓖.lintegral_eq_tsum'' _
    have hmeas : ∀ l : Λ, AEMeasurable (fun b => ‖F0 u ((l : A) + b)‖ₑ) (lam.restrict 𝓖) :=
      fun l => (((hm0 u).comp_measurePreserving
        (measurePreserving_add_left lam (l : A))).enorm).restrict
    rw [ee, ← lintegral_tsum hmeas]
    calc ∫⁻ b in 𝓖, ∑' l : Λ, ‖F0 u ((l : A) + b)‖ₑ ∂lam
        ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal (∑' l : Λ, Um (e (l, u))) ∂lam := by
          refine lintegral_mono (fun b => ?_)
          simp_rw [← ofReal_norm_eq_enorm]
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (horb u b).1]
          exact ENNReal.ofReal_le_ofReal (horb u b).2
      _ = ENNReal.ofReal (∑' l : Λ, Um (e (l, u))) := by simp [h1]
  refine ⟨fun u => ⟨hint0 u, hnb u⟩, ?_⟩

  have hT := key (Z := X) id Function.injective_id
  simp only [id] at hT
  have hsig := (Equiv.sigmaFiberEquiv c).hasSum_iff.mpr hT
  have hg : HasSum (fun y => ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam)
      (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) :=
    hsig.sigma (fun y => key (Z := {x // c x = y}) Subtype.val Subtype.val_injective)

  have hzero : ∀ y, y ≠ y0 → ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam = 0 := by
    intro y hy
    obtain ⟨ν, hν1, hνq⟩ := hν y hy
    refine setIntegral_eq_zero_of_translate lam Λ 𝓖 h𝓖 _ ν (ch ν) hν1 (fun l b => ?_) (fun b => ?_)
    · have hs : ∑' z : {x // c x = y}, F z ((l : A) + b) = ∑' z : {x // c x = y}, F z b := by
        calc ∑' z : {x // c x = y}, F z ((l : A) + b)
            = ∑' z : {x // c x = y}, F (τ l z) b := tsum_congr fun z => hτ l z b
          _ = ∑' z : {x // c x = y}, F z b :=
            ((τ l).subtypeEquiv (p := fun x => c x = y) (q := fun x => c x = y)
              (fun a => by rw [hcτ])).tsum_eq (fun z : {x // c x = y} => F z b)
      rw [hs, hmul, hΛ, one_mul]
    · have hs : ∑' z : {x // c x = y}, F z (ν + b) = ∑' z : {x // c x = y}, F z b :=
        tsum_congr fun z => hνq z z.2 b
      rw [hs, hmul]
      ring
  have hT' := hg.unique (hasSum_single y0 (fun y hy => hzero y hy))
  rw [hT']

  let ee : Λ × U ≃ {x // c x = y0} := Equiv.ofBijective
    (fun p => ⟨e p, (hfib _).2 ⟨p, rfl⟩⟩)
    ⟨fun a b h => he (congrArg Subtype.val h), fun q => by
      obtain ⟨p, hp⟩ := (hfib q).1 q.2
      exact ⟨p, Subtype.ext hp⟩⟩
  have hsum : ∀ b, ∑' z : {x // c x = y0}, F z b = ∑' p : Λ × U, F (e p) b := fun b =>
    (ee.tsum_eq (fun z => F z b)).symm
  simp_rw [hsum]
  have hK := key e he
  have hK' : HasSum (fun p : U × Λ => ∫ b in 𝓖, F (e (p.2, p.1)) b * ch b ∂lam)
      (∫ b in 𝓖, (∑' p : Λ × U, F (e p) b) * ch b ∂lam) :=
    (Equiv.prodComm U Λ).hasSum_iff.mpr hK
  refine hK'.prod_fiberwise (fun u => ?_)
  have hs := hK'.summable.prod_factor u
  have hint1 : Integrable (fun b => F0 u b * ch b) lam :=
    (hint0 u).mono ((hint0 u).aestronglyMeasurable.mul hch) (ae_of_all _ fun b => by simp [hnorm])
  have hval : ∫ b, F0 u b * ch b ∂lam = ∑' l : Λ, ∫ b in 𝓖, F (e (l, u)) b * ch b ∂lam := by
    rw [h𝓖.integral_eq_tsum'' _ hint1]
    refine tsum_congr fun l => ?_
    refine integral_congr_ae (ae_of_all _ fun b => ?_)
    change F0 u ((l : A) + b) * ch ((l : A) + b) = F (e (l, u)) b * ch b
    rw [hF0, hmul, hΛ, one_mul]
  rw [hval]
  exact hs.hasSum

end GlobalTheory.CompanionTheory.UnfoldFam
end
end

