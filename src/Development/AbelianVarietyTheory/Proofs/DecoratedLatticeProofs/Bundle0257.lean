module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriods
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSawStep

variable {D : D7}

theorem per_smul_right {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem per_smul_left {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (a : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (a • φ) f = a * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem trc_smul {V : HSp D} (e : GA D V →₀ ℂ) (b : ℂ) (f : GA D V → ℂ) : trc e (b • f) = b • trc e f := by
  funext g
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

theorem liftS_smul {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (b : ℂ) (G : GA D T → ℂ)
    (f : WO S T → ℂ) : liftS om ν 𝓕 (b • G) f = b • liftS om ν 𝓕 G f := by
  funext g
  simp only [liftS_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem rapidDec_smul {V : HSp D} (b : ℂ) (F : GA D V → ℂ) (hF : RapidDec V F) : RapidDec V (b • F) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨fun γ hγ g => by simp only [Pi.smul_apply, h1 γ hγ g], h2.const_smul b, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h3 N
  refine ⟨‖b‖ * C, fun g => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg b)

theorem contAut_zero (V : HSp D) : IsContAut V (fun _ => (0 : ℂ)) := ⟨fun _ _ _ => rfl, continuous_const⟩

theorem perF_smul {c : Comm D} (tt : Tup c) (n ρ : ℕ) (h : n + 2 * ρ + 2 = D.R.m) (φ : tt.Ch n → GA D (c.X n) → ℂ) (b : ℂ)
    (f : GA D (c.V n) → ℂ) : tt.perF n ρ h φ (b • f) = b * tt.perF n ρ h φ f := by
  simp only [Tup.perF, trc_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => per_smul_right _ _ _ _ _

theorem perF_comb (hPS : PerSum D) {c : Comm D} (hc : c.Is) (tt : Tup c) (n ρ : ℕ) (h : n + 2 * ρ + 2 = D.R.m) (k : ℂ)
    (co : c.Fr n →₀ ℂ) (φ : tt.Ch n → c.Fr n → GA D (c.X n) → ℂ) (hφ : ∀ β y, IsContAut (c.X n) (φ β y))
    (f : GA D (c.V n) → ℂ) (hf : IsContAut (c.V n) f) :
    tt.perF n ρ h (fun β => k • ∑ y' ∈ co.support, co y' • φ β y') f =
      k * ∑ y' ∈ co.support, co y' * tt.perF n ρ h (fun β => φ β y') f := by
  have e : ∀ β, (c.B n ρ h).per c.ψ (k • ∑ y' ∈ co.support, co y' • φ β y') (trc (tt.e n β) f) =
      k * ∑ y' ∈ co.support, co y' * (c.B n ρ h).per c.ψ (φ β y') (trc (tt.e n β) f) := by
    intro β
    have hT : IsContAut _ (trc (tt.e n β) f) :=
      (((_root_.GlobalTheory.SeeSaw.per_linear_trc D c.ψ hc.std ρ (c.B n ρ h) (fun _ => 0) (contAut_zero _)).2 (tt.e n β) f hf).1)
    rw [per_smul_left]
    congr 1
    exact hPS c.ψ hc.std ρ (c.B n ρ h) (trc (tt.e n β) f) hT (c.Fr n) co.support co (fun y' => φ β y') (fun y' _ => hφ β y')
  simp only [Tup.perF, e]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.mul_sum]


set_option maxHeartbeats 2000000 in
theorem stepX_of_laws : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D →
    RapidVal D → ValMove D → PerSum D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ValX t → TwoX t → RdX t → StepX t := by
  intro hHC D c 𝒯 t hDS hRV hVM hPS hc ht hloc hVal hTwo hRd
  intro j σ h I _ s α ψ G hψ hvan y v
  obtain ⟨χ0, hχ0⟩ := hRd j (by omega)
  have hφ : ∀ i a, IsContAut (c.X j) ((t (s i)).rd j a (ψ i) y) := fun i a => (hχ0 (s i) (ψ i) (hψ i) a y).1
  have hspan : GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) (c.M (j + 1 + 1)) (c.It (j + 1)) := hc.span (j + 1) (by omega)
  simp only [Tup.per]
  refine _root_.GlobalTheory.SeeSaw.perF_rel_of_steps hHC D c 𝒯 t hc j (σ + 1) h I s (fun i => α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)))
    (fun i a => (t (s i)).rd j a (ψ i) y) (fun i => (t (s i)).io j ((t (s i)).io (j + 1) (G i))) ht hφ
    (c.V (j + 1 + 1)) (c.V (j + 1 + 1)) (c.par (j + 1 + 1)) (c.M (j + 1 + 1)) (c.It (j + 1)) hspan ?_ v
  intro P₁ P₂ v''
  have key : ∀ i, ((t (s i)).cI j * (t (s i)).cI (j + 1)) •
      ((t (s i)).io j ((t (s i)).io (j + 1) (G i))).1 (c.It j P₁ (c.It (j + 1) P₂ v'')) =
      liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'') ((t (s i)).pt (j + 1) P₂))
        ((t (s i)).pt j P₁) := by
    intro i
    rw [(ht (s i)).io (j + 1) (by omega) (G i) P₂ v'', liftS_smul, (ht (s i)).io j (by omega) _ P₁ _, smul_smul, mul_comm]
  have e : ∀ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) * (t (s i)).perF j (σ + 1) h (fun a => (t (s i)).rd j a (ψ i) y)
      (((t (s i)).io j ((t (s i)).io (j + 1) (G i))).1 (c.It j P₁ (c.It (j + 1) P₂ v''))) =
      α i * (t (s i)).perF j (σ + 1) h (fun a => (t (s i)).rd j a (ψ i) y)
        (liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
          (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'') ((t (s i)).pt (j + 1) P₂))
          ((t (s i)).pt j P₁)) := by
    intro i
    rw [← key i, perF_smul, mul_assoc]
  rw [Finset.sum_congr rfl fun i _ => e i]
  have hR0 : ∀ i, RapidDec _ ((G i).1 v'') := by
    intro i
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1 + 1) (by omega)
    exact hRV c.θ hc.inf _ _ (c.M (j + 1 + 1)) J χ (G i).1 (hJ (G i).2) v''
  have hR1 : ∀ i, RapidDec _ (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'')
      ((t (s i)).pt (j + 1) P₂)) := by
    intro i
    rw [(ht (s i)).io (j + 1) (by omega) (G i) P₂ v'']
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1) (by omega)
    exact rapidDec_smul _ _ (hRV c.θ hc.inf _ _ (c.M (j + 1)) J χ _ (hJ ((t (s i)).io (j + 1) (G i)).2) _)
  refine _root_.GlobalTheory.SeeSaw.VanMany.vanMany D c 𝒯 t hDS hc ht hloc j σ h P₁ P₂ I s α (fun i a => (t (s i)).rd j a (ψ i) y) (fun i => (G i).1 v'')
    hφ hR0 hR1 ?_
  intro a ha a' ha'
  obtain ⟨C, hC, hCe⟩ := hVal j σ h P₁ P₂ a ha a' ha'
  obtain ⟨co, hco⟩ := hTwo j (by omega) C hC y
  obtain ⟨sm, hsm⟩ := GlobalTheory.RealTransSm.rTrans_eq_map D c.θ (c.V (j + 1 + 1)) (c.par (j + 1 + 1)) (c.M (j + 1 + 1)) hc.inf a' ha'
  refine ⟨fun i => (t (s i)).cV j * (t (s i)).perF (j + 1 + 1) σ (idx_step h)
      ((t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C) (rTrans a' ((G i).1 v'')),
    fun i => hCe (s i) (ψ i) (hψ i) y (G i) v'', ?_⟩
  obtain ⟨χ2, hχ2⟩ := hRd (j + 1 + 1) (by omega)
  have hψ'' : ∀ i, (t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i))) ∈ (t (s i)).Ram (j + 1 + 1) := fun i =>
    (ht (s i)).stabK (j + 1) (by omega) _ ((ht (s i)).stabK j (by omega) _ ((ht (s i)).stabS j (by omega) _ (hψ i)))
  have term : ∀ i, α i * ((t (s i)).cV j * (t (s i)).perF (j + 1 + 1) σ (idx_step h)
      ((t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C) (rTrans a' ((G i).1 v''))) =
      ∑ y' ∈ co.support, co y' * (α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1)) *
        (t (s i)).per (j + 1 + 1) σ (idx_step h) ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (G i) y' (sm v'')) := by
    intro i
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1 + 1) (by omega)
    have hw : rTrans a' ((G i).1 v'') = (G i).1 (sm v'') := (hsm J χ (G i).1 (hJ (G i).2) v'').symm
    have htwo : (t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C = fun β =>
        ((t (s i)).cK j * (t (s i)).cK (j + 1)) • ∑ y' ∈ co.support, co y' •
          (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y' :=
      funext (hco (s i) _ ((ht (s i)).stabS j (by omega) _ (hψ i)))
    have hGw : RapidDec _ ((G i).1 (sm v'')) := hRV c.θ hc.inf _ _ (c.M (j + 1 + 1)) J χ (G i).1 (hJ (G i).2) _
    rw [hw, htwo, perF_comb hPS hc _ _ _ _ _ co _ (fun β y' => (hχ2 (s i) _ (hψ'' i) β y').1) _ ⟨hGw.1, hGw.2.1⟩]
    simp only [Tup.per, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => term i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [← Finset.mul_sum, hvan y' (sm v''), mul_zero]

end GlobalTheory.SeeSawStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUniformiserIdeleValueUnramifiedCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_uniformiserIdele_value_unramifiedChar : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.SplitUnifIdele.value_eq_val | exact GlobalTheory.SplitUnifIdele.value_eq_val | (intros; apply GlobalTheory.SplitUnifIdele.value_eq_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitWeilPhiInnerProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_phi_inner_product : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ), r ≤ a → r ≤ b → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (phiQ (a := a) (b := b) v r mu) (phiQ (a := a) (b := b) v r mu) = (((GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal * (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (b - r)))⁻¹) : ℝ) : ℂ) ∧ phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  first | exact @GlobalTheory.NrmVol.phiQ_ip | exact GlobalTheory.NrmVol.phiQ_ip | (intros; apply GlobalTheory.NrmVol.phiQ_ip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepClass1Of
section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem stepClass1_of (h : CorankOneIsEquivalenceOnRow) : StepClass1 := by
  intro D X Y u hc νL νB ng
  obtain ⟨hR, hS, hT⟩ := h D X Y u u hc
  have hsub : ∀ t ∈ (Y.tO u u).genSet, t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  intro t ht t' ht'
  rw [genT_ngSet] at ht ht'
  change t ∈ (Y.tO u u).genSet at ht
  change t' ∈ (Y.tO u u).genSet at ht'
  have es : (genT (scT (Y.tO u u))).s0 t t' = 1 ↔ (Y.tO u u).s0 t t' = 1 := by
    simp only [genT, scT, and_true]
    by_cases hc : (Y.tO u u).s0 t t' = 1
    · simp [hc]
    · simp [hc]
  show ((scT (Y.tO u u)).rowOf t = (scT (Y.tO u u)).rowOf t' ∧ (genT (scT (Y.tO u u))).s0 t t' = 1) ↔
    cls1 Y u t = cls1 Y u t'
  rw [es]
  change ((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (Y.tO u u).s0 t t' = 1) ↔ cls1 Y u t = cls1 Y u t'
  constructor
  · rintro ⟨hr, h1⟩
    have b1 := hS t (hsub t ht) t' (hsub t' ht') hr h1
    ext x
    simp only [cls1, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr, hT t' (hsub t' ht') t (hsub t ht) x (hsub x hx) hr.symm hrx.symm b1 hx1⟩
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr.symm, hT t (hsub t ht) t' (hsub t' ht') x (hsub x hx) hr hrx.symm h1 hx1⟩
  · intro hc
    have hm : t' ∈ cls1 Y u t' := ⟨ht', rfl, hR t' (hsub t' ht')⟩
    rw [← hc] at hm
    exact ⟨hm.2.1.symm, hm.2.2⟩

end GlobalTheory.Core.One
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLoc1OfFam
section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem stepLoc1_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFam1) : StepLoc1 := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLeG_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

end GlobalTheory.Core.One
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageWittIndexLtAndPlacesTwoSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.WittTwo

theorem wittIndex_lt_and_two_split : ∀ (D : D7) (c : Com D) (j : ℕ) (s : PiLocalization₂ D), j ≤ D.R.m → s.Is c j → GlobalTheory.Cusp.wittIndex s.V < D.R.t ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D c j s hj hs
  refine ⟨?_, fun v h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hpar : ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (s.V.gram.map τ) (sigYD D.R j).1 (sigYD D.R j).2 := by
    intro τ
    have h := hs.sigOK τ
    rw [hs.sig τ] at h
    exact h
  obtain ⟨W, hW, e⟩ := (GlobalTheory.Cusp.isGreatest_wittIndex (s.V : HSpace D.host.E)).1
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := GlobalTheory.ParallelWitt.finrank_le (E := D.host.E) s.V τ (hpar τ) W (fun x hx y hy => by
    have := hW hy
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this x hx)
  have h3 := D.R.three_m_lt_t
  simp only [sigYD] at h1
  omega

end GlobalTheory.ChainOnto.WittTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsOpenLevelCompleteSobolev
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaComplete

theorem lim_clauses : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (U : AddSubgroup (WO S T)) (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ f : WO S T → ℂ, TendstoUniformly u f Filter.atTop → (∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) ∧ (∀ x ∈ U, x.map (infPart D) = 0 → heisO ψ S T x f = f) ∧ Continuous f := by
  intro D ψ S T U u hu f hf
  have ht : ∀ w, Filter.Tendsto (fun j => u j w) Filter.atTop (nhds (f w)) := fun w => hf.tendsto_at w
  refine ⟨fun γ w => ?_, fun x hx h0 => ?_, hf.continuous (Filter.Frequently.of_forall fun j => (hu j).1.cont)⟩
  · refine tendsto_nhds_unique (ht _) ?_
    have e : (fun j => u j (ratW T S γ + w)) = fun j => ψ (-(symplOH S T (ratW T S γ) w)) * u j w :=
      funext fun j => (hu j).1.quasi γ w
    rw [e]
    exact (ht w).const_mul _
  · funext w
    refine tendsto_nhds_unique ((ht (w + x)).const_mul (ψ (symplOH S T w x))) ?_
    have e : (fun j => ψ (symplOH S T w x) * u j (w + x)) = fun j => u j w :=
      funext fun j => congrFun ((hu j).2 x hx h0) w
    rw [e]
    exact ht w

theorem lim_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := _root_.GlobalTheory.ThetaLimDeriv.heisDer_of_tendstoUniformly
theorem lim_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := _root_.GlobalTheory.ThetaDens.contDiff_of_tendstoUniformly_words

theorem limit_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → F [] ∈ thetaLevel ψ S T U ∧ ∀ l, GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (F []) = F l := by
  intro D ψ hψ θ hθ S T U hU u hu F hF
  have h0 := lim_clauses D ψ S T U u hu (F []) (hF [])
  have hth : IsThetaFunO ψ S T (F []) :=
    ⟨h0.1, ⟨U, hU, h0.2.1⟩, h0.2.2, lim_smooth D ψ hψ θ hθ S T u (fun j => (hu j).1) F hF []⟩
  refine ⟨⟨hth, h0.2.1⟩, fun l => ?_⟩
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih]
    exact lim_deriv D ψ hψ θ hθ S T (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) (F (a :: l))
      (fun j => GlobalTheory.Size.theta_word hψ hθ l (hu j).1) (hF l) a (hF (a :: l))

theorem complete : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∃ f ∈ thetaLevel ψ S T U, ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  intro D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc
  have hC := _root_.GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc
  have hlim : ∀ l w, ∃ z, Filter.Tendsto (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j) w) Filter.atTop (nhds z) :=
    fun l w => cauchySeq_tendsto_of_complete ((hC l).cauchySeq (Set.mem_univ w))
  choose F hF using hlim
  have hFu : ∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop :=
    fun l => tendstoUniformlyOn_univ.1 ((hC l).tendstoUniformlyOn_of_tendsto fun w _ => hF l w)
  obtain ⟨h1, h2⟩ := limit_theta D ψ hψ θ hθ S T U hU u hu F hFu
  refine ⟨F [], h1, _root_.GlobalTheory.ThetaDens.sobO_sub_tendsto_zero D ψ hψ θ hθ S T μ 𝓕 hμ u (F []) h1.1 (fun j => (hu j).1) fun l => ?_⟩
  rw [h2 l]
  exact hFu l

end GlobalTheory.ThetaComplete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodingerStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_schwartzBruhat_continuous_schrodinger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ φ : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → Continuous f ∧ sch ψ A B ν 𝓨 f = φ := by
  first | exact @GlobalTheory.Core.Rk.ThetaOf.theta_series_sch | exact GlobalTheory.Core.Rk.ThetaOf.theta_series_sch | (intros; apply GlobalTheory.Core.Rk.ThetaOf.theta_series_sch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeParahoricEntriesEqColumnData
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.EntryAtTwist

theorem bas_eq_one {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (W : TwData k) (j c : ℕ) (h : j + c = s + 1) : (W.T s R).bas j c h = 1 := by
  first | rfl | (simp [TwData.T, twistChain, Chain.ofTwist])

theorem entryAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → EntryAgree Ch sel mu cst σ₀ P ι s W ν L := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hcst hAt L G hL
  have hSum := GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hcst hAt
  have hVol := GlobalTheory.T.local_volume_agrees_row_subgroup_unitary X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hcst hAt
  intro j c h al be g g' hg hg' e' e he' he x
  have hnm := hAt.nmem
  obtain ⟨A₀, B₀, hAB⟩ := hSum j c h (L.h j al P) (L.h (j + 1) be P) g g' hg hg'
    (hL.boundQ j al P hnm) (hL.boundQ (j + 1) be P hnm) (hL.depthQ' P hnm)
  have hF := hAB (max A₀ cst.A) (max B₀ cst.B) (le_max_left _ _) (le_max_left _ _) e' e he' he x
  rw [hL.deep _ _ (le_max_right _ _) (le_max_right _ _) j (by omega) al be P] at hF
  have hV := (hVol (j + 1) c (by omega) (L.h (j + 1) be P) g' hg').1
  simp only [Chain.entry, xi, bas_eq_one]
  rw [hF, Complex.ofReal_inv, hV]
  simp only [XiAt, map_mul, map_inv₀]
  ring

end GlobalTheory.EntryAtTwist
end

