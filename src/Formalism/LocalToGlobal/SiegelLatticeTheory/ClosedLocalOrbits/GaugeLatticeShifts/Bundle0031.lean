module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FlagExtensionRegularity
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.RealObj.FlagExtensionRegularity

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fam_castLE {n r l : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (hl : l ≤ r) (h : l ≤ r + 1) (b : Fin l) :
    fam e z (Fin.castLE h b) = e (Fin.castLE hl b) := by
  have : Fin.castLE h b = Fin.castSucc (Fin.castLE hl b) := Fin.ext rfl
  rw [this, fam, Fin.snoc_castSucc]

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a
  simp [famSc]

theorem span_map {n r : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (e : Fin r → Fin n → ℂ) (a : ℕ) {y : Fin n → ℂ}
    (hy : y ∈ spanLt e a) : g *ᵥ y ∈ spanLt (fun c => g *ᵥ e c) a := by
  unfold spanLt at *
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, rfl⟩ := hw
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add w1 w2 _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
  | smul c w _ h1 => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ h1

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem uMat_mul_inv' {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a * uMat a⁻¹ = 1 := by
  simp [uMat]

theorem dl_eq (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) {l : ℕ} (hl : l ≤ D.R.rS) :
    Dl (ZX X u u' 1 γ v) l =
      (HermitianBlockSpans.blk (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => uMat (γ v) *ᵥ rv X.B.I v (X.eR a)) hl).det := by
  have h : l ≤ D.R.rS + 1 := hl.trans (Nat.le_succ _)
  unfold Dl
  rw [dite_eq_left h]
  congr 1
  ext b c
  simp only [Matrix.submatrix_apply, ZX, Zhat, frm, famSc_one, HermitianBlockSpans.blk, Matrix.of_apply]
  rw [fam_castLE _ _ hl h, fam_castLE _ _ hl h]

variable {X} {u u' : D.what₂.Word} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (X u u')

end Formalism.L2.SG.RealObj.FlagExtensionRegularity
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
section
noncomputable section

namespace Formalism.L2.SG.Pf.FormAllPf

open MeasureTheory Set
open scoped ENNReal

section Gen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem decomp (μR : Measure G) (R : Set G) (hR : μR Rᶜ = 0) (Γ0 : Subgroup G) [Countable Γ0]
    (P Q : Set G) (hP : MeasurableSet P) (hQ : MeasurableSet Q) (hQu : ∀ r ∈ R, ∃! s, s ∈ Γ0 ∧ s * r ∈ Q) :
    μR P = ∑' s : Γ0, μR (P ∩ (fun x => (s : G) * x) ⁻¹' Q) := by
  classical
  have hmeas : ∀ s : Γ0, MeasurableSet (P ∩ (fun x => (s : G) * x) ⁻¹' Q) :=
    fun s => hP.inter (measurable_const_mul (s : G) hQ)
  have hdisj : Pairwise (Function.onFun (AEDisjoint μR)
      (fun s : Γ0 => P ∩ (fun x => (s : G) * x) ⁻¹' Q)) := by
    intro s t hst
    show μR ((P ∩ (fun x => (s : G) * x) ⁻¹' Q) ∩ (P ∩ (fun x => (t : G) * x) ⁻¹' Q)) = 0
    refine measure_mono_null ?_ hR
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxR
    obtain ⟨y, _, huniq⟩ := hQu x hxR
    apply hst
    have e1 : (s : G) = y := huniq s ⟨s.2, hx.1.2⟩
    have e2 : (t : G) = y := huniq t ⟨t.2, hx.2.2⟩
    exact Subtype.ext (e1.trans e2.symm)
  have hRae : ∀ᵐ x ∂μR, x ∈ R := by
    first
      | exact ae_iff.2 hR
      | exact (mem_ae_iff.2 hR : R ∈ ae μR)
      | simpa [ae_iff] using hR
  have hae : P =ᵐ[μR] ⋃ s : Γ0, (P ∩ (fun x => (s : G) * x) ⁻¹' Q) := by
    filter_upwards [hRae] with x hx
    constructor
    · intro hxP
      obtain ⟨s, hs, hsQ⟩ := (hQu x hx).exists
      exact Set.mem_iUnion.2 ⟨⟨s, hs⟩, hxP, hsQ⟩
    · intro h
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 h
      exact hs.1
  rw [measure_congr hae, measure_iUnion₀ hdisj fun s => (hmeas s).nullMeasurableSet]

theorem fd_meas_eq (μR : Measure G) (R : Set G) (hR : μR Rᶜ = 0) (Γ0 : Subgroup G) [Countable Γ0]
    (hinv : ∀ s ∈ Γ0, μR.map (fun x => s * x) = μR) (A K : Set G) (hA : MeasurableSet A) (hK : MeasurableSet K)
    (hAu : ∀ r ∈ R, ∃! s, s ∈ Γ0 ∧ s * r ∈ A) (hKu : ∀ r ∈ R, ∃! s, s ∈ Γ0 ∧ s * r ∈ K) : μR A = μR K := by
  rw [decomp μR R hR Γ0 A K hA hK hKu, decomp μR R hR Γ0 K A hK hA hAu,
    ← (Equiv.inv Γ0).tsum_eq (fun s : Γ0 => μR (K ∩ (fun x => (s : G) * x) ⁻¹' A))]
  refine tsum_congr fun s => ?_
  show μR (A ∩ (fun x => (s : G) * x) ⁻¹' K) = μR (K ∩ (fun x => ((s : G))⁻¹ * x) ⁻¹' A)
  have hB : MeasurableSet (K ∩ (fun x => ((s : G))⁻¹ * x) ⁻¹' A) :=
    hK.inter (measurable_const_mul _ hA)
  have hpre : (fun x => (s : G) * x) ⁻¹' (K ∩ (fun x => ((s : G))⁻¹ * x) ⁻¹' A) =
      A ∩ (fun x => (s : G) * x) ⁻¹' K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, inv_mul_cancel_left]
    exact and_comm
  rw [← hpre, ← Measure.map_apply (measurable_const_mul _) hB, hinv s s.2]

def invSigma {G : Type*} [Group G] (m0 : MeasurableSpace G) (R : Set G) : MeasurableSpace G where
  MeasurableSet' := fun B => MeasurableSet[m0] B ∧ ∀ r ∈ R, (fun x => r * x) ⁻¹' B = B
  measurableSet_empty := ⟨@MeasurableSet.empty G m0, fun r _ => preimage_empty⟩
  measurableSet_compl := fun B hB => ⟨hB.1.compl, fun r hr => by rw [preimage_compl, hB.2 r hr]⟩
  measurableSet_iUnion := fun B hB => ⟨MeasurableSet.iUnion fun i => (hB i).1,
    fun r hr => by rw [preimage_iUnion]; exact iUnion_congr fun i => (hB i).2 r hr⟩

theorem integral_eq_of_inv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] [CompleteSpace V] (μ μ' : Measure G) (R : Set G) (f : G → V) (hf : Measurable f)
    (hfi : ∀ r ∈ R, ∀ x, f (r * x) = f x)
    (hmeas : ∀ B, MeasurableSet B → (∀ r ∈ R, (fun x => r * x) ⁻¹' B = B) → μ B = μ' B) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ' := by
  have hm : invSigma ‹MeasurableSpace G› R ≤ ‹MeasurableSpace G› := by
    intro B hB
    exact And.left hB
  have hfm : Measurable[invSigma ‹MeasurableSpace G› R] f := by
    intro B hB
    exact (⟨hf hB, fun r hr => by ext x; simp [hfi r hr x]⟩ :
      MeasurableSet[‹MeasurableSpace G›] (f ⁻¹' B) ∧ ∀ r ∈ R, (fun x => r * x) ⁻¹' (f ⁻¹' B) = f ⁻¹' B)
  have hsm : StronglyMeasurable[invSigma ‹MeasurableSpace G› R] f := hfm.stronglyMeasurable
  have htrim : μ.trim hm = μ'.trim hm := by
    refine @Measure.ext G (invSigma ‹MeasurableSpace G› R) _ _ fun B hB => ?_
    rw [trim_measurableSet_eq hm hB, trim_measurableSet_eq hm hB]
    exact hmeas B (And.left hB) (And.right hB)
  rw [integral_trim hm hsm, integral_trim hm hsm, htrim]

end Gen

end Formalism.L2.SG.Pf.FormAllPf

namespace Formalism.L2.SG.Pf

open MeasureTheory Set Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish
  NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormAllC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (μR ν : Measure X.B.I.Ginf) (K : Set X.B.I.Ginf),
    (∀ r ∈ Rset t, X.psiInfU u r = X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) →
    IsHaarOnSet X.B.I (Rset t) μR → IsQuotMeasS X.B.I μR ν →
    MeasurableSet K → (∀ r ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * r ∈ K) →
    haveI := FiniteDimensional.complete ℂ (X.Vpi u)
    OOt t = (μR K).toReal • OO ν Set.univ (X.Wu u) (X.Wu u') t.pt.1

theorem formAllC_holds : FormAllC := by
  intro D X Y u u' t μR ν K hchi hH hQ hKm hKu
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)

  have hFE : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := fundExistsC_holds D X Y u u' t
  have hFO : IsSFund X.B.I (ROinf t) (FundOf t) := by
    unfold FundOf; rw [dite_eq_left hFE]; exact hFE.choose_spec

  set Γ0 := ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin with hΓ0
  have hΓc : Countable Γ0 := by
    have := ROsub_discrete X (X.Fu u) (X.Fu u') t.lam t.lam' ((Y.rowsOK u).1 t.lam t.mem).1.1 t.lin
    exact countable_of_discrete Γ0
  have hΓR : ∀ s ∈ Γ0, s ∈ Rset t := by
    rintro _ ⟨x, n, hxn, rfl, hn, hn'⟩
    refine ⟨nLamNinf_holds D X u _ x n hxn hn, ?_⟩
    have hrep : RatLink X t.pt t.lin := t.rep.2.1
    have h2 := ratLink_mul X (ratLink_mul X (ratLink_inv X hrep) hxn) hrep
    have h3 := nLamNinf_holds D X u' _ _ _ h2 hn'
    simpa [Prod.fst_mul, Prod.fst_inv] using h3
  have hμinv : ∀ s ∈ Γ0, μR.map (fun x => s * x) = μR := fun s hs => hH.2.2.2 s (hΓR s hs)

  have hsec : ∀ x, μR ((fun s => s * x) ⁻¹' FundOf t) = μR K := by
    intro x
    refine FormAllPf.fd_meas_eq μR (Rset t) hH.2.2.1 Γ0 hμinv _ K (hFO.1.preimage (measurable_mul_const x)) hKm
      (fun r _ => ?_) hKu
    obtain ⟨s, hs, hsx⟩ := hFO.2.1 (r * x)
    refine ⟨s, ⟨hs, by simpa [mul_assoc] using hsx⟩, fun s' ⟨hs', hs'x⟩ => ?_⟩
    have h1 : s' * r * x ∈ FundOf t := hs'x
    have h2 : (s * s'⁻¹) * (s' * r * x) ∈ FundOf t := by simpa [mul_assoc] using hsx
    have := hFO.2.2 _ h1 _ (Γ0.mul_mem hs (Γ0.inv_mem hs')) h2
    exact (mul_inv_eq_one.1 this).symm

  set f : X.B.I.Ginf → (X.Vpi u' →L[ℂ] X.Vpi u) := fun x => rk1 (X.Wu u x) (X.Wu u' (t.pt.1⁻¹ * x)) with hfdef
  have hfc : Continuous f :=
    Formalism.L2.SG.RealObj.RankOneTensors.continuous_rankOneOperator (X.Wu_spec u).2.2.1
      ((X.Wu_spec u').2.2.1.comp (continuous_const.mul continuous_id))
  have hfi : ∀ r ∈ Rset t, ∀ x, f (r * x) = f x := by
    intro r hr x
    simp only [hfdef]
    rw [wu_N X u hr.1 x, show t.pt.1⁻¹ * (r * x) = (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * x) by group,
      wu_N X u' hr.2 _, ← hchi r hr]
    exact rankOneInnerOperator_smul_smul_eq_mul_conj_smul _ (Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u r) _ _
  letI : MeasurableSpace (X.Vpi u' →L[ℂ] X.Vpi u) := borel _
  haveI : BorelSpace (X.Vpi u' →L[ℂ] X.Vpi u) := ⟨rfl⟩
  haveI : SecondCountableTopology (X.Vpi u' →L[ℂ] X.Vpi u) := inferInstance
  have hfm : Measurable f := hfc.measurable

  have hB : ∀ B, MeasurableSet B → (∀ r ∈ Rset t, (fun x => r * x) ⁻¹' B = B) →
      ((Formalism.L2.SG.ProjRows.muInf X.B.I).restrict (FundOf t)) B = ((μR K) • ν) B := by
    intro B hBm hBi
    rw [Measure.restrict_apply hBm, Measure.smul_apply, smul_eq_mul]
    have hq := hQ ((B ∩ FundOf t).indicator 1) ((measurable_const).indicator (hBm.inter hFO.1))
    rw [lintegral_indicator_one (hBm.inter hFO.1)] at hq
    rw [hq, ← lintegral_indicator_const hBm]
    refine lintegral_congr fun x => ?_
    have e1 : (fun s => (B ∩ FundOf t).indicator (1 : X.B.I.Ginf → ℝ≥0∞) (s * x)) =
        ((fun s => s * x) ⁻¹' (B ∩ FundOf t)).indicator 1 := by
      funext s; rfl
    rw [e1, lintegral_indicator_one ((hBm.inter hFO.1).preimage (measurable_mul_const x)),
      ← measure_inter_conull (t := Rset t) hH.2.2.1]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← hsec x, ← measure_inter_conull (s := (fun s => s * x) ⁻¹' FundOf t) hH.2.2.1]
      congr 1
      ext s
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩
        refine ⟨⟨?_, h2⟩, h3⟩
        have := congrArg (fun S => x ∈ S) (hBi s h3)
        simp only [mem_preimage] at this
        exact this ▸ hx
    · rw [Set.indicator_of_notMem hx]
      have hempty : (fun s => s * x) ⁻¹' (B ∩ FundOf t) ∩ Rset t = ∅ := by
        ext s
        refine ⟨fun hs => ?_, fun h => h.elim⟩
        obtain ⟨⟨h1, -⟩, h3⟩ := hs
        have := congrArg (fun S => x ∈ S) (hBi s h3)
        simp only [mem_preimage] at this
        exact absurd (this ▸ h1) hx
      rw [hempty, measure_empty]

  show OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u') t.pt.1 = _
  unfold OO
  rw [Measure.restrict_univ, ← integral_smul_measure]
  exact FormAllPf.integral_eq_of_inv _ _ (Rset t) f hfm hfi hB

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstFinal
section
noncomputable section

namespace Formalism.L2.SG.Pf

theorem WB.rhsWLim' [Fact Formalism.L2.SG.Pf.WB.RhsWLim] : WB.RhsWLim := Fact.out


variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem jacGauge : JacGauge := jacGauge_of_rhsW WB.rhsWLim'

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LiftOntoCOf
section
namespace Formalism.L2.SG.Pf

theorem liftOntoC_of (hLI : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.SG.TermTieOf.LatIso D) : Formalism.L2.SG.Pf.SatGram.LiftOntoC :=
  fun D X Y u u' => Act.liftOnto (hLI D) (ratPt_holds D X) Y u u' (toTermRel_holds X u u' _ _)

end Formalism.L2.SG.Pf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsAmp
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_wRow_lb {D : D7} (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hA : Formalism.L2.SG.PairVal.AutFin D F0 what₂) :
    ∃ m : ℝ, 0 < m ∧ ∀ Λ ∈ what₂, m ≤ wRow D F0 Λ := by
  rcases what₂.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · refine ⟨what₂.inf' h (wRow D F0), ?_, fun Λ hΛ => Finset.inf'_le _ hΛ⟩
    rw [Finset.lt_inf'_iff]
    exact fun Λ hΛ => Formalism.L2.SG.PairVal.wRow_pos D F0 (hA Λ hΛ)

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

end Formalism.L2.SG.RowsAbsX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal
section
noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem trExistsC_of (hP : ∀ (D : D7) (X : HidaSetting D), SatGram.PsiCond X) : TRExistsC :=
  fun D X _ => SatGram.typedRed_exists' SatGramLoc.split_prime_local_holds SatGramLoc.reduction_structure_holds (hP D X)

theorem psiCond_holds {D : D7} (X : HidaSetting D) : SatGram.PsiCond X :=
  open Formalism.L2.SG.Pf.SatGram in
  psi_conductor_all_places D X

theorem trExistsC_holds : TRExistsC :=
  trExistsC_of (fun _ X => psiCond_holds X)

section

variable {D : D7} (X : HidaSetting D)

theorem typed_count_holds (TR : TypedRed X) (i : Fin 2) :
    Fintype.card {v : TR.Pl // Fintype.card (TR.Fq v) = D.host.g i} = Module.finrank ℚ X.B.I.F :=
  open Formalism.L2.SG.Pf.SatGram Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.GGMirabolic in
  typed_count (redExists_holds X) (gUnif_holds X) (gResCard_holds X) (gCount_of splitPrimeLoc_holds) TR i

theorem tt_eq_holds (TR : TypedRed X) :
    ∏ v, (1 + 3 / (Fintype.card (TR.Fq v) : ℝ)) =
      (1 + 3 / (D.host.g 0 : ℝ)) ^ Module.finrank ℚ X.B.I.F * (1 + 3 / (D.host.g 1 : ℝ)) ^ Module.finrank ℚ X.B.I.F := by
  have h0 := typed_count_holds X TR 0
  have h1 := typed_count_holds X TR 1
  rw [Fintype.card_subtype] at h0 h1
  have hfilt : Finset.univ.filter (fun v => ¬ Fintype.card (TR.Fq v) = D.host.g 0) =
      Finset.univ.filter (fun v => Fintype.card (TR.Fq v) = D.host.g 1) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => (TR.card_q v).resolve_left h
    · intro h h'
      exact D.host.g_ne (h'.symm.trans h)
  have e0 : ∏ v ∈ Finset.univ.filter (fun v => Fintype.card (TR.Fq v) = D.host.g 0),
      (1 + 3 / (Fintype.card (TR.Fq v) : ℝ)) = (1 + 3 / (D.host.g 0 : ℝ)) ^ Module.finrank ℚ X.B.I.F := by
    rw [Finset.prod_congr rfl (g := fun _ => (1 + 3 / (D.host.g 0 : ℝ)))
      (fun v hv => by rw [(Finset.mem_filter.mp hv).2]), Finset.prod_const, h0]
  have e1 : ∏ v ∈ Finset.univ.filter (fun v => ¬ Fintype.card (TR.Fq v) = D.host.g 0),
      (1 + 3 / (Fintype.card (TR.Fq v) : ℝ)) = (1 + 3 / (D.host.g 1 : ℝ)) ^ Module.finrank ℚ X.B.I.F := by
    rw [hfilt, Finset.prod_congr rfl (g := fun _ => (1 + 3 / (D.host.g 1 : ℝ)))
      (fun v hv => by rw [(Finset.mem_filter.mp hv).2]), Finset.prod_const, h1]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun v => Fintype.card (TR.Fq v) = D.host.g 0), e0, e1]

theorem gamma_one_typed_places_holds (TR : TypedRed X) :
    Gam1 TR = ∏ p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1),
      (Formalism.L2.SG.TypedSets.glkC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) /
        (Formalism.L2.SG.TypedSets.ukC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) :=
  open Formalism.L2.SG.Pf.SatGram Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.GGMirabolic in
  gamma_one_eq_prod_typed_places (redExists_holds X) (gUnif_holds X) (gResCard_holds X) (gCount_of splitPrimeLoc_holds) TR

theorem gSplitX_holds : Formalism.L2.SG.LocVol.GSplitX X := by
  intro p
  have hg0 : D.host.g 0 ≠ 0 := (D.host.g_prime 0).ne_zero
  have hg1 : D.host.g 1 ≠ 0 := (D.host.g_prime 1).ne_zero
  have hty := (Formalism.L2.SG.TypedSets.mem_typSet X.B.I.F _ _ hg0 hg1 p.1).1 p.2
  have hg : ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    rw [X.g_eq, Nat.cast_mul]
    rcases hty with h | h
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h
  refine ⟨?_, ?_⟩
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    unfold Formalism.L2.SG.LocVol.gAt
    split_ifs with h0
    · exact gResCard_holds X p.1 0 h0
    · exact gResCard_holds X p.1 1 (hty.resolve_left h0)
  · unfold Formalism.L2.SG.LocVol.etaV
    rw [if_pos (split_at_g X p.1 hg)]

end

end Formalism.L2.SG.Pf
end
end

