module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0072
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.FlagAct


variable {D : D7} {c : Com D} {s : PiLocalization₂ D}

theorem not_isConjPl_of_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∀ PP ∈ P, ∀ PP' ∈ P, ¬ Lev.IsConjPl PP PP' := by
  classical
  intro PP hP PP' hP' hc
  obtain ⟨⟨es, hes, he⟩, h0⟩ := h
  have hsum : ∑ x ∈ P ×ˢ P, es x.1 * cA D (es x.2) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_product, ← h0, he, map_sum, Finset.sum_mul_sum]
  have hidem : ∀ x ∈ P ×ˢ P,
      (es x.1 * cA D (es x.2)) * (es x.1 * cA D (es x.2)) = es x.1 * cA D (es x.2) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hx
    rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]
  have horth : es PP * cA D (es PP') = 0 :=
    GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) (ι := Pl D.host.E × Pl D.host.E)
      (fun n z hn hz => GlobalTheory.PlaceVec.natCast_mul_eq_zero (D := D) n z hn hz) (fun x => es x.1 * cA D (es x.2)) (P ×ˢ P)
      hidem hsum (PP, PP') (Finset.mem_product.2 ⟨hP, hP'⟩)
  have hfw : ∀ x, x ∈ PP.asIdeal → Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    intro x hx
    obtain ⟨c', hc', hcv⟩ := hc x hx
    have e1 : c' = Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext hcv
    rw [← e1]; exact hc'
  have hiff : ∀ x, x ∈ PP.asIdeal ↔ Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    have hle : PP.asIdeal ≤ PP'.asIdeal.comap (Formalism.L2.Col.cO D.host.E) := fun x hx => hfw x hx
    haveI := PP'.isPrime
    have heq := PP.isMaximal.eq_of_le (Ideal.IsPrime.comap (Formalism.L2.Col.cO D.host.E)).ne_top hle
    intro x
    rw [heq]
    exact Ideal.mem_comap
  have hconj := GlobalTheory.MovedIdem.isIdemAt_conj (hes PP' hP') hiff
  have heq : es PP = cA D (es PP') :=
    (GlobalTheory.ExportSeries.idemAt_eq (hes PP hP)).symm.trans (GlobalTheory.ExportSeries.idemAt_eq hconj)
  have hz : es PP = 0 := by
    calc es PP = es PP * es PP := ((hes PP hP).1.1).symm
      _ = es PP * cA D (es PP') := congrArg (es PP * ·) heq
      _ = 0 := horth
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
  have h3 := ((hes PP hP).2 x hx0).1 hxP
  rw [hz, zero_mul, map_zero] at h3
  exact h3 (zero_mem _)

theorem liftsExist_stage {c : Com D} (hc : c.Is) {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) :
    Lev.LiftsExist s.V s.β s.L := by
  obtain ⟨N, hN, -⟩ := hs.base
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  obtain ⟨e, he⟩ := hc.split
  have hnc := not_isConjPl_of_idemSum he
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  refine GlobalTheory.ParahoricLift.liftsExist s.V s.β s.L s.Λ N hN (fun PP hP PP' hP' => ?_) ?_
  · rw [hPg] at hP
    rw [hPg, hQ] at hP'
    rcases hP' with h | h
    · exact hnc PP hP PP' h
    · exact absurd h (Finset.notMem_empty _)
  · rw [hQ]; exact Finset.disjoint_empty_right _

end GlobalTheory.ChainOnto.FlagAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJReal

variable {D : D7}

theorem detPlus_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus 1 1 a b = b.det ^ n * a.det ^ m := by
  unfold GlobalTheory.WeilParts.detPlus
  have e2 : (1 + 1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = (2 : ℂ) • 1 := by
    rw [two_smul]
  rw [Matrix.transpose_one, Matrix.one_kronecker_one, sub_self, smul_zero, add_zero, e2, Matrix.smul_mul,
    Matrix.one_mul, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_kronecker,
    Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin]

theorem exp_identity (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (e mS mT : ℤ) (nS nT : ℕ) (hS : (nS : ℤ) = mS + mS)
    (hT : (nT : ℤ) = mT + mT) :
    (a ^ (e - mT))⁻¹ * b ^ (e - mS) * (b ^ nS * a⁻¹ ^ nT) = a ^ (-e - mT) * b ^ (e + mS) := by
  rw [inv_pow, ← zpow_natCast b, ← zpow_natCast a, ← zpow_neg a, ← zpow_neg a]
  calc (a ^ (-(e - mT)) * b ^ (e - mS) * (b ^ (nS : ℤ) * a ^ (-(nT : ℤ))))
      = a ^ (-(e - mT)) * a ^ (-(nT : ℤ)) * (b ^ (e - mS) * b ^ (nS : ℤ)) := by ring
    _ = a ^ (-(e - mT) + -(nT : ℤ)) * b ^ (e - mS + (nS : ℤ)) := by rw [← zpow_add₀ ha, ← zpow_add₀ hb]
    _ = a ^ (-e - mT) * b ^ (e + mS) := by
      congr 2
      · rw [hT]; ring
      · rw [hS]; ring

end GlobalTheory.KJReal

namespace GlobalTheory.KJReal

end GlobalTheory.KJReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneLeMulOfOneLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumLoc

variable {D : D7}

theorem idem_mul_sum {es : Formalism.L2.DIV.Pl D.host.E → AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hes : ∀ Q ∈ S, Formalism.L2.NTheta.IsIdemAt (es Q) Q) (hc : (∑ Q ∈ S, es Q) * cA D (∑ Q ∈ S, es Q) = 0)
    {P : Formalism.L2.DIV.Pl D.host.E} (hP : P ∈ S) : es P * ∑ Q ∈ S, es Q = es P := by
  have h1 : ∀ i ∈ S, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ S, ∀ j ∈ S, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es S h1 hc
  rw [Finset.mul_sum, Finset.sum_eq_single P
    (fun Q hQ hQP => GlobalTheory.PlaceDatum.idemAt_mul (hes P hP) (hes Q hQ) (hcross P hP Q hQ) (hcross Q hQ P hP) hQP)
    (fun h => absurd hP h), h1 P hP]

end GlobalTheory.IdemSumLoc

namespace GlobalTheory.IdemSumLoc

end GlobalTheory.IdemSumLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PostOnMemEEatOfCenter
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

set_option maxHeartbeats 800000

open Formalism.BasicNotions.TH Formalism.IndefR.Lev

namespace GlobalTheory.MiTop.CentralShift

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem actL_rTr_of_center (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : LevDat D.host.E ℂ V.rank) (g0 : G0 Ld.Pg Ld.r)
    {z : GA D V} (hz : z ∈ Subgroup.center (GA D V)) (f : GA D V → ℂ) :
    actL V β Ld g0 (rTr V z f) = rTr V z (actL V β Ld g0 f) := by
  funext x
  show actG0 V β Ld g0 (rTr V z f) x = actG0 V β Ld g0 f (x * z)
  unfold actG0
  split_ifs with hk
  · simp only [rTr]
    rw [mul_assoc x hk.choose z, mul_assoc x z hk.choose, Subgroup.mem_center_iff.mp hz hk.choose]
  · rfl

theorem gaL_rTr_of_center {G : Type} [Group G] [Fintype G] (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : LevDat D.host.E ℂ V.rank)
    (eG : G ≃* G0 Ld.Pg Ld.r) (c : G → ℂ) {z : GA D V} (hz : z ∈ Subgroup.center (GA D V)) (f : GA D V → ℂ) :
    gaL V β Ld eG c (rTr V z f) = rTr V z (gaL V β Ld eG c f) := by
  unfold gaL
  funext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, actL_rTr_of_center β Ld _ hz]
  simp [rTr, Finset.sum_apply]

theorem ipM_eq_of_iff (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {T T' U U' : MMap M}
    (h : ∀ c, IsMultIP M μ 𝓕 T T' c ↔ IsMultIP M μ 𝓕 U U' c) : ipM M μ 𝓕 T T' = ipM M μ 𝓕 U U' := by
  have e : IsMultIP M μ 𝓕 T T' = IsMultIP M μ 𝓕 U U' := funext fun c => propext (h c)
  unfold ipM
  rw [e]

theorem map_mul_right_center (μ : Measure (GA D V)) (hμ : μ.IsHaarMeasure) {z : GA D V}
    (hz : z ∈ Subgroup.center (GA D V)) : Measure.map (fun g => g * z) μ = μ := by
  have e : (fun g : GA D V => g * z) = fun g => z * g := funext fun g => Subgroup.mem_center_iff.mp hz g
  rw [e]
  exact map_mul_left_eq_self μ z

theorem lift_postOn (T : MMap M) (z : GA D V) (v : SmT M) :
    PiTensorProduct.lift (postOn M (GlobalTheory.FinTranslate.rTrL V z) T) v = rTr V z (PiTensorProduct.lift T v) := by
  have : PiTensorProduct.lift (postOn M (GlobalTheory.FinTranslate.rTrL V z) T) =
      GlobalTheory.FinTranslate.rTrL V z ∘ₗ PiTensorProduct.lift T := by
    apply PiTensorProduct.ext
    ext w
    simp [postOn, PiTensorProduct.lift.tprod]
  rw [this]
  rfl

end General

section Main

open GlobalTheory.MiTop.CentralShift

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end Main

end GlobalTheory.MiTop.CentralShift

namespace GlobalTheory.MiTop

open GlobalTheory.MiTop.CentralShift

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelNormSqModerateGrowthLarge
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem normSq_theta_modGrowth_big : GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation →
    ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t →
    ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ →
    (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧
      GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  intro hSWF hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat mH hmH Φ hΦ
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  obtain ⟨ha, ht, hb, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.Core.Rk.exists_doubled_weilDatum hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.DoublingTheta.thetaClause D ψ A B χA χB om omh hP.weil homh
  obtain ⟨hφ, hid⟩ := hTC Φ Φ hΦ.1 hΦ.1
  have hK := GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ Φ hΦ hΦ
  have h2ab : 2 * A.rank < B.rank := by omega
  have hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank := by
    rcases hwitt with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  obtain ⟨hint, hEV⟩ := _root_.GlobalTheory.Core.Rk.IP.thetaMean_eq_eis_of_weil hSWF D ψ A B (by omega) h2ab hw χB omh homh ν 𝓕 hP.covol mH hmH
    (delta A B Φ Φ) hφ

  have key : ∀ g h, thetaKO om g h Φ * conj (thetaKO om g h Φ) =
      ((χB (detA A g) : Circle) : ℂ) * thetaKO omh (io A (g, g)) h (delta A B Φ Φ) := by
    intro g h
    rw [(hid g g h).2]
    have e : ((χB (detA A g) : Circle) : ℂ) * (((χB (detA A g))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g h Φ * conj (thetaKO om g h Φ))) * e
  have knorm : ∀ g h, ‖thetaKO om g h Φ‖ ^ 2 = ‖thetaKO omh (io A (g, g)) h (delta A B Φ Φ)‖ := by
    intro g h
    have := congrArg norm (key g h)
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_conj, ← sq] at this
    rw [this]
  have hleft : ∀ g, LeftInv (GQ B) fun h => thetaKO om g h Φ := fun g γ hγ h => by
    show thetaKO om g (γ * h) Φ = thetaKO om g h Φ
    have e : ((g, γ * h) : GA D A × GA D B) = (1, γ) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hP.weil.om_aut 1 (one_mem _) _ hγ _ (hP.weil.om_pres _ _ hΦ.1)
  have hcont : ∀ g, Continuous fun h => thetaKO om g h Φ := fun g =>
    (hP.weil.om_cont Φ hΦ.1 0).comp (Continuous.prodMk_right g)
  have hL2 : ∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ := by
    intro g
    refine ⟨hleft g, ?_⟩
    have hm : AEStronglyMeasurable (descend (GQ B) fun h => thetaKO om g h Φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ B) mH) := by
      rw [aestronglyMeasurable_quotMeasure_iff_lift, (hleft g).lift_descend]
      exact (hcont g).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hint (io A (g, g))).norm.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend]
    exact (knorm g _).symm
  refine ⟨hL2, ?_⟩

  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := _root_.GlobalTheory.SwSecMem.swSec_mem_degPS hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ Φ) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨hCt, hReg⟩ := hSEC D A (by omega) a hP.maj hI χB⁻¹ B.rank hHk (resEta_inv homh.resT) (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ Φ)) hmem
  obtain ⟨k, hk⟩ := hReg (sZero A B)
  have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
    have e : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, Complex.div_re]
    rw [e]
    have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast h2ab
    linarith
  have hF := hCt.1
  have hv0 := hF.eisValueAt hF.analyticOnNhd_flat hre
  have hv : GlobalTheory.Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (sZero A B)
      (ThetaMean.thetaMean omh mH (delta A B Φ Φ)) := by
    rw [hEV]; simpa only [flatH_self] using hv0
  obtain ⟨r, hr, -, -, C₁, N, hC₁⟩ := GlobalTheory.Eis.EisRegularAt.of_eisValueAt hk hv
  have hE : ∀ x, ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) x‖ ≤ C₁ * GlobalTheory.Grow.height (dblSp A) x ^ N := by
    intro x
    have e := hv.eisCont_eq
    have := hC₁ (sZero A B) (Metric.mem_ball_self hr) x
    rw [e] at this
    exact this
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := (norm_nonneg _).trans (hE 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (GlobalTheory.Grow.height_pos _ _) _)
  obtain ⟨C₂, c, hC₂⟩ := GlobalTheory.Grow.IoHeight.main D A
  have hvol := GlobalTheory.RallisIP.Model.vol_pos (B := B) mH
  have hpet : ∀ g, ‖petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ)‖ =
      (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖ := by
    intro g
    have e1 : petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ) =
        ((χB (detA A g) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g, g)) h (delta A B Φ Φ)) q ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g _
    rw [e1, norm_mul, Circle.norm_coe, one_mul, ← measure_smul_average, norm_smul, ThetaMean.thetaMean,
      Real.norm_of_nonneg measureReal_nonneg]
  refine ⟨(autMeasure B mH).real Set.univ * C₁ * C₂ ^ N, 2 * c * N, fun g => ?_⟩
  rw [hpet g]
  have h2 : GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N ≤ (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N := by
    refine pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ?_ N
    have := hC₂ g g
    rwa [← sq, ← pow_mul] at this
  calc (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖
      ≤ (autMeasure B mH).real Set.univ * (C₁ * GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N) :=
        mul_le_mul_of_nonneg_left (hE _) hvol.le
    _ ≤ (autMeasure B mH).real Set.univ * (C₁ * (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁0) hvol.le
    _ = (autMeasure B mH).real Set.univ * C₁ * C₂ ^ N * GlobalTheory.Grow.height A g ^ (2 * c * N) := by
        rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToEAfMulIncAMemOfIsIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemIntegral

theorem toEAf_mem_of_finPart_mem {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D w) ∈ _
  generalize finPart D w = z at hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [Algebra.TensorProduct.comm_tmul]
    exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_incA_mem {D : D7} (r : 𝓞 D.host.E) : finPart D (incA D (r : D.host.E)) ∈ intAE D := by
  have : finPart D (incA D (r : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (r : D.host.E) := rfl
  rw [this]
  exact AddSubgroup.subset_closure ⟨1, fun v => by simp, r, rfl⟩

theorem mem_of_idemAt {D : D7} {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    {a : D.host.E} (ha : Formalism.L2.Col.IntAt PP a) :
    toEAf D (e * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨r, s, hs, hsa⟩ := ha
  have hs0 : s ≠ 0 := fun h => hs (h ▸ zero_mem _)
  have hsE : (s : D.host.E) ≠ 0 := by exact_mod_cast hs0
  have ha : a = ((s : D.host.E))⁻¹ * (r : D.host.E) := by
    change (s : D.host.E) * a = (r : D.host.E) at hsa
    rw [← hsa, ← mul_assoc, inv_mul_cancel₀ hsE, one_mul]
  have h1 : finPart D (e * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact hs ((he.2 s hs0).2 h)
  rw [ha, (incA D).map_mul, ← mul_assoc, (toEAf D).map_mul]
  exact mul_mem (toEAf_mem_of_finPart_mem h1) (toEAf_mem_of_finPart_mem (finPart_incA_mem r))

end GlobalTheory.IdemIntegral

end
end

