module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.PrimStd

open GlobalTheory.SeeSaw (idV FI dI)
open scoped Pointwise

theorem modulBar_ne_bot {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) : P.modulBar sc ≠ ⊥ := by
  unfold Places.modulBar
  intro h
  apply P.modul_ne_bot sc
  have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
  simpa [smul_smul] using this

end GlobalTheory.AscFin.PrimStd


open GlobalTheory.SeeSaw (idV FI dI) in
open GlobalTheory.AscFin.PrimStd in
theorem GlobalTheory.AscFin.primAt_std_bessel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0,
    PrimAt W.ψ (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) v := by
  intro D _ T L μ0 _ sc G W M _ F hF ρ h v hv
  have hψ := W.ψ_std
  obtain ⟨-, f2, f3, -, f5, -, -⟩ := _root_.GlobalTheory.SeeSaw.idV_props D W.ψ hψ v
  obtain ⟨h2, he, -⟩ := hF.hB ρ h
  have hlat := G.sp.colLat (2 * ρ + 2) (by omega) h
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (modulBar_ne_bot G.pl sc)
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hmB)
  have hAb : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hm)
  have hst : ∀ p, stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p ≠ 0 := fun p =>
    mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb))
  have hx : ∀ n : ℕ, (-D.host.xi0) ^ n ≠ 0 := fun n => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  let 𝔟 : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (p.1 + 1))⁻¹ *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p)
  have hb0 : ∀ p, 𝔟 p ≠ 0 := fun p => mul_ne_zero
    (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (hx _)) (hst _)
  have key : ∀ (p : Fin ρ), ∀ a ∈ idAt D (· = v),
      GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v) ↔ a ∈ idV (𝔟 p) v := by
    intro p a ha
    have e1 : GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a = fun k => (a * incA D ((-D.host.xi0) ^ (p.1 + 1))) *
        incA D ((G.colDec (2 * ρ + 2) (by omega) h).a k (Fin.castLE (by omega) p)) := by
      funext k
      show a * incA D ((F.dB ρ h).e k p) = _
      rw [he]
      simp only [colsOf, map_mul, mul_assoc]
    have hL1 := GlobalTheory.T.column_mem_lattice_iff_ideal (G.colDec (2 * ρ + 2) (by omega) h) (by norm_num) (G.sp.P (2 * ρ + 2)).lat
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) v (Fin.castLE (by omega) p) (a * incA D ((-D.host.xi0) ^ (p.1 + 1)))
    rw [e1]
    refine (show _ ↔ _ from hlat ▸ hL1).trans ?_
    have h3 := f3 (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p)) _
      (inv_ne_zero (hx (p.1 + 1))) a
    rw [inv_inv] at h3
    exact ⟨fun h1 => h3.2 ⟨by rwa [mul_comm (incA D _) a], ha⟩, fun h1 => by rw [mul_comm a]; exact (h3.1 h1).1⟩
  intro i j hij s hs
  have key2 : (∀ a : AE D, GlobalTheory.FinPl.colMul (F.dB ρ h).jX j a ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v) →
      GlobalTheory.FinPl.colMul (F.dB ρ h).jX i (s * a) ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v)) ↔
      ∀ a ∈ idV (𝔟 j) v, s * a ∈ idV (𝔟 i) v := by
    constructor
    · intro h1 a ha
      have haA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ a ha
      exact (key i (s * a) (Ideal.mul_mem_left _ _ haA)).1 (h1 a ((key j a haA).2 ha))
    · intro h1 a hc
      have haA := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul (F.dB ρ h) hc
      exact (key i (s * a) (Ideal.mul_mem_left _ _ haA)).2 (h1 a ((key j a haA).1 hc))
  rw [key2, f2 _ _ (hb0 j) (hb0 i) s hs]
  have hsucc := stairId_succ (𝔞 := G.pl.stA sc) hAb (Fin.castLE (by omega) i : Fin (2 * ρ + 2 - 1)) (Fin.castLE (by omega) j)
    (by simp [Fin.coe_castLE, hij])
  have hrat : 𝔟 i * (𝔟 j)⁻¹ = FractionalIdeal.spanSingleton _ (-D.host.xi0) * (G.pl.stA sc * G.pl.stAbar sc) := by
    rw [mul_inv_eq_iff_eq_mul₀ (hb0 j)]
    have e2 : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ = -D.host.xi0 * ((-D.host.xi0) ^ (j.1 + 1))⁻¹ := by
      have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero
      rw [hij]
      field_simp
      ring
    show FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _ = _ * (FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _)
    rw [hsucc, e2, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    ring
  have hneg : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) = FractionalIdeal.spanSingleton _ D.host.xi0 :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, by simp⟩
  have hsplit : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) * (G.pl.stA sc * G.pl.stAbar sc) *
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) = dI D := by
    rw [hneg]
    unfold Places.stA Places.stAbar dI
    field_simp
  have hL := _root_.GlobalTheory.ChiGrid.Places.idV_mul_modul G.pl sc v hv
  have e3 : idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) * (G.pl.stA sc * G.pl.stAbar sc)) v = idV (dI D) v := by
    rw [← hsplit, (hL _).2, (hL _).1]
  rw [hrat, e3]
  exact f5 s hs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesFourierJacobiLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff Pointwise
open GlobalTheory.AscFin


open GlobalTheory.StairLine GlobalTheory.SeeSaw in
theorem GlobalTheory.AscFin.primAt_jac_std : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, PrimAt W.ψ (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  intro D hOff T L μ0 hL sc G W M hM F hF ρ h v hv
  obtain ⟨hc, he, -⟩ := hF.hJ ρ h
  have hlat := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  let 𝔟 : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)
  have hline : ∀ p : Fin ρ, ∀ a, GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔
      a ∈ idV (𝔟 p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := hlat
    rw [e2]
    exact line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega)
      (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v a
  intro i j hij s hs
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    unfold Places.modulBar
    intro h0
    apply G.pl.modul_ne_bot sc
    have h1 := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using h1
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hB : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hne : ∀ p, 𝔟 p ≠ 0 := fun p => mul_ne_zero
    (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)))
    (by
      unfold stairId
      refine mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)))
  have key : (∀ a : AE D, GlobalTheory.FinPl.colMul (F.dJ ρ h).jX j a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) →
      GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i (s * a) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v)) ↔
      ∀ a ∈ idV (𝔟 j) v, s * a ∈ idV (𝔟 i) v :=
    ⟨fun H a ha => (hline i _).1 (H a ((hline j a).2 ha)), fun H a hc => (hline i _).2 (H a ((hline j a).1 hc))⟩
  rw [key, _root_.GlobalTheory.IdealQuot.mul_subset_iff D v _ _ (hne j) (hne i) s hs, ← DiffDual.idV_dI_iff D W.ψ W.ψ_std v s hs]
  have hid : 𝔟 i * (𝔟 j)⁻¹ * (((G.pl.modul sc * G.pl.modulBar sc : Ideal (𝓞 D.host.E))) : FI D) = dI D := by
    have hst := stairId_succ (𝔞 := G.pl.stA sc) (c := 2 * ρ + 1 - 1) hB (Fin.castLE (by omega) i) (Fin.castLE (by omega) j)
      (by simp only [Fin.coe_castLE]; exact hij)
    have hSj : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j) ≠ 0 := by
      unfold stairId
      exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))
    show FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (i.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) i) *
      (FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (j.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j))⁻¹ * _ = _
    rw [hst]
    revert hSj
    generalize stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j) = Sj
    intro hSj
    rw [FractionalIdeal.coeIdeal_mul, mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
    unfold Places.stA Places.stAbar dI
    have hx : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (-D.host.xi0) ^ (j.1 + 1) = -D.host.xi0 := by
      rw [hij, pow_succ (-D.host.xi0) (i.1 + 1), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)), one_mul]
    calc _ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ (i.1 + 1))⁻¹) *
          FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((-D.host.xi0) ^ (j.1 + 1)) * D.host.AA * D.host.AAbar *
          (Sj * Sj⁻¹) * (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) *
          (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ hSj, mul_inv_cancel₀ hN, mul_inv_cancel₀ hN', FractionalIdeal.spanSingleton_mul_spanSingleton, hx,
          mul_one, mul_one, mul_one]
        congr 2
        rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
        exact ⟨-1, by simp⟩
  constructor
  · intro hs'
    refine idV_le_of_loc (fun z hz => ?_) hs'
    obtain ⟨t, ht, htm⟩ := exists_modul G.pl sc hv
    exact ⟨t, ht, by rw [← hid, mul_comm (algebraMap _ _ _)]; exact FractionalIdeal.mul_mem_mul hz htm⟩
  · intro hs'
    refine GlobalTheory.SeeSaw.idV_mono ?_ v hs'
    rw [← hid]
    calc _ ≤ 𝔟 i * (𝔟 j)⁻¹ * 1 := by first | exact FractionalIdeal.mul_left_mono _ FractionalIdeal.coeIdeal_le_one | exact mul_le_mul_right FractionalIdeal.coeIdeal_le_one _ | exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _ | exact mul_le_mul' le_rfl FractionalIdeal.coeIdeal_le_one
      _ = _ := mul_one _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilDoublingFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.GaussThetaAlg

def transposeMulEquiv {A : Type} [CommRing A] {α β γ : Type} [Fintype β] [DecidableEq β] (e : γ ≃ α)
    (G H : Matrix β β A) (hHG : H * G = 1) : Matrix β γ A ≃+ Matrix α β A where
  toFun u := uᵀ.submatrix e.symm id * G
  invFun x := (x * H)ᵀ.submatrix id e
  left_inv u := by
    show ((uᵀ.submatrix e.symm id * G) * H)ᵀ.submatrix id e = u
    rw [Matrix.mul_assoc, mul_eq_one_comm.1 hHG, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    show ((x * H)ᵀ.submatrix id e)ᵀ.submatrix e.symm id * G = x
    have : ((x * H)ᵀ.submatrix id e)ᵀ.submatrix e.symm id = x * H := by
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [this, Matrix.mul_assoc, hHG, Matrix.mul_one]
  map_add' u v := by
    show (u + v)ᵀ.submatrix e.symm id * G = _
    rw [← Matrix.add_mul]
    rfl

theorem mem_algF_of_isFinF {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M)
    (B : Fr X) (f : WO M X → ℂ) (hf : IsFinF ψ θ ε A B f) : f ∈ algF ψ θ ε A B := by
  refine Submodule.subset_span ⟨f, 1, hf, ?_⟩
  show f = pureTensorL _ f 1
  have h1 : (1 : MvPolynomial (FVar D X.rank M.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp [MvPolynomial.coe_basisMonomials]
  simp only [pureTensorL]
  rw [h1, Module.Basis.constr_basis]
  simp [opPow]

theorem isFinF_thO (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ)
    (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig) (hψ : Bs.ψ = ψ)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
    (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : Vs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s')
    (hemb : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
      Ws.θ w = ((B.cart τ).submatrix e e).map conj)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ)
    (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ) (hg : M.IsGauss Bs.ψ Bs.emb g)
    (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    IsFinF ψ θ ε A B (GlobalTheory.TripleRead.thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) := by
  classical
  have hsg : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε <;> ext i j <;> simp [sgn, HSpace.gram]
  have hdet : IsUnit ((if ε then -1 else 1 : D.host.E) • S.gram).det := by
    rw [Matrix.det_smul]
    refine IsUnit.mul (IsUnit.pow _ (by cases ε <;> simp)) ?_
    exact LatVac.gram_det_isUnit S
  have hHG : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹ *
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet]
    simp
  obtain ⟨f, hf, hD⟩ := _root_.GlobalTheory.GaussThetaFinite.isFinF_of_isGauss D ψ θ hθ ε S X A B e.symm Bs hBs hψ Vs Ws r s r' s' hJ
    (by rw [hJW]; rfl) hV hW (fun w => by
      obtain ⟨τ, h1, h2, h3⟩ := hemb w
      exact ⟨τ, h1, h2, by rw [h3]; rfl⟩) M hM
    (transposeMulEquiv e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram))
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹) hHG)
    (fun u => rfl) g φ hg hφ hvac
  convert hf using 1
  funext x
  show GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho ψ (GlobalTheory.TripleRead.ptO (sgn ε S).gram e x)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) = f x
  rw [hD.2, hsg]
  congr 1
  show (((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹)ᵀ.submatrix id e)ᵀ.submatrix e.symm id) *
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = x
  have hx : ((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹)ᵀ.submatrix id e)ᵀ.submatrix e.symm id =
      x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)⁻¹ := by
    ext i j
    simp
  rw [hx, Matrix.mul_assoc, hHG, Matrix.mul_one]

end GlobalTheory.GaussThetaAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoUnitaryGroupIdempotentLocalizationFiniteS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_snd_one_sub_idemS :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) => sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) atTop (𝓝 0) := by
  classical
  have hin : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) w, w ∈ T → evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) = 0 := by
    intro T w hw
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) = 0
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS, if_pos hw, sub_self]
  have hint : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) w,
      evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) ∈ w.adicCompletionIntegers F := by
    intro T w
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) ∈ w.adicCompletionIntegers F
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS]
    split_ifs
    · rw [sub_self]; exact zero_mem _
    · rw [sub_zero]; exact one_mem _
  let A : ∀ w : HeightOneSpectrum (𝓞 F), Set (w.adicCompletion F) := fun w => w.adicCompletionIntegers F
  let o : ∀ w, A w := fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩
  let g : Finset (HeightOneSpectrum (𝓞 F)) → ∀ w, A w := fun T w => ⟨_, hint T w⟩
  have hg : Tendsto g atTop (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({w} : Finset _)] with T hT
    exact Subtype.ext (hin T w (hT (Finset.mem_singleton_self w))).symm
  have h := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_infIdem : At (evI F) (pairA F 1 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * 1, u.2 * 0) = (0, 0)
  rw [h1, zero_mul, mul_zero]

theorem one_sub_idemS_eq (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) :
    1 - GlobalTheory.FinDecomp.idemS F T = pairA F 1 0 + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) := by
  have h := GlobalTheory.FinDecomp.fst_idemS (F := F) T
  refine Prod.ext ?_ ?_
  · change 1 - fstA F (GlobalTheory.FinDecomp.idemS F T) = 1 + 0
    rw [h, sub_zero, add_zero]
  · change sndA F (1 - GlobalTheory.FinDecomp.idemS F T) = 0 + sndA F (1 - GlobalTheory.FinDecomp.idemS F T)
    rw [zero_add]

theorem tendsto_cut :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) => pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T))) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (0 : Ainf F))).prodMk_nhds (tendsto_snd_one_sub_idemS (F := F))
  exact h

theorem tendsto_phi {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE F E)) (hM : pairA F 1 0 • (M - 1) = 0) :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) => GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M) atTop (𝓝 M) := by
  have key : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M =
      M + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) • (1 - M) := by
    intro T
    have h0 : pairA F 1 0 • (1 - M) = 0 := by rw [← neg_sub, smul_neg, hM, neg_zero]
    have h1 : GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M = M + (1 - GlobalTheory.FinDecomp.idemS F T) • (1 - M) := by
      simp only [GlobalTheory.FinDecomp.phi, sub_smul, smul_sub, one_smul]; abel
    rw [h1, congrArg (· • (1 - M)) (one_sub_idemS_eq T), add_smul, h0, zero_add]
  simp_rw [key]
  have h := (tendsto_const_nhds (x := M)).add ((tendsto_cut (F := F)).smul_const (1 - M))
  have e : M + (0 : AF F) • (1 - M) = M := by rw [zero_smul, add_zero]
  rw [e] at h
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

theorem tendsto_loc_idemS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J),
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K - 1) = 0) →
    Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idemS F T) (GlobalTheory.FinDecomp.idemS_mul_self T) K) Filter.atTop (nhds K) := by
  intro F E _ _ _ _ _ σ d J K hK
  have hM : pairA F 1 0 • (mat K - 1) = 0 := hK _ at_infIdem
  have hN : pairA F 1 0 • (mat K⁻¹ - 1) = 0 := by
    have h : mat K⁻¹ - 1 = mat K⁻¹ * (1 - mat K) := by
      rw [Matrix.mul_sub, Matrix.mul_one, GlobalTheory.FinDecomp.mat_inv_mul]
    rw [h, ← Matrix.mul_smul, ← neg_sub (mat K), smul_neg, hM, neg_zero, Matrix.mul_zero]
  rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  change Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K),
        MulOpposite.op (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K⁻¹)))) atTop
      (𝓝 (mat K, MulOpposite.op (mat K⁻¹)))
  exact (tendsto_phi _ hM).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_phi _ hN))

end GlobalTheory.FinDecompLim
end
end

