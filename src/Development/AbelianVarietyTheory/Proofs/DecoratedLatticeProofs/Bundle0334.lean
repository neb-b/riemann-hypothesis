module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapLawsFactorFourierJacobiSource
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapTranslationLawsJacobiToBesselFree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapFactorIsLocalModel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierHyperbolicTermsNearRefere
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW.EfNear

variable {D : D7} (X : HidaSetting D)

theorem nat_smul_mL (k : ℕ) {x : VA X.B.I} (hx : x ∈ mL X.B.I X.B.g) :
    (k : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx k

theorem dvd_smul_mL {d M : ℕ} (hd : d ∣ M) {x : VA X.B.I}
    (hx : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g) :
    (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (k : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), mul_smul]
  exact nat_smul_mL X k hx

theorem term_near {v0 w0 v w y : VA X.B.I} (hw0 : w0 ∈ X.B.I.Lf) (hy : y ∈ X.B.I.Lf) {c1 c2 c3 : ℕ}
    (h1 : (c1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (v0 - v) ∈ mL X.B.I X.B.g)
    (h2 : (c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (w0 - w) ∈ mL X.B.I X.B.g)
    (h3 : (c3 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v ∈ X.B.I.Lf) :
    ((c1 * c2 * c3 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I w y • v - hA X.B.I w0 y • v0) ∈
      mL X.B.I X.B.g := by
  have e : hA X.B.I w y • v - hA X.B.I w0 y • v0 =
      -(hA X.B.I w0 y • (v0 - v)) - hA X.B.I (w0 - w) y • v := by
    rw [GlobalTheory.St.G.FrameClose.hA_sub_left, smul_sub, sub_smul]; abel
  rw [e, smul_sub]
  refine sub_mem ?_ ?_
  · refine dvd_smul_mL X (dvd_mul_of_dvd_left (dvd_mul_right c1 c2) c3) ?_
    rw [smul_neg, smul_comm]
    refine neg_mem ?_
    have := (mL X.B.I X.B.g).smul_mem (⟨_, GlobalTheory.St.G.FrameClose.hA_int hw0 hy⟩ : IntAf X.B.I.F X.B.I.E) h1
    rwa [Subring.smul_def] at this
  · refine dvd_smul_mL X (d := c2 * c3) ⟨c1, by ring⟩ ?_
    have e2 : ((c2 * c3 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (w0 - w) y • v) =
        hA X.B.I ((c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (w0 - w)) y •
          ((c3 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) := by
      rw [GlobalTheory.St.G.FrameClose.hA_nat_left, smul_smul, smul_smul, Nat.cast_mul]
      congr 1; ring
    rw [e2]
    exact Formalism.L2.SG.PoincareInHH.Cut.GU.smul_mL X (GlobalTheory.St.G.FrameClose.zmod_of_mL h2 hy) h3

end GlobalTheory.ScalW.EfNear

namespace GlobalTheory.ScalW


open GlobalTheory.ScalW.EfNear in
theorem ef_near_ref : ∀ (D : D7) (X : HidaSetting D), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, ∀ a, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a - hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g ∧ (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
  intro D X
  choose c1 hc1 h1 using fun a => (X.basisApprox a).1
  choose c2 hc2 h2 using fun a => (X.basisApprox a).2
  choose c3 hc3 h3 using fun a => GlobalTheory.St.G.FrameClose.den_of_inAt (X.vectorsInLattice.1 a).1 (X.basisApprox a).1
  choose c4 hc4 h4 using fun a => GlobalTheory.St.G.FrameClose.den_of_inAt (X.vectorsInLattice.1 a).2 (X.basisApprox a).2
  refine ⟨∏ a, c1 a * c2 a * c3 a * c4 a,
    Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left (hc1 a) (hc2 a)) (hc3 a)) (hc4 a), ?_⟩
  intro y hy a
  have hdvd : c1 a * c2 a * c3 a * c4 a ∣ ∏ b, c1 b * c2 b * c3 b * c4 b :=
    Finset.dvd_prod_of_mem (fun b => c1 b * c2 b * c3 b * c4 b) (Finset.mem_univ a)
  constructor
  · refine dvd_smul_mL X (d := c1 a * c2 a * c3 a) (dvd_trans ⟨c4 a, rfl⟩ hdvd) ?_
    exact term_near X (v0 := X.e0 a) (w0 := X.f0 a) (v := eV X a) (w := fV X a) (X.vectorsInLattice.1 a).2 hy (h1 a) (h2 a) (h3 a)
  · refine dvd_smul_mL X (d := c2 a * c1 a * c4 a) (dvd_trans ⟨c3 a, by ring⟩ hdvd) ?_
    exact term_near X (v0 := X.f0 a) (w0 := X.e0 a) (v := fV X a) (w := eV X a) (X.vectorsInLattice.1 a).1 hy (h2 a) (h1 a) (h4 a)

end GlobalTheory.ScalW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierLevelCharacterSumCongr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NPartConj

variable (I : Formalism.MainNotions.S.AutInst)

theorem nsmul_mL' {g k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem nsmul_Lf' {k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ I.Lf) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem mL_le_Lf' (g : ℕ) : Formalism.L2.SG.HidaSetting.mL I g ≤ I.Lf :=
  Submodule.span_le.2 (by rintro _ ⟨y, hy, rfl⟩; exact nsmul_Lf' I hy)

theorem K_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : I.fmat x *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  have h : Formalism.L2.SG.HidaSetting.mL I g ≤
      (Formalism.L2.SG.HidaSetting.mL I g).comap (Formalism.L2.SG.Pf.unitaryCongruence.mvO I (I.fmat x)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      show I.fmat x *ᵥ ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • y) ∈ Formalism.L2.SG.HidaSetting.mL I g
      rw [Matrix.mulVec_smul]
      exact Formalism.L2.SG.Pf.unitaryCongruence.smul_mem_mL I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hy))
  exact h hv

theorem K_sub_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : (I.fmat x - 1) *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact sub_mem (K_mL' I hx hv) hv

theorem hcn_of {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {n N N0 : Formalism.L2.SG.HidaSetting.VA I}
    (hN : I.fmat x *ᵥ N0 = N) {c : ℕ}
    (h : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0) ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g := by
  have e : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N =
      I.fmat x *ᵥ ((c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hN, smul_sub]
  rw [e]; exact K_mL' I hx h

theorem conj_sub (x m : I.Gf) (n : Formalism.L2.SG.HidaSetting.VA I) :
    (I.fmat (x⁻¹ * m * x) - 1) *ᵥ n = I.fmat x⁻¹ *ᵥ ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
  rw [Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul, Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.one_mulVec]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.sub_mulVec,
    Matrix.one_mulVec]

theorem term_cong {g : ℕ} {x m : I.Gf} (hx : x ∈ I.Kset) (hm : m ∈ I.Kset)
    {f F n N : Formalism.L2.SG.HidaSetting.VA I} (hf : f ∈ I.Lf) (hn : n ∈ I.Lf) (hFx : I.fmat x *ᵥ F = F) {c : ℕ}
    (hcf : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (f - F) ∈ Formalism.L2.SG.HidaSetting.mL I g)
    (hcn : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g) :
    Formalism.L2.SG.HidaSetting.ZMod' I g (((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N))) := by
  set C : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) with hC
  have e1 : Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) =
      Formalism.L2.SG.HidaSetting.hA I (I.fmat x *ᵥ f) ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
    rw [conj_sub, PIW.NormChiNBi.hA_left_inv, inv_inv]
  have hsig : Formalism.L2.SG.HidaSetting.sigA I C = C := by rw [hC, map_natCast]
  have esc : ∀ u v : Formalism.L2.SG.HidaSetting.VA I, Formalism.L2.SG.HidaSetting.hA I (C • u) ((I.fmat m - 1) *ᵥ (C • v)) =
      C * C * Formalism.L2.SG.HidaSetting.hA I u ((I.fmat m - 1) *ᵥ v) := by
    intro u v
    rw [Matrix.mulVec_smul, PIW.NormChiNBi.hA_smul_left, PIW.NormChiNBi.hA_smul_right, hsig]; ring
  have hδf : C • (I.fmat x *ᵥ f) - C • F ∈ Formalism.L2.SG.HidaSetting.mL I g := by
    have e : C • (I.fmat x *ᵥ f) - C • F = I.fmat x *ᵥ (C • (f - F)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hFx, smul_sub]
    rw [e]; exact K_mL' I hx hcf
  have hA'L : C • F ∈ I.Lf := by
    have e : C • F = C • f - C • (f - F) := by rw [smul_sub]; abel
    rw [e]; exact sub_mem (nsmul_Lf' I hf) (mL_le_Lf' I g hcf)
  have hBL : (I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n)) ∈ I.Lf :=
    Formalism.L2.SG.Pf.unitaryCongruence.K_sub_mv I hm (nsmul_Lf' I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hn))
  have key : ((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N)) =
      Formalism.L2.SG.HidaSetting.hA I (C • (I.fmat x *ᵥ f) - C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n))) +
      Formalism.L2.SG.HidaSetting.hA I (C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n) - C • N)) := by
    rw [PIW.NormChiNBi.hA_sub_left, Matrix.mulVec_sub, PIW.NormChiNBi.hA_sub_right, e1, esc, esc, esc, Nat.cast_mul]
    ring
  rw [key]
  obtain ⟨s, hs, hs'⟩ := PIW.NormChiNBi.hA_mL_left I g hδf hBL
  obtain ⟨t, ht, ht'⟩ := PIW.NormChiNBi.hA_mL_right I g (K_sub_mL' I hm hcn) hA'L
  exact ⟨s + t, add_mem hs ht, by rw [hs', ht', mul_add]⟩

end GlobalTheory.NPartConj

namespace GlobalTheory.NPartConj

theorem term_each (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf)
    (hm : m ∈ X.B.I.Kset) (a : Fin D.R.rS) :
    ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  obtain ⟨c1, hc1, h1⟩ := (X.basisApprox a).2
  have hFx : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
  have hx := X.xu_K u
  obtain ⟨c2, hc2, N0, hN0, h2⟩ : ∃ c2 : ℕ, Nat.Coprime c2 X.B.g ∧ ∃ N0 : VA X.B.I,
      X.B.I.fmat (X.xu u) *ᵥ N0 = incl X.B.I (nxt X.eR (X.zR u) a) ∧
      ((c2 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0)) ∈ mL X.B.I X.B.g := by
    unfold nxt
    split_ifs with h
    · obtain ⟨c2, hc2, h2⟩ := (X.basisApprox ⟨a.1 + 1, h⟩).1
      exact ⟨c2, hc2, _, (X.xu_fix u _).1, h2⟩
    · obtain ⟨c2, hc2, h2⟩ := X.xu_z u
      refine ⟨c2, hc2, X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u), ?_, ?_⟩
      · rw [Matrix.mulVec_mulVec, PIW.NormChiNBi.fmat_mul_inv', Matrix.one_mulVec]
      · have h3 := neg_mem h2
        rwa [← smul_neg, neg_sub] at h3
  have hcop : Nat.Coprime (c1 * c2) X.B.g := Nat.Coprime.mul_left hc1 hc2
  refine ⟨(c1 * c2) * (c1 * c2), Nat.Coprime.mul_left hcop hcop, ?_⟩
  have hcf : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact nsmul_mL' X.B.I h1
  have hcN : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_smul]; exact nsmul_mL' X.B.I h2
  exact term_cong X.B.I hx hm (X.vectorsInLattice.1 a).2 (PIW.NormChiNBi.nxt_mem X a) hFx hcf
    (hcn_of X.B.I hx hN0 hcN)

theorem nsum_cong : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf), m ∈ X.B.I.Kset → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ a, (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) - hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  intro D X u m hm
  choose c hc h using term_each D X u m hm
  refine ⟨∏ a, c a, Nat.Coprime.prod_left fun a _ => hc a, ?_⟩
  rw [Finset.mul_sum]
  refine Formalism.L2.SG.Pf.unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ a)
  rw [hk]
  have e : ∀ T : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F,
      ((c a * k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T =
        (k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((c a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T) := by
    intro T; push_cast; ring
  rw [e]
  exact Formalism.L2.SG.Pf.unitaryCongruence.Z_smul X.B.I X.B.g (natCast_mem _ k) (h a)

end GlobalTheory.NPartConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierNegativeVectorTermNear
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ScalW

theorem znear_term : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) - hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := by
  intro D X u
  obtain ⟨c, hc, hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' := X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u with hz'
  have hm' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  refine ⟨c * c, Nat.Coprime.mul_left hc hc, ?_⟩
  intro y hy
  have hcz : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' ∈ X.B.I.Lf := by
    have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (GlobalTheory.St.G.FrameClose.nat_smul_mem c hz0) (GlobalTheory.St.G.FrameClose.mL_le _ hm')
  obtain ⟨t1, ht1, e1⟩ := GlobalTheory.St.G.FrameClose.zmod_of_mL hm' hy
  rw [GlobalTheory.St.G.FrameClose.hA_nat_left, GlobalTheory.St.G.FrameClose.hA_sub_left] at e1
  have hs : hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E := GlobalTheory.St.G.FrameClose.hA_int hz0 hy
  have hs' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E :=
    mul_mem (natCast_mem _ c) hs
  have e : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I z' y • z' - hA X.B.I X.z0 y • X.z0) =
      t1 • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z')) +
      ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0)) := by
    simp only [smul_smul, smul_sub, Nat.cast_mul]
    have e2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t1 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y := by
      linear_combination e1
    have e3 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        t1 * ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) +
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      linear_combination (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e2
    rw [e3, add_smul, show (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) by ring]
    abel
  rw [e]
  refine add_mem ?_ ?_
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, ht1⟩ : IntAf X.B.I.F X.B.I.E) (Submodule.subset_span ⟨_, hcz, rfl⟩)
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, hs'⟩ : IntAf X.B.I.F X.B.I.E) hm'

end GlobalTheory.ScalW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TorusCong

open Formalism.L2.SG.Pf.unitaryCongruence GlobalTheory.St.G.FrameClose

theorem one_sub_T_zmod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ZMod' X.B.I X.B.g ((M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  intro D X u
  obtain ⟨c', hc', hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' : VA X.B.I := X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) with hz'
  have hm' : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  have hzz : hA X.B.I z' z' = -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [hz', Formalism.L2.SG.PoincareInHH.Cut.hA_fmat, HidaSetting.zR, Formalism.L2.SG.PoincareInHH.Cut.hA_crd, X.zu_norm,
      map_neg, map_natCast, map_neg, map_natCast]
  set m : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) with hmdef
  set w0 : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 with hw0def
  have hw0 : w0 ∈ X.B.I.Lf := nat_smul_mem c' hz0
  have hw : m + w0 ∈ X.B.I.Lf := add_mem (mL_le X.B.g hm') hw0
  have h1 : ZMod' X.B.I X.B.g (hA X.B.I m (m + w0)) := zmod_of_mL hm' hw
  have h2 : ZMod' X.B.I X.B.g (hA X.B.I w0 m) := by
    rw [hA_symm]; exact Z_sig _ _ (zmod_of_mL hm' hw0)
  have hsplit : hA X.B.I (m + w0) (m + w0) - hA X.B.I w0 w0 = hA X.B.I m (m + w0) + hA X.B.I w0 m := by
    rw [hA_add_left, hA_add_right, hA_add_right]; ring
  have hmw : m + w0 = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' := by
    rw [hmdef, hw0def, ← smul_add, sub_add_cancel]
  have hsq : ∀ x : VA X.B.I, hA X.B.I ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x) ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x)
      = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * hA X.B.I x x := by
    intro x; rw [hA_nat_left, hA_smul_right]; ring
  have hA1 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0)) := by
    have e : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) =
        hA X.B.I m (m + w0) + hA X.B.I w0 m := by
      rw [← hsplit, hmw, hw0def, hsq, hsq]; ring
    rw [e]; exact Z_add _ _ h1 h2
  have hA2 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1)) := by
    have := Z_smul X.B.I X.B.g (natCast_mem (IntAf X.B.I.F X.B.I.E) (c' ^ 2)) X.formsAtZero.1
    simpa [Nat.cast_pow] using this
  refine ⟨c' ^ 2, Nat.Coprime.pow_left 2 hc', ?_⟩
  have e : ((c' ^ 2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) =
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) +
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1) := by
    rw [hzz, Nat.cast_pow]; ring
  rw [e]; exact Z_add _ _ hA1 hA2

end GlobalTheory.TorusCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleStep
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open GlobalTheory.LocMod Filter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.DblInhab

section Gram

variable (E : Type) [Field E] [CharZero E] [StarRing E]



end Gram


section Place

open GlobalTheory.FinPl (SplitPt Pl idAt intAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := GlobalTheory.LocChar.ι_one (ofSplit q)

theorem sec_mul_pr (a : k) (o : AE D) : q.sec (a * q.pr o) = q.sec a * o := by
  have h := q.sec_pr (q.sec a * o)
  rw [map_mul, q.pr_sec] at h
  rw [h, ← mul_assoc]
  exact congrArg (· * o) (GlobalTheory.LocChar.e_mul_ι (ofSplit q) a)

theorem sec_mem_idAt (a : k) : q.sec a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  obtain ⟨hee, hec, -⟩ := q.split
  have he : q.e ∈ idAt D (· = q.v) := by
    refine ((_root_.GlobalTheory.FinPl.placeIdem_acts D q.v ε hε).1 q.e).2 ?_
    rw [← hsum, add_mul, hee, mul_comm (cA D q.e), hec, add_zero]
  have h : q.e * q.sec a = q.sec a := GlobalTheory.LocChar.e_mul_ι (ofSplit q) a
  rw [← h]
  exact Ideal.mul_mem_right _ _ he

theorem sec_mem_intAt (a : k) : q.sec a ∈ intAt D (· = q.v) ↔ valuation k a ≤ 1 :=
  (and_iff_right (sec_mem_idAt q a)).trans (q.int_iff a).symm

theorem pr_le_one {o : AE D} (ho : o ∈ intAt D (· = q.v)) : valuation k (q.pr o) ≤ 1 := by
  refine (q.int_iff _).2 ?_
  rw [q.sec_pr, ← sec_one, map_mul]
  exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ((q.int_iff 1).1 (one_mem _)) ho.2

end Place


end GlobalTheory.LocMod.DblInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.LocMod

theorem flatFB_holds : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatFB D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm
  have hstd : IsStdChar D ψ (-1) := st.weil.std
  obtain ⟨hcont, hne⟩ := (_root_.GlobalTheory.LocChar.weil_char_split D k p ψ hstd).2.1 ψk hχ
  have hc : c = 2 * σ + 1 := hBF.1
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ) :=
    { toFun := fun Φ => flatFB st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add (f := _)]
        exact (_root_.GlobalTheory.FlatAdd.flatFB_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (_root_.GlobalTheory.FlatAdd.flatFB_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ)).2 a }
  obtain ⟨L₀, hL₀⟩ := _root_.GlobalTheory.PartRed.flRow_factor k ψk ν hcont hne hν n n' c σ (WO J.W₀ B.V₀ → ℂ) L hc
    (_root_.GlobalTheory.FlatColLawFB.flatFB_mulcol D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (_root_.GlobalTheory.LocMod.flatFB_mulrow D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (_root_.GlobalTheory.LocMod.flatFB_trans_free D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (_root_.GlobalTheory.FlatFBUnip.unip_law D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
  exact ⟨L₀, _root_.GlobalTheory.LocFlatFB.factor_isModel D hFLs hOm k p ν hν ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm L₀ hL₀, hL₀⟩

end GlobalTheory.LocMod

end
end

