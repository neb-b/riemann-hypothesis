module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0324

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem mem_mL_of_coprime_smul (I : AutInst) (g c : ℕ) (hc : Nat.Coprime c g) {v : VA I} (hv : v ∈ I.Lf)
    (hcv : (c : I.E ⊗[I.F] Af I.F) • v ∈ mL I g) : v ∈ mL I g := by
  have hb : ((c : ℤ) * Nat.gcdA c g + (g : ℤ) * Nat.gcdB c g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  have hR1 : ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) * (c : I.E ⊗[I.F] Af I.F) +
      ((Nat.gcdB c g : ℤ) : I.E ⊗[I.F] Af I.F) * (g : I.E ⊗[I.F] Af I.F) = 1 := by
    have := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hb
    push_cast at this
    linear_combination this
  have e : v = ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) • ((c : I.E ⊗[I.F] Af I.F) • v) +
      ((Nat.gcdB c g : ℤ) : I.E ⊗[I.F] Af I.F) • ((g : I.E ⊗[I.F] Af I.F) • v) := by
    rw [smul_smul, smul_smul, ← add_smul, hR1, one_smul]
  have hint : ∀ n : ℤ, ∀ w ∈ mL I g, ((n : I.E ⊗[I.F] Af I.F)) • w ∈ mL I g := fun n w hw =>
    (mL I g).smul_mem (⟨(n : I.E ⊗[I.F] Af I.F), intCast_mem _ n⟩ : IntAf I.F I.E) hw
  rw [e]
  exact add_mem (hint _ _ hcv) (hint _ _ (smul_mem_mL I hv))

theorem iota_symm_inv_g {D : D7} (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹)) =
      algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((X.B.g : X.B.I.F)⁻¹) := by
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  have hG : D.host.g 0 * D.host.g 1 = X.B.g := X.g_eq.symm
  have h1 : algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹) * ((X.B.g : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) = 1 := by
    rw [← hG, ← map_natCast (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hG ▸ hg)), map_one]
  have ha : ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹)) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
    rw [← map_natCast ιA.symm, ← map_mul, h1, map_one]
  have hb := inv_g X.B.I X.B.g hg
  set a := ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹))
  set b := algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((X.B.g : X.B.I.F)⁻¹)
  calc a = a * (b * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by rw [hb, mul_one]
    _ = (a * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * b := by ring
    _ = b := by rw [ha, one_mul]

theorem hA_pair_cong (I : AutInst) (g : ℕ) (H : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hH : ∀ z ∈ mL I g, H *ᵥ z ∈ mL I g) (P P' Q Q' : VA I) (hPP : P - P' ∈ mL I g) (hQQ : Q - Q' ∈ mL I g)
    (hP' : P' ∈ I.Lf) (hHQ : H *ᵥ Q ∈ I.Lf) :
    ZMod' I g (hA I P (H *ᵥ Q) - hA I P' (H *ᵥ Q')) := by
  have e : hA I P (H *ᵥ Q) - hA I P' (H *ᵥ Q') = hA I (P - P') (H *ᵥ Q) + hA I P' (H *ᵥ (Q - Q')) := by
    have e1 : hA I P (H *ᵥ Q) = hA I (P - P') (H *ᵥ Q) + hA I P' (H *ᵥ Q) := by
      rw [← hA_add_left, sub_add_cancel]
    rw [e1, Matrix.mulVec_sub, hA_sub_right]; ring
  rw [e]
  refine Z_add I g ?_ ?_
  · rw [hA_symm I (H *ᵥ Q)]
    exact Z_sig I g (mL_Qs I g hHQ hPP)
  · exact mL_Qs I g hP' (hH _ hQQ)

end GlobalTheory.St.G.ColChar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem chi_link (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (Fr : FrQ D wt)
    (hL : FrLink X u wt ιA Fr)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) :
    X.psiEf (divN X.B.I X.B.g (ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) Fr.b Fr.bd y.1.1))) = Fr.chi y.1 := by
  have hpsi : ∀ a, Fr.psi a = X.psiEf (ιA.symm a) := hL.2.2.2
  unfold AdFrame.chi
  rw [hpsi, map_mul, iota_symm_inv_g X ιA]
  rfl

end GlobalTheory.St.G.ColChar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem psiK_eq_chi : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (hK : X.LevelSubgroupCharacter) (Fr : FrQ D wt), FrLink X u wt ιA Fr → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ hk : h ∈ Ku X u hK, ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = Fr.chi y.1 := by
  intro D X u wt ιA hW hI hK Fr hL h y hRep hk
  obtain ⟨hlat, hform, -, -, -, hrep⟩ := _root_.GlobalTheory.St.G.MHat.mhat_coords D X u wt ιA hW hI
  have hpsi : ∀ a, Fr.psi a = X.psiEf (ιA.symm a) := hL.2.2.2
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  obtain ⟨hfe, hfz, -, hbb⟩ := Formalism.L2.SG.Pf.reference_frame_congruences X
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hz0 : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have hbw : ∀ i, X.bw i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).1
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  obtain ⟨κ, hκdef⟩ : ∃ κ : X.B.I.Gf, κ = (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u := ⟨_, rfl⟩
  have hκ : κ ∈ X.K2 := by rw [hκdef]; exact hk
  have hκK : κ ∈ X.B.I.Kset := hκ.1
  have hxK : X.xu u ∈ X.B.I.Kset := X.xu_K u
  have hxκ : X.xu u * κ = (h : X.B.I.Gf) * X.xu u := by rw [hκdef]; group
  have hhK : (h : X.B.I.Gf) ∈ X.B.I.Kset := by
    have e : (h : X.B.I.Gf) = X.xu u * κ * (X.xu u)⁻¹ := by rw [hκdef]; group
    rw [e]; exact K_mul _ (K_mul _ hxK hκK) (K_inv _ hxK)

  have hpres : ∀ x : X.B.I.Gf, x ∈ X.B.I.Kset → ∀ z ∈ mL X.B.I X.B.g, X.B.I.fmat x *ᵥ z ∈ mL X.B.I X.B.g :=
    fun x hx z hz => pres X.B.I hx X.B.g ∅ (mL X.B.I X.B.g) (by simp) (by simp) le_rfl z (mL_Mo X.B.I hz)
  have hpres1 : ∀ z ∈ mL X.B.I X.B.g, (X.B.I.fmat κ - 1) *ᵥ z ∈ mL X.B.I X.B.g :=
    fun z hz => pres1 X.B.I hκK X.B.g ∅ (mL X.B.I X.B.g) (by simp) le_rfl z (mL_Mo X.B.I hz)

  have hxinv : ∀ v : VA X.B.I, X.B.I.fmat (X.xu u) *ᵥ v = v → X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = v := by
    intro v hv
    calc X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = X.B.I.fmat (X.xu u)⁻¹ *ᵥ (X.B.I.fmat (X.xu u) *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]
  have hfixE : ∀ b, X.B.I.fmat κ *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := by
    intro b
    have h1 : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := (X.xu_fix u b).1
    have h2 := Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u h _ (Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix X u b)
    rw [hκdef, fmat_mul, fmat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, hxinv _ h1]
  have hfixZ : X.B.I.fmat κ *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) := by
    have h2 := Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u h _ (Formalism.L2.SG.PoincareInHH.Cut.zR_mem_fix X u)
    have hxx : X.B.I.fmat (X.xu u) *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = incl X.B.I (X.zR u) := by
      rw [Matrix.mulVec_mulVec, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul_inv, Matrix.one_mulVec]
    rw [hκdef, fmat_mul, fmat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxx, h2]

  have key : ∀ v w : VA X.B.I, v ∈ X.B.I.Lf → X.B.I.fmat κ *ᵥ w = w →
      InAt X.B.I X.B.g X.B.g (v - w) → (X.B.I.fmat κ - 1) *ᵥ v ∈ mL X.B.I X.B.g := by
    intro v w hv hw hvw
    obtain ⟨c, hc, hcv⟩ := hvw
    refine mem_mL_of_coprime_smul X.B.I X.B.g c hc (K_sub_mv X.B.I hκK hv) ?_
    have hw0 : (X.B.I.fmat κ - 1) *ᵥ w = 0 := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hw, sub_self]
    have e : (X.B.I.fmat κ - 1) *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (v - w)) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat κ - 1) *ᵥ v) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hw0, sub_zero]
    rw [← e]; exact hpres1 _ hcv
  have hnxt : ∀ a, (X.B.I.fmat κ - 1) *ᵥ nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g := by
    intro a
    unfold nxt
    split_ifs with ha
    · exact key _ _ (he0 _) (hfixE _) (X.basisApprox _).1
    · refine key _ _ hz0 hfixZ ?_
      obtain ⟨c, hc, hcv⟩ := X.xu_z u
      refine ⟨c, hc, ?_⟩
      have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) =
          -((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0)) := by
        rw [← smul_neg, neg_sub]
      rw [e]; exact neg_mem hcv

  have hterm : ∀ (i : Fin D.R.k) (hi : i.1 + 1 < D.R.k),
      ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw ⟨i.1 + 1, hi⟩) -
        ιA.symm (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
          (Fr.bd i) (y.1.1 *ᵥ Fr.b ⟨i.1 + 1, hi⟩))) := by
    intro i hi
    generalize hj : (⟨i.1 + 1, hi⟩ : Fin D.R.k) = j
    have hT : ιA.symm (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
          (Fr.bd i) (y.1.1 *ᵥ Fr.b j)) =
        hA X.B.I (embA X wt ιA (Fr.bd i)) (X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA (Fr.b j)) := by
      rw [← hform, RingEquiv.symm_apply_apply, hrep h y hRep]
    have hT2 : hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw j) =
        hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)
          (X.B.I.fmat (h : X.B.I.Gf) *ᵥ (X.B.I.fmat (X.xu u) *ᵥ X.bw j)) := by
      rw [← Formalism.L2.SG.PoincareInHH.Cut.hA_fmat X (X.xu u) (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw j),
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← fmat_mul, ← fmat_mul, hxκ]
    rw [hT, hT2]
    refine hA_pair_cong X.B.I X.B.g _ (hpres _ hhK) _ _ _ _ ?_ ?_ ((hlat (Fr.bd i)).1 (Fr.bd_mem i))
      (K_mv X.B.I hhK (K_mv X.B.I hxK (hbw j)))
    · have := neg_mem (hL.2.2.1 i); rwa [neg_sub] at this
    · have := neg_mem (hL.2.1 j); rwa [neg_sub] at this

  have hZ : ZMod' X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ -
      ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
        Fr.b Fr.bd y.1.1) - 0) := by
    have e : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ -
        ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
          Fr.b Fr.bd y.1.1) - 0 =
        (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a)) +
        ∑ i : Fin D.R.k, ((if hi : i.1 + 1 < D.R.k then
            hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw ⟨i.1 + 1, hi⟩) else 0) -
          ιA.symm (if hi : i.1 + 1 < D.R.k then
            hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
              (Fr.bd i) (y.1.1 *ᵥ Fr.b ⟨i.1 + 1, hi⟩) else 0)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Afun, supSum, map_sum, Finset.sum_sub_distrib]; ring
    rw [e]
    refine Z_add X.B.I X.B.g (Z_sum X.B.I X.B.g _ _ fun a _ => ?_) (Z_sum X.B.I X.B.g _ _ fun i _ => ?_)
    · exact congruence_fixed_term X.B.I X.B.g _ _ (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 hfe hfz a)
        (mL_Qs X.B.I X.B.g (hf0 a) (hnxt a))
    · by_cases hi : i.1 + 1 < D.R.k
      · simp only [dif_pos hi]; exact hterm i hi
      · simp only [dif_neg hi, map_zero, sub_self]; exact Z_zero X.B.I X.B.g
  have h0 : X.psiEf (divN X.B.I X.B.g 0) = 1 := by
    rw [divN, mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  calc ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ)
      = X.psiEf (divN X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ)) := by rw [hκdef]; rfl
    _ = X.psiEf (divN X.B.I X.B.g (ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D)
          (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) Fr.b Fr.bd y.1.1))) := by
      have hE := psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hZ
      rw [h0, mul_one] at hE
      exact hE
    _ = Fr.chi y.1 := by
      exact chi_link D X u wt ιA Fr hL y

end GlobalTheory.St.G.ColChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstant
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapConstant

set_option maxHeartbeats 2000000 in
theorem gap_thresholds (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
              (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
      GlobalTheory.CellAmp.GapCell k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have h3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  have hNdef : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hs, h3]
  set P : ℝ := (r : ℝ) + 1 with hPdef
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hNd
  have hP1 : 1 ≤ P := by linarith
  have hN2 : 2 * P ≤ N := by rw [hNdef]; linarith
  have hN1 : 1 ≤ N := by linarith
  have h2P : 0 < 2 * P := by linarith
  have hsq : 0 < Real.sqrt (2 * P) := Real.sqrt_pos.mpr h2P
  have hsq1 : 1 ≤ Real.sqrt (2 * P) := Real.one_le_sqrt.mpr (by linarith)
  have hrp : (2 * P) ^ ((9 : ℝ) / 2) = (2 * P) ^ 4 * Real.sqrt (2 * P) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add h2P]
    norm_num
  rw [hrp]
  set X : ℝ := 3 * P * N ^ 2 + N ^ 3 with hX
  have ha : Formalism.FourierDecayAlt.ThreeDimData.aOf r (1000 * ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X) = 2000 * P ^ 4 * X := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [← hPdef]
    field_simp
    ring

  have hAS : Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * P * N ^ 2 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN
    have e : ((2 * r + k : ℕ) : ℝ) = 2 * (r : ℝ) + k := by push_cast; ring
    rw [e]
    have hd0 : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 := by nlinarith
    have hd : (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 ≤ 2 * P * N := by
      rw [hNdef]; nlinarith
    have hm : 2 * (r : ℝ) + k ≤ N := by rw [hNdef]; linarith
    calc (2 * (r : ℝ) + k) * ((r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2)
        ≤ N * (2 * P * N) := mul_le_mul hm hd hd0 (by linarith)
      _ = 2 * P * N ^ 2 := by ring
  have hAS0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN
    apply mul_nonneg (Nat.cast_nonneg _); nlinarith
  have hAG : Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * N * P := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have : (k : ℝ) + r ≤ N := by rw [hNdef]; linarith
    nlinarith
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hM : Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ 2 * P ^ 2 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; rw [hPdef]; nlinarith
  have hM0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r := by unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity

  have hP35 : P ^ 3 ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP15 : P ≤ P ^ 5 := by simpa using pow_le_pow_right₀ hP1 (show 1 ≤ 5 by norm_num)
  have hP25 : P ^ 2 ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP5 : 1 ≤ P ^ 5 := one_le_pow₀ hP1
  have hN12 : N ≤ N ^ 2 := by nlinarith
  have hN21 : 1 ≤ N ^ 2 := by nlinarith
  have hN2_0 : 0 ≤ N ^ 2 := by positivity
  have hP50 : 0 ≤ P ^ 5 := by positivity
  have hbig : 6000 * P ^ 5 * N ^ 2 ≤ 2000 * P ^ 4 * X := by
    rw [hX]
    have : 0 ≤ P ^ 4 * N ^ 3 := by positivity
    nlinarith
  have m1 : P ^ 3 * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP35 hN2_0
  have m2 : P ^ 3 * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP35 hN12 (by positivity) hP50
  have m3 : P * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP15 hN12 (by positivity) hP50
  have m4 : (1 : ℝ) ≤ P ^ 5 * N ^ 2 := one_le_mul_of_one_le_of_one_le hP5 hN21
  have m5 : P * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP15 hN2_0
  have m6 : P ^ 2 * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP25 hN2_0
  have hprod : Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul hM (show Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 2 * P * N ^ 2 + 4 * N * P by linarith)
      (add_nonneg hAS0 hAG0) (by nlinarith)
  have hprod2 : ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsqN : 0 ≤ (2 * P) ^ 4 * Real.sqrt (2 * P) - 1 := by
    have : 1 ≤ (2 * P) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  refine ⟨⟨hk, ?_, ?_, ?_⟩, ?_⟩
  · have hX3 : N ^ 3 ≤ X := by rw [hX]; nlinarith
    have hN3 : 0 ≤ N ^ 3 := by positivity
    have : X ≤ ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X := by nlinarith
    nlinarith
  · rw [ha]
    have e : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) =
      2 * (Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)) := by ring
    rw [e]
    have : (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) = 4 * (P ^ 3 * N ^ 2) + 8 * (P ^ 3 * N) := by ring
    nlinarith
  · rw [ha]
    have e : (9 : ℝ) * ((r : ℝ) + 1) * N ^ 2 = 9 * (P * N ^ 2) := by rw [← hPdef]; ring
    rw [e]
    nlinarith
  · unfold GlobalTheory.CellAmp.GapCell
    rw [ha]
    have e : 10 * ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) =
      10 * (((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)) := by ring
    rw [e]
    have : P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) = 2 * (P ^ 3 * N ^ 2) + 4 * (P ^ 3 * N) := by ring
    nlinarith

theorem gap_constant_exists : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  refine ⟨1000, fun D ε lam hg => ⟨_, hg, ?_⟩⟩
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact gap_thresholds D.R.k D.R.rS hk

end GlobalTheory.GapConstant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepresentativeBoundedEvaluation
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.EvalBound

theorem exists_contRep_bound_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  intro B d hB hL hn hg
  obtain ⟨F, hF, hc, hw⟩ := GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf B d hB hL 0 _ (tens_mem_VP B d hB)
  have he := GlobalTheory.StepAverage.isClosedEmbedding_entries_inf B.I
  have hσ : IsURep B.σs := (GlobalTheory.Dec.tensorRep B d hB).1
  obtain ⟨-, -, hN, hC, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  let a : B.I.Ginf → ℂ := fun g => F fun v i j => uMat (g v) i j
  have hs : SmoothInf B.I a := fun x => ⟨F, hF.contDiffAt, Filter.Eventually.of_forall fun _ => rfl⟩
  have hac : HasCompactSupport a := hc.comp_isClosedEmbedding he
  have hai : Integrable a (muInf B.I) := by
    unfold muInf
    exact (hF.continuous.comp he.continuous).integrable_of_hasCompactSupport hac
  obtain ⟨T, hT1, hT2⟩ := GlobalTheory.absOpInt B.I.Ginf (muInf B.I) _ (realRep B) (fun g x => hN _ x)
    (fun x => (hC x).comp (continuous_id.prodMk continuous_const)) a hai
  obtain ⟨C, hC⟩ := GlobalTheory.SmoothGrowth.convolutionSmoothL2 B B.g hn hg a hs hac
  refine ⟨C, fun A hA hk => ?_⟩
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := hC _ hk T ⟨hai, hT2⟩
  have hfix : T (A (B.tens B.w)) = A (B.tens B.w) := by
    rw [hT1]
    conv_rhs => rw [hw]
    rw [← A.integral_comp_comm (GlobalTheory.StepAverage.integrable_inf B hσ _ hF.continuous hc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have h := congrArg (fun S => S (B.tens B.w)) (hA g)
    simp only [map_smul]
    exact congrArg (a g • ·) h.symm
  rw [hfix] at hf4
  exact ⟨f, ⟨hf2, hf1.1, hf4⟩, hf3⟩

end GlobalTheory.EvalBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainMeasureEq
section
open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst)

namespace GlobalTheory.AdelicVol

theorem exists_fundamentalDomain_measure_eq (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund) :
    ∃ (μ : Measure (HA (AF I.F) I.cm.sig I.J)) (S : Set (HA (AF I.F) I.cm.sig I.J)), μ.IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF I.F) I.cm.sig I.J) S μ ∧ μ S = I.muA μf fund := by
  obtain ⟨-, -, T, hT, -, -⟩ := GlobalTheory.AdelicModels.exists_adelic_equiv I
  obtain ⟨Γ, hΓ, -, -, hdom⟩ := GlobalTheory.RatDiscrete.rational_points I
  have hF : IsFundamentalDomain Γ fund (I.muA μf) := hdom μf fund hfund
  haveI : BorelSpace (HA (AF I.F) I.cm.sig I.J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : IsTopologicalGroup (HA (AF I.F) I.cm.sig I.J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : SecondCountableTopology I.Gf := (GlobalTheory.CongTop.adelic_topology I).2.2.1
  haveI : BorelSpace I.GA := inferInstance
  haveI hG1 : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => inferInstance
  haveI hG2 : ∀ v, SigmaFinite (Formalism.REAL.muG (I.ε v)) := fun v => inferInstance
  haveI hP : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := inferInstance
  haveI hPs : SigmaFinite (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) := inferInstance
  haveI : (I.muA μf).IsHaarMeasure := by unfold AutInst.muA; infer_instance
  have hTm : Measurable T := T.continuous.measurable
  have hTsm : Measurable T.symm := T.symm.continuous.measurable
  let μ : Measure (HA (AF I.F) I.cm.sig I.J) := Measure.map T.symm (I.muA μf)
  haveI hμ : μ.IsHaarMeasure :=
    T.symm.toMulEquiv.isHaarMeasure_map (I.muA μf) T.symm.continuous T.continuous
  let e : Γ → HFinIn (AF I.F) I.cm.sig I.J := fun g =>
    ⟨T.symm g, (hT (T.symm g)).2 (by
      rw [ContinuousMulEquiv.apply_symm_apply, ← hΓ]
      exact g.2)⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply T.symm.injective
      exact congrArg Subtype.val hab
    · intro h
      have hm : T h.1 ∈ I.GFset := (hT h.1).1 h.2
      rw [← hΓ] at hm
      refine ⟨⟨T h.1, hm⟩, Subtype.ext ?_⟩
      exact T.symm_apply_apply _
  have hsc : ∀ g : Γ, Function.Semiconj T (fun x : HA (AF I.F) I.cm.sig I.J => e g • x) (fun y : I.GA => (g : I.GA) * y) := by
    intro g x
    show T ((T.symm (g : I.GA)) * x) = (g : I.GA) * T x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hmp : MeasurePreserving T μ (I.muA μf) := by
    refine ⟨hTm, ?_⟩
    rw [Measure.map_map hTm hTsm]
    have : (T ∘ T.symm) = id := funext fun y => T.apply_symm_apply y
    rw [this, Measure.map_id]
  refine ⟨μ, T ⁻¹' fund, hμ, hF.preimage_of_equiv hmp.quasiMeasurePreserving he hsc, ?_⟩
  rw [Measure.map_apply hTsm (hTm hfund.1), ← Set.preimage_comp]
  have : (T ∘ T.symm) = id := funext fun y => T.apply_symm_apply y
  rw [this, Set.preimage_id]

theorem vol_finite_pos : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund → I.muA μf fund < ⊤ ∧ I.muA μf fund ≠ 0 ∧ 0 < I.vol μf fund := by
  intro I μf _ _ fund hfund
  obtain ⟨hcm, hJ, -⟩ := GlobalTheory.AdelicModels.exists_adelic_equiv I
  obtain ⟨μ, S, hμ, hS, hμS⟩ := exists_fundamentalDomain_measure_eq I μf fund hfund
  have hfin : μ S < ⊤ := GlobalTheory.Mem.VolFin.finVol I.F I.E I.cm.sig hcm I.n I.J hJ μ hμ S hS
  have hne : μ S ≠ 0 :=
    ((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary I.F I.E I.cm.sig I.n I.J μ hμ).2 S S hS hS).2
  rw [← hμS]
  refine ⟨hfin, hne, ?_⟩
  show 0 < ((I.muA μf) fund).toReal
  rw [← hμS]
  exact ENNReal.toReal_pos hne hfin.ne

end GlobalTheory.AdelicVol
end

