module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0297
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecond
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormaliserGLintEqScalarMulGLint
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.NormaliserGLint

open Matrix

theorem exists_unif (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletion F, Formalism.UG.IsUnifV F v ϖ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F), ?_⟩
  unfold Formalism.UG.IsUnifV
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  rfl

theorem mul_entries_mem {L : Type} [Field L] (O : Subring L) {n : ℕ} {A B : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) : ∀ i j, (A * B) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => O.mul_mem (hA i k) (hB k j)

theorem mulVec_entries_mem {L : Type} [Field L] (O : Subring L) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    {z : Fin n → L} (hA : ∀ i j, A i j ∈ O) (hz : ∀ i, z i ∈ O) : ∀ i, (A *ᵥ z) i ∈ O := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => O.mul_mem (hA i k) (hz k)

theorem le_of_zpow_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) {p q : ℤ} {w : v.adicCompletion F}
    (hw : w ∈ Formalism.UG.Ov F v) (h : ϖ ^ q = ϖ ^ p * w) : p ≤ q := by
  have hv := congrArg Valued.v h
  rw [map_mul, map_zpow₀, map_zpow₀, hϖ] at hv
  have hw' : Valued.v w ≤ 1 := hw
  have key : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ q ≤
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ p := by
    rw [hv]; exact mul_le_of_le_one_right' hw'
  rw [← WithZero.coe_zpow, ← WithZero.coe_zpow, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zsmul,
    Multiplicative.ofAdd_le] at key
  simp at key
  omega

end GlobalTheory.NormaliserGLint

namespace GlobalTheory.NormaliserGLint

open Matrix

theorem conj_eq_glint_mul_mul :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (N : GL (Fin n) (v.adicCompletion F)),
    (∀ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ z : Fin n → v.adicCompletion F, (∀ i, z i ∈ Formalism.UG.Ov F v) →
      ∃ z' : Fin n → v.adicCompletion F, (∀ i, z' i ∈ Formalism.UG.Ov F v) ∧
        (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec
            ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z) =
          (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z') →
    ∀ X : Matrix (Fin n) (Fin n) (v.adicCompletion F), ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
      ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X *
            (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
          (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro F _ _ v n N hN X
  obtain ⟨ϖ, hϖ⟩ := exists_unif F v
  have hϖO : ϖ ∈ Formalism.UG.Ov F v := by
    change Valued.v ϖ ≤ 1
    rw [hϖ]
    exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1)
  have h0 : ϖ ≠ 0 := by rintro rfl; simp [Formalism.UG.IsUnifV] at hϖ
  obtain ⟨m, -, a, ha, b, hb, hNab⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ N
  set O := Formalism.UG.Ov F v with hO
  have hbe := Formalism.UG.P.cartan_entries_of_mem O b hb
  have hbi := Formalism.UG.P.cartan_entries_of_mem O _ (inv_mem hb)
  have hae := Formalism.UG.P.cartan_entries_of_mem O a ha
  have hai := Formalism.UG.P.cartan_entries_of_mem O _ (inv_mem ha)
  have ha1 : ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have ha2 : (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hb2 : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ha1x : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, ha1, Matrix.one_mul]
  have ha2x : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, ha2, Matrix.one_mul]
  have key : ∀ i j : Fin n, i ≠ j → m i ≤ m j := by
    intro i j hij
    set E : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.single i j 1 with hE
    have hsq : E * E = 0 := by rw [hE]; simp [Matrix.single_mul_single_of_ne, hij.symm]
    have hEmem : ∀ r s, E r s ∈ O := by
      intro r s
      simp only [hE, Matrix.single_apply]
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    have h1mem : ∀ r s, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) r s ∈ O := by
      intro r s
      rw [Matrix.one_apply]
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    have hAB : ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (1 + E) *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) *
        ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (1 - E) *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1 := by
      have hpm : (1 + E) * (1 - E) = 1 := by
        rw [add_mul, one_mul, mul_sub, mul_one, hsq]; abel
      simp only [Matrix.mul_assoc, ha1x]
      rw [← Matrix.mul_assoc (1 + E), hpm, Matrix.one_mul, ha2]
    obtain ⟨g, hg, hgA⟩ := Formalism.UG.P.cartan_exists_glint O _ _ hAB
      (mul_entries_mem O (mul_entries_mem O hae fun r s => O.add_mem (h1mem r s) (hEmem r s)) hai)
      (mul_entries_mem O (mul_entries_mem O hae fun r s => O.sub_mem (h1mem r s) (hEmem r s)) hai)
    have hz : ∀ k, (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
        Pi.single j 1) k ∈ O := mulVec_entries_mem O hbi fun k => by
      rw [Pi.single_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    obtain ⟨z', hz', hEq⟩ := hN g hg _ hz
    rw [hgA, hNab] at hEq
    have hL := congrArg (fun w => ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w) hEq
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, ha1x, hb2, Matrix.mul_one] at hL
    have hi := congrFun hL i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hi
    rw [← Matrix.mulVec_mulVec] at hi
    simp only [Formalism.UG.diagPow, Matrix.mul_diagonal, Matrix.mulVec_diagonal, Matrix.add_apply,
      Matrix.one_apply_ne hij, hE, Matrix.single_apply_same, zero_add, one_mul] at hi
    exact le_of_zpow_eq hϖ (mulVec_entries_mem O hbe hz' i) hi
  obtain ⟨c, hc, hD⟩ : ∃ c : v.adicCompletion F, c ≠ 0 ∧
      Formalism.UG.diagPow F v ϖ m = c • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rcases n with _ | k
    · exact ⟨1, one_ne_zero, by ext i; exact i.elim0⟩
    · refine ⟨ϖ ^ (m 0), zpow_ne_zero _ h0, ?_⟩
      ext i j
      simp only [Formalism.UG.diagPow, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs with h
      · subst h
        have hm : m i = m 0 := by
          rcases eq_or_ne i 0 with rfl | hi
          · rfl
          · exact le_antisymm (key i 0 hi) (key 0 i hi.symm)
        rw [hm, mul_one]
      · rw [mul_zero]
  refine ⟨(a * b)⁻¹, inv_mem (mul_mem ha hb), a * b, mul_mem ha hb, ?_⟩
  have hNc : (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      c • ((a * b : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rw [hNab, hD, Units.val_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hNi : ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    have h1 : ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1 := by
      rw [hNc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one]
    calc _ = ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
          ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
            (c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
          rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hNi, hNc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.NormaliserGLint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentSumNoMonodromyLengthOne
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SegSumOne

theorem segSum_of_mono0 : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (l : List (Segment (w.adicCompletion E))), (segSum rc l).mono0 →
      (∀ Δ ∈ l, Δ.len = 1) ∧ segSum rc l = sumList (l.map fun Δ => rc Δ.first) := by
  intro E Ω _ _ _ _ _ A w h rc hrc l hm
  obtain ⟨a, ha, H⟩ := hrc
  have hlen : ∀ Δ ∈ l, Δ.len = 1 := by
    intro Δ hΔ
    have hirr : IsIrrWD ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)) := by
      rw [← H.nu]; exact (H.cusp _ (Δ.isCusp_first.nu _))
    have hmi : (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).mono0 :=
      GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm _ (List.mem_map.2 ⟨Δ, hΔ, rfl⟩)
    have hpos := Δ.len_pos
    by_contra hne
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by omega) hmi
  refine ⟨hlen, ?_⟩
  unfold segSum
  congr 1
  refine List.map_congr_left fun Δ hΔ => ?_
  rw [hlen Δ hΔ, GlobalTheory.SegLen.lpChar_lpSp_one']
  simp [WD.lpTw_zero]

end GlobalTheory.SegSumOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

theorem finPart_surjective (D : D7) : Function.Surjective (Formalism.L2.Theta.finPart D) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a x =>
    exact ⟨((0, a) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] x, rfl⟩
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (Formalism.L2.Theta.finPart D).map_add a b⟩

theorem comp_idem : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  intro D sp hF p c hπ
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  refine ⟨?_, ?_⟩
  · apply c.injective
    rw [← hπ, hπe, map_one]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := finPart_surjective D x
    obtain ⟨b, rfl⟩ := finPart_surjective D y
    have hab : p.π a = p.π b := by rw [hπ, hπ, hxy]
    have key : p.e * a = p.e * b := by rw [← p.ι_π, ← p.ι_π, hab]
    rw [← map_mul, ← map_mul, key]

end GlobalTheory.PlaceSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameConjGLintLeSelfDualLatticeStabilize
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitFrameLattice


set_option maxHeartbeats 1000000 in
theorem glint_mul_frame_basis : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V V.rank) (sp : SplitPlace D.host.E)
    (β β' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    β * β' = 1 → β' * β = 1 →
    (∀ κ, Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ κ) =
      β * ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm) * β') →
    (∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank ↔ Ps.ψ κ ∈ Formalism.L2.Theta.KsphC V ∅) →
    ∀ (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) →
    (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) →
    (∀ x ∈ Formalism.L2.Theta.intAE D,
      sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) →
    sp.proj (GlobalTheory.NJoin.tensCast hF ε) = 1 →
    (∀ z, Formalism.IndefR.Mult.IntVec z → (fun a => ε * B.mulVec z a) ∈ Formalism.L2.NTheta.LamHat V) →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, Formalism.IndefR.Mult.IntVec z ∧ (fun a => ε * y a) = fun a => ε * B.mulVec z a) →
    ∀ g ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v),
    ∀ z : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
      (∀ i, z i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) →
      ∃ z' : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
        (∀ i, z' i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) ∧
        (g : Matrix (Fin V.rank) (Fin V.rank) _).mulVec
            ((β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z) =
          (β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z' := by
  intro D hF V Ps sp β β' hββ' hβ'β hfr hK ε sec B hsec hsecI hint hε b1 b2 g hg z hz
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+*
      sp.v.adicCompletion (maximalRealSubfield D.host.E) :=
    sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom
  have hfun : (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) = ⇑φ := rfl
  have hφε : φ ε = 1 := hε
  rw [hfun]
  obtain ⟨emb, htriv, hloc⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp
  have hκ : emb g ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank :=
    GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp (emb g) (htriv g) (by rw [hloc]; exact hg)
  have hKs := (hK (emb g)).1 hκ
  have hz0 : Formalism.IndefR.Mult.IntVec (sec ∘ z) := fun i => hsecI _ (hz i)
  have hy := b1 _ hz0
  have hy' := (hKs.2.1 _).1 hy
  obtain ⟨z'', hz'', e⟩ := b2 _ hy'
  refine ⟨φ ∘ z'', fun i => hint _ (hz'' i), ?_⟩
  have mv : ∀ (M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) x,
      φ ∘ (M.mulVec x) = (M.map φ).mulVec (φ ∘ x) := fun M x => funext fun i => RingHom.map_mulVec φ M x i
  have hε' : ∀ w : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      φ ∘ (fun a => ε * w a) = φ ∘ w := fun w => funext fun a => by
    simp only [Function.comp_apply, map_mul, hφε, one_mul]
  have hg' : (((emb g).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map
      (GlobalTheory.NJoin.tensCast hF).symm).map φ = (g : Matrix (Fin V.rank) (Fin V.rank) _) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    show sp.proj (GlobalTheory.NJoin.tensCast hF ((GlobalTheory.NJoin.tensCast hF).symm _)) = _
    rw [RingEquiv.apply_symm_apply]
    conv_rhs => rw [← hloc g]
    rfl
  have hM : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g))).map φ =
      β.map φ * (g : Matrix (Fin V.rank) (Fin V.rank) _) * β'.map φ := by
    rw [hfr (emb g), Matrix.map_mul, Matrix.map_mul, hg']
  have hzφ : φ ∘ (sec ∘ z) = z := funext fun i => hsec _
  have hβ : β'.map φ * β.map φ = 1 := by
    rw [← Matrix.map_mul, hβ'β, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have E := congrArg (fun w => φ ∘ w) e
  rw [hε', hε', mv, mv, hε', mv, hzφ, hM] at E
  have E2 := congrArg (fun w => (β'.map φ).mulVec w) E
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hβ, Matrix.one_mul] at E2
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  exact E2

end GlobalTheory.SplitFrameLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameMemHyperspecialIffMaxCompactTrivOut
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.FrameHyp.mem_hyp_iff : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → ∀ (sp : SplitPlace D.host.E)
    (κ : Formalism.AUTREP.GAf D.host.E n), Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w ↔ κ ∈ Umax D.host.E n ∧ TrivOutside {sp.v} κ := by
  intro D hF V n Ps hstd sp κ
  constructor
  · rintro ⟨hK, e, f, hef, hs⟩
    exact ⟨(hstd.2 κ).2 hK,
      (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V n Ps hstd e f hef κ).1 hs⟩
  · rintro ⟨hU, hT⟩
    obtain ⟨-, e, f, hef, -⟩ := GlobalTheory.DefLiftHecke.one_mem_hyp V sp.w
    exact ⟨(hstd.2 κ).1 hU, e, f, hef,
      (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V n Ps hstd e f hef κ).2 hT⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySecond
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.EigInert.heckeFunI_umax_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    ∃ (C : Finset (GAf L n ⧸ Umax L n)) (a : GAf L n ⧸ Umax L n → ℂ) (x : GAf L n ⧸ Umax L n → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n (Umax L n) Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ :=
  GlobalTheory.SatIso.heckeFunI_eq_sum Dv _ h (_root_.GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv (_root_.GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
    (_root_.GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) _ (fun _ _ => Iff.rfl) h hh)

end

