module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JordanExponentsMaximalHermitianLatticeBadPrime
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantModuleIsometriesEqNormOneResidues
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0102
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointTermAndLiftSameRealDoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0397
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularOfLocalStandardLatticeTranslates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicFrameVectorPrimitiveInInnerLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDimensionalRowsSpaceDiscreteSeriesCount
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
section
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

namespace GlobalTheory.Mass.MaxFormula

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] in
theorem nondegenerate_of_pos {h : V →ₗ⋆[K] V →ₗ[K] K} [NumberField K] (hd : IsTotPosDef h) :
    h.Nondegenerate := by
  have han : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x h0 φ
    simp [hx] at this
  exact ⟨fun x hx => han x (hx x), fun x hx => han x (hx x)⟩

theorem localMassFactor_eq_of_mem_badPrimes (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) {P : Ideal (𝓞 K)}
    (hP : P ∈ badP h M) :
    lamP h M (P.comap (algebraMap (𝓞 F) (𝓞 K))) =
      ((qIn P : ℝ) ^ Module.finrank K V - (-1) ^ Module.finrank K V) / ((qIn P : ℝ) + 1) := by
  have hnd := nondegenerate_of_pos hd
  obtain ⟨hc, hq2, hq, -⟩ := (GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM).2.2.2 P hP
  have hPm : P.IsMaximal := hP.1
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have h𝔭 : 𝔭.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P
  obtain ⟨hJ1, hJ2⟩ := jordan_splitting_exists K F V hK hF h hs
  have hfull := hM.1.1
  have hlat := hfull.toIsLattice
  obtain ⟨b, a, hJ⟩ := hJ1 ⊤ M (fun x _ hx => hnd.1 x fun y => hx y trivial)
    ⟨hlat.fg, hfull.span_eq_top⟩ hM.1.2 𝔭 h𝔭
  obtain ⟨i, hi, hj⟩ := _root_.GlobalTheory.MaxLatExpo.main K F V hK hF h hs hd M hM P hP b a hJ
  have hv : vd h M 𝔭 = 1 := by
    rw [hJ2 M hlat 𝔭 h𝔭 b a hJ, vJof, Finset.sum_eq_single i (fun j _ => hj j) (by simp)]
    exact hi
  have hcJ : cJof 𝔭 a = 1 := by
    rw [cJof, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun h1 => by_contra fun h2 => h1 (hj j h2), ?_⟩
    rintro rfl
    rw [hi]
    exact one_ne_zero
  have hN : Ideal.absNorm 𝔭 = qIn P := by
    have := absNorm_comap_inert hK hF hPm hc
    rw [hq] at this
    exact Nat.pow_left_injective two_ne_zero this
  have hη : etaF K F 𝔭 = -1 := by rw [h𝔭def, etaF_comap hK hF hPm, if_pos hc]
  have hdisc : (discAut h ⊤ M 𝔭 : ℝ) = (qIn P : ℝ) + 1 := by
    have hq0 : (qIn P : ℝ) ≠ 0 := by exact_mod_cast (by omega : qIn P ≠ 0)
    rw [_root_.GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount K F V hK hF h hs M hlat 𝔭 h𝔭 b a hJ i hi hj,
      ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 le_rfl, ThirdPropositionSlot.alphaStd_one, hη, hN]
    field_simp
    ring
  have hm : 1 ≤ Module.finrank K V := by
    have := i.pos
    rwa [finrank_top] at this
  obtain ⟨m, hm'⟩ : ∃ m, Module.finrank K V = m + 1 := ⟨_, (Nat.sub_add_cancel hm).symm⟩
  have hpos := alphaStd_pos hK hF h𝔭 m
  have hq0 : (0 : ℝ) < qIn P := by exact_mod_cast (by omega : 0 < qIn P)
  rw [lamP, alpha_discriminant_holds K F V hK hF h hs hd M hlat hM.1.2 𝔭 h𝔭 b a hJ, hv, hcJ, hdisc, hm',
    Nat.add_sub_cancel, mul_one]
  have hstep : alphaStd K 𝔭 (m + 1) =
      alphaStd K 𝔭 m * (1 - (-1) ^ (m + 1) * ((qIn P : ℝ) ^ (m + 1))⁻¹) := by
    rw [alphaStd, Finset.prod_Icc_succ_top (by omega), hη, hN, zpow_neg, zpow_natCast, ← hN, ← hη]
    rfl
  rw [hstep, hN]
  field_simp

theorem lamG_eq_lamMax (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) :
    lamG F h M = lamMax h M := by
  have hst := GlobalTheory.MaxLatStruct.main K V h hK hs (nondegenerate_of_pos hd) M hM
  have hfin := hst.1
  let g : {P // P ∈ hfin.toFinset} → {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} := fun P =>
    ⟨P.1.comap (algebraMap (𝓞 F) (𝓞 K)), by
      have : P.1.IsMaximal := (hfin.mem_toFinset.1 P.2).1
      exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P.1⟩
  have hg : Function.Injective g := by
    intro P Q hPQ
    have hP := hfin.mem_toFinset.1 P.2
    have hQ := hfin.mem_toFinset.1 Q.2
    have := (comap_eq_comap_iff hK hF hP.1 hQ.1).1 (congrArg Subtype.val hPQ)
    rw [(hst.2.2.2 P.1 hP).1, or_self] at this
    exact Subtype.ext this.symm
  rw [lamG, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin,
    tprod_eq_prod (s := hfin.toFinset.attach.image g), Finset.prod_image fun _ _ _ _ e => hg e,
    ← Finset.prod_attach hfin.toFinset]
  · exact Finset.prod_congr rfl fun P _ => localMassFactor_eq_of_mem_badPrimes hK hF hs hd hM (hfin.mem_toFinset.1 P.2)
  · intro 𝔭 h𝔭
    obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
    have hlat := hM.1.1
    apply localMassFactor_of_valuation_eq_zero hK hF hs hd hlat hM.1.2 𝔭.2
    rw [← hP𝔭]
    refine (isUnimodularAt_iff_vd hK hF hs hd hlat hM.1.2 hP).1 (by_contra fun hb => h𝔭 ?_)
    exact Finset.mem_image.2 ⟨⟨P, hfin.mem_toFinset.2 ⟨hP, hb⟩⟩, Finset.mem_attach _ _,
      Subtype.ext hP𝔭⟩

theorem main : MaxMass := by
  intro K _ _ _ hK n hn
  obtain ⟨F, _, _, _, hF⟩ := exists_fixF K hK
  obtain ⟨c₁, -, hall⟩ := massConst_all binary_hermitian_represents liStat hK hF
  refine ⟨c₁ * ∏ j ∈ Finset.Icc 2 n, massRatioRightSide K j, fun V _ _ _ _ _ h hs hp hr M hM => ?_⟩
  have hd : IsTotPosDef h := fun x hx φ => hp φ x hx
  rw [hall n hn V h M hs hd hr hM.1.1 hM.1.2, lamG_eq_lamMax hK hF hs hd hM]

end GlobalTheory.Mass.MaxFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermHasRealRelativePoint
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RelPtLift

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem loUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) (h' : IsLoUni l') : IsLoUni (l * l') := by
  first
  | exact @_root_.GlobalTheory.LowerUnipotentMul.main
  | exact _root_.GlobalTheory.LowerUnipotentMul.main
  | (apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LowerUnipotentMul.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LowerUnipotentMul.main ..)

theorem upUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) (h' : IsUpUni l') : IsUpUni (l * l') := by
  first
  | exact @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul
  | exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul
  | (apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul ..)

end Uni

variable {k r : ℕ}

def sgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

theorem sgn_sq : sgn r * sgn r = 1 := by
  rw [sgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  simp

theorem zhatO_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ZhatO k r z z' g = Formalism.QuantumDeterminants.Zhat k r z z' g * sgn r := by
  ext a b
  rw [sgn, Matrix.mul_diagonal, mul_comm]
  rfl

theorem upUni_sgn_conj {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU0 : ∀ c b, b < c → U c b = 0)
    (hU1 : ∀ c, U c c = 1) : IsUpUni (sgn r * U * sgn r) := by
  intro a b
  rw [sgn, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hab => by rw [hU0 a b hab]; ring, fun hab => ?_⟩
  subst hab
  rw [hU1, mul_one, ← mul_pow]
  simp

theorem loUni_conjT {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU0 : ∀ c b, b < c → U c b = 0)
    (hU1 : ∀ c, U c c = 1) : IsLoUni Uᴴ := by
  intro a b
  refine ⟨fun hab => by rw [conjTranspose_apply, hU0 b a hab, star_zero], fun hab => ?_⟩
  subst hab
  rw [conjTranspose_apply, hU1, star_one]

theorem det_Hpk : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1

theorem mem_UH_of_Sset {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.Sset k r z) : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
  Formalism.QuantumDeterminants.Sset_UH ha

theorem zhat_dcoset {z z' : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hz' : Formalism.QuantumDeterminants.inWb k r z')
    {a a' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.Sset k r z)
    (ha' : a' ∈ Formalism.QuantumDeterminants.Sset k r z') (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∃ U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, (∀ c b, b < c → U c b = 0) ∧ (∀ c, U c c = 1) ∧
      (∀ c b, b < c → U' c b = 0) ∧ (∀ c, U' c c = 1) ∧
      Formalism.QuantumDeterminants.Zhat k r z z' (a * g * a'⁻¹) = Uᴴ * Formalism.QuantumDeterminants.Zhat k r z z' g * U' := by
  obtain ⟨-, -, hinv⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  obtain ⟨-, -, hinv'⟩ := Formalism.QuantumDeterminants.sGroup k r z' hz'
  obtain ⟨U, hU0, hU1, hF⟩ := Formalism.QuantumDeterminants.S_F hz (hinv a ha)
  obtain ⟨U', hU0', hU1', hF'⟩ := Formalism.QuantumDeterminants.S_F hz' (hinv' a' ha')
  have hdet : IsUnit a.det := ((Formalism.QuantumDeterminants.uHGroup _ _ det_Hpk).2.2 a (mem_UH_of_Sset ha)).1
  have hai : (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * a⁻¹ = Formalism.QuantumDeterminants.Hpk k r := Formalism.QuantumDeterminants.Sset_UH (hinv a ha)
  have hHa : Formalism.QuantumDeterminants.Hpk k r * a = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
    calc Formalism.QuantumDeterminants.Hpk k r * a = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * a⁻¹ * a := by rw [hai]
      _ = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  refine ⟨U, U', hU0, hU1, hU0', hU1', ?_⟩
  rw [Formalism.QuantumDeterminants.Zhat_eq, Formalism.QuantumDeterminants.Zhat_eq]
  calc (Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * g * a'⁻¹) * Formalism.QuantumDeterminants.Fm k r z'
      = (Formalism.QuantumDeterminants.Fm k r z)ᴴ * (Formalism.QuantumDeterminants.Hpk k r * a) * g * (a'⁻¹ * Formalism.QuantumDeterminants.Fm k r z') := by
        simp only [Matrix.mul_assoc]
    _ = (Formalism.QuantumDeterminants.Fm k r z)ᴴ * ((a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r) * g * (Formalism.QuantumDeterminants.Fm k r z' * U') := by
        rw [hHa, hF']
    _ = (a⁻¹ * Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z' * U' := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Uᴴ * ((Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z') * U' := by
        rw [hF, conjTranspose_mul]; simp only [Matrix.mul_assoc]

theorem relPt_dcoset (D : D7) {z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z)
    (hz' : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z') {a a' γ : MatKR D.R.k D.R.rS} (ha : a ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z)
    (ha' : a' ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z') {p : Point ℂ (D.R.rS + 1)} (h : RelPt D z z' γ p) :
    RelPt D z z' (a * γ * a'⁻¹) p := by
  obtain ⟨hUH, ⟨L, V, hL, hV, hZ⟩, hGf⟩ := h
  obtain ⟨-, -, hinv'⟩ := Formalism.QuantumDeterminants.sGroup _ _ z' hz'
  have hG := Formalism.QuantumDeterminants.uHGroup _ _ (det_Hpk (k := D.R.k) (r := D.R.rS))
  refine ⟨hG.2.1 _ (hG.2.1 _ (mem_UH_of_Sset ha) _ hUH) _ (mem_UH_of_Sset (hinv' a' ha')), ?_, ?_⟩
  · obtain ⟨U, U', hU0, hU1, hU0', hU1', he⟩ := zhat_dcoset hz hz' ha ha' γ
    have hZ' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' γ = L * ptMat p * V * sgn D.R.rS := by
      rw [← hZ, zhatO_eq, Matrix.mul_assoc, sgn_sq, Matrix.mul_one]
    refine ⟨Uᴴ * L, V * (sgn D.R.rS * U' * sgn D.R.rS), loUni_mul (loUni_conjT hU0 hU1) hL,
      upUni_mul hV (upUni_sgn_conj hU0' hU1'), ?_⟩
    rw [zhatO_eq, he, hZ']
    simp only [Matrix.mul_assoc]
  · rw [Formalism.QuantumDeterminants.gInv _ _ z z' hz hz' a ha a'⁻¹ (hinv' a' ha') γ]
    exact hGf

end GlobalTheory.RelPtLift

theorem GlobalTheory.RelPtLift.relPt_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ, ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) p := by
  intro D X Y hF hI θ C u u' t s hs hG hr τ
  obtain ⟨p, hp⟩ := relPtEx_holds hI C u u' t hG hr τ
  obtain ⟨a, ha, a', ha', heq⟩ := GlobalTheory.TermCoset.dcoset D X Y hF hI θ C u u' t s hs τ
  refine ⟨p, ?_⟩
  rw [heq]
  exact GlobalTheory.RelPtLift.relPt_dcoset D (Formalism.L2.SG.Pf.zTr C u τ).1 (Formalism.L2.SG.Pf.zTr C u' τ).1 ha ha' hp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeOfLocallyStandardFrame
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatAdapt

theorem witt_flag (D : D7) (T : D.host.E) (hT : T ≠ 0) (F F' : FlagG (VS D) D.R.rS T) :
    ∃ g : GV D, g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ ∀ a, g (F.fvec a) = F'.fvec a := by
  have hind : ∀ G : FlagG (VS D) D.R.rS T, LinearIndependent D.host.E G.fvec := by
    intro G
    unfold FlagG.fvec
    rw [linearIndependent_finSnoc]
    refine ⟨G.e_indep, fun hz => hT ?_⟩
    have h0 : ∀ x ∈ Submodule.span D.host.E (Set.range G.e), (VS D).hT x G.z = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact G.z_orth a
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    have := h0 _ hz
    rw [G.z_norm] at this
    exact neg_eq_zero.1 this
  have hgram : ∀ G : FlagG (VS D) D.R.rS T, ∀ i j, (VS D).hT (G.fvec i) (G.fvec j) =
      if i = Fin.last _ ∧ j = Fin.last _ then -T else 0 := by
    intro G i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_norm]
      | cast b =>
        simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
        rw [← (VS D).herm.eq (G.e b) G.z, G.z_orth b, map_zero]
        simp [Fin.castSucc_ne_last]
    | cast a =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_orth, Fin.castSucc_ne_last]
      | cast b => simp [FlagG.fvec, G.e_iso, Fin.castSucc_ne_last]
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.St.WittT.witt_family F.fvec F'.fvec (hind F) (hind F')
    (fun i j => by rw [hgram F, hgram F'])
  exact ⟨g, hg, hgi⟩

theorem iso_X {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) :
    ∀ y ∈ G.X, ∀ x ∈ G.X, (VS D).hT y x = 0 := by
  intro y hy x hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    induction hy using Submodule.span_induction with
    | mem v hv => obtain ⟨a, rfl⟩ := hv; exact G.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem xa_last {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) : G.Xa D.R.rS = G.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp

theorem lsub_eq {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : Lsub Λ F = Lsub Λ F' := by
  simp only [Lsub, Lrep, Xsp, h]

theorem xlam_eq {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : XLam Λ F = XLam Λ F' := by
  simp only [XLam, Xsp, h]

theorem row_lattice_of_local_standard : ∀ (D : D7) (Tn : ℕ), Tn ≠ 0 → ∀ (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ g, Adapt g (lf D F0) G ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  intro D Tn hTn F0 G Z A hA Λ hΛ hloc
  have hU := _root_.GlobalTheory.Unfold.StdDual.unimodular_of_local
  have hX := _root_.GlobalTheory.RowLatXS.xlam_eq_span_scaled
  have hZ := _root_.GlobalTheory.IsotropicLift.exists_add_mem
  have hP := _root_.GlobalTheory.FramePrim.coef_integral
  have hM := _root_.GlobalTheory.MkFlag.mkflag
  have hTr := _root_.GlobalTheory.RowLatTransport.rowLat_transport
  have hC := _root_.GlobalTheory.FixConvRow.isFixedConv_of_XLam_eq
  have hu := hU D Z A Λ hΛ hloc
  obtain ⟨e', he', hXe⟩ := hX D _ G Z A hA Λ hΛ hloc
  obtain ⟨x, hx, hzx⟩ := hZ D _ G Z A hA Λ hΛ hloc
  have hpr := hP D _ G Z A hA Λ hΛ hloc
  obtain ⟨G', hGe, hGz, hGX⟩ := hM D _ G.fl e' x he' hx
  have hT0 : ((Tn : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hTn
  obtain ⟨g, hg, hga⟩ := witt_flag D _ hT0 F0 G'
  have hX' : XLam Λ (lf D G') = XS D G' := by
    rw [xlam_eq (lf D G') G hGX, hXe, XS, hGe]
  have hpr' : ∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
    intro c hc
    rw [lsub_eq (lf D G') G hGX] at hc
    refine hpr c ?_
    have hcx : c • G.fl.z = c • G'.z - c • x := by rw [hGz, smul_add]; abel
    rw [hcx]
    refine Submodule.sub_mem _ hc ?_
    have hxX : c • x ∈ (Xsp G : Submodule D.host.E (VS D).V) := Submodule.smul_mem _ c hx
    refine ⟨Submodule.mem_sup_right hxX, ?_⟩
    show c • x ∈ orth (VS D) (Xsp G)
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro y hy
    exact iso_X G.fl y hy _ hxX
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hTr D _ F0 G' g hg hga Λ hΛ hu (hGz ▸ hzx) hX' hpr'
  refine ⟨g, ⟨hg, fun a => ?_⟩, h1, ⟨h2, h3, ⟨h4, rfl⟩, hC D _ F0 _ h5 h6⟩, h5⟩
  show g (F0.fvec a) - G.fl.fvec a ∈ G.fl.Xa a.val
  rw [hga a]
  induction a using Fin.lastCases with
  | last =>
    simp only [FlagG.fvec, Fin.snoc_last, Fin.val_last, hGz, xa_last]
    simpa using hx
  | cast b =>
    simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.val_castSucc, hGe]
    exact he' b

end GlobalTheory.RowLatAdapt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeCoordinatesImageIffPreserved
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem latMap_Lc_iff : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X ↔ Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) := by
  intro D X n γ hγ
  have key : GlobalTheory.SgGlob.latMap γ (Lc X) =
      (Formalism.HermitianLatticesTheory.gmap n (VS D).L0).comap ((vecOf X).restrictScalars (𝓞 D.host.E)) := by
    ext c
    simp only [GlobalTheory.SgGlob.latMap, Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, Submodule.mem_comap, Lc,
      LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨c', hc', rfl⟩
      exact ⟨vecOf X c', hc', n_vecOf hγ c'⟩
    · rintro ⟨y, hy, hny⟩
      refine ⟨crdH X y, by rw [vecOf_crdH]; exact hy, ?_⟩
      rw [← hγ, hny, crdH_vecOf]
  have hsurj : Function.Surjective ((vecOf X).restrictScalars (𝓞 D.host.E)) := fun y =>
    ⟨crdH X y, vecOf_crdH X y⟩
  rw [key]
  exact (Submodule.comap_injective_of_surjective hsurj).eq_iff

end GlobalTheory.CovDomGrp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRat
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountFinal

theorem countingTheorem_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hV
  have hDec : GlobalTheory.DSId.DecGap := _root_.GlobalTheory.DecGapBound.decGap_of_formulaGap _root_.GlobalTheory.Jet.FormGapFree.formulaGap
  have hPt : GlobalTheory.Deep.PtBound := GlobalTheory.Deep.ptBound_of_decGap hDec
  have hAbs : GlobalTheory.FlagMeas.AbsoluteVolume := _root_.GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep hV
  have hFM : GlobalTheory.FlagMeas.FlagMeasureBound := _root_.GlobalTheory.FlagMeas.Bound.flagMeasureBound hV
  have hFin := _root_.GlobalTheory.RowsFinMult.rows_finiteDimensional hDec hAbs
  have hNear := GlobalTheory.NearMod.nearModerate hFM _root_.GlobalTheory.FlagMeas.constantBound GlobalTheory.NearElement.near_unipotent hPt
  have hFar := _root_.GlobalTheory.Deep.farModerate_of_farBound hFM (GlobalTheory.FarTerms.farBound_of_ptBound hPt)
  have hRare := GlobalTheory.FlagRareProof.flagRare_of_nonzeroFlagBound (_root_.GlobalTheory.NonzeroFlag.nonzeroFlagBound hV)
  have hDeep := GlobalTheory.T.deepRegion_kernelDiagonal_bound hAbs (_root_.GlobalTheory.DeepKernel.deep_kernel_bound_of_ptBound hPt hFin)
  exact _root_.GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds hFin hFM hPt hNear hFar hRare hDeep

end GlobalTheory.CountFinal
end

