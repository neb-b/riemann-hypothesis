module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVanishingLevelUnitBlockMulInvStab
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section
namespace GlobalTheory.BotPairSmall.BlockK

theorem blockJ_upper : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (o d : ℕ) (j : GA D d), j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d →
    ∀ i l : Fin d, i.1 < o → o ≤ l.1 →
      ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i l ∈ hatId D (D.host.conj • 𝔪) := by
  intro D 𝔪 o d j hj i l hi hl
  have hj' : j⁻¹ ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d := inv_mem hj
  rw [GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet] at hj'
  have h1 := hj'.2 l i hi hl
  have hu := (GlobalTheory.NormSum.PtsMem.mem_GA D _).1 j.2
  have hJJ : ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) *
      (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by
    rw [← Units.val_mul]; simp
  have hinv : (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) =
      (((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)).map (sgA D)).transpose := by
    calc _ = ((((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)).map (sgA D)).transpose *
          ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))) *
          (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) := by rw [hu, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  rw [hinv, Matrix.transpose_apply, Matrix.map_apply] at h1
  have h2 := GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId h1
  rwa [GlobalTheory.NormSum.VacMove.sgA_sgA] at h2

theorem det_mem_OhE {D : D7} {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D)) (h : ∀ i l, M i l ∈ OhE D) : M.det ∈ OhE D := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

theorem mul_mem_OhE {D : D7} {a : ℕ} (M M' : Matrix (Fin a) (Fin a) (AE D)) (h : ∀ i l, M i l ∈ OhE D)
    (h' : ∀ i l, M' i l ∈ OhE D) : ∀ i l, (M * M') i l ∈ OhE D := fun i l => by
  rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (h _ _) (h' _ _)

theorem exists_k (hB2 : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)) (a : ℕ) (Z : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) (f w : AE D), f ∈ OhE D → w ∈ OhE D → f * f = f → f * sgA D f = 0 → f = inc D ((Z.det : 𝓞 D.host.E) : D.host.E) * w → 1 - f ∈ hatId D 𝔫 → ∃ k ∈ intG D a, ∀ i l, (Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D 𝔫) (hB3 : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪)) (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (a : ℕ)
    (Dt Dp : Matrix (Fin a) (Fin a) (AE D)) (hDt : ∀ i l, Dt i l ∈ OhE D) (hDp : ∀ i l, Dp i l ∈ OhE D)
    (hc : ∀ i l, (Dp * Dt - 1) i l ∈ hatId D (D.host.conj • 𝔪)) :
    ∃ k ∈ intG D a, ∀ i l, (Dt - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈
      hatId D (D.host.conj • 𝔪) := by
  have hn : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  choose Z hZ using fun i l => GlobalTheory.CongIdx.exists_rep hn (hDt i l)
  set Zm : Matrix (Fin a) (Fin a) (𝓞 D.host.E) := Matrix.of Z with hZm
  set φ : 𝓞 D.host.E →+* AE D := (inc D).comp (algebraMap (𝓞 D.host.E) D.host.E) with hφ
  set Zi : Matrix (Fin a) (Fin a) (AE D) := Zm.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) with hZi
  have hZiO : ∀ i l, Zi i l ∈ OhE D := fun i l => GlobalTheory.NormSum.VacMove.inc_int D _
  have hP : ∀ i l, (Dp * Zi - 1) i l ∈ hatId D (D.host.conj • 𝔪) := by
    intro i l
    have e : Dp * Zi - 1 = Dp * (Zi - Dt) + (Dp * Dt - 1) := by
      rw [Matrix.mul_sub]; abel
    rw [e, Matrix.add_apply]
    refine add_mem ?_ (hc i l)
    rw [Matrix.mul_apply]
    refine sum_mem fun m _ => GlobalTheory.CongIdx.mul_mem_hatId (hDp _ _) ?_
    rw [Matrix.sub_apply, ← neg_sub]
    exact neg_mem (hZ m l)
  have hdet := GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of _ (mul_mem_OhE _ _ hDp hZiO) hP
  have hZdet : Zi.det = inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) := by
    have : Zi = φ.mapMatrix Zm := rfl
    rw [this, ← RingHom.map_det]; rfl
  rw [Matrix.det_mul, hZdet] at hdet
  obtain ⟨u, hu⟩ := GlobalTheory.CongIdx.exists_rep hn (det_mem_OhE Dp hDp)
  have key : inc D ((Zm.det * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : inc D ((Zm.det * u : 𝓞 D.host.E) : D.host.E) - 1 =
        -(inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) * (Dp.det - inc D (u : D.host.E))) +
          (Dp.det * inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) - 1) := by
      push_cast; rw [map_mul]; ring
    rw [e]
    exact add_mem (neg_mem (GlobalTheory.CongIdx.mul_mem_hatId (GlobalTheory.NormSum.VacMove.inc_int D _) hu)) hdet
  obtain ⟨f, hf, w, hw, hff, hfs, hfw, h1f⟩ := hB3 D 𝔪 hcop _ _ key
  obtain ⟨k, hk, hkc⟩ := hB2 D _ a Zm f w hf hw hff hfs hfw h1f
  refine ⟨k, hk, fun i l => ?_⟩
  have e : (Dt - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l =
      (Dt i l - inc D (Z i l : D.host.E)) +
        (Zi - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l := by
    simp only [Matrix.sub_apply, hZi, Matrix.map_apply, hZm, Matrix.of_apply]; ring
  rw [e]
  exact add_mem (hZ i l) (hkc i l)

theorem blockJ_unitBlock : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (o a d : ℕ), o + a = d → ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∀ i l, (((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D o a d).map (inc D) - (unitBlock D o a d).map (inc D) * (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D (D.host.conj • 𝔪) := by
  intro D 𝔪 hm hcop o a d hd j hj
  subst hd
  have hA := blockJ_upper D 𝔪 o (o + a) j hj
  have hI := (mem_intG j).1 (GlobalTheory.BotPairSmall.blockJ_le D 𝔪 o (o + a) hj)
  set J : Matrix (Fin (o + a)) (Fin (o + a)) (AE D) := ((j : GL (Fin (o + a)) (AE D)) : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) with hJ
  set Ji : Matrix (Fin (o + a)) (Fin (o + a)) (AE D) := (((j⁻¹ : GA D (o + a)) : GL (Fin (o + a)) (AE D)) : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) with hJi
  have hJO : ∀ i l, J i l ∈ OhE D := fun i l => (hI i l).1
  have hJiO : ∀ i l, Ji i l ∈ OhE D := fun i l => by
    have := (hI i l).2
    simpa [hJi] using this
  have hJJ : Ji * J = 1 := by
    rw [hJi, hJ, ← Units.val_mul]; simp
  let Dt : Matrix (Fin a) (Fin a) (AE D) := fun p l => J (Fin.natAdd o p) (Fin.natAdd o l)
  let Dp : Matrix (Fin a) (Fin a) (AE D) := fun p l => Ji (Fin.natAdd o p) (Fin.natAdd o l)
  have hc : ∀ p l, (Dp * Dt - 1) p l ∈ hatId D (D.host.conj • 𝔪) := by
    intro p l
    have e1 := congrFun (congrFun hJJ (Fin.natAdd o p)) (Fin.natAdd o l)
    rw [Matrix.mul_apply, Fin.sum_univ_add] at e1
    have e2 : (1 : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) (Fin.natAdd o p) (Fin.natAdd o l) =
        (1 : Matrix (Fin a) (Fin a) (AE D)) p l := by
      by_cases h : p = l
      · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      · have h' : Fin.natAdd o p ≠ Fin.natAdd o l := fun e => h (Fin.ext (by
          have := congrArg Fin.val e; simp only [Fin.coe_natAdd] at this; omega))
        rw [Matrix.one_apply_ne h', Matrix.one_apply_ne h]
    rw [e2] at e1
    have e3 : (Dp * Dt - 1) p l = -∑ m : Fin o, Ji (Fin.natAdd o p) (Fin.castAdd a m) * J (Fin.castAdd a m) (Fin.natAdd o l) := by
      rw [Matrix.sub_apply, Matrix.mul_apply, ← e1]; ring
    rw [e3]
    refine neg_mem (sum_mem fun m _ => GlobalTheory.CongIdx.mul_mem_hatId (hJiO _ _) (hA _ _ ?_ ?_))
    · simp
    · simp
  obtain ⟨k, hk, hkc⟩ := exists_k _root_.GlobalTheory.GlueUnitary.glue_unitary (_root_.GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit _root_.GlobalTheory.AlgIntIdem.idem) D 𝔪 hm hcop a Dt Dp (fun _ _ => hJO _ _) (fun _ _ => hJiO _ _) hc
  refine ⟨k, hk, fun i l => ?_⟩
  set K := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK
  have h1 : (J * (unitBlock D o a (o + a)).map (inc D)) i l = J i (Fin.natAdd o l) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd o l)]
    · rw [Matrix.map_apply]; unfold unitBlock
      rw [Matrix.of_apply, if_pos (by simp only [Fin.coe_natAdd]), map_one, mul_one]
    · intro m _ hm
      have : ¬ (m.1 = o + l.1) := fun h => hm (Fin.ext (by simp only [Fin.coe_natAdd]; exact h))
      rw [Matrix.map_apply]; unfold unitBlock
      rw [Matrix.of_apply, if_neg this, map_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.sub_apply, h1]
  refine Fin.addCases (fun i' => ?_) (fun p => ?_) i
  · have h2 : ((unitBlock D o a (o + a)).map (inc D) * K) (Fin.castAdd a i') l = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      have : ¬ ((Fin.castAdd a i' : Fin (o + a)).1 = o + m.1) := by simp only [Fin.coe_castAdd]; omega
      rw [Matrix.map_apply]; unfold unitBlock
      rw [Matrix.of_apply, if_neg this, map_zero, zero_mul]
    rw [h2, sub_zero]
    exact hA _ _ (by simp) (by simp)
  · have h2 : ((unitBlock D o a (o + a)).map (inc D) * K) (Fin.natAdd o p) l = K p l := by
      rw [Matrix.mul_apply, Finset.sum_eq_single p]
      · rw [Matrix.map_apply]; unfold unitBlock
        rw [Matrix.of_apply, if_pos (by simp only [Fin.coe_natAdd]), map_one, one_mul]
      · intro m _ hm
        have : ¬ ((Fin.natAdd o p : Fin (o + a)).1 = o + m.1) := by
          simp only [Fin.coe_natAdd]; intro h; exact hm (Fin.ext (by omega))
        rw [Matrix.map_apply]; unfold unitBlock
        rw [Matrix.of_apply, if_neg this, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2]
    exact hkc p l

end GlobalTheory.BotPairSmall.BlockK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingExtendScalarsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem funEquiv_symm_mapVV {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (σ : ι → DomWeight n) (v : VV K fun τ => (σ τ).dual) :
    (GlobalTheory.FunObj.funEquiv σ).symm (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      GlobalTheory.CoefModel.mapVV φ σ ((GlobalTheory.FunObj.funEquiv σ).symm v) := by
  have h1 : IsFunForm σ ((funEquiv σ).symm v) v := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm v)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := GlobalTheory.BrRat.isFunForm_map φ σ h1
  have h3 := (isFunForm_iff_eq σ _ _).1 h2
  rw [LinearEquiv.symm_apply_eq]
  exact h3

theorem _root_.GlobalTheory.T.branchingPairing_extendScalars : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n N : ℕ} (φ : K →+* ℂ) (σ : ι → DomWeight n) (hN : N = n + 1)
    (Λ : ι → DomWeight N) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    GlobalTheory.FunObj.brPair σ hN Λ (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro K ι _ _ _ n N φ σ hN Λ u v
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, GlobalTheory.BrPairF.brPairF_apply, pairBK_apply, pairB_apply,
    GlobalTheory.BrRat.covOf_eq, funEquiv_symm_mapVV, GlobalTheory.CoefModel.mapVV_coe, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply, Submodule.subtype_apply, GlobalTheory.CoefModel.mapVV_coe,
    GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLevelQuotientGroupLeProdAbsNormPowSq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumSize.GamSize

private theorem prod_norm_le {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ P ∈ S, (n : 𝓞 E) ∈ P.asIdeal) : ∏ P ∈ S, Ideal.absNorm P.asIdeal ≤ n ^ Module.finrank ℚ E := by
  have hd : ∏ P ∈ S, P.asIdeal ∣ Ideal.span {(n : 𝓞 E)} := by
    refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun P hP => ?_
    · exact (Ideal.isCoprime_iff_sup_eq).2
        (P.isMaximal.coprime_of_ne Q.isMaximal fun e => hPQ (HeightOneSpectrum.ext e))
    · rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact h P hP
  have h2 := map_dvd Ideal.absNorm hd
  rw [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h2
  exact Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hn) _) h2

private theorem card_GL_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : ℕ) :
    Nat.card (GL (Fin r) (𝓞 E ⧸ P.asIdeal)) ≤ Ideal.absNorm P.asIdeal ^ (r * r) := by
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have h1 : Nat.card (GL (Fin r) (𝓞 E ⧸ P.asIdeal)) ≤ Nat.card (Fin r → Fin r → (𝓞 E ⧸ P.asIdeal)) :=
    Nat.card_le_card_of_injective (fun g => (g.1 : Fin r → Fin r → _)) fun _ _ e => Units.ext e
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, ← pow_mul] at h1
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact h1

private theorem card_levelQuotientGroup_le_prod_absNorm_pow_sq {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ P ∈ S, (n : 𝓞 E) ∈ P.asIdeal) (r : ℕ) :
    Nat.card (G0 S r) ≤ n ^ (Module.finrank ℚ E * (r * r)) := by
  rw [Nat.card_pi, pow_mul]
  calc ∏ P : S, Nat.card (GL (Fin r) (kP P.1)) ≤ ∏ P : S, Ideal.absNorm P.1.asIdeal ^ (r * r) :=
        Finset.prod_le_prod' fun P _ => card_GL_le P.1 r
    _ = (∏ P ∈ S, Ideal.absNorm P.asIdeal) ^ (r * r) := by
        rw [Finset.prod_pow, Finset.prod_coe_sort S fun P => Ideal.absNorm P.asIdeal]
    _ ≤ _ := Nat.pow_le_pow_left (prod_norm_le S hn h) _

private theorem card_dvd_of_inj {E : Type} [Field E] [NumberField E] {N : ℕ} {H : Type} [Group H] [Finite H]
    (ρ : H →* Matrix (Fin N) (Fin N) E) (hρ : Function.Injective ρ) :
    Nat.card H ∣ 8 ^ (Module.finrank ℚ E * N) * (2 * (Module.finrank ℚ E * N)).factorial := by
  let s : Set (Fin N → E) := Set.range fun p : H × Fin N => (ρ p.1).mulVec (Pi.single p.2 1)
  let L : Submodule (𝓞 E) (Fin N → E) := Submodule.span (𝓞 E) s
  have hf : L.FG := Submodule.fg_span (Set.finite_range _)
  have hs : Submodule.span E (L : Set (Fin N → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), by simp only [map_one, Matrix.one_mulVec, Pi.basisFun_apply]⟩
  have hL : ∀ h, ∀ x ∈ L, (ρ h).mulVec x ∈ L := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact Submodule.subset_span ⟨(h * p.1, p.2), by simp only [map_mul, Matrix.mulVec_mulVec]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact L.add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact L.smul_mem a hx
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StabOrder.exists_faithful L hf hs ρ hρ hL
  have e := (MonoidHom.ofInjective hψ).toEquiv
  rw [Nat.card_congr e]
  exact GlobalTheory.card_finite_subgroup_GL_int_dvd _ ψ.range (Finite.of_equiv _ e)

private theorem exists_rat {D : D7} (V : HSp D) :
    ∃ ρ : GQ V →* Matrix (Fin V.rank) (Fin V.rank) D.host.E, Function.Injective ρ := by
  haveI : Nontrivial (AF D.host.F) :=
    (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  haveI : Nontrivial (TensorProduct D.host.F (AF D.host.F) D.host.E) :=
    (Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective :
      Function.Injective (Algebra.TensorProduct.includeLeft :
        AF D.host.F →ₐ[D.host.F] TensorProduct D.host.F (AF D.host.F) D.host.E)).nontrivial
  have hi : Function.Injective (incA D) := (incA D).injective
  have hex : ∀ g : GQ V, ∃ u : Matrix (Fin V.rank) (Fin V.rank) D.host.E, u.map (incA D) = (matHom V g.1).1 := by
    rintro ⟨g, u, -, hu⟩
    exact ⟨u.1, congrArg Units.val hu⟩
  choose u hu using hex
  refine ⟨⟨⟨u, ?_⟩, fun g h => ?_⟩, fun g h e => ?_⟩
  · apply Matrix.map_injective hi
    change (u 1).map (incA D) = (1 : Matrix _ _ _).map (incA D)
    rw [hu, Matrix.map_one _ (map_zero _) (map_one _), Subgroup.coe_one, map_one, Units.val_one]
  · apply Matrix.map_injective hi
    change (u (g * h)).map (incA D) = (u g * u h).map (incA D)
    rw [Matrix.map_mul, hu, hu, hu, Subgroup.coe_mul, map_mul, Units.val_mul]
  · have e' : u g = u h := e
    have h2 := hu g
    rw [e', hu] at h2
    exact Subtype.ext (Subtype.ext (Units.ext h2.symm))

private theorem dgam_dvd {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) :
    (A.fam.R t).S.DGam ∣ 8 ^ (2 * D.R.f * D.R.rankX') * (2 * (2 * D.R.f * D.R.rankX')).factorial := by
  change (A.MtildeCSD t).DGam ∣ _
  refine Finset.lcm_dvd fun (c : (A.MtildeCSD t).Cl) _ => ?_
  obtain ⟨ρ, hρ⟩ := exists_rat D.sp.X'
  let e := (R.B.R t).pres.stabI c
  have h := card_dvd_of_inj (H := (A.MtildeCSD t).Gam c) (ρ.comp ((Subgroup.subtype _).comp e.toMonoidHom))
    (hρ.comp (Subtype.val_injective.comp e.injective))
  rw [GlobalTheory.StabOrder.finrank_host, Nat.card_eq_fintype_card] at h
  rw [← D.sp.X'_rank]
  exact h

private theorem card_le {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.toLevCh.Is A.μ0)
    (P : Subgroup Γ) : Nat.card P ≤ (D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * (D.R.r * D.R.r)) := by
  have h1 := card_levelQuotientGroup_le_prod_absNorm_pow_sq R.Pg (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero) (fun PP hPP => by
    obtain ⟨k, hk⟩ := (h.Pg PP).1 hPP
    have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := Formalism.L2.Host.PiBar.overP _ hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h2
    · exact Ideal.mul_mem_left _ _ h2) D.R.r
  rw [GlobalTheory.StabOrder.finrank_host, ← Nat.card_congr R.eG.toEquiv] at h1
  exact (Nat.card_le_card_of_injective _ P.subtype_injective).trans h1

private theorem num {g0 g1 f r ρ N N' m d a c : ℕ} {L b : ℝ} (hL : 1 ≤ L) (hb : b = Real.exp L)
    (h0 : 0 < g0) (h1 : 0 < g1) (l0 : Real.log g0 ≤ 9 * L + 1) (l1 : Real.log g1 ≤ 9 * L + 1)
    (hr : r ≤ N) (hρ : ρ ≤ N) (hN : N ≤ N') (hm : 4 ≤ m) (hf : 1 ≤ f) (hd : 1 ≤ d)
    (hs : (m : ℝ) * f * (N : ℝ) ^ 2 * d ≤ b)
    (ha : a ≤ (g0 * g1) ^ (2 * f * (r * r))) (hc : c ∣ 8 ^ (2 * f * ρ) * (2 * (2 * f * ρ)).factorial) :
    (a : ℝ) * c ≤ Real.exp (50 * f * N' * b * L) := by
  have hb1 : 1 ≤ b := hb ▸ Real.one_le_exp (by linarith)
  have hNN : N ≤ N ^ 2 := Nat.le_self_pow two_ne_zero N
  have k1 : 2 * (2 * f * ρ) ≤ m * f * N ^ 2 * d :=
    calc 2 * (2 * f * ρ) = 4 * f * ρ * 1 := by ring
      _ ≤ _ := by gcongr; exact hρ.trans hNN
  have k2 : N ≤ m * f * N ^ 2 * d :=
    calc N = 1 * 1 * N * 1 := by ring
      _ ≤ _ := by gcongr; omega
  have k1' : ((2 * (2 * f * ρ) : ℕ) : ℝ) ≤ Real.exp L := by
    rw [← hb]; exact le_trans (by exact_mod_cast k1) hs
  have k2' : (N : ℝ) ≤ b := le_trans (by exact_mod_cast k2) hs
  have g0' : (g0 : ℝ) ≤ Real.exp (10 * L) := (Real.log_le_iff_le_exp (by exact_mod_cast h0)).1 (by linarith)
  have g1' : (g1 : ℝ) ≤ Real.exp (10 * L) := (Real.log_le_iff_le_exp (by exact_mod_cast h1)).1 (by linarith)
  have h8 : (8 : ℝ) ≤ Real.exp (3 * L) := by
    have := Real.exp_one_gt_two
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ Real.exp L ^ 3 := by gcongr; exact this.le.trans (Real.exp_le_exp.2 hL)
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have ha' : (a : ℝ) ≤ Real.exp (40 * f * (r * r) * L) :=
    calc (a : ℝ) ≤ ((g0 : ℝ) * g1) ^ (2 * f * (r * r)) := by exact_mod_cast ha
      _ ≤ (Real.exp (10 * L) * Real.exp (10 * L)) ^ (2 * f * (r * r)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hc1 : c ≤ 8 ^ (2 * f * ρ) * (2 * (2 * f * ρ)) ^ (2 * (2 * f * ρ)) :=
    (Nat.le_of_dvd (by positivity) hc).trans (Nat.mul_le_mul_left _ (Nat.factorial_le_pow _))
  have hc' : (c : ℝ) ≤ Real.exp (10 * f * ρ * L) :=
    calc (c : ℝ) ≤ (8 : ℝ) ^ (2 * f * ρ) * ((2 * (2 * f * ρ) : ℕ) : ℝ) ^ (2 * (2 * f * ρ)) := by exact_mod_cast hc1
      _ ≤ Real.exp (3 * L) ^ (2 * f * ρ) * Real.exp L ^ (2 * (2 * f * ρ)) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hL0 : 0 ≤ L := by linarith
  have r1 : (r : ℝ) ≤ N' := by exact_mod_cast hr.trans hN
  have r2 : (r : ℝ) ≤ b := le_trans (by exact_mod_cast hr) k2'
  have r3 : (ρ : ℝ) ≤ N' * b := le_trans (by exact_mod_cast hρ.trans hN) (le_mul_of_one_le_right (by positivity) hb1)
  calc (a : ℝ) * c ≤ Real.exp (40 * f * (r * r) * L) * Real.exp (10 * f * ρ * L) := by gcongr
    _ ≤ Real.exp (40 * f * (N' * b) * L) * Real.exp (10 * f * (N' * b) * L) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end GlobalTheory.SumSize.GamSize

open GlobalTheory.SumSize.GamSize in
theorem _root_.GlobalTheory.T.kernelLossBound_nonneg_and_level_card_le_exp : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch C b => 0 ≤ bOne ch.G C b ∧
  (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b) := by
  refine ⟨0, fun CF _ => ⟨50, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ => ?_⟩⟩⟩
  obtain ⟨-, -, hmf, hm, -, hs, -, hg, -⟩ := hS.size
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have hlog : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb0 : 0 ≤ large₂.sc.b := (Real.exp_pos _).le
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hρ : D.R.rankX' ≤ D.R.N D.R.m := by
    simp only [Ranks.rankX', Ranks.N, Ranks.r, mul_add, mul_one]; omega
  have hr : D.R.r ≤ D.R.N D.R.m := le_trans (Nat.le_add_right _ _) hρ
  have hN : D.R.N D.R.m ≤ bigN D := Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  refine ⟨?_, ?_⟩
  · unfold bOne
    rw [hlog]
    positivity
  · refine (num hL hb (D.host.g_prime 0).pos (D.host.g_prime 1).pos (hg 0) (hg 1) hr hρ hN (by omega) hf hd hs
      (card_le R hS.core.lev F.P0) (dgam_dvd R A.μ0)).trans (Real.exp_le_exp.2 ?_)
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h1 : 50 * (D.R.f : ℝ) * bigN D * large₂.sc.b * large₂.sc.L ≤ aOne ch.G C large₂.sc.b := by
      unfold aOne
      rw [hlog]
      refine le_add_of_le_of_nonneg ?_ (by positivity)
      gcongr
    exact h1.trans (le_mul_of_one_le_left (le_trans (by positivity) h1) hm1)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointIntegralFrameMemSpanEigenLattice
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem GlobalTheory.PtDeg.intFrame_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hyT G t' n n' m1' m2' h1 h2 C a y' hchg hint i
  obtain ⟨v', hv', hv'φ⟩ := _root_.GlobalTheory.LieLatGen.exists_isLieBasis_fibre E H K B t₀ m2 F T iK t' n'
  obtain ⟨vV, hvV, hvVM⟩ := _root_.GlobalTheory.LieSpan.exists_isLieBasis_span E H K B F 𝔓 T iK hiK ρV hρV G n
  choose M w hMw hMn hMspan using hvVM
  obtain ⟨ub, hubT, -, -, hubu⟩ := hint
  obtain ⟨u', hu'1, hu'2⟩ := hubu ρ i
  obtain ⟨av, w₁, hw₁, hw₁c⟩ := _root_.GlobalTheory.PtDeg.LieModel.generic_coords_in_span E H K B t₀ m2 F T iK ρV hρV G t' n n' m2' h2 v' hv' hv'φ vV M hvV
    (fun k => ⟨w k, hMw k, hMn k⟩) (ub ρ i) u' (hubT ρ i) hu'2
  have hbase : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    rw [← hw₁]; exact Over.w w₁
  obtain ⟨w₂, hw₂, hw₂c⟩ := GlobalTheory.T.framedPoint_genericFibre_coordinates_eq_frame E H Dw l Xo c K y B t₀ m1 m2 F ρ u hu T iK yT hyT t' n' m1' h1 v' hv'
    hv'φ C a y' hchg i u' hbase hu'1
  obtain rfl : w₁ = w₂ := Over.OverMorphism.ext (hw₁.trans hw₂.symm)
  have htan : IsTangent w₁ :=
    (GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1).2.1 _ _ hw₁c
  have heq := (hv'.2 w₁ htan).unique hw₁c hw₂c
  have hWlie : (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V
      ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
    rw [← heq]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hMspan k)
  obtain ⟨r', -, hr'⟩ := _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat K B.pol F (𝓞 E) B.t.act
  have hueig : ∀ j a, r' a (u j) = ((tt a : 𝓞 K) : K) • u j := by
    intro j a
    have := ((hr' tt (u j)).2).1 (_root_.GlobalTheory.PtDeg.frameCoord_mem_span_eigLat E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu j) a
    rw [this, ← algebraMap_smul K (tt a) (u j)]
  have hx := _root_.GlobalTheory.EigenSpanSat.span_eigen_sat K F.P₀.g F.lieLat (𝓞 E) (fun a => LinearMap.toMatrix' (r' a))
    (fun a => ((tt a : 𝓞 K) : K)) 𝔓 T iK hiK (_root_.GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K B.pol F).1 _ hWlie (fun a => by
      rw [Matrix.mulVec_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, smul_comm]
      congr 1
      funext k
      rw [show (fun k => iK (u j k)) = iK ∘ u j from rfl, ← RingHom.map_mulVec, LinearMap.toMatrix'_mulVec, hueig j a]
      simp)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨c', ⟨hc1, hc2⟩, rfl⟩
  refine ⟨c', (hr' tt c').1.2 ⟨hc1, fun a => ?_⟩, rfl⟩
  have := hc2 a
  rw [LinearMap.toMatrix'_mulVec] at this
  rw [this, ← algebraMap_smul K (tt a) c']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerCompositionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_composition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.ThKEvAdm.comp_mem_adm | exact GlobalTheory.ThKEvAdm.comp_mem_adm | (intros; apply GlobalTheory.ThKEvAdm.comp_mem_adm <;> assumption)
end

