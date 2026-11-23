module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Definitions.Foundations.ReferenceTupleNeBaseTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianGrowthConjTorsionTranslatesVacuum
section
namespace GlobalTheory.ConjGrowth

section SlopeTestRemainingChoices

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ConjJet
open scoped BigOperators

theorem fnConj_sum (D : D7) {N N' n : ℕ} (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (c : Fin n → M)
    (F : Fin n → VC D N N' → ℂ) (hF : ∀ i, Differentiable ℂ (F i)) (hM : ∀ i, CoefIn D (F i) M)
    (hd : ∀ i, Differentiable ℂ (fnConj D M ρ (F i))) (h0 : ∀ i, fnConj D M ρ (F i) ≠ 0) :
    fnConj D M ρ (fun z => ∑ i, (c i : ℂ) * F i z) = fun z => ∑ i, ρ (c i) * fnConj D M ρ (F i) z := by
  funext z
  have ht : ∀ α, TaylorLogMetric.taylor D (fun z => ∑ i, (c i : ℂ) * F i z) α =
      ((∑ i, c i * ⟨_, hM i α⟩ : M) : ℂ) := by
    intro α
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.ConjSeries.taylor_eq_coeff, taylorDir_sum _ _ fun i _ =>
      GlobalTheory.ProdThetaConj.an0 ((hF i).const_mul (c i : ℂ)), map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← GlobalTheory.ConjSeries.taylor_eq_coeff, GlobalTheory.ProdThetaConj.taylor_const_mul (hF i)]
  have hcj : ∀ x : M, cj M ρ x = ρ x := fun x => by simp [cj, TaylorLogMetric.liftM]
  have hs : HasSum (fun α => ∑ i, ρ (c i) * (TaylorLogMetric.taylor D (fnConj D M ρ (F i)) α * mono D α z))
      (∑ i, ρ (c i) * fnConj D M ρ (F i) z) :=
    hasSum_sum fun i _ => (GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' _ (hd i) z).mul_left _
  rw [← hs.tsum_eq]
  refine tsum_congr fun α => ?_
  change cj M ρ _ * _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ht, hcj, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(GlobalTheory.ConjSeries.taylor_fnConj D N N' M ρ (F i) (hd i) (h0 i)).1 α, map_mul, mul_assoc, ← hcj ⟨_, hM i α⟩]

theorem vBar_vBar (D : D7) {N N' : ℕ} (z : VC D N N') : vBar D (vBar D z) = z := by
  funext τ i j
  simp [vBar]

theorem cBar_cBar (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) : cBar D (cBar D G) = G := by
  funext z
  simp [cBar, vBar_vBar]

def Facts (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E))
    (G : VC D a d → ℂ) (ρ : Qbar →ₐ[ℚ] ℂ) : Prop :=
  0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧ fnConj D Qbar ρ G ≠ 0 ∧
    (∀ y, LaQ D (tor0 D cc δ) L L' y → ∃ y', fnConj D Qbar ρ (U D (tor0 D cc δ) y G) =
      U D (torConj D (tor0 D cc δ) Qbar ρ) y' (fnConj D Qbar ρ G)) ∧
    ∀ x z, ‖U D (torConj D (tor0 D cc δ) Qbar ρ) x (fnConj D Qbar ρ G) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) *
        normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
          (fnConj D Qbar ρ G) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ)))

theorem facts_fix (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) :
    Facts D cc δ L L' G ρ := by
  have hGT := vacuum_mem_thetaSpace_pair D hI cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (hI.t0Ex cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := hI.curve cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := hI.perm Qbar ρ hρ hdata.1
  refine ⟨by rw [hΛ]; exact area_pos D hI.g1 cc' δ' hc', ?_, fun y hy => ?_, fun x z => ?_⟩
  · intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hI.g1 cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  · obtain ⟨m, hm, hmy⟩ := id hy
    obtain ⟨y', hy', -⟩ := hI.galEx cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy
      (by omega)
    have hgal := (hI.gal cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m
      hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA)
      (by rw [comb_one]; exact hAU y hy)).1
    rw [comb_one] at hgal
    exact ⟨y', hgal⟩
  · have := sup_perm D hI.g1 cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
      hTh x z
    rw [Hf_re, ← mul_div_assoc] at this
    exact this

theorem facts_all (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (ρ : Qbar →ₐ[ℚ] ℂ) :
    Facts D cc δ L L' G ρ := by
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hfix | hfix, htor, hbar⟩ := hI.bar cc δ hc Qbar ρ hdata
  · exact facts_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG ρ hfix
  obtain ⟨k1, k2, k3, k4⟩ := facts_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG _ hfix
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
  rw [U_zero] at hn2
  have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
      (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
    congrArg Tor.abelian₂ htor
  rw [hL, area_conj] at k1 k4
  rw [(hbar a d L L' G).1] at k2 k3 k4
  rw [htor] at k3 k4
  rw [hn2] at k4
  have hU := (hbar a d L L' (fnConj D Qbar ρ G)).2.1
  refine ⟨k1, fun h => k2 ?_, fun y hy => ?_, fun x z => ?_⟩
  · rw [h]
    funext z
    simp [cBar]
  · obtain ⟨y', hy'⟩ := k3 y hy
    refine ⟨vBar D y', ?_⟩
    rw [(hbar a d L L' _).1, ← vBar_vBar D y', ← hU] at hy'
    have := congrArg (cBar D) hy'
    rwa [cBar_cBar, cBar_cBar] at this
  · have := k4 (vBar D x) (vBar D z)
    rw [← hU] at this
    simpa only [cBar, vBar_vBar, vBar, RCLike.norm_conj, Complex.conj_conj] using this

end SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem conj_growth : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
  ∀ (a b : ℕ) (e0 : VC D a b → ℂ), Even (a * b) → oddE0 D cc δ t0 a b e0 →
  ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
  ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), 0 < k →
  (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) →
  ∀ (ρ : Qbar →ₐ[ℚ] ℂ) (t' : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t' →
    0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧
    CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) Qbar ∧
    Differentiable ℂ (fnConj D Qbar ρ fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) ∧
    ∀ z, ‖fnConj D Qbar ρ (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) *
        nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t') ^ (fF D * a * b) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  intro D hI cc δ t0 hc ht a b e0 hev he Ls Lt h1 h2 κ hκ k n r s hk hs hr ρ t' ht'
  have hsd : ∀ N, SD D (stdL D N) := fun N => by
    obtain ⟨Lt, h, h1, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    exact h1 ▸ (h 1).2
  have hG := GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual D hI cc δ t0 hc ht a b _ _ Ls Lt (hsd a) (hsd b) h1 h2 e0 he.2.2.2.1
  change ThetaVectorUpToUnits D (tor0 D cc δ) t0 Ls Lt
    (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) at hG
  generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0 = G at hG ⊢
  have hGT := GlobalTheory.ConjJet.vacuum_mem_thetaSpace_pair D hI cc δ t0 hc ht a b Ls Lt h1 h2 G hG
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, hAU, hAC, -⟩ := hI.alg cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨k1, k2, k3, k4⟩ := facts_all D hI cc δ t0 hc ht a b Ls Lt h1 h2 hev G hG ρ
  rw [hN] at k4
  obtain ⟨hκ1, hκ2⟩ := hκ
  have hq : ∀ i, LaQ D (tor0 D cc δ) Ls Lt (s i) := fun i => ⟨k, hk, hs i⟩
  choose y hy using fun i => k3 (s i) (hq i)
  have he' : (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i) G z) =
      fun z => ∑ i, ((⟨κ, hκ1⟩ * r i : Qbar) : ℂ) * U D (tor0 D cc δ) (s i) G z := by
    funext z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    rfl
  have hd : ∀ i, Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) (s i) G)) := fun i => by
    rw [hy]; exact GlobalTheory.ConjJet.U_diff D _ _ _ hTh.1
  rw [he', fnConj_sum D Qbar ρ _ _ (fun i => GlobalTheory.ConjJet.U_diff D _ _ _ hGT.1) (fun i => hAU _ (hq i)) hd
    (fun i => by rw [hy]; exact GlobalTheory.ConjJet.U_ne_zero D _ _ _ k2)]
  refine ⟨k1, hAC n _ s (fun i => (⟨κ, hκ1⟩ * r i : Qbar).2) hq,
    Differentiable.fun_sum fun i _ => (hd i).const_mul _, fun z => ?_⟩
  have hb := fun i => k4 (y i) z
  have h0 := (sq_nonneg _).trans (k4 0 z)
  generalize (3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) * _ * _ : ℝ) = B at hb h0 ⊢
  have hb' : ∀ i, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) (s i) G) z‖ ≤ √B := fun i => by
    rw [hy]; exact Real.le_sqrt_of_sq_le (hb i)
  rw [← Real.le_sqrt (norm_nonneg _) h0]
  calc _ ≤ ∑ i, ‖ρ (r i)‖ * √B := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        have h3 : ‖ρ ⟨κ, hκ1⟩‖ = 1 := hκ2 ρ.toRingHom
        rw [norm_mul, map_mul, norm_mul, h3, one_mul]
        exact mul_le_mul_of_nonneg_left (hb' i) (norm_nonneg _)
    _ ≤ 1 * √B := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hr ρ.toRingHom) (Real.sqrt_nonneg _)
    _ = √B := one_mul _

end GlobalTheory.ConjGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GbigTwo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Chars)

theorem gbig_two {Q1 Q2 Q : GP} (h1 : GBig Q1) (h2 : GBig Q2)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  refine ⟨max a1 a2, fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max c1 c2, max x1 x2, fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ ?_ ?_⟩
  · exact g1 C (le_trans (le_max_left _ _) hC) D large₂ hε (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G
  · exact g2 C (le_trans (le_max_right _ _) hC) D large₂ hε (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def Carried (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) {A A' WW : HSp D} (X : Tri T A A' WW)
    (Bs : Base D.host.F D.host.E) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Γ : Geo D.sp.cm.sig A.rank A'.rank) (s : T) : Prop :=
  GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f s) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' s) ∧
    (∀ P g h, thetaKO (X.ω s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f s) P) = X.ker W.ψ W.θ s P h g) ∧
    (∀ P g h, thetaKO (X.ω' s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' s) P) = X.ker' W.ψ W.θ s P h g) ∧
    ∀ om om', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' →
      ∃ e cA cB, GlobalTheory.SquareAgree.IsOver W.ψ W.θ FA FA' FW (GlobalTheory.SqStep.chs G i j s).α (GlobalTheory.SqStep.chs G i j s).β X.m X.fd
        X.m' X.fd' (X.ω s) (X.ω' s) e Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' cA cB

end GlobalTheory.SqStepBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareCharQuotientFiniteUnitIdeleRootOfUnity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareCharUnit

theorem exists_root_of_locIn {D : D7} {K : Type} [Field K] (σ : K →+* ℂ) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E)
    (h : ChrEq c χ) (hL : LocIn σ χ) (x : (AE D)ˣ) (hx : Formalism.L2.Pj.FinUnit x) :
    ∃ ζ : K, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ σ ζ = ((c x : Circle) : ℂ) := by
  have hmem : ((c x : Circle) : ℂ) ∈ σ.fieldRange := by
    obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2 (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ h
    obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
      (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom x)
    rw [hprod x hx.1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
    exact prod_mem fun P _ => hL P _
  obtain ⟨ζ, hζ⟩ := hmem
  obtain ⟨-, -, -, m, hm, hpow⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c h.1.1
  refine ⟨ζ, ⟨m, hm, σ.injective ?_⟩, hζ⟩
  rw [map_pow, map_one, hζ, ← Circle.coe_pow, hpow x hx, Circle.coe_one]

theorem nu_finUnit_root : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (t : T) (x : (AE D)ˣ), Formalism.L2.Pj.FinUnit x →
    ∃ ζ : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      D.what₂.embLL ζ = (((Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) /
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) x : Circle) : ℂ) := by
  intro D T Lc sc G μ₀ hL hC i j t x hx
  have hi := i.2
  obtain ⟨a, ⟨n₁, h₁, e₁⟩, ha⟩ := exists_root_of_locIn D.what₂.embLL _ _ (hL.mu0 j) (hC.mu0 j) x hx
  obtain ⟨b, ⟨n₂, h₂, e₂⟩, hb⟩ := exists_root_of_locIn D.what₂.embLL _ _ (hL.xi t) (hC.xi t) x hx
  obtain ⟨c, ⟨n₃, h₃, e₃⟩, hc⟩ := exists_root_of_locIn D.what₂.embLL _ _
    (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)) (hC.chi (D.R.m - i) (by omega) (by omega)) x hx
  refine ⟨a * b / c, ⟨n₁ * n₂ * n₃, by positivity, ?_⟩, ?_⟩
  · rw [div_pow, mul_pow]
    have f₁ : a ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_assoc, pow_mul, e₁, one_pow]
    have f₂ : b ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_right_comm, mul_comm, pow_mul, e₂, one_pow]
    have f₃ : c ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_comm, pow_mul, e₃, one_pow]
    rw [f₁, f₂, f₃, one_mul, div_one]
  · rw [mul_div_mul_right_eq_div, map_div₀, map_mul, ha, hb, hc, MonoidHom.div_apply, Circle.coe_div]
    congr 1

end GlobalTheory.SquareCharUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfOfChars
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotWeights

open Formalism.L2.Host (HChar)
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

variable {D : D7}

theorem hasInf_of_chars {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (χ : HChar D.host.E)
    (h : ∀ x, P.W.chV'.f x ^ P.W.ep' = χ.1 (finIdl D x)) :
    χ.HasInf (GlobalTheory.Mem.Chr.embTau D) (fun τ => P.W.ep' * P.W.chV'.n τ) := by
  intro a
  have h1 := χ.2.2 a
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, mul_comm] at h1
  rw [← h (GlobalTheory.NormSum.UnramHecke.incU D a)] at h1
  have h2 := P.W.chV'.aut a
  have h3 : ((χ.inf a : ℂˣ) : ℂ) = (((P.W.chV'.f (GlobalTheory.NormSum.UnramHecke.incU D a) : ℂˣ) : ℂ) ^ P.W.ep')⁻¹ := by
    have := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one, Units.val_zpow_eq_zpow_val] at this
    exact eq_inv_of_mul_eq_one_right this
  have hf := eq_inv_of_mul_eq_one_left h2
  rw [h3, hf, inv_zpow, inv_inv, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm]
  rfl

end GlobalTheory.BotWeights

namespace GlobalTheory.BotWeights

open Formalism.L2.Host (HChar)

theorem weights_const : GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (δ t0 : ℂ), ∃ n₀ : D.what₂.Tau → ℕ,
      ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → P.n = n₀ := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G i j δ t0 => ?_⟩⟩
  have key : ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
      ((Lc.C.mu0 j / G.ch.chiH (D.R.m - i))⁻¹ : HChar D.host.E).HasInf (GlobalTheory.Mem.Chr.embTau D)
        (fun τ => P.W.ep' * P.W.chV'.n τ) := by
    intro s Q P P' hB k
    have h := hasInf_of_chars P _ hB.chars.2 k
    rw [← h]
    obtain ⟨n, hn, ho⟩ := hL.xi_fin s
    have hx := GlobalTheory.Mem.Chr.TieModel.inf_eq_one_of_order hn ho k
    have hx' : (Lc.xiH s).inf k = 1 := hx
    simp only [nuH, div_eq_mul_inv, Formalism.L2.Host.HChar.inf_inv, Formalism.L2.Host.HChar.inf_mul, hx', mul_one]
  by_cases hex : ∃ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P'
  · obtain ⟨s₀, Q₀, P₀, P₀', h₀⟩ := hex
    refine ⟨P₀.n, fun s Q P P' hB => funext fun τ => ?_⟩
    have e := congrFun (GlobalTheory.Mem.Chr.TieModel.hasInf_unique _ (GlobalTheory.Mem.Chr.TieModel.embTau_inj D)
      (GlobalTheory.Mem.Chr.TieModel.embTau_ne_conj D) (key s Q P P' hB) (key s₀ Q₀ P₀ P₀' h₀)) τ
    have w1 := P.wt τ
    have w2 := P₀.wt τ
    have d1 : (P.d : ℤ) = ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by exact_mod_cast hB.rank.2.2.1
    have d2 : (P₀.d : ℤ) = ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by exact_mod_cast h₀.rank.2.2.1
    have : (P.n τ : ℤ) = P₀.n τ := by linarith
    exact_mod_cast this
  · exact ⟨0, fun s Q P P' hB => absurd ⟨s, Q, P, P', hB⟩ hex⟩

end GlobalTheory.BotWeights
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementNegativeIndexPred
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplementSig

open Matrix

theorem hasSignature_plane : Formalism.UG.HasSignature (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp)
    (Matrix.of fun i k => Sum.elim (fun _ => ![1, 1 / 2] i) (fun _ => ![1, -1 / 2] i) k) ?_
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat] <;> norm_num

theorem sig : ∀ (D : D7) (S S₁ : HSp D) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) (q : ℕ), S.rank = S₁.rank + 2 →
    Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ u, S.hT x (ι u) = 0 ∧ S.hT y (ι u) = 0) → NegIdx S (q + 1) →
    ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S₁.gram.map τ) (S₁.rank - q) q := by
  intro D S S₁ ι x y q hr hι hxx hyy hxy ho hneg τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ

  have hS : Formalism.UG.HasSignature (S.gram.map τ) (S.rank - (q + 1)) (q + 1) := by
    obtain ⟨ρ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D τ
    · subst hσ
      simpa [gramAt] using hneg ρ
    · subst hσ
      have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hneg ρ)
      rw [Matrix.map_map] at h1
      exact h1
  obtain ⟨⟨a, b⟩, h₁⟩ := GlobalTheory.WittLow.exists_sig S₁ τ
  have c₁ := (Formalism.UG.P.sig_data _ _ _ h₁).1
  have cS := (Formalism.UG.P.sig_data _ _ _ hS).1
  simp only [Fintype.card_fin] at c₁ cS
  let v : Fin S₁.rank ⊕ Fin 2 → S.V := Sum.elim (fun i => ι (S₁.frame i)) ![x, y]
  have hyx : S.hT y x = 1 := by
    have h := S.herm.eq x y
    rw [hxy, map_one] at h
    exact h.symm
  have hv : (Matrix.of fun k l => S.hT (v k) (v l)) =
      fromBlocks S₁.gram 0 0 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E) := by
    ext (i | i) (j | j)
    · simp only [v, Matrix.of_apply, fromBlocks_apply₁₁, Sum.elim_inl, HSpace.gram]; exact hι _ _
    · fin_cases j
      · have h := S.herm.eq x (ι (S₁.frame i))
        rw [(ho _).1, map_zero] at h
        simp [v, ← h]
      · have h := S.herm.eq y (ι (S₁.frame i))
        rw [(ho _).2, map_zero] at h
        simp [v, ← h]
    · fin_cases i
      · simpa [v] using (ho _).1
      · simpa [v] using (ho _).2
    · fin_cases i <;> fin_cases j <;> simp [v, hxx, hyy, hxy, hyx]
  have hF : Formalism.UG.HasSignature ((Matrix.of fun k l => S.hT (v k) (v l)).map τ) (a + 1) (b + 1) := by
    rw [hv, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero τ), Matrix.map_zero _ (map_zero τ)]
    have e : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E).map τ = !![0, 1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [e]
    exact GlobalTheory.FrameComplement.hasSignature_fromBlocks h₁ hasSignature_plane
  have key := Formalism.BasicNotions.sig_family S τ hτ v hF hS
  have hb : b = q := by omega
  have ha : a = S₁.rank - q := by omega
  subst hb ha
  exact h₁

end GlobalTheory.PlaneComplementSig
end
end

