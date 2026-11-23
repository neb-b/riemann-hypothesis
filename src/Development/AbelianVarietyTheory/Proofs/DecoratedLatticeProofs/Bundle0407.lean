module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0400
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalRingCardinality.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLatMonoId
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem sum_pair_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    star x ⬝ᵥ ((Aᴴ * B) *ᵥ y) = star (A *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

variable (d : HypDec S S₀ ρ)

theorem pair_decomp (x y : Fin S.rank → D.host.E) :
    star x ⬝ᵥ (S.gram *ᵥ y) = star (d.qY *ᵥ x) ⬝ᵥ (d.qX *ᵥ y) + star (d.q0 *ᵥ x) ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) +
      star (d.qX *ᵥ x) ⬝ᵥ (d.qY *ᵥ y) := by
  rw [gram_eq d, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, pair_mul, pair_mul, pair_mul,
    ← Matrix.mulVec_mulVec]

theorem star_single (i : Fin ρ) (b : D.host.E) : star (Pi.single i b : Fin ρ → D.host.E) = Pi.single i (star b) := by
  funext j; by_cases h : j = i <;> simp [h, Pi.single_apply]

theorem pair_e (i : Fin ρ) (b : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e *ᵥ Pi.single i b) ⬝ᵥ (S.gram *ᵥ y) = star b * (d.qY *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e, wittDecomposition_coreProj_mul_e_eq_zero, qY_e, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_e' (i : Fin ρ) (c : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e' *ᵥ Pi.single i c) ⬝ᵥ (S.gram *ᵥ y) = star c * (d.qX *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e', wittZeroProjection_mul_dualBasis_eq_zero, qY_e', Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_i₀ (x₀ : Fin S₀.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.i₀ *ᵥ x₀) ⬝ᵥ (S.gram *ᵥ y) = star x₀ ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_i₀, wittDecomposition_coreProj_mul_core_eq_one, qY_i₀, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add]

theorem decomp (y : Fin S.rank → D.host.E) : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
    d.sum_eq_one_rat, Matrix.one_mulVec]

theorem exists_ne_zero {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ b ∈ 𝔟, b ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (FractionalIdeal.eq_zero_iff.2 hc)

theorem exists_ne_zero_dualC (𝔟 : FI D) : ∃ c ∈ dualC 𝔟, c ≠ 0 := by
  obtain ⟨a, ha, hint⟩ := 𝔟.isFractional
  refine ⟨star (algebraMap (𝓞 D.host.E) D.host.E a), fun b hb => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hint b hb
    have : star b * star (algebraMap (𝓞 D.host.E) D.host.E a) = star (algebraMap (𝓞 D.host.E) D.host.E r) := by
      rw [hr, Algebra.smul_def, star_mul', mul_comm]
    rw [this]
    exact GlobalTheory.HypLattice.star_mem_int ⟨r, rfl⟩
  · rw [Ne, star_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).2 (nonZeroDivisors.ne_zero ha)

theorem dualC_le_span {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ γ : D.host.E, dualC 𝔟 ≤ Submodule.span (𝓞 D.host.E) {γ} := by
  obtain ⟨β, hβ, hβ0⟩ := exists_ne_zero h
  refine ⟨(star β)⁻¹, fun c hc => ?_⟩
  obtain ⟨o, ho⟩ := hc β hβ
  have hs : star β ≠ 0 := by rwa [Ne, star_eq_zero]
  refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
  rw [Algebra.smul_def, ho, mul_comm (star β), mul_assoc, mul_inv_cancel₀ hs, mul_one]

theorem mulVec_single_smul {n : ℕ} (M : Matrix (Fin S.rank) (Fin n) D.host.E) (i : Fin n) {a b : D.host.E} (hb : b ≠ 0) :
    M *ᵥ Pi.single i a = (a * b⁻¹) • (M *ᵥ Pi.single i b) := by
  rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one]

variable {L₀ : Lat S₀} {𝔟 : ℕ → FI D}

theorem isLattice_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : Submodule.IsLattice D.host.E L₀) :
    Submodule.IsLattice D.host.E (splitL d L₀ 𝔟) := by
  choose γ hγ using fun i : Fin ρ => dualC_le_span (h𝔟 i)
  refine ⟨?_, ?_⟩
  · let T : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
      (⨆ i : Fin ρ, (𝔟 i : Submodule (𝓞 D.host.E) D.host.E).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))) ⊔
        L₀.map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ⊔
        ⨆ i : Fin ρ, (Submodule.span (𝓞 D.host.E) {γ i}).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e' *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))
    have hT : T.FG :=
      ((Submodule.fg_iSup _ fun i : Fin ρ => (FractionalIdeal.fg_of_isNoetherianRing le_rfl (𝔟 i)).map _).sup
        (hL₀.fg.map _)).sup (Submodule.fg_iSup _ fun i : Fin ρ => (Submodule.fg_span_singleton _).map _)
    refine hT.of_le fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    have hs : ∀ (M : Matrix (Fin S.rank) (Fin ρ) D.host.E) (w : Fin ρ → D.host.E), M *ᵥ w = ∑ i, w i • (M *ᵥ Pi.single i 1) := by
      intro M w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
    rw [decomp d y, hs d.e, hs d.e']
    refine add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
      (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, h2, rfl⟩)))
      (Submodule.mem_sup_right ?_)
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, h1 i, rfl⟩
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, hγ i (h3 i), rfl⟩
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isSelfDualC_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : IsSelfDualC S₀ L₀) : IsSelfDualC S (splitL d L₀ 𝔟) := by
  have hR : ∀ z : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = z) ↔ z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
    fun z => Iff.rfl
  have h0 : ∀ y₀ : Fin S₀.rank → D.host.E, y₀ ∈ L₀ ↔ ∀ x₀ ∈ L₀, star x₀ ⬝ᵥ (S₀.gram *ᵥ y₀) ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range := fun y₀ => by
    rw [hL₀.2 y₀]
    simp only [hR, sum_pair_eq]
  refine ⟨isLattice_splitL d h𝔟 hL₀.1, fun y => ?_⟩
  simp only [hR, sum_pair_eq]
  constructor
  · intro hy x hx
    obtain ⟨hy1, hy2, hy3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    obtain ⟨hx1, hx2, hx3⟩ := (mem_splitL d L₀ 𝔟 x).1 hx
    rw [pair_decomp]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) ((h0 _).1 hy2 _ hx2)) (sum_mem fun i _ => ?_)
    · have := GlobalTheory.HypLattice.star_mem_int (hx3 i _ (hy1 i))
      rwa [star_mul', star_star, mul_comm] at this
    · exact hy3 i _ (hx1 i)
  · intro hy
    refine (mem_splitL d L₀ 𝔟 y).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
    · have hi : 𝔟 i ≠ 0 := h𝔟 i
      rw [← inv_inv (𝔟 i), FractionalIdeal.mem_inv_iff (inv_ne_zero hi)]
      intro z hz
      have hc : star z ∈ dualC (𝔟 i) := fun b hb => by
        have := GlobalTheory.HypLattice.star_mem_int (GlobalTheory.HypLattice.mem_one_iff_range.1 ((FractionalIdeal.mem_inv_iff hi).1 hz b hb))
        rwa [star_mul', mul_comm] at this
      have := hy _ (e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i hc))
      rw [pair_e', star_star, mul_comm] at this
      exact GlobalTheory.HypLattice.mem_one_iff_range.2 this
    · rw [h0]
      intro x₀ hx₀
      have := hy _ (i₀_mem (d := d) (𝔟 := 𝔟) hx₀)
      rwa [pair_i₀] at this
    · intro b hb
      have := hy _ (e_mem (L₀ := L₀) (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hb))
      rwa [pair_e] at this

end GlobalTheory.SeeSaw.SplitLat

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStepPointOfChartBasePoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.KxPoint

theorem pointOf_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {C : Type} (chOf : (I.stp u a i).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : C → Subgroup (TC.GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → TC.GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : C → TC.GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ β, (∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, TC.PtOf (k β) q) → (∀ P ∈ I.SQ, P ∉ I.Q a → (k β).1.map (adAt B.host.F P) = 1) → ∃ (b0 : Idx I.sel (I.tup a) (I.idx a) i) (p0 : PtAt B.R I.sel (I.tup a) (I.cst a) u i), TC.PtOf (k β) (extTo I.SQ p0.1.1) ∧ p0.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) ∧ ∀ c, chOf c = β → c.1 = b0 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn p0 := by
  intro B X I hI hP u a i hi C chOf Lb U chi y st k hR β hq hk
  have hPr : (B.primes X).Ok := (base_fields_primes_ok B X).2.1
  have hd := ChEx.q_disj I hI a
  obtain ⟨c₀, hc₀⟩ := hR.onto β
  obtain ⟨q, hqk⟩ := hq
  obtain ⟨p, hpk, hpN⟩ := hR.k_std β
  have hqN : q.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) := by
    rw [← hpN]
    exact GlobalTheory.BaseCosetPt.lat_eq_of_carries
      (Formalism.L2.Ker.full_of_sd ⟨q.deco.2.lat, q.deco.2.uni⟩)
      (Formalism.L2.Ker.full_of_sd ⟨p.deco.2.lat, p.deco.2.uni⟩) hqk.lat hpk.lat
  obtain ⟨r', hr'1, hr'2, hr'3⟩ := ChExM.exists_pt_inv hd ((I.stp u a i).rep c₀) q
  have hcos : cosetIn r' = cosetIn ((I.stp u a i).rep c₀) :=
    (ChExM.cosetIn_iff hd (MemChart.hqG hPr) _ _).2 ⟨hr'2, hr'3⟩
  refine ⟨c₀.1, r', ?_, ?_, ?_⟩
  · rw [hr'1]
    refine ⟨hqk.uni, hqk.lat, hqk.f, hqk.be, fun P i' j => ?_⟩
    rw [extTo_fr]
    by_cases hPQ : P.1 ∈ I.Q a
    · rw [ptFr_of_mem q (hd P.1 hPQ) hPQ]
      exact hqk.fr ⟨P.1, hPQ⟩ i' j
    · have hPG : P.1 ∉ (B.primes X).vGs := by
        obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 P.2
        exact ChEx.q_disj I hI b P.1 hb
      have hfr : ptFr q P.1 = 1 := by
        unfold ptFr
        rw [dite_eq_right hPG, dite_eq_right hPQ, hqN]
        unfold GlobalTheory.Mem.Col2.latFr
        exact if_pos rfl
      have hkP := congrFun (congrFun (hk P.1 P.2 hPQ) i') j
      rw [hfr]
      simp only [Matrix.map_apply] at hkP
      rw [hkP]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · rw [hr'1]; exact hqN
  · intro c hc
    obtain ⟨h1, h2⟩ := (hR.key c c₀).1 (hc.trans hc₀.symm)
    exact ⟨h1, h2.trans hcos.symm⟩

end GlobalTheory.KxPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposi
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section

namespace GlobalTheory.HypSumWitt

open scoped ComplexOrder

theorem gramAt_hypSp (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ =
      (Matrix.fromBlocks (1 : Matrix (Fin t) (Fin t) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  unfold gramAt
  rw [GlobalTheory.Doubling.gram_hdbl]
  ext i j
  simp [GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, GlobalTheory.OrthSumSp.posSp_gram]
  generalize finSumFinEquiv.symm i = a
  generalize finSumFinEquiv.symm j = b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, apply_ite]

theorem gsq (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ * gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ = 1 := by
  rw [gramAt_hypSp, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem gct (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    (gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ)ᴴ = gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ := by
  rw [gramAt_hypSp, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  simp

theorem exists_hypSum_orthDec_hypDec : ∀ (D : D7) (W : HSp D) (t : ℕ), HSpace.SigOK W → ∃ (H B : HSp D) (_ : OrthDec B W H) (_ : HypDec B W t), HSpace.SigOK H ∧ HSpace.SigOK B ∧ H.rank = 2 * t ∧ (∀ τ, H.sig τ = (t, t)) ∧ ∃ sH : RealMat H, ∀ τ, IsCartanInv (gramAt D H τ) (sH τ) := by
  intro D W t hW
  refine ⟨GlobalTheory.OrthSumSp.hypSp D t, _, GlobalTheory.OrthSumSp.orthSumDec D W _, GlobalTheory.OrthSumSp.hypSumDec D W t,
    GlobalTheory.OrthSumSp.hypSp_sigOK D t, GlobalTheory.Doubling.sigOK_hsum hW (GlobalTheory.OrthSumSp.hypSp_sigOK D t), ?_,
    GlobalTheory.OrthSumSp.hypSp_sig D t, fun τ => gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ, fun τ => ⟨gsq D t τ, ?_, ?_⟩⟩
  · show t + t = 2 * t; omega
  · rw [gct, Matrix.mul_assoc, gsq, Matrix.mul_one]
  · rw [gsq]; exact Matrix.PosDef.one
end GlobalTheory.HypSumWitt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTranslatesOfValuesFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm

theorem isTr_unique {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {g : ι → Matrix (Fin n) (Fin n) ℂ}
    {y₁ y₂ y' : Frames G} (h₁ : IsTr g y₁ y') (h₂ : IsTr g y₂ y') : y₁.1 = y₂.1 := by
  funext τ
  have hu : IsUnit (g τ).det := by
    have h := y'.2 τ
    rw [h₁ τ, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have e : g τ * y₁.1 τ = g τ * y₂.1 τ := by rw [← h₁ τ, ← h₂ τ]
  calc y₁.1 τ = (g τ)⁻¹ * (g τ * y₁.1 τ) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (g τ)⁻¹ * (g τ * y₂.1 τ) := by rw [e]
    _ = y₂.1 τ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem jOf_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), ∃ J, JOf R j J := by
  intro B X I _ _ l Z G _ _ Pl0 T F Ks _ _ _ R _ j
  refine ⟨fun v k z' => if h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1),
      IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' then j v ⟨h.choose.1, h.choose.2⟩ else 0, ?_⟩
  intro v k _ z z' hz
  have h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' := ⟨z, hz⟩
  simp only [dif_pos h]
  have e := isTr_unique h.choose_spec hz
  exact congrArg (j v) (Subtype.ext e)

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.StdOff

section Gen

open GlobalTheory.FinPl GlobalTheory.FinPl.AlmostAll GlobalTheory.FinPl.AeUnit

variable {D : D7}

theorem incA_mul_mem_intAt {v : Pl D} {c : D.host.E} {N : ℕ} (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal)
    (hint : IsIntegral ℤ ((N : D.host.E) * c)) : ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro a ha
  have hv' : ((N : ℤ) : 𝓞 D.host.F) ∉ v.asIdeal := by rwa [Int.cast_natCast]
  have hN : N ≠ 0 := by
    rintro rfl
    exact hv (by simp)
  have hNF : ((N : ℤ) : D.host.F) ≠ 0 := by exact_mod_cast hN
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, inv_smul_singleV_mem v N hv', ⟨(N : ℤ) • c, by rw [zsmul_eq_mul, Int.cast_natCast]; exact hint⟩, ?_⟩
  exact tmul_eq_inv_smul_tmul N hNF _ c

theorem latA_eq_latV_of {v : Pl D} {N M : ℕ} (hvN : (N : 𝓞 D.host.F) ∉ v.asIdeal) (hvM : (M : 𝓞 D.host.F) ∉ v.asIdeal)
    (hNI : ∀ a ∈ D.host.AA, ∃ b : 𝓞 D.host.E, algebraMap _ _ b = a * (N : D.host.E)) (hMI : (M : D.host.E) ∈ D.host.AA)
    (S : HSp D) (L : Lat S) : latA S L (· = v) = latV S L (· = v) := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact hvN (by simp)
  have hM : M ≠ 0 := by
    rintro rfl
    exact hvM (by simp)
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨h1, h2⟩ := smul_inv_mem hvN hα h0
    refine ⟨_, h1, h2, 1, rfl, b • x, L.smul_mem b hx, funext fun i => ?_⟩
    rw [tmul_eq hN, ← mul_assoc, mul_comm (N : D.host.E) a, ← hb, one_mul, Pi.smul_apply, Algebra.smul_def b]
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain rfl : a = 1 := ha
    obtain ⟨h1, h2⟩ := smul_inv_mem hvM hα h0
    refine ⟨_, h1, h2, (M : D.host.E), hMI, x, hx, funext fun i => ?_⟩
    rw [tmul_eq hM, one_mul]

theorem notMem_of_coprime {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsPrime) {a b : ℕ} (h : a.Coprime b) (hb : (b : R) ∈ P) :
    (a : R) ∉ P := fun ha => by
  obtain ⟨x, y, hxy⟩ : IsCoprime (a : R) (b : R) := Nat.Coprime.cast h
  exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ P.add_mem (P.mul_mem_left _ ha) (P.mul_mem_left _ hb)))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitAA_of (p : SplitPt D k) {l : ℕ} (hl : l.Prime) (hv : (l : 𝓞 D.host.F) ∈ p.v.asIdeal)
    (hq : (D.host.QS * D.host.q).Coprime l) (hd : D.host.d.Coprime l) (hc : (Ideal.absNorm D.host.ccK).Coprime l) : p.UnitAA := by
  have hb : (Ideal.absNorm D.host.𝔟).Coprime l := by
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd, GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hl, ← hl.coprime_iff_not_dvd]
    exact hq.symm
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hd4 : 2 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs2 := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hs2
    exact hd0 (neg_eq_zero.1 hs2.symm)
  have hsi : IsIntegral ℤ D.host.sqrtMinusD := IsIntegral.of_pow two_pos (by rw [hs2]; exact (isIntegral_natCast _).neg)
  refine ⟨fun a ha => ⟨incA_mul_mem_intAt (N := Ideal.absNorm D.host.ccK * D.host.d)
    (notMem_of_coprime p.v.isPrime (hc.mul_left hd) hv) ?_ a ha, incA_mul_mem_intAt (N := 1)
    (notMem_of_coprime p.v.isPrime (Nat.coprime_one_left l) hv) ?_ a ha⟩,
    latA_eq_latV_of (notMem_of_coprime p.v.isPrime hb hv) (notMem_of_coprime p.v.isPrime hc hv)
      (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)⟩
  · convert hsi using 1
    unfold Host.xi0
    push_cast
    field_simp
    linear_combination -hs2
  · have : ((1 : ℕ) : D.host.E) * D.host.xi0⁻¹ = -((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) := by
      unfold Host.xi0
      rw [Nat.cast_one, one_mul, inv_div, div_neg, div_one]
    rw [this]
    exact ((isIntegral_natCast _).mul hsi).neg

theorem mxAt_of_half (q : SplitPt D k) {m n : ℕ} {w : Mx D m n} (h : IsHalf (q.e + cA D q.e) w) : MxAt (· = q.v) w := by
  obtain ⟨ε, h1, h2⟩ := q.above
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  intro i j
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff, ← h2]
  exact h i j

theorem sec_mem_idAt (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  have h1 : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have h2 : (p.e + cA D p.e) * p.sec a = p.sec a := by
    rw [← h1, ← mul_assoc, add_mul, p.split.1, mul_comm (cA D p.e), p.split.2.1, add_zero]
  exact mxAt_of_half p (m := 1) (n := 1) (w := Matrix.of fun _ _ => p.sec a) (fun _ _ => h2) 0 0

theorem mem_latV_int {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) (v : Pl D) (y : Fin S.rank → AE D) :
    y ∈ latV S L (· = v) ↔ ∀ i, y i ∈ intAt D (· = v) :=
  GlobalTheory.FinPl.Model.mem_latV_std S L (fun x => (hL x).trans (forall_congr' fun i =>
    ⟨fun h => ⟨⟨x i, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩)) v y

end Gen

section Loc

open GlobalTheory.LatPair IsLocalRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

section Level

open GlobalTheory.FinPl

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E}

end Level

end GlobalTheory.SeeSaw.StdOff

end
end

