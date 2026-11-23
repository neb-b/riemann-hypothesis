module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0468
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixReductionEqZeroOffPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.AdjRedOff

theorem resS_idemSum_eq_zero {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hI : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {PP : Pl D.host.E} (hPP : PP ∉ P) :
    Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D e, hI⟩ = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  choose hi _ using fun Q : P => GlobalTheory.IdemRes.resS_idem_eq_one D (es Q) Q (hes Q Q.2)
  let t : P → Formalism.L2.Herm.intAf D.host.F D.host.E := fun Q => ⟨toEAf D (es Q), hi Q⟩
  have e1 : (⟨toEAf D (∑ Q ∈ P, es Q), hI⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ Q, t Q := by
    apply Subtype.ext
    change toEAf D (∑ Q ∈ P, es Q) = _
    rw [← Finset.sum_coe_sort P]
    refine (GlobalTheory.TameProd.map_sum_ringHom (toEAf D) _ _).trans ?_
    exact (map_sum (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype t Finset.univ).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum]
  refine Finset.sum_eq_zero fun Q _ => ?_
  exact GlobalTheory.TameProd.resS_idem_eq_zero (hes Q Q.2) (fun h => hPP (by rw [← h]; exact Q.2)) _

end GlobalTheory.AdjRedOff

theorem GlobalTheory.AdjRedOff.redM_frMapAdj_off : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  ∀ PP : Pl D.host.E, PP ∉ R.Pg ∪ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io _ e he x hx hint PP hPP
  obtain ⟨hI, -⟩ := GlobalTheory.TameProd.resS_idemSum he
  ext a b
  have hm := hint a b
  simp only [redM, dif_pos hm, Matrix.zero_apply]
  have e1 : (⟨frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b, hm⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨toEAf D e, hI⟩ * ⟨frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b, hm⟩ :=
    Subtype.ext (GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ hx a b).symm
  rw [e1, map_mul, GlobalTheory.AdjRedOff.resS_idemSum_eq_zero he hI hPP, zero_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRepApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

def conjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep S T :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd (Equiv.refl (WO S T))).comp ω

theorem conjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (p : GA D S × GA D T) (F : WO S T → ℂ) :
    conjRep ω p F = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (ω p (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F)) := rfl

def adjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep T S :=
  GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint (conjRep ω)

theorem adjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (h : GA D T) (g : GA D S) (F : WO T S → ℂ) :
    adjRep ω (h, g) F = fun y => ω (g, h) (fun x => F (adjO T S x)) (adjO S T y) := by
  funext y
  show starRingEnd ℂ (starRingEnd ℂ (ω (g, h) (fun x => starRingEnd ℂ (starRingEnd ℂ (F (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x))))
    (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S y))) = _
  simp only [Complex.conj_conj, GlobalTheory.ConjAdjWeil.dagger_eq]


open GlobalTheory.FockAdjoint in
def swapHom {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank →ₐ[ℂ] PolF D S.rank T.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1)


open GlobalTheory.FockAdjoint in
def swapInv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D S.rank T.rank →ₐ[ℂ] PolF D T.rank S.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1)

open GlobalTheory.FockAdjoint in
theorem swapHom_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D T.rank S.rank) :
    swapHom A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapHom]

open GlobalTheory.FockAdjoint in
theorem swapInv_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D S.rank T.rank) :
    swapInv A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapInv]


open GlobalTheory.FockAdjoint in
def swapEquiv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank ≃ₐ[ℂ] PolF D S.rank T.rank :=
  AlgEquiv.ofAlgHom (swapHom A B) (swapInv A B)
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapInv_X, map_mul, swapHom_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapHom_X, map_mul, swapInv_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])

end GlobalTheory.AdjTr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateResidueFlagTermsReindexSymmetricEdge
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjComb

open Classical

theorem sum_eq_of_inj {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α → M) (G : β → M)
    (φ : α → β) (hφ : Function.Injective φ) (hval : ∀ x, F x = G (φ x)) (hs : ∀ b, G b ≠ 0 → ∃ x, φ x = b) :
    ∑ x, F x = ∑ b, G b :=
  Finset.sum_bij_ne_zero (fun x _ _ => φ x) (fun _ _ _ => Finset.mem_univ _) (fun _ _ _ _ _ _ h => hφ h)
    (fun b _ hb => by
      obtain ⟨x, rfl⟩ := hs b hb
      exact ⟨x, Finset.mem_univ _, by rw [hval]; exact hb, rfl⟩)
    (fun x _ _ => hval x)

theorem conj_residue_reindex : ∀ {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (ρ k : ℕ), n = 2 * ρ + k + 1 → r = n → ∀ U : GL (Fin n) κ, upperLeftBlock hr U ∈ unip κ r → ∀ (s : Bool) (fF fN : Fin ρ → Fin n) (gB : Fin k → Fin n), (∀ a, (fF a).1 = 2 * ρ + k - a.1) → (∀ a, (fN a).1 = if a.1 + 1 < ρ then 2 * ρ + k - (a.1 + 1) else ρ + k) → (∀ i, (gB i).1 = ρ + k - 1 - i.1) → (∑ a, (sgnD ρ k (fN a) : κ) * (U⁻¹).val (fN a) (fF a)) + (∑ i : Fin k, if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = ∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then ((GlobalTheory.SeeConjChar.wB ρ k s i j : ℤ) : κ) * (upperLeftBlock hr U).val i j else 0 := by
  intro κ _ n r hr ρ k hn hrn U hU s fF fN gB hfF hfN hgB
  subst hrn
  have hm : U ∈ blockTri (κ := κ) (blk2 r) := fun i j h => absurd h (by simp [blk2, i.2, j.2])
  have hR : upperLeftBlock hr U = U := Units.ext (Matrix.ext fun i j => by rw [upper_block_val_submatrix hr hm]; rfl)
  rw [hR] at hU ⊢
  have hUi : U⁻¹ ∈ unip κ r := inv_mem hU
  have hinv : ∀ p q : Fin r, q.1 = p.1 + 1 → (U⁻¹).val p q = - U.val p q := by
    intro p q hpq
    have hlt : p < q := by rw [Fin.lt_def]; omega
    have h := unip_mul_entry hUi hU hlt (fun l h1 h2 => by
      rw [Fin.lt_def] at h1 h2; omega)
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (ne_of_lt hlt)] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  obtain ⟨φ, hφl, hφr⟩ : ∃ φ : Fin ρ ⊕ Fin k → Fin r × Fin r, (∀ a, φ (Sum.inl a) = (fN a, fF a)) ∧
      (∀ i, φ (Sum.inr i) = (⟨ρ + k - 2 - i.1, by omega⟩, gB i)) := ⟨Sum.elim _ _, fun _ => rfl, fun _ => rfl⟩
  refine Eq.trans (Fintype.sum_sum_type (Sum.elim _ _)).symm ?_
  rw [← Fintype.sum_prod_type']
  refine sum_eq_of_inj _ _ φ ?_ ?_ ?_
  · rintro (a|i) (b|j) h
    · rw [hφl, hφl, Prod.mk.injEq] at h
      have h1 := hfF a; have h2 := hfF b; have h3 := congrArg Fin.val h.2
      exact congrArg Sum.inl (Fin.ext (by have := a.2; have := b.2; omega))
    · rw [hφl, hφr, Prod.mk.injEq] at h
      have h1 := hfF a; have h2 := hgB j; have h3 := congrArg Fin.val h.2
      exfalso; have := a.2; have := j.2; omega
    · rw [hφr, hφl, Prod.mk.injEq] at h
      have h1 := hfF b; have h2 := hgB i; have h3 := congrArg Fin.val h.2
      exfalso; have := b.2; have := i.2; omega
    · rw [hφr, hφr, Prod.mk.injEq] at h
      have h1 := hgB i; have h2 := hgB j; have h3 := congrArg Fin.val h.2
      exact congrArg Sum.inr (Fin.ext (by have := i.2; have := j.2; omega))
  · rintro (a|i)
    · rw [hφl]
      simp only [Sum.elim_inl]
      have h1 := hfF a; have h2 := hfN a; have ha := a.2
      by_cases hc : a.1 + 1 < ρ
      · rw [if_pos hc] at h2
        have hq : (fF a).1 = (fN a).1 + 1 := by omega
        have hs : symEdge ρ k (fN a) (fF a) := Or.inl ⟨hq, by omega, by omega⟩
        have hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = -1 := by
          unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega
        have hd : (sgnD ρ k (fN a) : κ) = 1 := by unfold sgnD; rw [if_neg (by omega)]
        rw [if_pos hs, hw, hd, hinv _ _ hq]; push_cast; ring
      · rw [if_neg hc] at h2
        have hq : (fF a).1 = (fN a).1 + 1 := by omega
        have hs : symEdge ρ k (fN a) (fF a) := Or.inl ⟨hq, by omega, by omega⟩
        have hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = 1 := by
          unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega
        have hd : (sgnD ρ k (fN a) : κ) = -1 := by unfold sgnD; rw [if_pos h2]
        rw [if_pos hs, hw, hd, hinv _ _ hq]; push_cast; ring
    · rw [hφr]
      show (if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = _
      have h1 := hgB i; have hi2 := i.2
      by_cases hi : i.1 + 1 < k
      · rw [dite_eq_left hi]
        have h3 := hgB ⟨i.1 + 1, hi⟩
        dsimp only at h3
        have hg : gB ⟨i.1 + 1, hi⟩ = ⟨ρ + k - 2 - i.1, by omega⟩ := Fin.ext (by dsimp only; omega)
        have hq : (gB i).1 = (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 := by dsimp only; omega
        have hs : symEdge ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) := Or.inl ⟨hq, by dsimp only; omega, by dsimp only; omega⟩
        have hd : (sgnD ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) : κ) = 1 := by
          unfold sgnD; rw [if_neg (by dsimp only; omega)]
        rw [hg, if_pos hs, hd, hinv _ _ hq]
        cases s
        · have hw : GlobalTheory.SeeConjChar.wB ρ k false (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = -1 := by
            unfold GlobalTheory.SeeConjChar.wB
            rw [if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl
          rw [hw]; simp
        · have hw : GlobalTheory.SeeConjChar.wB ρ k true (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = 0 := by
            unfold GlobalTheory.SeeConjChar.wB
            rw [if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl
          rw [hw]; simp
      · rw [dite_eq_right hi, if_neg]
        rintro (⟨h4, h5, h6⟩ | ⟨h4, h5⟩) <;> dsimp only at h4 h5 <;> omega
  · rintro ⟨p, q⟩ hne
    dsimp only at hne
    by_cases hs : symEdge ρ k p q
    swap
    · exact absurd (if_neg hs) hne
    rw [if_pos hs] at hne
    have hw : GlobalTheory.SeeConjChar.wB ρ k s p q ≠ 0 := fun h => hne (by rw [h]; simp)
    unfold GlobalTheory.SeeConjChar.wB at hw
    have hp2 := p.2; have hq2 := q.2
    rcases hs with ⟨hq, hp1, hp3⟩ | ⟨hp, hq⟩
    · by_cases h1 : p.1 < ρ
      · simp [h1] at hw
      by_cases h2 : p.1 + 1 < ρ + k
      · refine ⟨Sum.inr ⟨ρ + k - 2 - p.1, by omega⟩, ?_⟩
        rw [hφr, Prod.mk.injEq]
        have h3 := hgB ⟨ρ + k - 2 - p.1, by omega⟩
        dsimp only at h3
        exact ⟨Fin.ext (by dsimp only; omega), Fin.ext (by omega)⟩
      by_cases h3 : p.1 = ρ + k
      · refine ⟨Sum.inl ⟨ρ - 1, by omega⟩, ?_⟩
        rw [hφl, Prod.mk.injEq]
        have h4 := hfN ⟨ρ - 1, by omega⟩; have h5 := hfF ⟨ρ - 1, by omega⟩
        dsimp only at h4 h5
        rw [if_neg (by omega)] at h4
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · refine ⟨Sum.inl ⟨2 * ρ + k - 1 - p.1, by omega⟩, ?_⟩
        rw [hφl, Prod.mk.injEq]
        have h4 := hfN ⟨2 * ρ + k - 1 - p.1, by omega⟩; have h5 := hfF ⟨2 * ρ + k - 1 - p.1, by omega⟩
        dsimp only at h4 h5
        rw [if_pos (by omega)] at h4
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · simp [show p.1 < ρ by omega] at hw

end GlobalTheory.SeeConjComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedLevelElementKeepsStandardLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedLevelElement_keeps_standardLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D, (v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔ Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m)))) := by
  first | exact @GlobalTheory.RowVertexInv.moved_keeps_std | exact GlobalTheory.RowVertexInv.moved_keeps_std | (intros; apply GlobalTheory.RowVertexInv.moved_keeps_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousSmulMx
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AnnNbhdCpt

variable {D : D7}

theorem pairA_add_one : pairA D.host.F 0 1 + pairA D.host.F 1 0 = 1 :=
  GlobalTheory.AdelicCoord.af_ext (by rw [map_add (f := _), map_one, GlobalTheory.AdelicCoord.fstA_pairA, GlobalTheory.AdelicCoord.fstA_pairA, zero_add])
    (by rw [map_add (f := _), map_one, GlobalTheory.AdelicCoord.sndA_pairA, GlobalTheory.AdelicCoord.sndA_pairA, add_zero])

theorem pairA_mul_pairA : pairA D.host.F 1 0 * pairA D.host.F 0 1 = 0 :=
  GlobalTheory.AdelicCoord.af_ext (by rw [map_mul, map_zero, GlobalTheory.AdelicCoord.fstA_pairA, GlobalTheory.AdelicCoord.fstA_pairA, mul_zero])
    (by rw [map_mul, map_zero, GlobalTheory.AdelicCoord.sndA_pairA, GlobalTheory.AdelicCoord.sndA_pairA, zero_mul])

theorem smul_fin_add (z : AE D) : pairA D.host.F 0 1 • z + pairA D.host.F 1 0 • z = z := by
  rw [← add_smul, pairA_add_one, one_smul]

theorem smul_fin_of_inf (z : AE D) (h : infPart D z = 0) : pairA D.host.F 0 1 • z = z := by
  have h' := (GlobalTheory.AdelicCoord.infPart_eq_zero_iff D z).1 h
  have := smul_fin_add z
  rwa [h', add_zero] at this

theorem infPart_smul_fin (z : AE D) : infPart D (pairA D.host.F 0 1 • z) = 0 := by
  rw [GlobalTheory.AdelicCoord.infPart_eq_zero_iff, smul_smul, pairA_mul_pairA, zero_smul]

theorem mem_idAt_true (z : AE D) : z ∈ idAt D (fun _ => True) ↔ infPart D z = 0 := by
  unfold idAt
  rw [Ideal.mem_inf, Ideal.mem_iInf, RingHom.mem_ker]
  exact ⟨fun h => h.1, fun h => ⟨h, fun w => absurd trivial w.2⟩⟩

theorem mxAt_true_iff {m n : ℕ} (x : Mx D m n) : MxAt (fun _ => True) x ↔ pairA D.host.F 1 0 • x = 0 := by
  unfold MxAt
  rw [← Matrix.ext_iff]
  simp only [Matrix.smul_apply, Matrix.zero_apply, mem_idAt_true, GlobalTheory.AdelicCoord.infPart_eq_zero_iff]

theorem continuous_smul_mx {m n : ℕ} (c : AF D.host.F) : Continuous fun x : Mx D m n => c • x := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) :=
    IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun x : Mx D m n => c • x i j
  exact (continuous_const (y := c)).smul (continuous_id.matrix_elem i j)

def annSet (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (Γ : AddSubgroup (WO S T)) : Set (WO S T) :=
  {u' | MxAt (fun _ => True) u' ∧ ∀ u ∈ Γ, ψ (symplO S T u u') = 1}


set_option maxHeartbeats 1000000 in
theorem isCompact_annSet (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (Γ : AddSubgroup (WO S T)) (U : Set (WO S T)) (hU : IsOpen U) (h0 : (0 : WO S T) ∈ U)
    (hUΓ : ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ Γ) : IsCompact (annSet ψ Γ) := by
  obtain ⟨h1, h2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  let e : AF D.host.F := pairA D.host.F 0 1
  let V : AddSubgroup (WO S T) :=
    { carrier := {u | e • u ∈ Γ}
      add_mem' := fun {a b} ha hb => by show e • (a + b) ∈ Γ; rw [smul_add]; exact add_mem ha hb
      zero_mem' := by show e • (0 : WO S T) ∈ Γ; rw [smul_zero]; exact zero_mem _
      neg_mem' := fun {a} ha => by show e • (-a) ∈ Γ; rw [smul_neg]; exact neg_mem ha }
  have hfinE : ∀ u : WO S T, MxAt (fun _ => True) (e • u) := fun u i j => by
    rw [mem_idAt_true, Matrix.smul_apply]; exact infPart_smul_fin _
  have hVo : IsOpen (V : Set (WO S T)) := by
    refine AddSubgroup.isOpen_of_mem_nhds V (g := 0) ?_
    refine Filter.mem_of_superset (((continuous_smul_mx e).isOpen_preimage U hU).mem_nhds (by
      show e • (0 : WO S T) ∈ U; rw [smul_zero]; exact h0)) fun u hu => hUΓ _ hu (hfinE u)
  obtain ⟨Q, hQc, hQ⟩ := GlobalTheory.AnnihMat.annihilator_inBox_full D ψ hψ S T V hVo
  have hfix : ∀ u : WO S T, MxAt (fun _ => True) u → e • u = u := fun u hu => by
    ext i j
    rw [Matrix.smul_apply]
    exact smul_fin_of_inf _ ((mem_idAt_true _).1 (hu i j))
  have hsub : annSet ψ Γ ⊆ (fun x : WO S T => e • x) '' Q := by
    rintro u' ⟨hfin, hann⟩
    obtain ⟨k, hk, hk0⟩ := hQ u' fun u hu hu0 => by
      have hu1 : MxAt (fun _ => True) u := fun i j => by
        rw [mem_idAt_true]; exact congrFun (congrFun hu0 i) j
      have : u ∈ Γ := by
        have h := hu
        change e • u ∈ Γ at h
        rwa [hfix u hu1] at h
      exact (psi_symplO_swap ψ _ _).2 (hann u this)
    refine ⟨k, hk, ?_⟩
    have hd : e • (u' - k) = 0 := by
      ext i j
      rw [Matrix.smul_apply, Matrix.zero_apply]
      exact (GlobalTheory.AdelicCoord.finPart_eq_zero_iff D _).1 (congrFun (congrFun hk0 i) j)
    rw [smul_sub, sub_eq_zero] at hd
    show e • k = u'
    rw [← hd, hfix u' hfin]
  have hcl : IsClosed (annSet ψ Γ) := by
    have e1 : annSet ψ Γ = {x : WO S T | pairA D.host.F 1 0 • x = 0} ∩
        ⋂ u ∈ Γ, {x : WO S T | ψ (symplO S T u x) = 1} := by
      ext x
      simp only [annSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mxAt_true_iff]
    rw [e1]
    refine IsClosed.inter (isClosed_eq (continuous_smul_mx _) continuous_const)
      (isClosed_biInter fun u _ => isClosed_eq ?_ continuous_const)
    exact hψ.1.1.comp (GlobalTheory.SplitScalar.continuous_symplO S T continuous_const continuous_id)
  exact (hQc.image (continuous_smul_mx e)).of_isClosed_subset hcl hsub

end GlobalTheory.AnnNbhdCpt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartz
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

namespace GlobalTheory.TripleAssembly

theorem darbAlg_le_schA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w),
    M.IsGood ψ → GlobalTheory.TripleAssembly.darbAlg M ψ τ ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ n d Y Z M ψ τ hM
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, -, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

end GlobalTheory.TripleAssembly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedTupleData_over_coefficientField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  first | exact @GlobalTheory.PinsOverField.pinsOverL | exact GlobalTheory.PinsOverField.pinsOverL | (intros; apply GlobalTheory.PinsOverField.pinsOverL <;> assumption)
end

