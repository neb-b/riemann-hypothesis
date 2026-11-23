module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ZD

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocTied6OfCmp
section
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

def toCompanionTheory {eB : Per.Bcris l ≃+* Per6.Bcris l} {eD : Per.BdR l ≃+* Per6.BdR l} {eP : Per.BdRp l ≃+* Per6.BdRp l}
    (h : Compat l eB eD eP) {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) : LocTied6 l P AI := by
  refine
    { eB := T.eB.trans eB
      eD := T.eD.trans eD
      zB := fun z => ?_
      zD := fun z => ?_
      om := fun x => ?_
      actB := fun g b => ?_
      actD := fun g b => ?_
      frob := fun b => ?_
      incl := ?_
      fil := fun K a x => ?_
      t := ?_
      ιA := fun a => ?_ }
  · rw [RingEquiv.trans_apply, T.zB z, h.zB z]
  · rw [RingEquiv.trans_apply, T.zD z, h.zD z]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    exact ⟨eP y, by rw [RingEquiv.trans_apply, hy, h.alg y], by rw [h.θ y]; exact hθ⟩
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actB g b, h.σB]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actD g b, h.σD]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.frob b, h.φB]
  · have H := (h.incl _).1 T.incl
    convert H using 1
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.trans_apply, RingEquiv.symm_trans_apply]
  · rw [T.fil K a x, RingEquiv.trans_apply, h.fil a]
  · obtain ⟨y, hy, he⟩ := T.t
    exact ⟨eP y, (h.log AI y).1 hy, by rw [RingEquiv.trans_apply, he, h.alg y]⟩
  · rw [RingEquiv.trans_apply, T.ιA a, h.aB a]

theorem locTied6_of_cmp (hC : Cmp l) (P : LocPrime l) (AI : LocAinf l P) :
    Nonempty (LocTied l P AI) → Nonempty (LocTied6 l P AI) := by
  rintro ⟨T⟩
  obtain ⟨eB, eD, eP, h⟩ := hC
  exact ⟨toCompanionTheory h T⟩

end Formalism.BasicNotions.CmpTie
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonOfComparison
section
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

def ofSix {eB : Per.Bcris l ≃+* Per6.Bcris l} {eD : Per.BdR l ≃+* Per6.BdR l} {eP : Per.BdRp l ≃+* Per6.BdRp l}
    (h : Compat l eB eD eP) {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : LocTied l P AI := by
  refine
    { eB := T.eB.trans eB.symm
      eD := T.eD.trans eD.symm
      zB := fun z => ?_
      zD := fun z => ?_
      om := fun x => ?_
      actB := fun g b => ?_
      actD := fun g b => ?_
      frob := fun b => ?_
      incl := ?_
      fil := fun K a x => ?_
      t := ?_
      ιA := fun a => ?_ }
  · rw [RingEquiv.trans_apply, T.zB z, ← h.zB z, RingEquiv.symm_apply_apply]
  · rw [RingEquiv.trans_apply, T.zD z, ← h.zD z, RingEquiv.symm_apply_apply]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    refine ⟨eP.symm y, ?_, ?_⟩
    · rw [RingEquiv.trans_apply, hy, RingEquiv.symm_apply_eq, h.alg, RingEquiv.apply_symm_apply]
    · rw [← h.θ, RingEquiv.apply_symm_apply]; exact hθ
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actB g b, RingEquiv.symm_apply_eq, h.σB,
      RingEquiv.apply_symm_apply]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actD g b, RingEquiv.symm_apply_eq, h.σD,
      RingEquiv.apply_symm_apply]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.frob b, RingEquiv.symm_apply_eq, h.φB,
      RingEquiv.apply_symm_apply]
  · refine (h.incl _).2 ?_
    convert T.incl using 1
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.trans_apply, RingEquiv.symm_trans_apply, RingEquiv.apply_symm_apply,
      RingEquiv.symm_symm]
  · rw [T.fil K a x, RingEquiv.trans_apply, h.fil a, RingEquiv.apply_symm_apply]
  · obtain ⟨y, hy, he⟩ := T.t
    refine ⟨eP.symm y, (h.log AI (eP.symm y)).2 (by rw [RingEquiv.apply_symm_apply]; exact hy), ?_⟩
    rw [RingEquiv.trans_apply, he, RingEquiv.symm_apply_eq, h.alg, RingEquiv.apply_symm_apply]
  · rw [RingEquiv.trans_apply, T.ιA a, ← h.aB a, RingEquiv.symm_apply_apply]

theorem local_comparison_of_comparison (hC : Cmp l) (P : LocPrime l) (AI : LocAinf l P) :
    Nonempty (LocTied6 l P AI) → Nonempty (LocTied l P AI) := by
  rintro ⟨T⟩
  obtain ⟨eB, eD, eP, h⟩ := hC
  exact ⟨ofSix h T⟩

end Formalism.BasicNotions.CmpTie
end
end

