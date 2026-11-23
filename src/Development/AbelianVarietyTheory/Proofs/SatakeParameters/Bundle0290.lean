module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialOfCountZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteLevelPreimageFinitelyManyCosets
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevCosetFin

open ReciprocityTheory.Aut

section Grp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem natCast_isUnit_AL {d : ℕ} (hd : 0 < d) : IsUnit (d : AL L) := by
  have e : (d : AL L) = algebraMap L (AL L) (d : L) := (map_natCast _ d).symm
  rw [e]
  exact (IsUnit.mk0 (d : L) (Nat.cast_ne_zero.2 hd.ne')).map _

theorem exists_finset_of_bdd (d : ℕ) (hd : 0 < d) (S : Set (GAf L n))
    (hS : ∀ κ ∈ S, ∀ i j, (d : AL L) * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L ∧
        (d : AL L) * ((κ⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L) :
    ∃ F : Finset (GAf L n), ∀ κ ∈ S, ∃ f ∈ F, f⁻¹ * κ ∈ Umax L n := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := GlobalTheory.IsotOrth.exists_finite_class (F := NumberField.maximalRealSubfield L) (E := L)
    (d * d) (Nat.mul_pos hd hd)
  haveI := hQ
  let cls : GAf L n → Fin n → Fin n → Q := fun κ i j =>
    if h : (d : AL L) * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L then c ⟨_, h⟩ else c 0
  have key : ∀ a ∈ S, ∀ b ∈ S, cls a = cls b → a⁻¹ * b ∈ Umax L n := by
    intro a ha b hb hab
    have hdiff : ∀ k l, ∃ y ∈ ALint L, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l -
        (a.1 : Matrix (Fin n) (Fin n) (AL L)) k l = (d : AL L) * y := by
      intro k l
      have e := congrFun (congrFun hab k) l
      simp only [cls, dif_pos (hS a ha k l).1, dif_pos (hS b hb k l).1] at e
      obtain ⟨z, hz⟩ := hc _ _ e.symm
      refine ⟨z.1, z.2, ?_⟩
      have hz' := congrArg Subtype.val hz
      apply (natCast_isUnit_AL (L := L) hd).mul_left_cancel
      push_cast at hz'
      rw [mul_sub, hz', mul_assoc]
    choose y hy hye using hdiff
    have h0 : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      have : (((a⁻¹ * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
      simpa using this
    have h1 : (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 +
        ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) *
          ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - (a.1 : Matrix (Fin n) (Fin n) (AL L))) := by
      rw [Matrix.mul_sub, h0, add_sub_cancel]
      rfl
    intro i j
    show (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
    rw [h1, Matrix.add_apply, Matrix.mul_apply]
    refine add_mem ?_ (Subring.sum_mem _ fun k _ => ?_)
    · rw [Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · rw [Matrix.sub_apply, hye k j, ← mul_assoc, mul_comm _ (d : AL L)]
      exact mul_mem (hS a ha i k).2 (hy k j)
  let T : Set (Fin n → Fin n → Q) := cls '' S
  have hT : T.Finite := Set.toFinite T
  let rep : (Fin n → Fin n → Q) → GAf L n := fun t => if h : t ∈ T then h.choose else 1
  refine ⟨hT.toFinset.image rep, fun κ hκ => ?_⟩
  have ht : cls κ ∈ T := ⟨κ, hκ, rfl⟩
  have hr : rep (cls κ) = ht.choose := dif_pos ht
  refine ⟨rep (cls κ), Finset.mem_image.2 ⟨cls κ, hT.mem_toFinset.2 ht, rfl⟩, ?_⟩
  rw [hr]
  exact key _ ht.choose_spec.1 _ hκ ht.choose_spec.2

end Grp

end GlobalTheory.LevCosetFin

namespace GlobalTheory.LevCosetFin

section Den

variable {D : D7}

theorem comm_mem_intT {x : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F}
    (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)) x ∈ GlobalTheory.LatCongImage.intT D.host.F := by
  induction hx using Subring.closure_induction with
  | mem z hz =>
    apply Subring.subset_closure
    rcases hz with ⟨⟨s, t, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
    · right
      exact ⟨t, by simp⟩
    · left
      exact ⟨a, ha, by simp⟩
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end Den

end GlobalTheory.LevCosetFin

namespace GlobalTheory.LevCosetFin

section Den2

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_den (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (P : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hP : Formalism.IndefR.principalLevelFrame.StdPsi hF P)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∃ d : ℕ, 0 < d ∧ ∀ κ, (finHom V).rangeRestrict (P.ψ κ) ∈ (levEnv V β Ld).J → ∀ i j,
      (d : AL D.host.E) * (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) i j ∈ ALint D.host.E := by
  obtain ⟨⟨B, B', hBB', hB'B, hmat⟩, -⟩ := hP
  let cmr : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F →+* FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toAlgHom.toRingHom
  let βs := (β.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr
  let βi := ((β⁻¹).1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr
  obtain ⟨d, hd, hdm⟩ := GlobalTheory.LatCongImage.exists_nat_mul_mem_family D.host.F
    (fun p : ((Fin V.rank × Fin n) ⊕ (Fin n × Fin V.rank)) ⊕ ((Fin V.rank × Fin V.rank) ⊕ (Fin V.rank × Fin V.rank)) =>
      Sum.elim (Sum.elim (fun q => B q.1 q.2) (fun q => B' q.1 q.2))
        (Sum.elim (fun q => βs q.1 q.2) (fun q => βi q.1 q.2)) p)
  refine ⟨d ^ 4, by positivity, fun κ hκ i j => ?_⟩
  have h1 : Formalism.IndefR.Lev.finE V (P.ψ κ) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Formalism.IndefR.Lev.flag1L Ld) := hκ
  obtain ⟨y, hy⟩ := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev h1)
  have hM1 := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => (g.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) hy
  set Mf := (finHom V (P.ψ κ)).1 with hMf
  have hM2 : β.1 * ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val) *
      (β⁻¹).1 = Mf.map (Formalism.IndefR.Lev.swapAE D) := hM1
  let Ym := ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val).map cmr
  have hback : (Mf.map (Formalism.IndefR.Lev.swapAE D)).map cmr = Mf := by
    ext a b
    show (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F))
      ((Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E) (Mf a b)) = Mf a b
    rw [← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]
  have hM3 : Mf = βs * Ym * βi := by
    rw [← hback, ← hM2, Matrix.map_mul, Matrix.map_mul]
  set K := (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hK
  have hK2 : K = B' * Mf * B := by
    have e := hmat κ
    have e' : Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ) = Mf := rfl
    rw [e'] at e
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB'B, Matrix.one_mul, Matrix.mul_assoc, hB'B, Matrix.mul_one]
  have hκij : (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) i j = Formalism.IndefR.principalLevelFrame.tensCastR hF (K i j) := by
    rw [hK, Matrix.map_apply, RingEquiv.apply_symm_apply]
  let Bs' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B'
  let Bs : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B
  let βs' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βs
  let βi' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βi
  let Ms : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := βs' * Ym * βi'
  have hB'1 : ∀ a b, Bs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B' a b ∈ _; exact hdm (Sum.inl (Sum.inr (a, b)))
  have hB1 : ∀ a b, Bs a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B a b ∈ _; exact hdm (Sum.inl (Sum.inl (a, b)))
  have hβs1 : ∀ a b, βs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βs a b ∈ _; exact hdm (Sum.inr (Sum.inl (a, b)))
  have hβi1 : ∀ a b, βi' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βi a b ∈ _; exact hdm (Sum.inr (Sum.inr (a, b)))
  have hY1 : ∀ a b, Ym a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b =>
    comm_mem_intT (D := D) ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b).2
  have hMs : ∀ a b, Ms a b ∈ GlobalTheory.LatCongImage.intT D.host.F :=
    GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hβs1 hY1) hβi1
  have hint : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * K i j ∈ GlobalTheory.LatCongImage.intT D.host.F := by
    have hK3 : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • K = Bs' * Ms * Bs := by
      rw [hK2, hM3]
      simp only [Bs', Bs, Ms, βs', βi', Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      congr 1
      push_cast
      ring
    have e := congrFun (congrFun hK3 i) j
    rw [Matrix.smul_apply, smul_eq_mul] at e
    rw [e]
    exact GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hB'1 hMs) hB1 i j
  rw [hκij, ← map_natCast (Formalism.IndefR.principalLevelFrame.tensCastR hF) (d ^ 4), ← map_mul]
  exact GlobalTheory.LatCongImage.swap_mem D.host.F hF hint

end Den2

end GlobalTheory.LevCosetFin


open GlobalTheory.LevCosetFin in
theorem GlobalTheory.LevCosetFin.preimage_levEnv_finite_cosets : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ F : Finset (GAf D.host.E D.R.nV), ∀ κ, (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J → ∃ f ∈ F, f⁻¹ * κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := by
  intro D cf nch tp X M rep hA j t
  obtain ⟨d, hd, hden⟩ := exists_den (Vc D j) D.R.nV (hA.PV j) hA.hF (hA.stdV j) (X.R.βV j) (X.R.datVt j t)
  obtain ⟨F, hF⟩ := exists_finset_of_bdd d hd
    {κ | (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J}
    (fun κ hκ a b => ⟨hden κ hκ a b, hden κ⁻¹ (by
      show (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ⁻¹) ∈ _
      rw [map_inv, map_inv]
      exact inv_mem hκ) a b⟩)
  exact ⟨F, fun κ hκ => hF κ hκ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInertLocalDatumAtInertPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumAtInert

open scoped TensorProduct

theorem exists_inertDatum_of_isInertAt (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (Pp : HeightOneSpectrum (𝓞 E))
    (hw : Formalism.UG.IsInertAt (maximalRealSubfield E) E (Pp.under (𝓞 (maximalRealSubfield E))) Pp) :
    Nonempty (InertDatum E n (Pp.under (𝓞 (maximalRealSubfield E))) Pp) := by
  classical
  set v := Pp.under (𝓞 (maximalRealSubfield E)) with hv
  have hunder : Pp.under (𝓞 (maximalRealSubfield E)) = v := rfl
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj E).toAlgHom hw hunder
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt E) hw hc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov E Pp = Formalism.UG.intL (Pp.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield E) E
    (v.adicCompletion (maximalRealSubfield E))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨⟨e, c, ϖ, k, ?_, hU, ?_, ?_, ?_⟩⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj E).toAlgHom _ x)) =
      c (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

theorem main : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)),
    Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp →
    ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (_ : InertDatum D.host.E D.R.nV v Pp),
      NG.OverPl Pp v := by
  intro D hF Pp hI
  obtain ⟨Dv⟩ := exists_inertDatum_of_isInertAt D.host.E D.R.nV Pp hI
  exact ⟨_, Dv, rfl⟩

end GlobalTheory.InertDatumAtInert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrincipalCongruenceInDefiniteLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VFormCong

theorem redFn_eq_one_of_finCong {D : D7} {V : TH.HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {N : ℕ} {k : GA D V}
    (hΛ : IsSDFrame V β Λ 1) (hN : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hk : GlobalTheory.Member.FinCong V N k) :
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V N a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V a).1 *ᵥ z - z = N • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap Λ N _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, hred⟩ := GlobalTheory.PrincInLevel.exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Lev.finE V k)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) N hfr (hc k hk) hc'
  have hy' : Formalism.L2.DIV.frGL β y = Lev.finE V k := hy
  intro PP hP
  rw [← hy', Formalism.L2.DIV.redFn_frGL]
  refine hred _ _ ?_
  rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hN PP hP)

theorem levFn_eq_one {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ n)
    (x : GL (Fin n) (Lev.EAf D)) (h3 : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP x = 1) :
    Formalism.L2.DIV.levFn β L x = 1 := by
  have e : Formalism.L2.DIV.levFn β L x = Formalism.L2.DIV.levFn β L 1 := by
    have hr : Formalism.L2.DIV.rTup β L x = Formalism.L2.DIV.rTup β L 1 := by
      funext PP
      show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP.1 x) = Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP.1 1)
      rw [h3 PP.1 (Or.inl PP.2), Formalism.L2.DIV.redFn_one]
    unfold Formalism.L2.DIV.levFn
    rw [hr]
    congr 1
    · congr 1
      exact Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => by
        rw [h3 PP (Or.inl hPP), Formalism.L2.DIV.redFn_one]
    · exact Finset.prod_congr rfl fun PP hPP => by
        rw [h3 PP (Or.inr hPP), Formalism.L2.DIV.redFn_one]
  rw [e]
  exact (Formalism.L2.DIV.levChar D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) β L).map_one

end GlobalTheory.VFormCong


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.VFormCong.exists_cong_levEnv : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J, (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨_, h⟩ = 1 := by
  intro D cf nch tp X M rep hA j t
  classical
  obtain ⟨N, hN0, hNmem⟩ : ∃ N : ℕ, 0 < N ∧ ∀ PP, PP ∈ (X.R.datVt j t).Pg ∨ PP ∈ (X.R.datVt j t).Q →
      ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    refine ⟨∏ PP ∈ (X.R.datVt j t).Pg ∪ (X.R.datVt j t).Q, Ideal.absNorm PP.asIdeal, Finset.prod_pos fun PP _ =>
      Nat.pos_of_ne_zero fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun PP hPP => ?_⟩
    obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP => Ideal.absNorm (IsDedekindDomain.HeightOneSpectrum.asIdeal PP))
      (Finset.mem_union.2 hPP)
    rw [hu, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  obtain ⟨N', hN', hcong⟩ :=
    GlobalTheory.StdFrameCong.exists_cong_finCong D (Vc D j) D.R.nV (hA.PV j) hA.hF (hA.stdV j) N hN0
  refine ⟨N', hN', fun κ hκ => ?_⟩
  have hk := hcong κ hκ
  have hβ := X.given.core.lev.βV j
  refine ⟨GlobalTheory.PrincInLevel.finCong_mem_levEnv D (Vc D j) (X.R.βV j) (X.R.ΛV j) (X.R.datVt j t) N _ hβ hNmem hk, ?_⟩
  apply Units.ext
  change ((Formalism.L2.DIV.levFn (X.R.βV j) (Lev.flag1L (X.R.datVt j t)) (Lev.finE (Vc D j) ((hA.PV j).ψ κ)) : ℂˣ) : ℂ) = 1
  rw [GlobalTheory.VFormCong.levFn_eq_one (X.R.βV j) (Lev.flag1L (X.R.datVt j t)) _
    (fun PP hP => GlobalTheory.VFormCong.redFn_eq_one_of_finCong (X.R.datVt j t) hβ hNmem hk PP hP)]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterSphericalInertPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SatInertEx

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, π.SphAt v → ∃ α, NG.SatAt π Dv α := by
  intro L _ _ _ n π v w hw Dv hsph
  exact _root_.GlobalTheory.SatExists.exists_satAt L n π v w hw hsph Dv

end GlobalTheory.SatInertEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedIwahoriNeBotOfTwist
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.IwaFix

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem fixed_iwahori_ne_bot_of_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (s : ℂ)
    (T : (twist ρ (detChar (Fin n) (absPow k s))).Equiv ρ') (h : fixed ρ' (iwahori k (Fin n)) ≠ ⊥) :
    fixed ρ (iwahori k (Fin n)) ≠ ⊥ := by
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨x, rfl⟩ := T.toLinearEquiv.surjective y
  refine (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_, fun hx => h0 (by simp [hx])⟩
  have e := T.toIntertwiningMap.isIntertwining _ _ g x
  have hd : absPow k s (Matrix.GeneralLinearGroup.det g) = 1 := by
    have h1 := GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (iwahori_le_KO k (Fin n) hg)
    ext; simp [absPow, h1]
  rw [twist_apply, detChar_apply, hd, Units.val_one, one_smul] at e
  have hy' := GlobalTheory.Parabolic.mem_fixed.1 hy g hg
  exact T.toLinearEquiv.injective (e.trans hy')

end GlobalTheory.AboveL.IwaFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceIsSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TieFrob

theorem xi_eq_of_heq {D : D7} {nch : NChoice D} {C C' : CharFrame D} (h : C = C') (Tp : TupTied D C nch)
    (Tp' : TupTied D C' nch) (e : HEq Tp Tp') : Tp.xi = Tp'.xi := by
  subst h; cases e; rfl

end GlobalTheory.TieFrob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSpanTranslatesOfFixedLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_translates_of_fixed_lattice : ∀ {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] (χ : G → G → ℂ), GlobalTheory.PlaceModel.IsBichar χ → ∀ (ρ : G → V →ₗ[ℂ] V) (X Yh L L' K : AddSubgroup G), L ≤ L' → L' ≤ X → K ≤ Yh → (∀ v, ρ 0 v = v) → (∀ x ∈ X, ∀ x' ∈ X, ∀ v, ρ x (ρ x' v) = ρ (x + x') v) → (∀ y ∈ Yh, ∀ y' ∈ Yh, ∀ v, ρ y (ρ y' v) = ρ (y + y') v) → (∀ x ∈ X, ∀ y ∈ Yh, ∀ v, ρ x (ρ y v) = χ x y • ρ y (ρ x v)) → (∃ R : Finset G, ∀ t ∈ L', ∃ r ∈ R, t - r ∈ L) → (∀ x ∈ L', ∀ y ∈ K, χ x y = 1) → (∀ y ∈ Yh, (∀ x ∈ L', χ x y = 1) → y ∈ K) → ∀ (W : Submodule ℂ V), (∀ v ∈ W, ∀ x ∈ X, ρ x v ∈ W) → (∀ v ∈ W, ∀ y ∈ Yh, ρ y v ∈ W) → ∀ f ∈ W, (∀ x ∈ L, ρ x f = f) → (∀ y ∈ K, ρ y f = f) → f ∈ Submodule.span ℂ {v | ∃ r ∈ X, ∃ g ∈ W, (∀ x ∈ L, ρ x g = g) ∧ (∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y g = g) ∧ v = ρ r g} := by
  first | exact @GlobalTheory.FourierSpan.mem_span_translates_of_fixed | exact GlobalTheory.FourierSpan.mem_span_translates_of_fixed | (intros; apply GlobalTheory.FourierSpan.mem_span_translates_of_fixed <;> assumption)
end

