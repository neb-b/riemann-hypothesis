module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDetSmulSubOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryStabilizerTransitionSelfDualFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameChange

open Formalism.L2.DIV
open scoped Matrix TensorProduct

set_option synthInstance.maxHeartbeats 160000

private theorem int_of_parts {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n]
    (G Gi : Matrix n n R) (hGG : G * Gi = 1) (ε ε' : R) (hε : ε ∈ O) (hε' : ε' ∈ O)
    (hs : (ε + ε') • (G - 1) = G - 1) (h1 : ∀ i j, ε * G i j ∈ O) (h2 : ∀ i j, ε' * G i j ∈ O)
    (h3 : ∀ i j, ε * Gi i j ∈ O) (h4 : ∀ i j, ε' * Gi i j ∈ O) :
    (∀ i j, G i j ∈ O) ∧ ∀ i j, Gi i j ∈ O := by
  have hone : ∀ i j, (1 : Matrix n n R) i j ∈ O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  have hs1 : (1 - ε - ε') ∈ O := O.sub_mem (O.sub_mem O.one_mem hε) hε'
  have hA : (1 - (ε + ε')) • G = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    have : (1 - (ε + ε')) • (G - 1) = 0 := by rw [sub_smul, one_smul, hs, sub_self]
    rw [smul_sub, sub_eq_zero] at this
    exact this
  have hB : (1 - (ε + ε')) • Gi = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    calc (1 - (ε + ε')) • Gi = ((1 - (ε + ε')) • (1 : Matrix n n R)) * Gi := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = ((1 - (ε + ε')) • G) * Gi := by rw [hA]
      _ = (1 - (ε + ε')) • (1 : Matrix n n R) := by rw [Matrix.smul_mul, hGG]
  constructor
  · intro i j
    have e1 := congrFun (congrFun hA i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : G i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * G i j + ε' * G i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h1 i j)) (h2 i j)
  · intro i j
    have e1 := congrFun (congrFun hB i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : Gi i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * Gi i j + ε' * Gi i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h3 i j)) (h4 i j)

private theorem smul_conj {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b b' X : GL n R) (ε : R)
    (h : ε • X.1 = ε • (b' * b⁻¹ : GL n R).1) :
    ε • (b⁻¹ * X * b : GL n R).1 = ε • (b⁻¹ * b' : GL n R).1 ∧
      ε • ((b⁻¹ * X * b)⁻¹ : GL n R).1 = ε • (b'⁻¹ * b : GL n R).1 := by
  have key : ∀ u v : GL n R, ε • (u * X * v : GL n R).1 = ε • (u * (b' * b⁻¹) * v : GL n R).1 := by
    intro u v
    simp only [Units.val_mul] at h ⊢
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · rw [key, show b⁻¹ * (b' * b⁻¹) * b = b⁻¹ * b' by group]
  · have := key (b⁻¹ * X⁻¹) (b * b'⁻¹ * b)
    rw [show b⁻¹ * X⁻¹ * X * (b * b'⁻¹ * b) = b'⁻¹ * b by group,
      show b⁻¹ * X⁻¹ * (b' * b⁻¹) * (b * b'⁻¹ * b) = (b⁻¹ * X * b)⁻¹ by group] at this
    exact this.symm

private theorem smul_conj_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b X : GL n R) (s : R)
    (h : s • (X.1 - 1) = X.1 - 1) :
    s • ((b⁻¹ * X * b : GL n R).1 - 1) = (b⁻¹ * X * b : GL n R).1 - 1 := by
  have e : (b⁻¹ * X * b : GL n R).1 - 1 = (b⁻¹).1 * (X.1 - 1) * b.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h]

private theorem exists_int_GL {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n] (γ : GL n R)
    (h1 : ∀ i j, γ.1 i j ∈ O) (h2 : ∀ i j, (γ⁻¹).1 i j ∈ O) : ∃ y : GL n O, y.1.map O.subtype = γ.1 := by
  let A : Matrix n n O := Matrix.of fun i j => ⟨γ.1 i j, h1 i j⟩
  let B : Matrix n n O := Matrix.of fun i j => ⟨(γ⁻¹).1 i j, h2 i j⟩
  have hA : A.map O.subtype = γ.1 := rfl
  have hB : B.map O.subtype = (γ⁻¹).1 := rfl
  have hinj : Function.Injective (fun M : Matrix n n O => M.map O.subtype) :=
    Matrix.map_injective O.subtype_injective
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, hA⟩
  · show (A * B).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · show (B * A).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem frame_inv_mul_int {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {b b' : GL (Fin n) (EAf D)} (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (i j : Fin n) :
    (b⁻¹ * b' : GL (Fin n) (EAf D)).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h1 : b'.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [hb']
    intro k
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have h2 := (hb _).1 h1 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
  exact h2


set_option maxHeartbeats 800000 in
private theorem mem_St_of_comp {D : D7} (e : AE D) (he : e * e = e) (V : HSp D)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    (b b' : GL (Fin V.rank) (EAf D)) (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (k : GA D V) (hk : SuppAt e V k)
    (hc : ∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) :
    Formalism.IndefR.Lev.finE V k ∈ St b := by
  have hidem : ∀ a : AE D, a * a = a → toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha =>
    Formalism.IndefR.Fin.LevelGroupLemmas.toEAf_mem_intAf (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, ha]))
  have hε := hidem e he
  have hε' := hidem (cA D e) (by rw [← map_mul, he])
  obtain ⟨X, hX⟩ : ∃ X : GL (Fin V.rank) (EAf D), X = Formalism.IndefR.Lev.finE V k := ⟨_, rfl⟩
  have hXv : X.1 = (mt V k).map (toEAf D) := by rw [hX]; rfl
  have hc' : toEAf D e • X.1 = toEAf D e • (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1 := by
    rw [hX]; exact Matrix.ext fun i j => hc i j
  obtain ⟨c1, c2⟩ := smul_conj b b' X (toEAf D e) hc'
  have hs : (toEAf D e + toEAf D (cA D e)) • (X.1 - 1) = X.1 - 1 := by
    refine Matrix.ext fun i j => ?_
    have h0 := congrArg (toEAf D) (hk i j)
    have h1 : toEAf D ((mt V k - 1) i j) = (X.1 - 1) i j := by
      rw [hXv, Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
    rw [map_mul, RingHom.map_add (f := _), h1] at h0
    exact h0
  have i1 : ∀ i j, (toEAf D e • (b⁻¹ * X * b : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c1]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb hb' i j)
  have i2 : ∀ i j, (toEAf D e • ((b⁻¹ * X * b)⁻¹ : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c2]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb' hb i j)
  obtain ⟨j1, j2⟩ := GlobalTheory.ConjIntegral.conj_smul_isIntM V Λ b hΛ hb X (hX ▸ GlobalTheory.LevSplit.finE_mem_UA V k)
    (b⁻¹ * X * b) rfl e i1 i2
  obtain ⟨g1, g2⟩ := int_of_parts (Formalism.L2.Herm.intAf D.host.F D.host.E) _ _ (Units.mul_inv (b⁻¹ * X * b)) _ _ hε hε'
    (smul_conj_sub_one b X _ hs) i1 j1 i2 j2
  obtain ⟨y, hy⟩ := exists_int_GL _ _ g1 g2
  refine ⟨y, ?_⟩
  have hy' : intGL D.host.F D.host.E V.rank y = b⁻¹ * X * b := Units.ext hy
  rw [← hX]
  show b * intGL D.host.F D.host.E V.rank y * b⁻¹ = X
  rw [hy']; group


set_option maxHeartbeats 800000 in
private theorem exists_unitary_frame_change : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y := by
  intro D e S hS V Λ hΛ b b' hb hb'
  have he : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hS
  have he' : e * cA D e = 0 := hS.2
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  let inv : EAf D →+* (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toRingEquiv.toRingHom
  have hinv : ∀ x, Lev.swapAE D (inv x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a c => rfl
    | add a c ha hc => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hc]
  let P : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1
  let Q : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b * b'⁻¹ : GL (Fin V.rank) (EAf D)).1
  have hPQ : P * Q = 1 := by
    show (b' * b⁻¹ * (b * b'⁻¹) : GL (Fin V.rank) (EAf D)).1 = 1
    rw [show b' * b⁻¹ * (b * b'⁻¹) = 1 by group]
    rfl
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.SplitLift.exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D)
    GlobalTheory.DualPairCheck.cA_cA _ _ hJ hJK e he he' hinf (P.map inv) (Q.map inv)
    (by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)])
  let k : GA D V := ⟨g, hg⟩
  have hval : ∀ i j, (Lev.finE V k).1 i j = Lev.swapAE D (finPart D (g.1 i j)) := fun i j => rfl
  have hcomp : ∀ i j, toEAf D e * (Lev.finE V k).1 i j = toEAf D e * P i j := by
    intro i j
    have h3 : finPart D e * finPart D (g.1 i j) = finPart D e * inv (P i j) := congrFun (congrFun h2 i) j
    rw [hval, show toEAf D e = Lev.swapAE D (finPart D e) from rfl, ← map_mul, h3, map_mul, hinv]
  have hk : SuppAt e V k := h1
  have hSt := mem_St_of_comp e he V Λ hΛ b b' hb hb' k hk hcomp
  refine ⟨k, hk, GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.stabLat_of_mem_St V Λ b hb k hSt, hcomp, ?_⟩
  intro y hy
  have hyv : (y : AE D) = e * (mt V k).det + (1 - e) := hy
  have hyd : y = Formalism.IndefR.Fin.LevelGroupLemmas.detAt e V k :=
    Units.ext (hyv.trans (Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he V k).symm)
  have hint : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])
  refine ⟨?_, ?_, ?_⟩
  · rw [hyv, RingHom.map_add (f := _), map_mul, RingHom.map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_int he hint V hSt
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_inv_int he hint V hSt

end GlobalTheory.FrameChange

end

theorem _root_.GlobalTheory.T.exists_unitaryStabilizer_transition_selfDualFrames : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y :=
  GlobalTheory.FrameChange.exists_unitary_frame_change
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalConstTerm
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCFct

theorem finiteDimensional_constTerm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → r < a → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) => fun g : GA E a => ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ)) := by
  intro E _ _ _ a hind L hL W hW X hX N r hr0 hra _ _ μ 𝓕 hμ h𝓕 h1
  set S := Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) with hS
  set ct : S → GA E a → ℂ := fun φ g => ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ with hct
  have hleft : ∀ φ ∈ S, ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
    intro φ hφ γ g
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c * ·) hx
  have hright : ∀ φ ∈ S, ∀ l ∈ L, ∀ g, φ.1 (g * finGL E a l) = φ.1 g := by
    intro φ hφ l hl g
    induction hφ using Submodule.span_induction with
    | mem x hx => exact congrArg (fun ψ : Sm E a => ψ.1 g) (hx.2.1 l hl)
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c * ·) hx
  set V := Submodule.span ℂ (Set.range ct) with hV
  have hVprop : ∀ f ∈ V, (∀ (y : BlockIx a r → Ad E) g, f (unip y * g) = f g) ∧ (∀ l ∈ L, ∀ g, f (g * finGL E a l) = f g) ∧
      ∀ g, (fun k : Kinf E a => f (g * infGL E a (Unitary.toUnits k))) ∈ W := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      refine ⟨fun y g => _root_.GlobalTheory.CuspRep.constTerm_unip_invariant E a r μ 𝓕 hμ h𝓕 _ (hleft φ.1 φ.2) y g, fun l hl g => ?_, fun g => ?_⟩
      · change ∫ x in 𝓕, φ.1.1 (unip x * (g * finGL E a l)) ∂μ = ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ
        simp_rw [← mul_assoc]
        exact congrArg (fun h : (BlockIx a r → Ad E) → ℂ => ∫ x in 𝓕, h x ∂μ) (funext fun x => hright φ.1 φ.2 l hl _)
      · exact _root_.GlobalTheory.HCFct.constTerm_cptTranslate_mem E a L W hW X N r μ 𝓕 hμ h𝓕 h1 φ.1 φ.2 g
    | zero => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => W.zero_mem⟩
    | add x y _ _ hx hy =>
      refine ⟨fun u g => ?_, fun l hl g => ?_, fun g => W.add_mem (hx.2.2 g) (hy.2.2 g)⟩
      · exact congrArg₂ (· + ·) (hx.1 u g) (hy.1 u g)
      · exact congrArg₂ (· + ·) (hx.2.1 l hl g) (hy.2.1 l hl g)
    | smul c x _ hx =>
      refine ⟨fun u g => ?_, fun l hl g => ?_, fun g => W.smul_mem c (hx.2.2 g)⟩
      · exact congrArg (c * ·) (hx.1 u g)
      · exact congrArg (c * ·) (hx.2.1 l hl g)
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.IwaParab.iwasawa_parab E a r L hL
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_finset_separating_finiteDimensional_functions (Kinf E a) W hW
  let M := {m : GA E a // (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0)}
  let ι := {t // t ∈ T} × {κ // κ ∈ s}
  let pt : ι → M → GA E a := fun i m => m.1 * finGL E a i.1.1 * infGL E a (Unitary.toUnits i.2.1)
  let Vi : ι → Submodule ℂ (M → ℂ) := fun i =>
    Submodule.span ℂ (Set.range fun φ : S => fun m : M => ct φ (pt i m))
  have hVi : ∀ i, FiniteDimensional ℂ (Vi i) := fun i =>
    _root_.GlobalTheory.LeviCT.finiteDimensional_levi E a hind L hL W hW X hX N r hr0 hra μ 𝓕 hμ h𝓕 h1 i.1.1 i.2.1
  let R : (GA E a → ℂ) →ₗ[ℂ] (ι → M → ℂ) :=
    LinearMap.pi fun i => LinearMap.pi fun m => LinearMap.proj (pt i m)
  have hR : ∀ f ∈ V, ∀ i, R f i ∈ Vi i := by
    intro f hf i
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      exact Submodule.subset_span ⟨φ, rfl⟩
    | zero => exact (Vi i).zero_mem
    | add x y _ _ hx hy => exact (Vi i).add_mem hx hy
    | smul c x _ hx => exact (Vi i).smul_mem c hx
  have hinj : ∀ f ∈ V, R f = 0 → f = 0 := by
    intro f hf h0
    obtain ⟨hN, hL', hK⟩ := hVprop f hf
    funext g
    obtain ⟨y, m, hm, t, ht, k, l, hl, rfl⟩ := hT g
    have e : f (unip y * m * finGL E a t * infGL E a (Unitary.toUnits k) * finGL E a l) =
        f (m * finGL E a t * infGL E a (Unitary.toUnits k)) := by
      rw [hL' l hl, mul_assoc, mul_assoc, ← mul_assoc m, hN]
    rw [e]
    have hw := hs _ (hK (m * finGL E a t)) (fun κ hκ => by
      have := congrFun (congrFun h0 ⟨⟨t, ht⟩, ⟨κ, hκ⟩⟩) ⟨m, hm⟩
      exact this)
    exact congrFun hw k
  let F : V →ₗ[ℂ] (i : ι) → Vi i := LinearMap.pi fun i =>
    ((LinearMap.proj i).comp (R.comp V.subtype)).codRestrict (Vi i) (fun f => hR f.1 f.2 i)
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    refine Subtype.ext (hinj f.1 f.2 (funext fun i => ?_))
    have := congrFun hf i
    exact congrArg Subtype.val this
  exact Module.Finite.of_injective F hF

end GlobalTheory.HCFct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardRationalMemUnitaryRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toAfE_inc (D : D7) (x : D.host.E) :
    GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
  have h1 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : Af D.host.F) x).trans (by rw [map_one, one_mul])
  have h2 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) x).trans (by rw [map_one, one_mul])
  show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x)) = _
  rw [h2, ← h1, RingEquiv.symm_apply_apply]

theorem adSwap_inc (D : D7) (x : D.host.E) : adSwap D (StandardLatticesGL3.inc D x) = inclEAf D x := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x)) = _
  rw [toAfE_inc]
  rfl

theorem finE_val_of_isRat {D : D7} {V : HSp D} {g : GA D V} {a : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (h : GlobalTheory.RatAut.IsRat V g a) :
    (Lev.finE V g).val = a.map (inclEAf D) := by
  have e : (Lev.finE V g).val =
      (Formalism.L2.Theta.mt V g).map (fun y => Lev.swapAE D
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y)) := rfl
  rw [e, show Formalism.L2.Theta.mt V g = _ from h]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply]
  show Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a i j)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rfl

theorem frConj_ratG : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E),
    Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 →
    ∀ γ ∈ GlobalTheory.NormSum.ratG D V.rank, ∃ q ∈ ratFin V, finG V q = GlobalTheory.FrameTransport.frConj fr γ.1 := by
  intro D V fr hfr
  let S : Subgroup (StandardLatticesGL3.GA D V.rank) :=
    ((ratFin V).map (finG V)).comap ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
  suffices hS : GlobalTheory.NormSum.ratG D V.rank ≤ S by
    intro γ hγ
    obtain ⟨q, hq, e⟩ := hS hγ
    exact ⟨q, hq, e⟩
  rw [GlobalTheory.NormSum.ratG, Subgroup.closure_le]
  rintro g ⟨γ₀, hγ₀⟩

  have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hg : ((g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (StandardLatticesGL3.sgA D)).transpose *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := g.2
  have hc : ((γ₀.map D.host.conj).transpose).map (StandardLatticesGL3.inc D) = ((γ₀.map (StandardLatticesGL3.inc D)).map (StandardLatticesGL3.sgA D)).transpose := by
    ext i j
    simp [StandardLatticesGL3.sgA, StandardLatticesGL3.inc, Formalism.UG.sigR, Formalism.UG.inclE]
  have hu : (γ₀.map D.host.conj).transpose * γ₀ = 1 := by
    apply Matrix.map_injective (GlobalTheory.NormSum.inc_inj D)
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, h1, Matrix.mul_one, ← hc, ← Matrix.map_mul] at hg
    exact hg.trans h1.symm
  have hu' : γ₀ᴴ * γ₀ = 1 := by
    have : γ₀ᴴ = (γ₀.map D.host.conj).transpose := Matrix.ext fun i j => by
      show star (γ₀ j i) = D.host.conj (γ₀ j i)
      exact Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D (γ₀ j i)
    rw [this, hu]

  set F : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hF
  set Fi : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr⁻¹ : GL (Fin V.rank) D.host.E).val with hFi
  have hFFi : F * Fi = 1 := by rw [hF, hFi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Fᴴ * V.gram * F = 1 := hfr
  have hJ : V.gram = Fiᴴ * Fi := by
    have := congrArg (fun M => Fiᴴ * M * Fi) hfr'
    simp only [Matrix.mul_one] at this
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]
  set a : Matrix (Fin V.rank) (Fin V.rank) D.host.E := F * γ₀ * Fi with ha
  have hau : aᴴ * V.gram * a = V.gram := by
    have e1 : aᴴ * V.gram * a = Fiᴴ * γ₀ᴴ * (Fᴴ * V.gram * F) * γ₀ * Fi := by
      rw [ha, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, hfr', Matrix.mul_one, Matrix.mul_assoc Fiᴴ, hu', Matrix.mul_one, hJ]
  obtain ⟨g', hg'Q, hg'⟩ := GlobalTheory.RatAut.exists_of_unitary V hau
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g') (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g')
  have hkC : k ∈ GfC V := MonoidHom.mem_ker.2 k1
  have hfin : finG V ⟨k, hkC⟩ = Lev.finE V g' := by
    show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g')
    rw [k2]
  refine ⟨⟨k, hkC⟩, ⟨g', hg'Q, hfin.symm⟩, ?_⟩
  show finG V ⟨k, hkC⟩ = frConj fr g.1
  rw [hfin, frConj_apply]
  apply Units.ext
  rw [finE_val_of_isRat hg', ← map_inv, Units.val_mul, Units.val_mul]
  have eb : ∀ (M : GL (Fin V.rank) D.host.E),
      (Formalism.UG.bc (inclEAf D) M).val = M.val.map (inclEAf D) := fun M => rfl
  have eg : (Formalism.UG.bc (adSwap D) g.1).val =
      γ₀.map (inclEAf D) := by
    show g.1.val.map (adSwap D) = _
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, Matrix.map_map]
    exact Matrix.ext fun i j => adSwap_inc D (γ₀ i j)
  rw [eb, eb, eg, ha, Matrix.map_mul, Matrix.map_mul]

end GlobalTheory.FrameTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_inclusion_raynaudExtension_algebraicPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left), (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) → HTChar p v P.Gt := by
  first | exact @GlobalTheory.CompHt.htChar_of_pointOver | exact GlobalTheory.CompHt.htChar_of_pointOver | (intros; apply GlobalTheory.CompHt.htChar_of_pointOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocalStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adelic_pureTensor_eq_product_local : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [∀ v : Pl (F := F), MeasurableSpace (κ → Fv F v)] [∀ v : Pl (F := F), BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μv : ∀ v : Pl (F := F), Measure (κ → Fv F v)) [∀ v, (μv v).IsAddHaarMeasure],
    (∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1) → ∃ c : ℂ, c ≠ 0 ∧
      ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), Continuous f → Integrable f μi → IsFam φ →
        Integrable (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) μ ∧
        ∫ x, f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ = c * (∫ x, f x ∂μi) * ∏ᶠ v, ∫ x, φ v x ∂(μv v) := by
  first | exact @GlobalTheory.AdelicHaarPure.integral_pure_haar | exact GlobalTheory.AdelicHaarPure.integral_pure_haar | (intros; apply GlobalTheory.AdelicHaarPure.integral_pure_haar <;> assumption)
end

