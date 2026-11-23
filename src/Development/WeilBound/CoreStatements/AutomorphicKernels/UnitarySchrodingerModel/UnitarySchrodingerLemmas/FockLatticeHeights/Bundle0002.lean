module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWGlue
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwFockk

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain


set_option maxHeartbeats 4000000 in
theorem heightWN_of (hF : HWFin) (hI : HWInf) (hL : LstdStd) : PositivityTheory.PfSWUS.SwMatch.HeightWN := by
  intro D n H hH θ hθ nb hnb w hw
  refine ⟨lstd D.host.F D.host.E n, (hL D.host.F D.host.E n).1, fun d bs => (hL D.host.F D.host.E n).2 d bs, ?_⟩
  intro lam hlam b
  obtain ⟨p, hp, k, hk, hpk⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n (w * nb b)
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  have hH' : H (w * nb b) = absA D (Matrix.GeneralLinearGroup.det a) := by
    rw [hpk]; exact hH p hp a ha k hk
  have hX : ((H (w * nb b) : ℝ≥0) : ℝ) =
      ((∏ w' : NumberField.InfinitePlace D.host.F, GlobalTheory.Doubling.absEw D.host.F D.host.E w'
        (GlobalTheory.Doubling.unitInf D.host.F D.host.E w' (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ) *
      ∏ᶠ v, ((GlobalTheory.Doubling.absEv D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v
        (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ) := by
    rw [hH']
    change ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ≥0) : ℝ) = _
    rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul]
    congr 1
    exact MonoidHom.map_finprod_of_injective NNReal.toRealHom.toMonoidHom NNReal.coe_injective _
  have h1 := hI D n θ hθ w hw nb hnb b p k hp hk hpk a ha
  have h2 := fun v => hF D n w hw nb hnb b p k hp hk hpk a ha v (lam v) (hlam v)
  rw [hX, PositivityTheory.SiegelWeilFormula.Gen.nuA, finprod_congr h2, finprod_inv_distrib, mul_inv]
  congr 1
  exact (eq_inv_of_mul_eq_one_right h1).symm

end PositivityTheory.PfSWUS.SwFockk

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.MemLatVIff
section
noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwFinM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compV_apply (v : HeightOneSpectrum (𝓞 F)) (y : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    compV v y = Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

section Tup

variable {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {n M : ℕ}

theorem mem_latV_iff (Y : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :
    Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v ↔ ∀ a i, Y a i ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v := Iff.rfl

theorem mul_mem_latV {σ : E →ₐ[F] E} (h : PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet σ bs))
    (X : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hX : ∀ i j, X i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v)
    (Y : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (hY : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v) :
    (HMul.hMul (α := Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
      (β := Matrix (Fin n) (Fin M) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) X Y : Fin n → Fin M → _) ∈
      HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v := by
  have hY' := (mem_latV_iff Y).1 hY
  refine (mem_latV_iff _).2 fun j i => ?_
  have e : (HMul.hMul (α := Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
      (β := Matrix (Fin n) (Fin M) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) X Y) j i = ∑ c, X j c * Y c i := rfl
  rw [e]
  have hs : (∑ c, X j c * Y c i) ∈ GlobalTheory.CompanionTheory.RvRingPf.ringOf h :=
    Subring.sum_mem _ fun c _ => Subring.mul_mem _ ((mem_ringOf h _).2 (hX j c)) ((mem_ringOf h _).2 (hY' c i))
  exact (mem_ringOf h _).1 hs

def lmulHomeo (X Xi : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (h1 : X * Xi = 1) (h2 : Xi * X = 1) :
    (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) ≃ₜ (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) where
  toFun Y := (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) X Y : Matrix (Fin n) (Fin M) _)
  invFun Y := (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) Xi Y : Matrix (Fin n) (Fin M) _)
  left_inv Y := by
    show HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) Xi
      (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) X Y) = Y
    exact (Matrix.mul_assoc Xi X (Matrix.of Y)).symm.trans
      (by rw [h2, Matrix.one_mul] : (Xi * X) * Matrix.of Y = Matrix.of Y)
  right_inv Y := by
    show HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) X
      (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) Xi Y) = Y
    exact (Matrix.mul_assoc X Xi (Matrix.of Y)).symm.trans
      (by rw [h1, Matrix.one_mul] : (X * Xi) * Matrix.of Y = Matrix.of Y)
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id

end Tup

section Parts

variable {n M : ℕ}

theorem projV_lmul (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
    (X : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.projV v (fun j i => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (A c j) * X c i) =
      fun j i => ∑ c, PositivityTheory.SiegelWeilFormula.Gen.matV v A c j * HeckeCharacterZeroLocus.SiegelWeilU.projV v X c i := by
  funext j i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.projV, map_sum, map_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (compV_apply v (A c j)).symm

theorem finPart_mul (x : Matrix (Fin M) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
    (A : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    (fun i j => Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) ((x * A) i j)) =
      fun i j => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (A c j) *
        Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (x i c) := by
  funext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, mul_comm]

end Parts

end GlobalTheory.CompanionTheory.SwFinM

end
end

