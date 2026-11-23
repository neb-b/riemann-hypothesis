module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLDirectSumPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertLift

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def sglL (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    v.adicCompletion (maximalRealSubfield L) →ₗ[maximalRealSubfield L] AFplus L where
  toFun := GlobalTheory.InertUmax.sgl L v
  map_add' a b := (GlobalTheory.SplitLift.sgl_add v a b).symm
  map_smul' c r := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    exact (GlobalTheory.SplitLift.alg_mul_sgl v c r).symm

def lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →ₗ[maximalRealSubfield L] AL L :=
  TensorProduct.map LinearMap.id (sglL v)

theorem lift_tmul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : L)
    (r : v.adicCompletion (maximalRealSubfield L)) :
    lift v (a ⊗ₜ r) = a ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v r := rfl

theorem lift_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x y : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    lift v (x * y) = lift v x * lift v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b s =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, lift_tmul, lift_tmul, lift_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.SplitLift.sgl_mul]
    | add y y' hy hy' => rw [mul_add, map_add (f := _), hy, hy', map_add (f := _), mul_add]
  | add x x' hx hx' => rw [add_mul, map_add (f := _), hx, hx', map_add (f := _), add_mul]

theorem compAt_lift_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ReciprocityTheory.Aut.compAt L v (lift v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [lift_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx']

theorem compAt_lift_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hu : u ≠ v)
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ReciprocityTheory.Aut.compAt L u (lift v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [lift_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v r hu, tmul_zero]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', add_zero]

theorem conj_lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    conjAL L (lift v x) =
      lift v (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    rw [lift_tmul, GlobalTheory.SplitLift.conjAL_tmul]
    simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, lift_tmul]
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _)]

def idem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L := lift v 1

theorem lift_mul_idem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (x : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    lift v x * idem v = lift v x := by
  rw [idem, ← lift_mul, mul_one]

end GlobalTheory.InertLift

namespace GlobalTheory.InertLift

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem idem_mul_idem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idem v * idem v = (idem v : AL L) :=
  lift_mul_idem v 1

def glue (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L →+* AL L where
  toFun q := lift v q.1 + (1 - idem v) * q.2
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, mul_one]; rw [← idem]; ring
  map_mul' q q' := by
    simp only [Prod.fst_mul, Prod.snd_mul, lift_mul]
    have h1 := lift_mul_idem v q.1
    have h2 := lift_mul_idem v q'.1
    have h3 := idem_mul_idem v
    linear_combination q'.2 * h1 + q.2 * h2 - (q.2 * q'.2) * h3
  map_zero' := by simp
  map_add' q q' := by simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring

theorem glue_apply (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    glue v q = lift v q.1 + (1 - idem v) * q.2 := rfl

theorem compAt_glue_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    ReciprocityTheory.Aut.compAt L v (glue v q) = q.1 := by
  rw [glue_apply, map_add (f := _), map_mul, map_sub, map_one, idem, compAt_lift_same, compAt_lift_same]; ring

theorem compAt_glue_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hu : u ≠ v)
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    ReciprocityTheory.Aut.compAt L u (glue v q) = ReciprocityTheory.Aut.compAt L u q.2 := by
  rw [glue_apply, map_add (f := _), map_mul, map_sub, map_one, idem, compAt_lift_ne v hu, compAt_lift_ne v hu]; ring

theorem conj_glue (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (q : (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :
    conjAL L (glue v q) = glue v
      (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) q.1,
        conjAL L q.2) := by
  rw [glue_apply, glue_apply, map_add (f := _), map_mul, map_sub, map_one, idem, conj_lift, conj_lift, map_one]

theorem matrix_pair_ext {n : ℕ} {R₁ R₂ : Type*} (A B : Matrix (Fin n) (Fin n) (R₁ × R₂))
    (h₁ : A.map Prod.fst = B.map Prod.fst) (h₂ : A.map Prod.snd = B.map Prod.snd) : A = B :=
  Matrix.ext fun i j => Prod.ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

end GlobalTheory.InertLift

namespace GlobalTheory.InertLift

theorem exists_trivOutside_loc_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w)
    (k : GL (Fin n) (w.adicCompletion L)), k ∈ Formalism.UG.GU Dv.σw n →
      ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k := by
  intro L _ _ _ n v w Dv k hk
  have hk' : Formalism.UG.cT Dv.σw (k : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (k : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      Formalism.UG.antiJ (w.adicCompletion L) n := hk
  set Pm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hPm
  set Pi : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L))
    with hPi
  set km : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (k : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hkm
  set m : Matrix (Fin n) (Fin n) (w.adicCompletion L) := Pm * km * Pi with hm
  have hPP : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : Formalism.UG.cT Dv.σw m * m = 1 := by
    calc Formalism.UG.cT Dv.σw m * m
        = Formalism.UG.cT Dv.σw Pi * ((Formalism.UG.cT Dv.σw km * (Formalism.UG.cT Dv.σw Pm * Pm) * km) * Pi) := by
          simp only [hm, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw Pi * ((Formalism.UG.cT Dv.σw Pm * Pm) * Pi) := by rw [Dv.Panti, hk']
      _ = Formalism.UG.cT Dv.σw (Pm * Pi) * (Pm * Pi) := by simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPP, Formalism.UG.cT_one, Matrix.one_mul]
  have hm1 : m * Formalism.UG.cT Dv.σw m = 1 := mul_eq_one_comm.mp key
  set sig := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) with hsig
  set eR : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L :=
    (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) with heR
  let M : Matrix (Fin n) (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
    m.map Dv.e.symm
  have hMe : M.map eR = m := by
    ext i j; simp [M, heR]
  have hM : M * conjT sig M = 1 := by
    apply Matrix.map_injective (f := eR) Dv.e.injective
    show (M * conjT sig M).map eR = (1 : Matrix (Fin n) (Fin n) _).map eR
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hc : (conjT sig M).map eR = Formalism.UG.cT Dv.σw (M.map eR) := by
      refine Matrix.ext fun i j => ?_
      show eR (sig (M j i)) = Dv.σw (eR (M j i))
      exact Dv.comm _
    rw [hc, hMe, hm1]
  let Z : Matrix (Fin n) (Fin n)
      ((L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :=
    fun i j => (M i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  let W : Matrix (Fin n) (Fin n)
      ((L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) × AL L) :=
    fun i j => (conjT sig M i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  have hZW : Z * W = 1 := by
    apply matrix_pair_ext
    · have e := Matrix.map_mul (L := Z) (M := W)
        (f := RingHom.fst (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) (AL L))
      refine e.trans ?_
      rw [Matrix.map_one _ rfl rfl]
      exact hM
    · have e := Matrix.map_mul (L := Z) (M := W)
        (f := RingHom.snd (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) (AL L))
      refine e.trans ?_
      rw [Matrix.map_one _ rfl rfl]
      exact Matrix.mul_one _
  let X : Matrix (Fin n) (Fin n) (AL L) := Z.map (glue v)
  have hconj : conjT (conjAL L) X = W.map (glue v) := by
    refine Matrix.ext fun i j => ?_
    simp only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]
    rw [conj_glue]
    congr 1
    refine Prod.ext rfl ?_
    simp only [Z, W, Matrix.one_apply, eq_comm]
    split_ifs <;> simp
  have hX : X * conjT (conjAL L) X = 1 := by
    rw [hconj]
    show Z.map (glue v) * W.map (glue v) = 1
    rw [← Matrix.map_mul, hZW, Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin n) (AL L) := ⟨X, conjT (conjAL L) X, hX, mul_eq_one_comm.mp hX⟩
  refine ⟨⟨g, hX⟩, ?_, ?_⟩
  · intro u hu
    have hu' : u ≠ v := hu
    refine Matrix.ext fun i j => ?_
    change ReciprocityTheory.Aut.compAt L u (glue v (Z i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [compAt_glue_ne v hu']
    simp only [Z, Matrix.one_apply]
    split_ifs <;> simp
  · have hb : Formalism.UG.bc (n := Fin n) eR
        (Matrix.GeneralLinearGroup.map (ReciprocityTheory.Aut.compAt L v) g) = Dv.P * k * Dv.P⁻¹ := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      change eR (ReciprocityTheory.Aut.compAt L v (glue v (Z i j))) = m i j
      rw [compAt_glue_same]
      simp [Z, M, heR]
    show Dv.P⁻¹ * Formalism.UG.bc (n := Fin n) eR (Matrix.GeneralLinearGroup.map (ReciprocityTheory.Aut.compAt L v) g) * Dv.P = k
    rw [hb]; group

end GlobalTheory.InertLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicUnitaryEqMulTrivOutsidePlaceAndAtPla
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.PlaceDecomp

theorem decomp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n),
    ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ g = x * y := by
  intro L _ _ _ n v κ
  classical
  set e : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1 with he_def
  have hsgl : GlobalTheory.InertUmax.sgl L v 1 * GlobalTheory.InertUmax.sgl L v 1 = GlobalTheory.InertUmax.sgl L v 1 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    change GlobalTheory.InertUmax.sgl L v 1 w * GlobalTheory.InertUmax.sgl L v 1 w = GlobalTheory.InertUmax.sgl L v 1 w
    rcases eq_or_ne w v with rfl | hw
    · simp only [GlobalTheory.InertUmax.sgl_same, mul_one]
    · simp only [GlobalTheory.InertUmax.sgl_ne L _ _ hw, mul_zero]
  have he2 : e * e = e := by rw [he_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsgl]
  have hce : conjAL L e = e := by simp [he_def, conjAL, Algebra.TensorProduct.map_tmul]
  have hcv : compAt L v e = 1 := by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hcw : ∀ w, w ≠ v → compAt L w e = 0 := fun w hw => by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L _ _ hw, TensorProduct.tmul_zero]
  let θ : AL L × AL L →+* AL L :=
    { toFun := fun q => e * q.1 + (1 - e) * q.2
      map_one' := by simp only [Prod.fst_one, Prod.snd_one]; ring
      map_mul' := fun q q' => by
        simp only [Prod.fst_mul, Prod.snd_mul]
        linear_combination (-(q.1 * q'.1 - q.1 * q'.2 - q.2 * q'.1 + q.2 * q'.2)) * he2
      map_zero' := by simp
      map_add' := fun q q' => by simp only [Prod.fst_add, Prod.snd_add]; ring }
  have hθ : ∀ q, θ q = e * q.1 + (1 - e) * q.2 := fun _ => rfl
  have hθc : ∀ a b, conjAL L (θ (a, b)) = θ (conjAL L a, conjAL L b) := by
    intro a b; rw [hθ, hθ, map_add (f := _), map_mul, map_mul, map_sub, map_one, hce]
  have hθv : ∀ q, compAt L v (θ q) = compAt L v q.1 := by
    intro q; rw [hθ, map_add (f := _), map_mul, map_mul, map_sub, map_one, hcv]; ring
  have hθw : ∀ w, w ≠ v → ∀ q, compAt L w (θ q) = compAt L w q.2 := by
    intro w hw q; rw [hθ, map_add (f := _), map_mul, map_mul, map_sub, map_one, hcw w hw]; ring
  let pr : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) →
      Matrix (Fin n) (Fin n) (AL L × AL L) :=
    fun A B i j => (A i j, B i j)
  have pr_mul : ∀ A B C D, pr A B * pr C D = pr (A * C) (B * D) := by
    intro A B C D; ext i j
    · show (∑ l, pr A B i l * pr C D l j).1 = ∑ l, A i l * C l j
      rw [Prod.fst_sum]; rfl
    · show (∑ l, pr A B i l * pr C D l j).2 = ∑ l, B i l * D l j
      rw [Prod.snd_sum]; rfl
  have pr_one : pr 1 1 = 1 := by
    ext i j <;> by_cases h : i = j <;> simp [pr, Matrix.one_apply, h]
  let M : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) →
      Matrix (Fin n) (Fin n) (AL L) :=
    fun A B => (pr A B).map θ
  have hM : ∀ A B i j, M A B i j = e * A i j + (1 - e) * B i j := fun _ _ _ _ => rfl
  have M_mul : ∀ A B C D, M A B * M C D = M (A * C) (B * D) := by
    intro A B C D; show (pr A B).map θ * (pr C D).map θ = (pr (A * C) (B * D)).map θ
    rw [← Matrix.map_mul, pr_mul]
  have M_one : M 1 1 = 1 := by
    show (pr 1 1).map θ = 1
    rw [pr_one, Matrix.map_one _ (map_zero θ) (map_one θ)]
  have M_conj : ∀ A B, conjT (conjAL L) (M A B) = M (conjT (conjAL L) A) (conjT (conjAL L) B) := by
    intro A B; ext i j
    show conjAL L (θ (A j i, B j i)) = θ (conjAL L (A j i), conjAL L (B j i))
    exact hθc _ _
  have M_diag : ∀ A, M A A = A := by intro A; ext i j; rw [hM]; ring
  set K : Matrix (Fin n) (Fin n) (AL L) := ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
    with hK
  have hKK : K * conjT (conjAL L) K = 1 := κ.2
  have hX : M K 1 * conjT (conjAL L) (M K 1) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  have hY : M 1 K * conjT (conjAL L) (M 1 K) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  let gX : GL (Fin n) (AL L) := ⟨M K 1, conjT (conjAL L) (M K 1), hX, mul_eq_one_comm.mp hX⟩
  let gY : GL (Fin n) (AL L) := ⟨M 1 K, conjT (conjAL L) (M 1 K), hY, mul_eq_one_comm.mp hY⟩
  have hc1 : ∀ w i j, compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro w i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  refine ⟨⟨gX, hX⟩, ⟨gY, hY⟩, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ≠ v := hw
    ext i j
    show compAt L w (θ (K i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) = _
    rw [hθw w hw', hc1]
  · intro w hw
    have hw' : w = v := by simpa using hw
    subst hw'
    ext i j
    show compAt L w (θ ((1 : Matrix (Fin n) (Fin n) (AL L)) i j, K i j)) = _
    rw [hθv, hc1]
  · apply Subtype.ext; apply Units.ext
    show K = M K 1 * M 1 K
    rw [M_mul, Matrix.mul_one, Matrix.one_mul, M_diag]

end GlobalTheory.PlaceDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericLevelCharacterAlternatingSignConjInv
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField Matrix Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodGenericInv

theorem typeSum_inv_eq {K G : Type} [Field K] [Group G] (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) (χ : G → K)
    (hχ : ∀ g h, χ (g * h * g⁻¹) = χ h) (t : G) (ht : ∀ h ∈ P, t * h * t⁻¹ ∈ P)
    (hψ : ∀ (h : G) (hh : h ∈ P), ψ ⟨t * h * t⁻¹, ht h hh⟩ = (ψ ⟨h, hh⟩)⁻¹) :
    ∑ h : P, χ (h : G) * ((((ψ⁻¹) h)⁻¹ : Kˣ) : K) = ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  have hinj : Function.Injective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) := by
    intro a b e
    apply Subtype.ext
    have := congrArg Subtype.val e
    simpa using this
  have hbij : Function.Bijective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) :=
    (Finite.injective_iff_bijective).1 hinj
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Equiv.ofBijective_apply, MonoidHom.inv_apply, inv_inv]
  rw [hχ, hψ h h.2]

def sgnDiag (κ : Type) [CommRing κ] (r : ℕ) : GL (Fin r) κ where
  val := Matrix.diagonal fun i => (-1) ^ i.val
  inv := Matrix.diagonal fun i => (-1) ^ i.val
  val_inv := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem sgnDiag_conj_apply {κ : Type} [CommRing κ] {r : ℕ} (u : GL (Fin r) κ) (i j : Fin r) :
    ((sgnDiag κ r * u * (sgnDiag κ r)⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (-1) ^ i.val * (-1) ^ j.val * (u : Matrix (Fin r) (Fin r) κ) i j := by
  show (Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val) * (u : Matrix (Fin r) (Fin r) κ) *
    Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {κ : Type} [CommRing κ] {r : ℕ}

theorem sgnDiag_conj_mem_unip {u : GL (Fin r) κ} (hu : u ∈ unip κ r) :
    sgnDiag κ r * u * (sgnDiag κ r)⁻¹ ∈ unip κ r := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j h
    rw [sgnDiag_conj_apply, unip_lower hu (show j < i from h), mul_zero]
  · rw [sgnDiag_conj_apply, unip_diag hu i, ← pow_add, ← two_mul, pow_mul]
    simp

theorem edgeSum_sup_conj (u : GL (Fin r) κ) :
    edgeSum supEdge (sgnDiag κ r * u * (sgnDiag κ r)⁻¹) = - edgeSum supEdge u := by
  unfold edgeSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [sgnDiag_conj_apply]
    unfold supEdge at h
    have hs : ((-1 : κ)) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by rw [← mul_pow]; simp
    rw [h, pow_succ]
    linear_combination (-(u : Matrix (Fin r) (Fin r) κ) i j) * hs
  · simp

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}

def alternatingSignDiagonalLevelGroup (Pg : Finset (Pl E)) (r : ℕ) : G0 Pg r := fun PP => sgnDiag (kP PP.1) r

theorem alternatingSignDiagonal_conj_mem_genericLevel (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹ ∈ (P0 Pg r ψ).H := by
  intro PP _
  exact sgnDiag_conj_mem_unip (hx PP (Set.mem_univ _))

theorem genericLevelCharacter_alternatingSign_conj_inv (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    (P0 Pg r ψ).chi ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ = ((P0 Pg r ψ).chi ⟨x, hx⟩)⁻¹ := by
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  show (∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP))
      ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ =
    ((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hx⟩)⁻¹
  rw [prod_apply, prod_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun PP _ => ?_
  apply Units.ext
  simp only [MonoidHom.comp_apply, addCharHom, MonoidHom.coe_toHomUnits, Units.val_inv_eq_inv_val]
  show ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (sgnDiag (kP PP.1) r * x PP * (sgnDiag (kP PP.1) r)⁻¹)))) =
    (ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (x PP)))))⁻¹
  rw [toAdd_ofAdd, toAdd_ofAdd, edgeSum_sup_conj, AddChar.map_neg_eq_inv]

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

theorem level_character_eq_of_eq {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    {L L' : LevelP Pg r LL} (h : L = L') (x : G0 Pg r) (hx : x ∈ L.H) (hx' : x ∈ L'.H) :
    L.chi ⟨x, hx⟩ = L'.chi ⟨x, hx'⟩ := by
  subst h; rfl

end GlobalTheory.GoodGenericInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalStdLatticeStabilizerMemMaxCompact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertStdLat.loc_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (κ : GAf L n), κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
  GlobalTheory.InertKU.loc_mem_KU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLDirectSumPotSemistableStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (a b : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (r' : ↥(Dec (F := E) A) →* GL (Fin b) (Om l)), GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw r' → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') → GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.sumRep r r') = (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpSum (GlobalTheory.Pst.wdAt P ι Bw h hj r') := by
  first | exact @GlobalTheory.Pst.SumParam.wdAt_sumRep | exact GlobalTheory.Pst.SumParam.wdAt_sumRep | (intros; apply GlobalTheory.Pst.SumParam.wdAt_sumRep <;> assumption)
end

